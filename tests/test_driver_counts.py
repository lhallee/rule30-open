"""driver_counts against enumeration of admissible words, the count over every left half, the center column with
column 1 random, the max-plus program of driver_density and an independent count of admissible words."""

from __future__ import annotations

import itertools
import math
import random
from collections.abc import Sequence
from fractions import Fraction

import numpy as np

from computations import driver_counts as dc
from computations.constrained_runs import admissible_run_hist
from computations.driver_density import driver_dp
from computations.rule30 import center_column


def naive_step(cells: list[int], c: int) -> list[int]:
    """One step of the left half held as a list (element k - 1 is cell -k, white beyond), cell by cell, center c."""
    right = [c] + cells
    return [(cells[k + 1] if k + 1 < len(cells) else 0) ^ (right[k + 1] | right[k]) for k in range(len(cells))]


def admissible_from(word: Sequence[int], half: list[int]) -> bool:
    """Whether `word` obeys c(t + 1) = not x_{-1}(t) at every black c(t), with the half driven by the word."""
    cells = half
    for t in range(len(word) - 1):
        if word[t] == 1 and word[t + 1] != 1 - cells[0]:
            return False
        cells = naive_step(cells, word[t])
    return True


def enumerate_counts(nmax: int, half: list[int]) -> list[list[int]]:
    """counts[n][b]: the admissible words of length n from `half` with b black cells among c(0 .. n - 2), by listing
    every admissible word depth first, the half stepped cell by cell."""
    counts = [[0] * (n + 1) for n in range(nmax + 1)]

    def go(word: list[int], cells: list[int]) -> None:
        counts[len(word)][sum(word[:-1])] += 1
        if len(word) == nmax:
            return
        nxt = naive_step(cells, word[-1])
        for d in ((1 - cells[0],) if word[-1] == 1 else (0, 1)):
            go(word + [d], nxt)

    go([1], half)
    return counts


def test_counts_against_enumeration() -> None:
    rng = random.Random(5)
    half = [rng.randint(0, 1) for _ in range(64)]
    for start, cells in ((None, [0] * 20), (dc.pack_half(half, 14), half[:20])):
        listed = enumerate_counts(14, cells)
        layers = list(dc.count_layers(14, start))
        assert [layer.n for layer in layers] == list(range(1, 15))
        assert all(layer.counts == listed[layer.n][:layer.n] for layer in layers)
        for n in range(2, 15):  # every word, not only the admissible branches
            every = [0] * n
            for tail in itertools.product((0, 1), repeat=n - 1):
                if admissible_from((1,) + tail, cells):
                    every[1 + sum(tail[:-1])] += 1
            assert every == layers[n - 1].counts


def test_counting_lemma_and_first_moment() -> None:
    # every word w is admissible from exactly 2^((n - 1) - b(w)) of the fillings of the cells -1 .. -(n - 1)
    for n in range(2, 11):
        halves = np.arange(1 << (n - 1), dtype=np.uint64)  # (2^(n - 1),), bit k - 1 is cell -k
        for tail in itertools.product((0, 1), repeat=n - 1):
            word = (1,) + tail
            x = halves.copy()  # (2^(n - 1),)
            ok = np.ones(len(x), dtype=bool)  # (2^(n - 1),)
            for t in range(n - 1):
                if word[t]:
                    ok &= (x & np.uint64(1)) == np.uint64(1 - word[t + 1])
                x = (x >> np.uint64(1)) ^ (x | (x << np.uint64(1)) | np.uint64(word[t]))
            assert int(ok.sum()) == 2 ** ((n - 1) - sum(word[:-1]))
    # so the counts summed over every left half are 2^(n - 1) E_n(b), and the densest admissible word B_n obeys the
    # union bound and the tail bound of Theorem 2 exactly over the fillings
    d, kappa = dc.threshold()
    for n in range(2, 9):
        total = [0] * n
        densest = []
        for bits in itertools.product((0, 1), repeat=n - 1):
            counts = dc.word_counts(n, dc.pack_half(list(bits), n))
            total = [a + v for a, v in zip(total, counts)]
            densest.append(max(b for b, v in enumerate(counts) if v > 0))
        assert total == [int(2 ** (n - 1) * dc.mean_count(n, b)) for b in range(n)]
        for k in range(1, n):
            share = Fraction(sum(B >= k for B in densest), 2 ** (n - 1))
            assert share <= sum(dc.mean_count(n, b) for b in range(k, n))
            a = k - 1 - d * (n - 2)
            if a >= 0:
                assert float(share) <= 2 ** (-kappa * a) / (1 - 2 ** -kappa)
    for n in range(2, 40):
        assert sum(dc.mean_count(n, b) for b in range(n)) == Fraction(3, 2) ** (n - 2)


def column_one_run(half: list[int], y: Sequence[int]) -> list[int]:
    """c(0) = 1, then c(t + 1) = x_{-1}(t) xor (c(t) or y(t)), the half driven by c and stepped cell by cell."""
    cells, word = half, [1]
    for t in range(len(y)):
        cells, nxt = naive_step(cells, word[-1]), cells[0] ^ (word[-1] | y[t])
        word.append(nxt)
    return word


def test_column_one_random() -> None:
    """With the white left half and column 1 replaced by every word y, c(t + 1) = x_{-1}(t) xor (c(t) or y(t)) gives
    N_n(b) 2^b of the 2^(n - 1) words y with b black cells among c(0 .. n - 2); with every left half as well, it gives
    every word c(0) = 1, c(1 .. n - 1) equally often."""
    for n in range(2, 12):
        got = [0] * n
        for y in itertools.product((0, 1), repeat=n - 1):
            got[sum(column_one_run([0] * (n + 2), y)[:-1])] += 1
        assert got == [v << b for b, v in enumerate(dc.word_counts(n))]
    for n in range(2, 8):
        seen: dict[tuple[int, ...], int] = {}
        for bits in itertools.product((0, 1), repeat=n - 1):
            for y in itertools.product((0, 1), repeat=n - 1):
                word = tuple(column_one_run(list(bits) + [0] * 3, y))
                seen[word] = seen.get(word, 0) + 1
        assert len(seen) == 2 ** (n - 1) and set(seen.values()) == {2 ** (n - 1)}


def test_keep_cells() -> None:
    rng = np.random.default_rng(1)
    X = rng.integers(0, 2, size=(5, 192), dtype=np.uint64)  # (5, 192), cell -(k + 1) in column k
    packed = np.zeros((5, 3), dtype=np.uint64)  # (5, 3)
    for k in range(192):
        packed[:, k // 64] |= X[:, k] << np.uint64(k % 64)
    for cells in (-1, 0, 1, 5, 63, 64, 65, 127, 128, 150, 191, 192, 300):
        kept = dc.keep_cells(packed, cells)  # (5, 3)
        for k in range(192):
            bit = (kept[:, k // 64] >> np.uint64(k % 64)) & np.uint64(1)
            assert (bit == (X[:, k] if k < cells else 0)).all()


def test_ratios_and_quoted_numbers() -> None:
    result = dc.sweep(70, 20)
    rows = {r.n: r for r in result.rows}
    assert all(r.mass == 1 for r in result.rows) and result.last == dc.word_counts(70)
    for n in range(3, 23):  # an independent dynamic program over (half, center, current run, longest run)
        assert rows[n].total == int(admissible_run_hist(n).sum())
    r = rows[40]
    assert r.total == 3_774_663  # the count quoted in driven-left-runs
    assert (r.top_b, r.tail_b, r.densest, r.mean_densest) == (20, 27, 27, 29)
    assert round(float(r.top), 4) == 1.14 and round(float(r.tail or 0), 4) == 0.2231
    assert result.top[1:] == (23, 12) and round(float(result.top[0]), 4) == 1.3471
    assert result.tail[1:] == (52, 35) and round(float(result.tail[0]), 4) == 0.6839
    # the largest ratio below n = 20 is one word, the single cell's column 1101110
    assert result.small == (Fraction(16, 5), 7, 5)
    dense = [(1,) + w for w in itertools.product((0, 1), repeat=6) if sum(w[:5]) == 4]
    assert [w for w in dense if admissible_from(w, [0] * 9)] == [tuple(int(v) for v in center_column(7))]
    # the densest word of each length is the max-plus count of driver_density (two 64-bit words from n = 64 on)
    best = [row.best for row in driver_dp(68)]
    assert all(r.densest == best[r.n - 2] for r in result.rows)


def test_first_moment_bound() -> None:
    d, kappa = dc.threshold()
    assert abs(dc.entropy(d) - d) < 1e-12 and round(d, 7) == 0.7729078 and round(kappa, 4) == 2.767
    # the dual form: min over s > 0 of log2(1 + 2^(s - 1)) / s is d*, attained at s = kappa
    s = np.linspace(0.01, 10, 99_901)  # (99901,)
    f = np.log2(1 + 2 ** (s - 1)) / s  # (99901,)
    assert abs(f.min() - d) < 1e-7 and abs(s[f.argmin()] - kappa) < 1e-3
    for n in range(2, 120):  # E_n(b) <= 2^(-kappa (b - 1 - d* (n - 2))), the tangent bound of the proof
        for b in range(1, n):
            assert math.log2(dc.mean_count(n, b)) <= -kappa * (b - 1 - d * (n - 2)) + 1e-9


def test_best_from() -> None:
    assert dc.best_from(70) == [row.best for row in driver_dp(70)]
    rng = random.Random(11)
    half = [rng.randint(0, 1) for _ in range(64)]
    start = dc.pack_half(half, 40)
    exact = dc.best_from(40, start)
    for T in range(12):  # every word from the same half, stepped cell by cell
        words = [(1,) + w for w in itertools.product((0, 1), repeat=T) if admissible_from((1,) + w, half[:20])]
        assert exact[T] == max(sum(w) for w in words)
    for T in range(1, 30):  # the max-plus count against the densest word of the counts, from the same half
        assert exact[T] == max(b for b, v in enumerate(dc.word_counts(T + 2, dc.pack_half(half, T + 2))) if v > 0)
    narrow = dc.best_from(40, start, beam=8)
    assert all(a <= e for a, e in zip(narrow, exact)) and dc.best_from(40, start, beam=10**6) == exact
