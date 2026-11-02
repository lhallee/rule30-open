"""driver_density against enumeration of admissible drivers, cell-by-cell simulation and the single cell."""

from __future__ import annotations

import random

import numpy as np

from computations.constrained_runs import constrained_states
from computations.driver_density import (admissible_drivers, brute_best, chain_beam, driver_dp, follow_lengths,
                                         greedy_driver, lifetimes, primitive_words, reentry, run_lengths,
                                         run_start_domains, state_features)
from computations.rule30 import center_column
from computations.run_mechanism import driven_step


def naive_step(cells: list[int], c: int) -> list[int]:
    """One step of the left half held as a list (element k - 1 is cell -k), cell by cell, with center c."""
    right = [c] + cells
    return [(cells[k + 1] if k + 1 < len(cells) else 0) ^ (right[k + 1] | right[k]) for k in range(len(cells))]


def admissible(word: list[int]) -> bool:
    cells = [0] * (len(word) + 2)
    for u in range(len(word) - 1):
        if word[u] == 1 and word[u + 1] != 1 - cells[0]:
            return False
        cells = naive_step(cells, word[u])
    return word[0] == 1


def naive_follow(word: list[int], w: str, horizon: int) -> int:
    """Letters of w (best phase) that an admissible continuation of `word` takes from its last letter on."""
    best = 0
    for ph in range(len(w)):
        if int(w[ph]) != word[-1]:
            continue
        n = 1
        while n < horizon and admissible(word + [int(w[(ph + s) % len(w)]) for s in range(1, n + 1)]):
            n += 1
        best = max(best, n)
    return best


def test_dp_matches_enumeration() -> None:
    rows = list(driver_dp(12, forks=(5,), track=True))
    for T in range(13):
        assert rows[T].best == brute_best(T)
        d = rows[T].driver
        assert d is not None and sum(d) == rows[T].best and admissible(d)
    words = list(admissible_drivers(13))
    assert all(admissible(list(w)) for w in words)
    assert rows[12].gains[5] == max(sum(w[5:]) for w in words)


def test_beam_against_dp() -> None:
    exact = [r.best for r in driver_dp(30)]
    assert [r.best for r in driver_dp(30, beam=10_000)] == exact
    narrow = list(driver_dp(30, beam=6, track=True))
    assert all(r.best <= e for r, e in zip(narrow, exact))
    assert admissible(narrow[-1].driver or []) and sum(narrow[-1].driver or []) == narrow[-1].best
    assert [r.best for r in chain_beam(30, 10_000, ["110", "11110"], min_len=3)] == exact
    assert all(r.best <= e for r, e in zip(chain_beam(30, 6, ["110"], min_len=3), exact))


def test_single_cell_is_below() -> None:
    col = [int(a) for a in center_column(61)]
    greedy = greedy_driver(60)
    assert admissible(col) and admissible(greedy)
    for r in driver_dp(60, forks=(20,)):
        assert sum(col[:r.t + 1]) <= r.best and sum(greedy[:r.t + 1]) <= r.best
        if r.t >= 20:
            assert sum(col[20:r.t + 1]) <= r.gains[20]


def test_lifetimes_against_simulation() -> None:
    rng = random.Random(3)
    words = ["110", "11110", "11010"]
    for t, B, C in constrained_states(9):
        if t == 9:
            got = {w: follow_lengths(B, C, w, 30) for w in words}
    drivers = list(admissible_drivers(10))
    for w in words:
        assert max(naive_follow(list(d), w, 30) for d in drivers) == int(got[w].max())
    row = next(lifetimes(9, 9, words, 30))
    assert row.lengths == {w: int(got[w].max()) for w in words}
    for d in rng.sample(drivers, 8):
        X = np.zeros((1, 1), dtype=np.uint64)  # (1, 1), the state that d reaches at time 9
        for u in range(9):
            X = driven_step(X, d[u])
        for w in words:
            assert follow_lengths(X, np.array([d[-1]], np.uint8), w, 30)[0] == naive_follow(list(d), w, 30)
    assert primitive_words(4, 0.6) == ["1", "110", "1110"]


def int_step(x: int, c: int) -> int:
    """One step of the left half held as an int (bit k - 1 is cell -k), with center c."""
    return (x >> 1) ^ (x | (x << 1) | c)


def int_successors(x: int, c: int) -> list[tuple[int, int]]:
    return [(int_step(x, c), d) for d in ((1 - (x & 1),) if c else (0, 1))]


def int_follow(x: int, c: int, w: str, ph: int) -> tuple[int, tuple[int, int], int]:
    """Letters of w from phase ph taken from state (x, c), the state where the stretch ends and its black letters."""
    n, black = 0, 0
    while True:
        n += 1
        black += c
        nxt = int(w[(ph + n) % len(w)])
        if c == 1 and 1 - (x & 1) != nxt:
            return n, (int_step(x, 1), 1 - (x & 1)), black
        x, c = int_step(x, c), nxt


def naive_reentry(w: str, t: int,
                  gmax: int) -> tuple[int, int, list[tuple[int, int] | None], dict[tuple[int, int], int]]:
    """l_w(t), the number of stretch ends, (least gap, most black cells in it) from each end and the stretch black
    count per end."""
    layer = {(0, 1)}
    for _ in range(t):
        layer = {s for x, c in layer for s in int_successors(x, c)}
    runs = [int_follow(x, c, w, ph) + (c,) for x, c in layer for ph in range(len(w)) if int(w[ph]) == c]
    L = max(r[0] for r in runs)
    ends: dict[tuple[int, int], int] = {}
    for n, e, black, _ in runs:
        if n == L:
            ends[e] = max(black, ends.get(e, 0))

    def life(x: int, c: int) -> int:
        return max(int_follow(x, c, w, ph)[0] for ph in range(len(w)) if int(w[ph]) == c)

    gaps: list[tuple[int, int] | None] = []
    for e in ends:
        front: dict[tuple[int, int], int] = {e: 0}  # state -> most black cells from the end up to before it
        g = None
        for k in range(gmax + 1):
            hits = [b for (x, c), b in front.items() if life(x, c) >= (L + 1) // 2]
            if hits:
                g = (k, max(hits))
                break
            nxt: dict[tuple[int, int], int] = {}
            for (x, c), b in front.items():
                for s in int_successors(x, c):
                    nxt[s] = max(nxt.get(s, 0), b + c)
            front = nxt
        gaps.append(g)
    return L, len(ends), gaps, ends


def test_reentry_and_runs() -> None:
    for w, t in (("110", 12), ("11110", 20), ("11111110", 20), ("11010", 16), ("110", 40)):
        r = reentry(w, t, gmax=20)
        L, n_ends, gaps, ends = naive_reentry(w, t, 20)
        found = [g for g in gaps if g is not None]
        assert (r.length, r.ends) == (L, n_ends)
        assert r.gap == min(g for g, _ in found)
        assert r.gap_max == (None if None in gaps else max(g for g, _ in found))
        assert r.gap_black in [b for g, b in found if g == r.gap]
        assert r.stretch_black in ends.values()
    assert run_lengths([1, 1, 0, 1, 0, 0, 1]) == ([2, 1, 1], [1, 2])
    col = [int(a) for a in center_column(80)]
    for a, L, reach in run_start_domains(col):
        assert L == reach or a + L == len(col)


def pack(bits: list[int]) -> np.ndarray:
    return np.array([[sum(b << k for k, b in enumerate(bits))]], dtype=np.uint64)  # (1, 1)


def test_features_against_lists() -> None:
    rng = random.Random(5)
    for _ in range(20):
        cells = [rng.randint(0, 1) for _ in range(64)]  # element k - 1 is cell -k
        single = [rng.randint(0, 1) for _ in range(64)]
        c = rng.randint(0, 1)
        f = state_features(pack(cells), np.array([c], np.uint8), pack(single)[0])[0]
        d1 = 1
        while d1 < 64 and cells[d1] != cells[d1 - 1]:
            d1 += 1
        d2 = 1
        while d1 + d2 < 64 and cells[d1 + d2] != cells[d1 + d2 - 1]:
            d2 += 1
        agree = 0
        while agree < 64 and cells[agree] == single[agree]:
            agree += 1
        want = [c, c * cells[0], d1, d2, d1 if c == 1 and cells[0] == 0 else 0, agree] + cells[:20] + [sum(cells[20:40])]
        assert list(f) == want
