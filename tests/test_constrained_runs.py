"""constrained_runs against brute-force enumeration of drivers, direct simulation of the single cell, and explicit
searches of the outer window automaton."""

from __future__ import annotations

import itertools
import random

import numpy as np

from computations.constrained_runs import (admissible_run_hist, carry_check, constrained_states, constrained_table,
                                           future_sets, residual_classes, state_depletion, uniform_run_hist,
                                           valuation, window_infinite_run, window_longest_run)
from computations.rule30 import spacetime

T = 12


def naive_step(cells: list[int], c: int) -> list[int]:
    """One step of the left half held as a list (element k - 1 is cell -k), cell by cell, with center c."""
    right = [c] + cells  # cells 0, -1, -2, ...
    return [(cells[k + 1] if k + 1 < len(cells) else 0) ^ (right[k + 1] | right[k]) for k in range(len(cells))]


def admissible(word: tuple[int, ...]) -> bool:
    """Whether c(0) .. c(n - 1) obeys c(u + 1) = not cell -1 at u whenever c(u) = 1, by direct simulation."""
    cells = [0] * (len(word) + 2)
    for u in range(len(word) - 1):
        if word[u] == 1 and word[u + 1] != 1 - cells[0]:
            return False
        cells = naive_step(cells, word[u])
    return word[0] == 1


def brute_states() -> dict[int, set[tuple[tuple[int, ...], int]]]:
    """Every (left half at t, c(t)) for t <= T over every driver word c(0) .. c(T) with c(0) = 1, kept while the
    prefix c(0) .. c(t) is admissible. Every admissible prefix extends, so this is every reachable state."""
    out: dict[int, set[tuple[tuple[int, ...], int]]] = {t: set() for t in range(T + 1)}
    for tail in itertools.product((0, 1), repeat=T):
        c = (1,) + tail
        cells = [0] * (T + 2)
        for t in range(T + 1):
            out[t].add((tuple(cells[:T]), c[t]))
            if t == T or (c[t] == 1 and c[t + 1] != 1 - cells[0]):
                break
            cells = naive_step(cells, c[t])
    return out


BRUTE = brute_states()


def as_tuple(row: np.ndarray, width: int) -> tuple[int, ...]:
    # row: (W,) uint64
    return tuple((int(row[k // 64]) >> (k % 64)) & 1 for k in range(width))


def test_states_match_brute_force() -> None:
    for t, B, C in constrained_states(T):
        got = {(as_tuple(B[i], T), int(C[i])) for i in range(len(B))}
        assert got == BRUTE[t], t


def test_single_cell_state_is_reachable() -> None:
    steps, half = 48, 50
    width = 2 * steps + 2 * half + 3
    row = np.zeros(width, dtype=np.uint8)  # (width,)
    row[width // 2] = 1
    st = spacetime(row, steps)  # (steps + 1, width)
    for t, B, C in constrained_states(steps):
        left = sum(int(st[t, width // 2 - k]) << (k - 1) for k in range(1, t + 1))
        center = int(st[t, width // 2])
        assert any(int(B[i, 0]) == left and int(C[i]) == center for i in range(len(B))), t


def brute_black_run(cells: list[int]) -> int:
    """The black run from a state with c = 1: the center stays black while cell -1 is white."""
    run = 1
    cells = cells + [0] * 4
    while cells[0] == 0:
        cells = naive_step(cells, 1)
        run += 1
    return run


def test_table_and_depletion_match_brute_force() -> None:
    rows = {r.t: r for r in constrained_table(T, compare=True)}
    deps = {d.t: d for d in state_depletion([8, T])}
    for t in range(1, T + 1):
        black = [brute_black_run(list(x[:t])) for x, c in BRUTE[t] if c == 1]
        assert rows[t].states == len(BRUTE[t])
        assert rows[t].rows == len({x for x, _ in BRUTE[t]})
        assert rows[t].black == max(black, default=0)
        # the constraint only removes left halves and runs
        assert rows[t].rows <= rows[t].free_rows and rows[t].black <= rows[t].free_black
        assert rows[t].white <= rows[t].free_white
        if t in deps and black:
            assert deps[t].black_states == len(black)
            assert deps[t].counts == {r: sum(b >= r for b in black) for r in range(1, max(black) + 1)}


def brute_futures(prefix: tuple[int, ...], k: int) -> frozenset[tuple[int, ...]]:
    return frozenset(u for u in itertools.product((0, 1), repeat=k) if admissible(prefix + u))


def test_residual_classes_match_brute_force() -> None:
    # distinct length-k future sets over every admissible prefix c(0) .. c(t), t <= 8, by direct simulation
    prefixes = [p for n in range(1, 10) for p in itertools.product((0, 1), repeat=n) if admissible(p)]
    got = {r.k: r.classes for r in residual_classes(8, [1, 2, 3, 4])}
    for k in (1, 2, 3, 4):
        assert got[k] == len({brute_futures(p, k) for p in prefixes}), k
    # the window reduction: the future of a state is that of its k-cell window
    for x, c in list(BRUTE[6])[:20]:
        win = sum(b << j for j, b in enumerate(x[:4]))
        fs = future_sets(np.array([win], dtype=np.uint64), np.array([c], dtype=np.uint8), 4)[0]  # (16,)
        cells = list(x) + [0, 0, 0, 0]
        direct = []
        for u in itertools.product((0, 1), repeat=4):
            word, ok, cur = (c,) + u, True, cells
            for j in range(4):
                if word[j] == 1 and word[j + 1] != 1 - cur[0]:
                    ok = False
                    break
                cur = naive_step(cur, word[j])
            direct.append(ok)
        assert fs.tolist() == direct
    # 2^k + 1 classes once every window is reached
    got5 = [(r.classes, r.white_classes) for r in residual_classes(30, [2, 3, 4, 5])]
    assert got5 == [(5, 2), (9, 4), (17, 8), (33, 16)]


def brute_window_run(w: int, n: int) -> int:
    """Longest black run within n steps of the outer automaton on w cells, by explicit search over the free cells and
    free centers, with the window held as a list."""
    best = 1
    frontier = {((0,) * w, 1, 1)}  # (window, center, trailing black run)
    for _ in range(n):
        nxt = set()
        for x, c, tr in frontier:
            for free in (0, 1):
                y = tuple(naive_step(list(x) + [free], c)[:w])
                for d in ((0, 1) if c == 0 else (1 - x[0],)):
                    nxt.add((y, d, tr + 1 if d else 0))
        frontier = nxt
        best = max(best, max(tr for _, _, tr in frontier))
    return best


def test_window_automaton() -> None:
    for w in (3, 4, 6):
        runs = window_longest_run(w, 60)  # (60,)
        assert [int(runs[n - 1]) for n in range(1, 13)] == [brute_window_run(w, n) for n in range(1, 13)]
        a, windows = window_infinite_run(w)
        # an endless black run from time a gives runs of n - a + 1 within n steps
        assert int(runs[59]) == 60 - a + 1
        # the only window that keeps it is the alternating one, cell -j black exactly for even j
        assert windows == [sum(1 << (j - 1) for j in range(2, w + 1, 2))]


def test_carry_valuation() -> None:
    rng = random.Random(3)
    for _ in range(2000):
        n = rng.getrandbits(rng.randint(1, 40))
        alt = 0
        while (n >> alt) & 1 == alt % 2:  # bit j of -2/3 is j mod 2
            alt += 1
        assert valuation(3 * n + 2) == alt
    m, total = carry_check(700, half=40)
    assert m == total > 250


def test_run_histograms() -> None:
    for n in range(1, 11):
        adm = np.zeros(n + 1, dtype=np.int64)  # (n + 1,)
        uni = np.zeros(n + 1, dtype=np.int64)  # (n + 1,)
        for tail in itertools.product((0, 1), repeat=n - 1):
            word = (1,) + tail
            longest = max(len(s) for s in "".join(map(str, word)).split("0"))
            uni[longest] += 1
            if admissible(word):
                adm[longest] += 1
        assert np.array_equal(admissible_run_hist(n), adm) and np.array_equal(uniform_run_hist(n), uni), n
