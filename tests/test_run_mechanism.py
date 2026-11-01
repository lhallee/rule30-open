"""run_mechanism against direct simulation, exhaustive enumeration and brute-force preimages."""

from __future__ import annotations

import itertools

import numpy as np

from computations.rule30 import center_column, spacetime
from computations.run_mechanism import (alternating_left, black_reach, center_window, class_black_max, far_periods, driven_rows, driver_bits,
                                        forced_cells, maximal_runs, preimages, mechanism, naive_left_half, white_reach,
                                        window_cells)


def single_rows(steps: int, half: int) -> np.ndarray:
    width = 2 * steps + 2 * half + 3
    cells = np.zeros(width, dtype=np.uint8)  # (width,)
    cells[width // 2] = 1
    st = spacetime(cells, steps)  # (steps + 1, width)
    return st[:steps, width // 2 - half: width // 2 + half + 1]  # (steps, 2 * half + 1)


def test_center_window() -> None:
    half = 20
    cells = window_cells(center_window(400, half), half)  # (400, 41)
    assert np.array_equal(cells[:, half], center_column(400))
    assert np.array_equal(cells, single_rows(400, half))


def test_maximal_runs() -> None:
    col = np.array([1, 1, 0, 1, 0, 0, 0, 1, 1], dtype=np.uint8)
    starts, lengths, colors = maximal_runs(col)
    assert starts.tolist() == [0, 2, 3, 4] and lengths.tolist() == [2, 1, 1, 3] and colors.tolist() == [1, 0, 1, 0]


def test_run_identities() -> None:
    m = mechanism(3000, half=40, min_len=6, progress=False)
    assert m.black_identity_failures == 0 and m.white_identity_failures == 0
    # each maximal black run is the alternating stretch of its first row, checked directly on a few runs
    cells = single_rows(300, 40)
    starts, lengths, colors = maximal_runs(cells[:, 40])
    for a, L, c in zip(starts[1:].tolist(), lengths[1:].tolist(), colors[1:].tolist()):
        if c == 1:
            assert alternating_left(cells, 40, a) == L


def test_driven_rows_exhaustive() -> None:
    # every left half reachable at time t is the left half of some driver, computed cell by cell
    for t, B, D in driven_rows(9):
        rows = {tuple(int((int(B[i, 0]) >> k) & 1) for k in range(t)) for i in range(len(B))}
        naive = {tuple(naive_left_half([1] + list(d))) for d in itertools.product([0, 1], repeat=t - 1)}
        assert rows == naive
        for i in range(len(B)):
            assert tuple(naive_left_half(driver_bits(D[i], t))) == tuple(int((int(B[i, 0]) >> k) & 1)
                                                                          for k in range(t))


def test_single_cell_is_reachable() -> None:
    steps, half = 60, 64
    cells = single_rows(steps + 1, half)  # (steps + 1, 129)
    for t, B, _ in driven_rows(steps):
        if t % 15:
            continue
        real = sum(int(cells[t, half - k]) << (k - 1) for k in range(1, t + 1))
        assert real in {int(B[i, 0]) for i in range(len(B))}
        # the bound covers the single cell's runs
        assert black_reach(B, t).max() >= alternating_left(cells, half, t)


def class_runs(a: int, extra: int) -> tuple[int, int]:
    """Longest black and white run of column 0 from time a over every row with the cells left of 0 white, cell 0 black
    and cells 1 .. a + extra free (direct simulation, of every row at once as the rows of one array)."""
    T = a + extra
    width = 2 * T + a + extra + 4
    c0 = T + 1
    free = np.array(list(itertools.product([0, 1], repeat=a + extra)), dtype=bool)  # (m, a + extra)
    rows = np.zeros((free.shape[0], width), dtype=bool)  # (m, width)
    rows[:, c0] = True
    rows[:, c0 + 1: c0 + 1 + a + extra] = free
    col = [rows[:, c0]]  # each (m,)
    for _ in range(T):
        left = np.concatenate([np.zeros((rows.shape[0], 1), dtype=bool), rows[:, :-1]], axis=1)  # (m, width)
        right = np.concatenate([rows[:, 1:], np.zeros((rows.shape[0], 1), dtype=bool)], axis=1)  # (m, width)
        rows = left ^ (rows | right)
        col.append(rows[:, c0])
    after = np.stack(col, axis=1)[:, a:]  # (m, T + 1 - a), column 0 from time a
    best = []
    for color in (False, True):
        differs = after != color  # (m, T + 1 - a)
        runs = np.where(differs.any(axis=1), differs.argmax(axis=1), differs.shape[1])  # (m,), the leading run
        best.append(int(runs.max()))
    return best[1], best[0]


def test_driven_bounds_cover_the_class() -> None:
    table = {t: (B, black_reach(B, t).max(), white_reach(B, t, t + 6).max()) for t, B, _ in driven_rows(7)}
    for a in (4, 6):
        b, w = class_runs(a, 6)
        assert b == class_black_max(a)
        assert b <= table[a][1]
        assert w <= table[a][2]


def brute_forced(word: list[int], s: int) -> set[int]:
    """Positions (relative to the word) on which all s-step preimages agree, by forward evaluation of every word, all
    at once as the rows of one array."""
    n = len(word)
    rows = np.array(list(itertools.product([0, 1], repeat=n + 2 * s)), dtype=np.uint8)  # (2^(n + 2s), n + 2s)
    image = rows
    for _ in range(s):
        image = image[:, :-2] ^ (image[:, 1:-1] | image[:, 2:])
    arr = rows[(image == np.array(word, dtype=np.uint8)).all(axis=1)]  # (m, n + 2s)
    return {i - s for i in np.nonzero(np.all(arr == arr[0], axis=0))[0].tolist()}


def test_forced_cells() -> None:
    for word in ([0, 1] * 5, [1, 0] * 5, [1] * 9, [0] * 9):
        for s, iv in enumerate(forced_cells(word, 2), start=1):
            fast = {x for lo, hi in iv for x in range(lo, hi + 1)}
            assert fast == brute_forced(word, s)
    alt = [(i + 1) % 2 for i in range(39, -1, -1)]  # ends black at cell 39
    assert forced_cells(alt, 3)[2] == [(-3, 39 - 12)]
    assert forced_cells([1] * 40, 2) == [[], []]


def test_far_periods() -> None:
    # one step back, a black block comes from the period-3 words 100 100 ... in its three phases
    assert far_periods([1] * 60, 1) == [{3}]
    rows = preimages(np.ones((1, 30), dtype=np.uint8))  # (4, 32)
    for r in rows:
        left = "".join(map(str, r[:24].tolist()))
        assert left in {("100" * 8)[i:i + 24] for i in range(3)} | {("100" * 9)[i:i + 24] for i in range(3)}
