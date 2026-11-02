"""run_slope_routes against cell-by-cell simulation of every driver, a tuple-based search and the space-time diagram."""

from __future__ import annotations

import itertools
from collections import deque

import numpy as np

from computations.rule30 import spacetime
from computations.run_slope_routes import (alternating_word, driver_pairs, first_times_by_width, onset_bound,
                                           right_end_first_times, settled_slope, skeleton, skeleton_from_table,
                                           white_followers, window_game_distances)


def left_history(driver: list[int], steps: int) -> list[int]:
    """Rows 0 .. steps - 1 of the left half driven by `driver` (zeros after it), each as one integer whose bit k - 1 is
    cell -k, stepped cell by cell at once by the rule on integers."""
    width = steps + 8
    rows = [0]
    for t in range(steps - 1):
        c = driver[t] if t < len(driver) else 0
        r = rows[-1]
        rows.append(((r >> 1) ^ (r | (r << 1) | c)) & ((1 << width) - 1))  # cell -k from cells -k - 1, -k, -k + 1
    return rows


def test_right_ends_against_every_driver() -> None:
    width, steps = 5, 11
    first = right_end_first_times(width, steps)  # (32,)
    brute = {}
    for t in range(1, steps + 1):
        for tail in itertools.product([0, 1], repeat=t - 1):
            word = left_history([1, *tail], t + 1)[t] & ((1 << width) - 1)
            brute.setdefault(word, t)
    assert {w: int(f) for w, f in enumerate(first) if f >= 0} == brute


def test_right_end_numbers() -> None:
    table = first_times_by_width(right_end_first_times(10, 50), 10)
    assert table[-1] == (10, 0, 47, 37)  # quoted in the entry (w = 10)
    assert [alt for _, _, _, alt in table[3:8]] == [5, 13, 16, 25, 28]


def game_distance_brute(width: int) -> int:
    """Breadth-first search on tuples: cells -1 .. -width, a free driver and a free entering cell."""
    start = (0,) * width
    target = tuple(1 if (k + 1) % 2 == 0 else 0 for k in range(width))
    seen = {start: 0}
    queue = deque([start])
    while queue:
        x = queue.popleft()
        if x == target:
            return seen[x]
        for c, e in itertools.product([0, 1], repeat=2):
            y = tuple((x[k + 1] if k + 1 < width else e) ^ (x[k] | (x[k - 1] if k else c)) for k in range(width))
            if y not in seen:
                seen[y] = seen[x] + 1
                queue.append(y)
    return -1


def test_window_game() -> None:
    for w in (2, 4, 6, 8):
        d = window_game_distances(w)
        assert d[alternating_word(w)] == game_distance_brute(w)
        assert (d >= 0).all()
    assert [int(window_game_distances(w)[alternating_word(w)]) for w in (10, 12)] == [6, 8]


def brute_pairs(j: int, horizon: int) -> tuple[set[tuple[tuple[int, ...], tuple[int, ...]]], int]:
    """Every pair (D_{j-1}, D_j) on times j .. horizon - 1 over the drivers c(0) = 1, c(1 .. j), and the largest onset
    of the pair's least common power-of-two period, all by direct simulation."""
    pairs = set()
    worst = 0
    for tail in itertools.product([0, 1], repeat=j):
        rows = left_history([1, *tail], horizon)
        diag = [[(rows[t] >> (t - i - 1)) & 1 if t > i else (([1, *tail][t]) if t == i else 0) for t in range(horizon)]
                for i in (j - 1, j)]
        pairs.add((tuple(diag[0][j:]), tuple(diag[1][j:])))
        p = 1
        while any(x[t + p] != x[t] for x in diag for t in range(horizon // 2, horizon - p)):
            p *= 2
        onset = max([t + 1 for x in diag for t in range(horizon - p) if x[t + p] != x[t]] + [j])
        worst = max(worst, onset)
    return pairs, worst


def test_driver_pairs_against_every_driver() -> None:
    horizon = 60
    rows = {r.depth: r for r in driver_pairs(8, horizon)}
    for j in (3, 6, 8):
        pairs, worst = brute_pairs(j, horizon)
        assert rows[j].pairs == len(pairs)
        assert rows[j].onset == worst
    assert [j for j, r in rows.items() if r.white] == [2, 7]
    assert all(r.classes == 1 and r.unsettled == 0 for r in rows.values())


def test_skeleton_against_spacetime() -> None:
    depth, steps = 40, 240
    cells = np.zeros(2 * steps + 1, dtype=np.uint8)  # (2 steps + 1,)
    cells[steps] = 1
    st = spacetime(cells, steps)  # (steps + 1, 2 steps + 1)
    D = np.array([[st[t, steps + j - t] for t in range(steps)] for j in range(depth)], dtype=np.uint8)  # (40, 240)
    a, b = skeleton_from_table(D), skeleton(depth, steps)
    for x, y in ((a.period, b.period), (a.white_run, b.white_run), (a.alt_run, b.alt_run)):
        assert np.array_equal(x, y)
    assert np.nonzero(a.white_run < 0)[0].tolist() == [2, 7, 28]
    assert int(np.argmax(a.period == 8)) == 29
    # the periodic part of D_j repeats: its cyclic white run is shorter than its period unless it is white
    assert all(-1 <= g < p for g, p in zip(a.white_run.tolist(), a.period.tolist()))


def test_onset_bound_holds_over_every_driver() -> None:
    sk = skeleton(33, 300)
    B = onset_bound(sk.white_run)  # (33,)
    for r in driver_pairs(32, 160):
        assert r.onset <= B[r.depth]
    assert settled_slope(1.5) == 3 / 13


def test_white_followers() -> None:
    # the single cell to depth 401 from the space-time diagram, against the period doubling read by `skeleton`
    steps = 1200
    cells = np.zeros(2 * steps + 1, dtype=np.uint8)  # (2 steps + 1,)
    cells[steps] = 1
    st = spacetime(cells, steps)  # (steps + 1, 2 steps + 1)
    D = np.array([[st[t, steps + j - t] for t in range(steps - 128, steps)] for j in range(402)],
                 dtype=np.uint8)  # (402, 128)
    found = white_followers(D)
    sk = skeleton(402, steps)
    assert [f.depth for f in found] == [2, 7, 28, 399]
    for f in found:
        assert f.flips == (sk.period[f.depth + 1] == 2 * sk.period[f.depth - 1])
        assert f.flips and f.complement_is_shift and f.period == sk.period[f.depth - 1]
    # a white diagonal whose follower neither flips nor has a shifted complement
    E = np.array([[1] * 16, [0] * 16, [1, 0, 0, 0] * 4], dtype=np.uint8)  # (3, 16)
    assert white_followers(E)[0].flips is False and white_followers(E)[0].complement_is_shift is False
