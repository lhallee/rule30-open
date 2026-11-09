"""relaxed_game against enumeration of every play cell by cell, a Python dynamic program without the cut, a full-row
Rule 30 run beside a cell held black, direct counts on random plays, the drivers of `driver_density`, and the numbers
its entry quotes."""

from __future__ import annotations

import itertools
import random

import numpy as np

from computations.driver_density import admissible_drivers, driver_dp
from computations.rule30 import step as row_step
from computations.run_mechanism import black_reach

from computations import relaxed_game as rg

def python_layers(T: int) -> list[dict[int, int]]:
    """Every left half reachable at t = 0 .. T with its largest payoff, uncut, over Python integers."""
    layers = [{0: 0}]
    for _ in range(T):
        new: dict[int, int] = {}
        for x, v in layers[-1].items():
            for e in (0, 1) if not x & 1 else (0,):
                y = rg.step(x, e)
                new[y] = max(new.get(y, -1), v + e)
        layers.append(new)
    return layers


def test_values_against_enumeration() -> None:
    brute = rg.brute_values(14)
    assert rg.values(14) == brute == rg.values_python(14)
    assert brute == [0, 1, 1, 1, 2, 3, 3, 4, 5, 6, 6, 6, 7, 8, 8]
    for T in (5, 9, 13):  # the cut depends on T; every cut gives the same values
        assert rg.values(T) == brute[:T + 1]
    E = rg.values(60)
    assert E[:41] == rg.values_python(40)
    assert (E[20], E[40], E[60]) == (10, 24, 38)
    # list_step, the enumeration's step, against the integer step
    rng = random.Random(4)
    for _ in range(200):
        x = rng.getrandbits(30)
        cells = [rg.cell(x, k) for k in range(1, 31)]
        for e in (0, 1):
            y = rg.step(x, e)
            assert rg.list_step(cells, e) == [rg.cell(y, k) for k in range(1, 32)]


def test_reach_windows_costs_against_python() -> None:
    layers = python_layers(30)
    rows = rg.reach(30)
    for r in rows:
        layer = layers[r.t]
        assert (r.states, r.best, r.longest) == (len(layer), max(layer.values()), max(map(rg.prefix, layer)))
    # the phase-A prefix against run_mechanism.black_reach (1 + the alternating right end, capped at t)
    t = 20
    xs = list(layers[t])
    B = np.array([[x] for x in xs], dtype=np.uint64)  # (n, 1)
    assert [min(rg.prefix(x), t) for x in xs] == list(black_reach(B, t) - 1)
    # windows and costs from s = 8, by the uncut dynamic program over the states reachable at s
    s, w = 8, 10
    states = {x: 0 for x in layers[s]}
    best_window, cost = [], []
    for i in range(1, w + 1):
        new: dict[int, int] = {}
        for x, v in states.items():
            for e in (0, 1) if not x & 1 else (0,):
                y = rg.step(x, e)
                new[y] = max(new.get(y, -1), v + e)
        states = new
        best_window.append(max(states.values()))
        z = []
        for k in itertools.count(1):
            ones = [v for x, v in states.items() if rg.prefix(x) >= k]
            if not ones:
                break
            z.append(i - max(ones))
        cost.append(z)
    assert rg.windows(s, w) == best_window
    assert rg.costs(s, w, 24) == cost


def test_beam() -> None:
    E = rg.values(40)
    wide = rg.beam(40, 100_000)  # wider than every layer: exact
    assert wide.best == E and sum(wide.play) == E[40]
    narrow = rg.beam(40, 5)
    assert all(b <= e for b, e in zip(narrow.best, E)) and sum(narrow.play) == narrow.best[40]
    rg.play_rows(narrow.play)  # legal
    assert rg.values(100)[100] == 62  # E(100), quoted


def held_black_rows(T: int) -> list[list[int]]:
    """Cells -1 .. -(T + 1) at times 0 .. T of Rule 30 beside cell 0 held black, from white, by `rule30.step` on a full
    row (bit i is cell i - W) with cell 0 set black and the cells right of it cleared after every step."""
    W = T + 2
    row, out = 1 << W, []
    for _ in range(T + 1):
        out.append([(row >> (W - k)) & 1 for k in range(1, T + 2)])
        row = (row_step(row) & ((1 << W) - 1)) | (1 << W)
    return out


def test_greedy_is_the_held_black_half_line() -> None:
    T = 300
    play = rg.greedy_play(T)
    rows = rg.play_rows(play)
    full = held_black_rows(T)
    for t in range(T + 1):
        assert [rg.cell(rows[t], k) for k in range(1, T + 2)] == full[t]
    col = rg.held_black_column(T)  # (T,)
    assert list(col) == [full[t][0] for t in range(T)]
    # the payoff is the number of white cells of column -1; no skips, so it is 1 + the black cells of column -2
    assert sum(play) == T - int(col.sum())
    a = rg.accounting(play)
    assert a.skips == a.wasteful == 0 and sum(play) == 1 + sum(full[t][1] for t in range(T - 1))
    assert x_minus_one_follows_minus_two(full)
    g = rg.greedy_play(1000)
    assert (sum(g[:100]), sum(g)) == (54, 495)  # quoted


def x_minus_one_follows_minus_two(full: list[list[int]]) -> bool:
    """Beside a held black cell, cell -1 at t + 1 is the negation of cell -2 at t."""
    return all(full[t + 1][0] == 1 - full[t][1] for t in range(len(full) - 1))


def test_accounting_identity() -> None:
    rng = random.Random(5)
    for trial in range(150):
        T = rng.randint(1, 100)
        p = (0.3, 0.7, 0.95)[trial % 3]
        cells, play, two, one = [0], [], [], []
        for _ in range(T):  # direct simulation with list_step
            e = int(rng.random() < p) if cells[0] == 0 else 0
            one.append(cells[0])
            two.append(cells[1] if len(cells) > 1 else 0)
            play.append(e)
            cells = rg.list_step(cells, e)
        zeros = T - sum(play)
        skips = [one[t] == 0 and play[t] == 0 for t in range(T)]
        Y = sum(1 for t in range(T - 1) if two[t] == 0)
        W = sum(1 for t in range(T - 1) if skips[t] and two[t] == 1)
        assert zeros == Y + 2 * W + int(skips[T - 1])
        a = rg.accounting(play)
        assert (a.white_two, a.wasteful, a.last_skip, a.skips) == (Y, W, int(skips[T - 1]), sum(skips))
        assert rg.accounting_holds(a) and sum(play) <= T - Y
        # the cells <= -2 play game G with e_1 = cell -1 and not cell -2; the two levels gain at most T + 1
        e1 = rg.next_level(play)
        assert [x >> 1 for x in rg.play_rows(play)] == rg.play_rows(e1) and sum(play) + sum(e1) <= T + 1
    assert rg.accounting_holds(rg.accounting(rg.beam(200, 2000).play))


def lambda_admissible(c: list[int]) -> bool:
    """Whether c(0) = 1 and c(t + 1) = not cell -1 at t whenever c(t) = 1, the half driven by c cell by cell."""
    cells = [0]
    for t in range(len(c) - 1):
        if c[t] == 1 and c[t + 1] != 1 - cells[0]:
            return False
        cells = rg.list_step(cells, c[t])
    return c[0] == 1


def test_reduction_from_lambda_l() -> None:
    rng = random.Random(6)
    E = rg.values(60)
    for trial in range(100):
        T = rng.randint(2, 60)
        c = rg.random_driver(T, rng, (0.5, 0.8, 1.0)[trial % 3])  # c(0 .. T)
        assert lambda_admissible(c)
        e = rg.driver_play(c)  # e(0 .. T - 1), a legal play
        x = 0
        for t, row in enumerate(rg.play_rows(e)):  # the same left halves as the driver's
            assert row == x
            if t < T:
                x = rg.step(x, c[t])
        B, D = sum(c[:T]), sum(e[:T - 1])  # over c(0 .. T - 1)
        assert D <= B <= (D + T + 1) / 2 and sum(e) <= E[T]
    M, Dmax = rg.lambda_values(40)
    assert M[:31] == [r.best for r in driver_dp(30)]
    assert all(d <= e for d, e in zip(Dmax, E))
    for n in range(2, 14):  # the most doubled black times over every admissible word c(0 .. n - 1)
        assert Dmax[n - 1] == max(sum(w[t] & w[t + 1] for t in range(n - 1)) for w in admissible_drivers(n))


def test_lemma_checks() -> None:
    assert rg.check_run_lemma(12) == 4096
    adv = rg.check_erosion(13)
    assert set(adv) == {0, 2, 4}
    assert rg.check_walls(10) > 0 and rg.check_front_speed(10) > 0
    assert rg.check_trapezoid(12) > 0 and rg.check_boundary_trapezoid(12) == 3 * 2048
    assert rg.check_moving_frame(4, 40) == 4 * 40 * 40 and rg.check_shielding(4, 40) > 0
    assert all(r.longest <= rg.slope_bound(r.t) for r in rg.reach(60))
    r60 = rg.reach(60)[-1]
    assert (r60.states, r60.best, r60.longest) == (31221, 38, 12)  # quoted


def test_checks_catch_a_wrong_rule() -> None:
    # the erosion check fails for Rule 45, whose stretches do not erode the same way
    original = rg.rule_image
    try:
        rg.rule_image = lambda row: [None] + [row[i - 1] ^ (row[i] | (1 - row[i + 1]))
                                             for i in range(1, len(row) - 1)] + [None]
        try:
            rg.check_erosion(11)
        except AssertionError:
            pass
        else:
            raise AssertionError("the erosion check accepted Rule 45")
    finally:
        rg.rule_image = original


def direct_windows(play: list[int], lam: int, kmin: int, side: str) -> float:
    T, best = len(play), float("inf")
    for a, k in rg.runs(play, 1):
        if k < kmin:
            continue
        lo, hi = {"both": (a - lam * k, a + k + lam * k), "before": (a - lam * k, a),
                  "after": (a + k, a + k + lam * k)}[side]
        best = min(best, sum(1 for t in range(max(lo, 0), min(hi, T)) if play[t] == 0) / k)
    return best


def test_covering_lemma() -> None:
    rng = random.Random(7)
    for trial in range(200):
        T = rng.randint(1, 150)
        p = rng.choice((0.5, 0.8, 0.95))
        word = [int(rng.random() < p) for _ in range(T)]
        ones, Z = sum(word), T - sum(word)
        for side, lam, kmin in (("both", 1, 1), ("before", 2, 3), ("after", 3, 2)):
            assert rg.charging_ratio(word, lam, kmin, side) == direct_windows(word, lam, kmin, side)
        for lam, K, C in itertools.product((1, 2), (1, 2, 4), (0, 1)):
            long = [(a, k) for a, k in rg.runs(word, 1) if k >= K]
            if not long:
                continue
            # the largest eps with CP: every run of k >= K has at least eps k - C zeros in its window
            zeros = [sum(1 for t in range(max(a - lam * k, 0), min(a + k + lam * k, T)) if word[t] == 0)
                     for a, k in long]
            eps = min((z + C) / k for z, (_, k) in zip(zeros, long))
            if eps <= 0:
                continue
            Kp = rg.covering_constant(lam, eps, C, K)
            assert ones <= Kp * (Z + 1) + 1e-9
            assert ones <= Kp / (Kp + 1) * (T + 1) + 1e-9


def test_held_black_column_quoted() -> None:
    col = rg.held_black_column(1000)  # (1000,)
    assert int(col.sum()) == 505 and rg.least_period(col[-600:], 200) is None
    assert rg.least_period(np.tile(np.array([0, 1, 1], dtype=np.uint8), 50), 10) == 3
