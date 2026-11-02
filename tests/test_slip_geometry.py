"""The slips of column 1 beside an alternating center, against direct runs and the right-channel finding's counts."""

from __future__ import annotations

import numpy as np

from computations import right_half, rule30, slip_geometry as g


def test_rows_match_direct_run() -> None:
    """The integer run with its cut-back equals a direct run of the rule on an array, in both phases."""
    for phase in (0, 1):
        assert np.array_equal(g.right_rows(300, 40, phase), g.direct_rows(300, 40, phase))


def test_column_matches_right_half() -> None:
    """Column 1 equals `right_half.column_one` for the words 01 and 10, and the two phases are one step apart."""
    assert np.array_equal(g.column_one(3000, 0), right_half.column_one("01", 0, 3000))
    assert np.array_equal(g.column_one(3000, 1), right_half.column_one("10", 0, 3000))
    assert np.array_equal(g.column_one(3001, 0)[1:], g.column_one(3000, 1))


def test_window_runs_agree() -> None:
    """The integer window run equals the array window run, for both boundaries; a window as wide as the light cone
    equals the true half."""
    for boundary in ("white", "iid"):
        assert np.array_equal(g.window_column_one(400, 20, boundary, seed=4),
                              g.window_rows(400, 20, boundary, seed=4)[:, 0])
    assert np.array_equal(g.window_column_one(300, 302, "white"), g.column_one(300))


def test_slip_count_of_the_finding() -> None:
    """826 slip events in 120,000 steps, as the right-channel finding counts them."""
    starts, ends = g.slip_events(g.column_one(120_000))
    assert starts.size == 826 and np.all(ends >= starts)


def test_slip_events_synthetic() -> None:
    """A periodic column has no slip; one shifted stretch gives exactly one event, starting where it starts."""
    block = np.array([int(b) for b in g.A_BLOCK * 3 + g.B_BLOCK], dtype=np.uint8)  # (36,)
    column = np.tile(block, 20)  # (720,)
    assert g.slip_events(column)[0].size == 0
    shifted = np.concatenate([column[:360], column[365:]])  # (715,)
    starts, _ = g.slip_events(shifted)
    first = int(np.flatnonzero(shifted[36:] != shifted[:-36])[0]) + 36
    assert starts.tolist() == [first]


def test_gap_runs_against_string_parse() -> None:
    """Runs of gaps of 5 between gaps of 3, against a parse of the white-step column as a string."""
    column = g.column_one(20_000)  # (20000,)
    gaps, runs, _ = g.gap_runs(column)
    assert set(np.unique(gaps).tolist()) <= {3, 5}
    white = "".join(map(str, column[0::2][500:]))  # white steps from step 1,000 on
    marks = "".join("a" if len(z) == 2 else "b" for z in white.strip("0").split("1")[1:-1])
    parsed = [len(r) for r in marks.split("a")[1:-1]]
    assert runs.tolist() == parsed
    lock = np.tile(np.array([int(b) for b in g.A_BLOCK * 3 + g.B_BLOCK], dtype=np.uint8), 100)  # (3600,)
    assert set(g.gap_runs(lock, phase=1, settle=0)[1].tolist()) == {3}  # AAAB from its start falls on odd white steps


def test_lock_depth() -> None:
    """The locked layer is the run of columns equal to themselves 36 steps earlier."""
    rows = np.zeros((40, 6), dtype=np.uint8)  # (40, 6)
    rows[38, 3] = 1
    rows[39, 0] = 1
    depth = g.lock_depth(rows)
    assert depth[36] == 6 and depth[38] == 3 and depth[39] == 0 and depth[0] == -1


def test_damage_speed() -> None:
    """The left edge of the damage of one flipped cell, against a direct run with `rule30.spacetime` for one row, and
    a speed near a quarter."""
    rng = np.random.default_rng(0)
    width = 201
    row = rng.integers(0, 2, width, dtype=np.uint8)  # (width,)
    flipped = row.copy()
    flipped[100] ^= 1
    a = rule30.spacetime(row, 60)  # (61, width)
    b = rule30.spacetime(flipped, 60)  # (61, width)
    left = [100 - int(np.flatnonzero(a[t] != b[t])[0]) for t in range(1, 61)]
    np.random.seed(0)
    shift = g.leftward_damage_speed(width, 60, 1, seed=0)  # (60,)
    rows = np.random.default_rng(0).integers(0, 2, (1, width), dtype=np.uint8)  # (1, width), the same draw
    assert np.array_equal(rows[0], row)
    assert shift.tolist() == left
    speed = g.leftward_damage_speed(512, 160, 64)  # (160,)
    assert 0.15 < (speed[159] - speed[79]) / 80 < 0.35


def test_reach() -> None:
    """The reach lies in the light cone, and randomizing the cells right of it with a fresh generator leaves column 1
    unchanged."""
    steps = 3000
    states = g.states_at([2000], steps)
    rng = np.random.default_rng(1)
    x = g.reach(states[2000], 2000, 32, 1, 16, rng)
    assert 0 < x <= 34  # column 1 at times 2000 .. 2032 sees columns 1 .. 34 at time 2000
    _, truth = g.advance(states[2000] & ((1 << 40) - 1), 2000, 33)
    other = np.random.default_rng(9)
    for _ in range(8):
        fresh = int.from_bytes(other.bytes(8), "little")
        _, col = g.advance((states[2000] & ((1 << x) - 1)) | (fresh << x), 2000, 33)
        assert np.array_equal(col, truth)


def test_dependence_and_renewal_tests() -> None:
    """Independent draws pass both tests; a sticky Markov chain fails the pair test; gaps that alternate fail the
    serial test."""
    rng = np.random.default_rng(3)
    draws = rng.integers(0, 4, 2000)  # (2000,)
    assert g.pair_dependence(draws, 3, permutations=200)[1] > 0.01
    sticky = np.cumsum(rng.random(2000) < 0.1) % 2  # (2000,)
    assert g.pair_dependence(sticky, 1, permutations=200)[1] < 0.01
    geometric = rng.geometric(0.1, 1500) + 10  # (1500,)
    out = g.renewal_tests(geometric, lags=1, permutations=200)
    assert out["ks_geometric"] < 0.05  # type: ignore[operator]
    alternating = np.tile([10, 50], 300) + rng.integers(0, 3, 600)  # (600,)
    assert g.renewal_tests(alternating, lags=1, permutations=200)["serial"][0][2] < 0.01  # type: ignore[index]
