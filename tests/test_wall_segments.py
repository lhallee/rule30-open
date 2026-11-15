"""Tests of computations.wall_segments: segments, window sets, tails and stripes against brute force and the kit's
wall."""

from __future__ import annotations

import numpy as np

from computations import game


def test_wall_segments() -> None:
    """The three-valued run of `wall_segments` against brute force: every segment of up to nine cells that it passes
    keeps the cell right of the column the same at each 0 over every row that starts at the wall. The segments that
    start and end with 0 and pass are exactly the five forms; the family's criterion on blocks does not depend on the
    rotation, and the family's blocks of period up to 13 are among those the finite game excludes."""
    import itertools
    import re
    from computations import wall_segments
    for m in range(1, 10):
        for bits in itertools.product("01", repeat=m):
            u = "".join(bits)
            if wall_segments.segment_good(u):
                assert wall_segments.brute_segment(u), u
    forms = re.compile(r"^(0+|0+10|0100|0110+|0110*10)$")
    for m in range(1, 15):
        for bits in itertools.product("01", repeat=m):
            u = "".join(bits)
            if u[0] == "0" and u[-1] == "0" and "1" * 9 not in u:
                assert wall_segments.segment_good(u) == bool(forms.match(u)), u
    assert wall_segments.in_family("1" * 9 + "010") and wall_segments.in_family("1")
    assert not wall_segments.in_family("1" * 9 + "00100") and not wall_segments.in_family("01")
    assert wall_segments.in_family("1" * 9 + "010" + "1" * 9 + "01100")
    rng = np.random.default_rng(45)
    for _ in range(40):
        block = "".join(rng.choice(["0", "1"], size=int(rng.integers(10, 20)), p=[0.2, 0.8]))
        rotations = {wall_segments.in_family(block[i:] + block[:i]) for i in range(len(block))}
        assert len(rotations) == 1, block
    family = [b for p in range(1, 14) for b in wall_segments.necklaces(p) if wall_segments.in_family(b)]
    assert len(family) == 16
    assert all(game.least_width(b, 10) is not None for b in family if b != "1")


def test_window_sets() -> None:
    """The sets of windows of `wall_segments` against brute force and the three values: every segment of up to nine
    cells that the sets of three-cell windows pass, brute force passes too, and so do the sets for every segment the
    three values pass; the parity families pass for small lengths; and the family's blocks of period up to 13 are
    among those the finite game excludes, the blocks with nine 1s in a row all of them."""
    import itertools
    from computations import wall_segments
    for m in range(1, 10):
        for bits in itertools.product("01", repeat=m):
            u = "".join(bits)
            if wall_segments.set_segment_good(u):
                assert wall_segments.brute_segment(u), u
            if wall_segments.segment_good(u):
                assert wall_segments.set_segment_good(u), u
    for k in range(4):
        assert wall_segments.set_segment_good("0" * (2 * k + 3) + "100")
        assert wall_segments.set_segment_good("0" * (2 * k + 3) + "110")
        assert wall_segments.set_segment_good("0" * (2 * k + 2) + "1010")
        assert not wall_segments.set_segment_good("0" * (2 * k + 4) + "100")
    family = [b for p in range(1, 14) for b in wall_segments.necklaces(p) if wall_segments.in_set_family(b)]
    nine = [b for p in range(2, 14) for b in wall_segments.necklaces(p) if "1" * 9 in b + b]
    excluded = [b for b in nine if game.least_width(b, 12) is not None]
    assert sorted(b for b in family if b != "1") == sorted(excluded)


def test_windows_after_ones() -> None:
    """The windows that runs of 1s leave, against the kit's wall: nine 1s leave exactly the windows 0 1 0 and 0 1 1,
    which `wall_windows` uses, and eight leave a window with first cell 1 besides, as the kit's
    `eight_black_not_enough` says."""
    from computations import wall_segments
    assert wall_segments.windows_after_ones(9) == wall_segments.wall_windows(3)
    assert wall_segments.windows_after_ones(8) == frozenset({(0, 1, 0), (0, 1, 1), (1, 0, 0)})
    assert all(len({w[0] for w in wall_segments.windows_after_ones(ones)}) == 2 for ones in range(1, 9))


def test_tails() -> None:
    """The tails of `WideWall`, against the two conditions checked by brute force over small periods: a black run of r
    rules out the tails with P - r at most 4 floor(r/9), and nine 1s and b 0s those with P - s - b at most
    4 floor((b - 1)/9) + 2; the kit's Theorems B and D ask more (`kit_theoremB_condition`, `kit_theoremD_condition`)."""
    from computations import wall_segments
    assert wall_segments.longest_tail(45) == (20, 1) and wall_segments.longest_tail(90) == (40, 11)
    assert [wall_segments.least_white_run(m) for m in (0, 2, 6, 10)] == [(1, 37), (1, 46), (10, 64), (19, 82)]
    for tail in range(0, 40):
        ours, kit = wall_segments.least_white_run(tail)
        assert min(b for b in range(1, 400) if tail <= 4 * ((b - 1) // 9) + 2) == ours
        assert min(b for b in range(1, 400) if 1 + 9 * ((tail + 9) // 2) <= b) == kit >= ours
    for run in range(9, 200):
        ours, kit = wall_segments.longest_tail(run)
        assert max(m for m in range(0, run) if m <= 4 * (run // 9)) == ours
        assert max([m for m in range(0, run) if 9 * ((m + 10) // 2) <= run], default=-1) == kit <= ours


def test_stripe() -> None:
    """The stripes of `WideWall`: brute force over every column and every cell beyond a stripe of L cells that ends in a
    black cell finds the cell right of the column the same for 2 L steps and not for 2 L + 1, for L up to 4, and the
    three-valued run first loses it at step 2 L for L up to 10, the range WideWall.md states. The shield (0 1)^j is the
    stripe of length 2 j."""
    from computations import wall_segments
    assert wall_segments.stripe(4) == [0, 1, 0, 1] and wall_segments.stripe(3) == [1, 0, 1]
    for length in range(1, 5):
        assert wall_segments.stripe_brute(length, 2 * length)
        assert not wall_segments.stripe_brute(length, 2 * length + 1)
    for length in range(1, 11):
        assert wall_segments.stripe_known_steps(length) == 2 * length
