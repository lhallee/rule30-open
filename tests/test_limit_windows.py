"""`computations.limit_windows` against direct simulation of driven rows and a second implementation with tuples."""

from __future__ import annotations

import itertools
import random

import numpy as np

from computations import game, limit_windows as lw
from computations.wall_segments import in_set_family, necklaces, window_step


def driven_first_cells(block: str, starts: int, periods: int, seed: int) -> list[set[int]]:
    """Cell k + 1 at each phase of the last period, for `starts` random rows right of a column that repeats `block`
    for `periods` periods: direct Rule 30 on 40 cells, the column written into the cell on its left. One set of
    observed values per phase."""
    rng = random.Random(seed)
    seen: list[set[int]] = [set() for _ in block]
    for _ in range(starts):
        cells = np.array([0] + [rng.randint(0, 1) for _ in range(40)] + [0], dtype=np.uint8)  # (42,) cell k at 0
        for period in range(periods):
            for phase, ch in enumerate(block):
                cells[0] = int(ch)
                if period == periods - 1:
                    seen[phase].add(int(cells[1]))
                nxt = cells.copy()  # (42,)
                nxt[1:-1] = cells[:-2] ^ (cells[1:-1] | cells[2:])
                cells = nxt
    return seen


def test_moves_against_cells() -> None:
    """One step of a window against Rule 30 applied to the cells with the column and the free cell written in."""
    width = 5
    moves = lw.window_moves(width)
    for col, free, window in itertools.product((0, 1), (0, 1), range(1 << width)):
        cells = [col] + [(window >> j) & 1 for j in range(width)] + [free]
        out = sum((cells[i - 1] ^ (cells[i] | cells[i + 1])) << (i - 1) for i in range(1, width + 1))
        assert moves[col, window, free] == out


def reference_good(block: str, width: int) -> bool:
    """`is_good` with sets of tuples and `wall_segments.window_step`."""
    windows = frozenset(itertools.product((0, 1), repeat=width))
    while True:
        after = windows
        for ch in block:
            after = window_step(after, int(ch))
        if after == windows:
            break
        windows = after
    for ch in block:
        if ch == "0" and len({w[0] for w in windows}) > 1:
            return False
        windows = window_step(windows, int(ch))
    return True


def test_good_against_reference() -> None:
    moves = lw.window_moves(4)
    blocks = [b for period in range(1, 9) for b in necklaces(period)]
    flags = [lw.is_good(b, moves) for b in blocks]
    assert flags == [reference_good(b, 4) for b in blocks]
    assert sum(flags) >= 1  # the constant block 1 at least


def test_driven_rows_agree_where_good() -> None:
    """For a good block every random row shows one value of cell k + 1 at each 0 once the history is long, and a block
    that is not good shows both."""
    moves = lw.window_moves(8)
    good, bad = "0" * 10 + "1", "01"
    assert lw.is_good(good, moves) and not lw.is_good(bad, moves)
    seen = driven_first_cells(good, starts=40, periods=40, seed=1)
    assert all(len(values) == 1 for ch, values in zip(good, seen) if ch == "0")
    seen = driven_first_cells(bad, starts=40, periods=40, seed=2)
    assert any(len(values) == 2 for ch, values in zip(bad, seen) if ch == "0")
    # the value that the limit windows give is the value that the rows show
    seen = driven_first_cells(good, starts=40, periods=40, seed=3)
    for ch, members, values in zip(good, lw.limit_sets(good, moves), seen):
        if ch == "0":
            assert values == {int(members[0]) & 1}


def test_white_cycle_against_boolean_powers() -> None:
    """The preperiod and period of a run of 0s on windows of 6 cells, against powers of the relation as a matrix."""
    width = 6
    moves = lw.window_moves(width)
    n = 1 << width
    relation = np.zeros((n, n), dtype=bool)  # (n, n) window u can become window v beside a 0
    for u in range(n):
        relation[u, moves[0, u, 0]] = relation[u, moves[0, u, 1]] = True
    power, seen = np.eye(n, dtype=bool), {}
    for j in range(2000):
        key = power.tobytes()
        if key in seen:
            assert lw.white_cycle(width) == (seen[key], j - seen[key])
            return
        seen[key] = j
        power = (power.astype(np.int32) @ relation.astype(np.int32)) > 0
    raise AssertionError("no repeat")


def test_wall_family_is_good() -> None:
    """Every block with nine 1s that the wall test excludes is good here, from windows of six cells."""
    moves = lw.window_moves(6)
    blocks = [b for period in range(9, 14) for b in necklaces(period) if in_set_family(b)]
    assert len(blocks) >= 10 and all(lw.is_good(b, moves) for b in blocks)


def test_tail_thresholds() -> None:
    """At 8 cells 0^q 1 is good exactly from q = 10 on and 0^q 11 from q = 9 (the kit's padded words need 9 and 8)."""
    table = lw.tail_thresholds(["1", "11", "101"], 8)
    assert table["1"] == (10, []) and table["11"] == (9, []) and table["101"][0] is None
    moves = lw.window_moves(8)
    assert not lw.is_good("0" * 9 + "1", moves) and lw.is_good("0" * 10 + "1", moves)
    assert all(lw.is_good("0" * q + "11", moves) for q in range(9, 60))  # past the preperiod 22 and period 4


def test_mixture_is_sound() -> None:
    """A consistent mixture makes every cyclic word of its segments good, runs of 1s of nine to fourteen included; an
    inconsistent one is refused."""
    generators = {"1": 10, "11": 9}
    ok, _, fails = lw.consistent(generators, 8, 9)
    assert ok and not fails
    moves = lw.window_moves(8)
    rng = random.Random(0)
    segments = [(tail, least) for tail, least in generators.items()] + [("1" * run, 9) for run in range(9, 15)]
    for _ in range(40):
        word = "".join(tail + "0" * (least + rng.randint(0, 6))
                       for tail, least in (rng.choice(segments) for _ in range(rng.randint(1, 4))))
        assert lw.is_good(word, moves)
    assert lw.consistent({"1": 9}, 8)[2] == ["1"]  # 0^9 1 is not good at 8 cells
    assert lw.consistent({}, 8, 1)[0]  # nine 1s and then any 0s: the wall of WallSets


def test_kit_words() -> None:
    """The generated sets against `game.kit_blocks`, for the blocks that are not all long runs of 1s."""
    pinned = {block: why for block, why in game.kit_blocks(13).items() if why != "long runs of 1s"}
    generated = {block for period in range(1, 14) for block in lw.kit_words(period)}
    assert generated == set(pinned)
