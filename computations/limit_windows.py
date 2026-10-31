"""Windows of cells beside a repeating column, followed through the column's whole history.

A column k repeats a block from some time on. The `width` cells right of it, cells k + 1 to k + width, form a window,
and the cell beyond the window is free at every step. One step beside a column that reads `col` maps a window to two
windows (`window_moves`). Over all `m` periods before a late time t the real window lies in the image of the set of all
windows under the block read `m` times; these sets decrease with `m`, so the real window lies in their limit
(`limit_sets`), the exact set of windows that a repeating column leaves after an unbounded history. If at every 0 of
the block the limit has one value of cell k + 1 (`is_good`), column k - 1, which is
`x_{t+1}(k) xor (x_t(k) or x_t(k + 1))`, repeats with the column, and the adjacent-column theorem forbids that: no
column of a row with a leftmost 1 repeats the block. `wall_segments.in_set_family` is the same test with windows of
three cells, started from the wall that nine 1s leave; here nothing is assumed about the history, and a white run
leaves a wall of its own.

Reading a run of 0s is a fixed relation on windows (`white_cycle`): its powers repeat with a period of 4 after a
preperiod (53 steps for 14 cells). So `tail_thresholds` can decide a whole family `0^q t`, for every `q`, by testing the
`q` up to the preperiod plus two periods, and `consistent` can decide a mixture of tails separated by white runs of
unbounded length, by the fixed point of the set of windows that any such history leaves.

    python -m computations.limit_windows --survey 20 --width 12 --workers 8   # blocks by period, against the kit
    python -m computations.limit_windows --tails 8 --width 14                 # least white run for every short tail
    python -m computations.limit_windows --mixtures 6 --width 14              # tails of up to 6 cells, mixed
    python -m computations.limit_windows --runs 8,12,16                       # one run of 1s alone, by width
    python -m computations.limit_windows --stabilize 6,8,10,12,14,16         # what a long run of 0s leaves
    python -m computations.limit_windows --cycle 14                           # preperiod and period of a white run
"""

from __future__ import annotations

import argparse
import itertools
import multiprocessing
import sys

import numpy as np
from tqdm.auto import tqdm

from computations import game
from computations.wall_segments import in_set_family


def window_moves(width: int) -> np.ndarray:
    """The two windows that each window can become in one step, for each column value.

    Window `u` holds cell k + 1 + j at bit j. Cell k + width + 1 is free (index 1 of the last axis); the cell left of
    the first reads the column. Returns an array of shape (2, 2^width, 2): column value, window, free cell."""
    n = 1 << width
    window = np.arange(n, dtype=np.int64)  # (n,)
    moves = np.zeros((2, n, 2), dtype=np.int64)  # (col, window, free)
    for col in (0, 1):
        for free in (0, 1):
            cells = window | (free << width)  # (n,) cell k + width + 1 at bit `width`
            left = ((cells << 1) | col) & (n - 1)  # (n,) bit j holds cell k + j, the column at bit 0
            middle = cells & (n - 1)  # (n,)
            right = (cells >> 1) & (n - 1)  # (n,)
            moves[col, :, free] = left ^ (middle | right)
    return moves


def step_set(members: np.ndarray, moves: np.ndarray, col: int) -> np.ndarray:
    """The sorted windows reachable in one step from the sorted windows `members` (shape (s,)), beside `col`."""
    seen = np.zeros(moves.shape[1], dtype=bool)  # (n,)
    seen[moves[col, members, 0]] = True
    seen[moves[col, members, 1]] = True
    return np.flatnonzero(seen)


def read_word(members: np.ndarray, moves: np.ndarray, word: str) -> np.ndarray:
    """The windows after the column reads `word`, from the windows `members`."""
    for ch in word:
        members = step_set(members, moves, int(ch))
    return members


def agree(members: np.ndarray) -> bool:
    """Whether every window of `members` has the same cell k + 1 (bit 0): the cell is known."""
    first = members & 1
    return bool(first.min() == first.max()) if len(members) else True


def limit_sets(block: str, moves: np.ndarray) -> list[np.ndarray]:
    """The limit of the windows that `block` leaves after `m` periods from every window, as m grows: for each phase i,
    the windows just before the column reads `block[i]`. Each is a sorted array of windows."""
    members = np.arange(moves.shape[1], dtype=np.int64)  # (n,)
    while True:
        after = read_word(members, moves, block)
        if np.array_equal(after, members):
            break
        members = after
    sets = []
    for ch in block:
        sets.append(members)
        members = step_set(members, moves, int(ch))
    return sets


def is_good(block: str, moves: np.ndarray) -> bool:
    """Whether the limit windows have one cell k + 1 at every 0 of `block`: then no column repeats `block`."""
    return all(agree(members) for ch, members in zip(block, limit_sets(block, moves)) if ch == "0")


def white_cycle(width: int) -> tuple[int, int]:
    """The preperiod p and period d of the relation 'one step beside a 0': its power j maps window u to the windows
    reachable in j steps, and the powers from j = p on repeat with period d. The rows of a power are bit sets, held as
    Python integers; the repeat is found by a hash and then checked by comparing the rows."""
    moves = window_moves(width)
    n = 1 << width
    first, second = moves[0, :, 0].tolist(), moves[0, :, 1].tolist()
    rows = [1 << u for u in range(n)]  # power 0
    seen: dict[int, int] = {}
    j = 0
    while True:
        key = hash(tuple(rows))
        if key in seen:
            earlier = seen[key]
            break
        seen[key] = j
        rows = [rows[first[u]] | rows[second[u]] for u in range(n)]
        j += 1
    check = [1 << u for u in range(n)]
    for _ in range(earlier):
        check = [check[first[u]] | check[second[u]] for u in range(n)]
    assert check == rows, "hash collision in the white cycle"
    return earlier, j - earlier


def white_stabilization(width: int) -> tuple[int, int, bool]:
    """The windows after the column reads 0 for t steps from every window decrease with t; returns the first t at
    which they stop, their number, and whether they have one value of cell k + 1."""
    moves = window_moves(width)
    members = np.arange(1 << width, dtype=np.int64)  # (n,)
    steps = 0
    while True:
        after = step_set(members, moves, 0)
        if np.array_equal(after, members):
            return steps, len(members), agree(members)
        members, steps = after, steps + 1


def block_of(white: int, tail: str) -> str:
    """The block of `white` 0s and then `tail`."""
    return "0" * white + tail


def tail_thresholds(tails: list[str], width: int, desc: str = "tails") -> dict[str, tuple[int | None, list[int]]]:
    """For each tail, the least `q0` such that `0^q tail` is good for every `q` at least `q0`, and the sporadic `q`
    below it that are good too (None if there is no `q0`). The preperiod p and period d of `white_cycle` make
    goodness for `q >= p + d` depend only on q mod d, so the `q` up to p + 2 d - 1 decide every `q`."""
    moves = window_moves(width)
    preperiod, period = white_cycle(width)
    top = preperiod + 2 * period - 1
    out = {}
    for tail in tqdm(tails, desc=desc, unit="tail", file=sys.stderr, mininterval=5):
        good = [is_good(block_of(q, tail), moves) for q in range(1, top + 1)]  # (top,) goodness of q = 1 .. top
        q0 = None
        for q in range(top, 0, -1):
            if not good[q - 1]:
                break
            q0 = q
        out[tail] = (q0, [q for q in range(1, top + 1) if good[q - 1] and (q0 is None or q < q0)])
    return out


def tails_up_to(length: int) -> list[str]:
    """Every word of 1 to `length` cells that starts and ends with 1."""
    return ["1"] + [("1" + "".join(mid) + "1") for size in range(2, length + 1)
                    for mid in itertools.product("01", repeat=size - 2)]


def orbit_of_white(members: np.ndarray, moves: np.ndarray) -> tuple[list[np.ndarray], int]:
    """The sets reached from `members` by reading 0s, until one repeats, and the index it returns to."""
    seen: dict[bytes, int] = {}
    orbit: list[np.ndarray] = []
    while True:
        key = members.tobytes()
        if key in seen:
            return orbit, seen[key]
        seen[key] = len(orbit)
        orbit.append(members)
        members = step_set(members, moves, 0)


def union_from(orbit: list[np.ndarray], preperiod: int, least: int) -> np.ndarray:
    """The union of the sets of a white orbit after at least `least` steps: past the preperiod every set of the cycle
    recurs, so the union starts at the preperiod when `least` is past it."""
    start = min(least, preperiod)
    return np.unique(np.concatenate(orbit[start:]))


def long_black_states(members: np.ndarray, moves: np.ndarray) -> list[np.ndarray]:
    """The windows after the column reads r 1s from `members`, for every r >= 9: r = 9 and then one more 1 at a time,
    until a set repeats. Windows of many cells keep learning from further 1s, so r = 9 alone does not stand for them."""
    seen: set[bytes] = set()
    states: list[np.ndarray] = []
    after = read_word(members, moves, "1" * 9)
    while after.tobytes() not in seen:
        seen.add(after.tobytes())
        states.append(after)
        after = step_set(after, moves, 1)
    return states


def consistent(generators: dict[str, int], width: int, long_black: int | None = None
               ) -> tuple[bool, np.ndarray, list[str]]:
    """Whether every cyclic word that concatenates `tail 0^q` with `q >= generators[tail]` is good, for the tails in
    `generators` (words that start with 1), and, if `long_black` is given, `1^r 0^q` for every r >= 9 and
    q >= `long_black`: the windows that any history of such segments leaves at the start of a segment shrink to a
    fixed set Y; the mixture is good if, from Y, the first cell is known at every 0 of every segment and of every white
    run after it. Returns the answer, Y, and the segments that fail (the long black runs as "1+")."""
    moves = window_moves(width)
    members = np.arange(1 << width, dtype=np.int64)  # (n,)
    while True:
        parts = [union_from(*orbit_of_white(read_word(members, moves, tail), moves), least)
                 for tail, least in generators.items()]
        if long_black is not None:
            parts += [union_from(*orbit_of_white(state, moves), long_black)
                      for state in long_black_states(members, moves)]
        new = np.intersect1d(np.unique(np.concatenate(parts)), members)
        if np.array_equal(new, members):
            break
        members = new
    fails = []
    for tail in generators:
        state, failed = members, False
        for ch in tail:
            if ch == "0" and not agree(state):
                failed = True
            state = step_set(state, moves, int(ch))
        if failed or not all(agree(s) for s in orbit_of_white(state, moves)[0]):
            fails.append(tail)
    if long_black is not None and not all(agree(s) for state in long_black_states(members, moves)
                                          for s in orbit_of_white(state, moves)[0]):
        fails.append("1+")
    return not fails, members, fails


def mixture(length: int, white: int, width: int) -> tuple[dict[str, int], list[str]]:
    """The tails of up to `length` cells, each with white runs of at least `white`, and runs of at least nine 1s with
    the same white runs, as one mixture: first the tails that are good alone at that white run, then, one at a time,
    the longest failing tail is dropped until the rest is consistent. Returns the generators kept and the tails
    dropped."""
    alone = tail_thresholds(tails_up_to(length), width, desc="alone")
    generators = {tail: white for tail in tails_up_to(length) if alone[tail][0] is not None and alone[tail][0] <= white}
    dropped: list[str] = []
    while True:
        ok, _, fails = consistent(generators, width, white)
        if ok:
            return generators, dropped
        assert fails != ["1+"], "long black runs fail on their own"
        worst = max((tail for tail in fails if tail != "1+"), key=lambda t: (len(t), t))
        del generators[worst]
        dropped.append(worst)


def runs_of(block: str) -> list[tuple[int, int]] | None:
    """The cyclic runs of `block` as (black, white) pairs from the start of a black run, or None if it is constant."""
    if "0" not in block or "1" not in block:
        return None
    start = block.index("0")
    rotated = block[start:] + block[:start]
    shift = rotated.index("1")
    rotated = rotated[shift:] + rotated[:shift]
    pairs, i = [], 0
    while i < len(rotated):
        black = 0
        while i < len(rotated) and rotated[i] == "1":
            black, i = black + 1, i + 1
        white = 0
        while i < len(rotated) and rotated[i] == "0":
            white, i = white + 1, i + 1
        pairs.append((black, white))
    return pairs


def kit_excludes(block: str) -> bool:
    """Whether the pinned kit or its main branch excludes `block`: every run of 1s at least nine long, every white run
    at least 17 (main), every (black, white) run in the four categories of main's `Rule30GrammarRuns`, a strip
    certificate, a padded word or a white-padding family (`game.kit_blocks`, as generated sets)."""
    pairs = runs_of(block)
    if pairs is None:
        return True
    categories = lambda black, white: ((black == 1 and white >= 10) or (black == 2 and white >= 8)
                                       or (black == 4 and white >= 7) or (black >= 9 and white >= 9))
    if all(black >= 9 for black, _ in pairs) or all(white >= 17 for _, white in pairs):
        return True
    if all(categories(black, white) for black, white in pairs):
        return True
    return block in kit_words(len(block))


def kit_words(period: int) -> set[str]:
    """The least rotations of the pinned kit's strip certificates, padded words, white-padding families and black-run
    blocks of exactly `period` cells (`game.kit_blocks` without the loop over all blocks)."""
    found = {word for word in game.KIT_WORDS if len(word) == period}
    for tail, white in (("1", 9), ("11", 8), ("10111", 9)):
        if period - len(tail) >= white:
            found.add(game.least_rotation("0" * (period - len(tail)) + tail))
    for tail, white in game.PADDING_FAMILIES:
        if period - len(tail) >= white:
            found.add(game.least_rotation("0" * (period - len(tail)) + tail))
    for block, black in game.BLACK_RUN_BLOCKS:
        if period - len(block) >= black:
            found.add(game.least_rotation("1" * (period - len(block)) + block))
    return found


def necklace_codes(period: int) -> np.ndarray:
    """The primitive necklaces of `period` cells as the integers of their least rotation (bit i is cell i)."""
    codes = np.arange(1 << period, dtype=np.int64)  # (2^period,)
    keep = np.ones(1 << period, dtype=bool)  # (2^period,)
    mask = (1 << period) - 1
    for shift in range(1, period):
        rotated = ((codes << shift) | (codes >> (period - shift))) & mask  # (2^period,)
        keep &= rotated > codes
    return codes[keep]


def code_word(code: int, period: int) -> str:
    """The block whose cell i is bit i of `code`."""
    return "".join(str((code >> i) & 1) for i in range(period))


def good_block(args: tuple[str, int]) -> bool:
    """`is_good` of one block at one width (module level, for worker processes)."""
    block, width = args
    return is_good(block, _moves(width))


_MOVES: dict[int, np.ndarray] = {}


def _moves(width: int) -> np.ndarray:
    if width not in _MOVES:
        _MOVES[width] = window_moves(width)
    return _MOVES[width]


def survey(max_period: int, width: int, workers: int) -> dict[int, list[str]]:
    """The good primitive blocks of each period up to `max_period`, each as its least rotation."""
    found: dict[int, list[str]] = {}
    pool = multiprocessing.get_context("spawn").Pool(workers) if workers > 1 else None
    for period in range(1, max_period + 1):
        blocks = [game.least_rotation(code_word(int(c), period)) for c in necklace_codes(period)]
        tasks = [(block, width) for block in blocks]
        bar = tqdm(tasks, desc=f"period {period}", unit="block", file=sys.stderr, mininterval=5, leave=False)
        flags = list(pool.imap(good_block, bar, chunksize=64)) if pool else [good_block(task) for task in bar]
        found[period] = sorted(block for block, flag in zip(blocks, flags) if flag)
    if pool:
        pool.close()
    return found


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--width", type=int, default=12)
    parser.add_argument("--survey", type=int, default=0, help="the good blocks of each period up to this one")
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--tails", type=int, default=0, help="the least white run for each tail of up to this length")
    parser.add_argument("--mixtures", type=int, default=0, help="mix the tails of up to this length")
    parser.add_argument("--runs", default="", help="widths, comma separated: the least white run after each run of 1 to "
                                                   "8 ones alone")
    parser.add_argument("--whites", default="18,22,26,30", help="the white runs the mixtures try, comma separated")
    parser.add_argument("--stabilize", default="", help="widths, comma separated: what a long white run leaves")
    parser.add_argument("--cycle", type=int, default=0, help="the preperiod and period of a white run at this width")
    args = parser.parse_args()

    for width in (int(value) for value in args.runs.split(",") if value):
        table = tail_thresholds(["1" * run for run in range(1, 9)], width, desc=f"width {width}")
        print(f"width {width}: " + "; ".join(f"1^{len(t)}: q >= {q0}" + (f" and {sporadic}" if sporadic else "")
                                            for t, (q0, sporadic) in table.items()))
    for width in (int(value) for value in args.stabilize.split(",") if value):
        steps, size, known = white_stabilization(width)
        print(f"width {width}: a run of 0s leaves {size} windows after {steps} steps, cell k + 1 "
              f"{'known' if known else 'not known'}")
    if args.cycle:
        print("preperiod, period of a run of 0s on windows of", args.cycle, "cells:", white_cycle(args.cycle))
    if args.survey:
        found = survey(args.survey, args.width, args.workers)
        total = 0
        for period, blocks in found.items():
            wall = [b for b in blocks if in_set_family(b)]
            kit = [b for b in blocks if kit_excludes(b)]
            new = [b for b in blocks if b not in set(wall) | set(kit)]
            long_white = [b for b in new if sum(white >= 8 for _, white in runs_of(b)) == 1]
            eight_ones = [b for b in new if all(white < 8 for _, white in runs_of(b)) and max(r for r, _ in runs_of(b)) >= 8]
            total += len(blocks)
            print(f"period {period}: {len(blocks)} good blocks, {len(wall)} in WallSets, {len(kit)} excluded by the kit, "
                  f"{len(new)} in neither, of which {len(long_white)} have one white run of at least 8 and "
                  f"{len(eight_ones)} a run of eight 1s or more and no such white run")
        print(f"up to period {args.survey}: {total} good blocks at width {args.width}")
    if args.tails:
        table = tail_thresholds(tails_up_to(args.tails), args.width)
        for length in range(1, args.tails + 1):
            row = {t: v for t, v in table.items() if len(t) == length}
            worst = max((v[0] for v in row.values() if v[0] is not None), default=None)
            none = [t for t, v in row.items() if v[0] is None]
            print(f"tails of {length} cells: {len(row) - len(none)} of {len(row)} have a threshold, the largest is "
                  f"{worst}; no threshold: {none}")
    if args.mixtures:
        for white in (int(value) for value in args.whites.split(",")):
            kept, dropped = mixture(args.mixtures, white, args.width)
            print(f"tails of up to {args.mixtures} cells, white runs of at least {white}: {len(kept)} kept, dropped "
                  f"{dropped}")


if __name__ == "__main__":
    main()
