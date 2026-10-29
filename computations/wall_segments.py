"""After nine 1s in a column the two cells right of it read 0 1. Which later segments keep the next cell known?

Three-valued Rule 30 on the two cells right of a column, with the cell beyond them unknown (`step`), starts from the
wall 0 1 that nine 1s leave (Lean: `wall_forms` in `Rule30Open.Columns.LongRuns`). A segment of the column is good
(`segment_good`) if the cell right of the column is known at each of its 0s. A block is in the family (`in_family`) if
it has nine 1s in a row, read cyclically, and every stretch after nine 1s is good; then the column left of it is a
function of the column, and no column of a row with a leftmost 1 can repeat the block (Lean: `wall_block_column` in
`Rule30Open.Columns.WallSegments`, with `wallGood` the same computation).

    python -m computations.wall_segments --max-period 20   # the family's blocks by period, against the kit's runs
    python -m computations.wall_segments --max-period 16 --game   # and against the finite game
    python -m computations.wall_segments --brute 12   # segments that brute force accepts beyond the five forms
    python -m computations.wall_segments --tails   # the tails long runs rule out, against the kit's Theorems B and D
"""

from __future__ import annotations

import argparse
import itertools
import sys
import numpy as np

from tqdm.auto import tqdm


Tri = int | None  # a known cell (0 or 1) or an unknown one (None)
WALL: tuple[Tri, Tri] = (0, 1)


def t_or(a: Tri, b: Tri) -> Tri:
    """Three-valued OR."""
    if a == 1 or b == 1:
        return 1
    if a is None or b is None:
        return None
    return 0


def t_xor(a: Tri, b: Tri) -> Tri:
    """Three-valued XOR."""
    return None if a is None or b is None else a ^ b


def step(state: tuple[Tri, Tri], col: int) -> tuple[Tri, Tri]:
    """One step of the two cells right of a column that reads `col`, the cell beyond them unknown (Lean: `tstep`)."""
    c1, c2 = state
    return t_xor(col, t_or(c1, c2)), t_xor(c1, t_or(c2, None))


def segment_good(segment: str) -> bool:
    """Whether, from the wall, the cell right of the column is known at every 0 of `segment`."""
    state = WALL
    for ch in segment:
        if ch == "0" and state[0] is None:
            return False
        state = step(state, int(ch))
    return True


def brute_segment(segment: str) -> bool:
    """Whether the true cell right of the column is the same at every 0 of `segment`, over every choice of the cells
    beyond the wall that can reach it: an independent check that `segment_good` is sound."""
    m = len(segment)
    width = m + 3
    n = 1 << width
    idx = np.arange(n, dtype=np.int64)  # (n,)
    cells = np.zeros((n, 2 + width + 2), dtype=np.uint8)  # (n, cells), column j + 1 right of the column at index j
    cells[:, 0], cells[:, 1] = 0, 1
    for j in range(width):
        cells[:, 2 + j] = (idx >> j) & 1
    for ch in segment:
        if ch == "0" and cells[:, 0].min() != cells[:, 0].max():
            return False
        left = np.concatenate([np.full((n, 1), int(ch), dtype=np.uint8), cells[:, :-1]], axis=1)  # (n, cells)
        right = np.concatenate([cells[:, 1:], np.zeros((n, 1), dtype=np.uint8)], axis=1)  # (n, cells)
        cells = left ^ (cells | right)
    return True


def in_family(block: str) -> bool:
    """Whether some phase of `block`, read cyclically, follows nine 1s, and from there the state, reset to the wall
    after every nine 1s, knows the cell right of the column at every 0 of one period (Lean: `wallGood`)."""
    period = len(block)
    col = [int(c) for c in block]
    resets = [i for i in range(period) if all(col[(i - 1 - j) % period] for j in range(9))]  # nine 1s before phase i
    if not resets:
        return False
    state = WALL
    for j in range(period):
        i = (resets[0] + j) % period
        if j > 0 and i in resets:
            state = WALL
        if col[i] == 0 and state[0] is None:
            return False
        state = step(state, col[i])
    return True


Window = tuple[int, ...]


def window_step(windows: frozenset[Window], col: int) -> frozenset[Window]:
    """One step of the set of windows right of a column that reads `col`, the cell beyond a window free (Lean:
    `sstep` for windows of three cells)."""
    out = set()
    for window in windows:
        for free in (0, 1):
            cells = (col,) + window + (free,)
            out.add(tuple(cells[i - 1] ^ (cells[i] | cells[i + 1]) for i in range(1, len(window) + 1)))
    return frozenset(out)


def wall_windows(width: int) -> frozenset[Window]:
    """The windows that nine 1s leave: the first two cells 0 1, the rest free."""
    return frozenset(w for w in itertools.product((0, 1), repeat=width) if w[0] == 0 and w[1] == 1)


def set_segment_good(segment: str, width: int = 3) -> bool:
    """Whether, from the wall, every window of the set has the same first cell at every 0 of `segment`."""
    windows = wall_windows(width)
    for ch in segment:
        if ch == "0" and len({w[0] for w in windows}) > 1:
            return False
        windows = window_step(windows, int(ch))
    return True


def in_set_family(block: str, width: int = 3) -> bool:
    """`in_family` with the set of windows in place of the three values (Lean: `wallSet` for width 3)."""
    period = len(block)
    col = [int(c) for c in block]
    resets = [i for i in range(period) if all(col[(i - 1 - j) % period] for j in range(9))]
    if not resets:
        return False
    windows = wall_windows(width)
    for j in range(period):
        i = (resets[0] + j) % period
        if j > 0 and i in resets:
            windows = wall_windows(width)
        if col[i] == 0 and len({w[0] for w in windows}) > 1:
            return False
        windows = window_step(windows, col[i])
    return True


def windows_after_ones(ones: int, width: int = 3) -> frozenset[Window]:
    """The windows of `width` cells right of a column after it reads 1 for `ones` steps, over every start of the cells
    that can reach them: nine 1s leave the wall, fewer leave both values of the first cell."""
    out = set()
    for bits in itertools.product((0, 1), repeat=width + ones + 1):
        cells = list(bits)  # cells right of the column, the first at index 0
        for _ in range(ones):
            ext = [1] + cells + [0]
            cells = [ext[i - 1] ^ (ext[i] | ext[i + 1]) for i in range(1, len(ext) - 1)]
        out.add(tuple(cells[:width]))
    return frozenset(out)


def stripe(length: int) -> list[int]:
    """The stripe of `length` cells right of the column that ends in a black cell: cell i, counted from 1, is black when
    `length - i` is even. The shield (0 1)^j that 9 j 1s leave is the stripe of length 2 j."""
    return [int((length - i) % 2 == 0) for i in range(1, length + 1)]


def stripe_known_steps(length: int) -> int:
    """The first step at which three-valued Rule 30, started from the stripe of `length` cells with every cell beyond
    unknown, can lose the cell right of the column, over every column it may read (Lean: `stripe_agree` proves that it
    does not before step 2 L)."""
    start = tuple(stripe(length) + [None] * 2)
    frontier = {start}
    for s in range(1, 4 * length + 4):
        nxt = set()
        for cells in frontier:
            for col in (0, 1):
                nxt.add(tuple(t_xor(col if i == 0 else cells[i - 1],
                                    t_or(cells[i], cells[i + 1] if i + 1 < len(cells) else None))
                              for i in range(len(cells))))
        frontier = nxt
        if any(cells[0] is None for cells in frontier):
            return s
    return -1


def stripe_brute(length: int, steps: int) -> bool:
    """Whether the true cell right of the column at each step below `steps` is the same for every choice of the cells
    beyond the stripe of `length` cells, for every column of `steps` values: brute force, independent of the three
    values. Cells farther than `steps` from the column cannot reach it in time, so the cells up to `steps + 1` are
    free and the rest are 0."""
    beyond = max(steps + 1 - length, 1)
    for col in itertools.product((0, 1), repeat=steps):
        seen: list[set[int]] = [set() for _ in range(steps)]
        for bits in itertools.product((0, 1), repeat=beyond):
            cells = stripe(length) + list(bits)  # (length + beyond,)
            for s in range(steps):
                seen[s].add(cells[0])
                ext = [col[s]] + cells + [0]
                cells = [ext[i - 1] ^ (ext[i] | ext[i + 1]) for i in range(1, len(ext) - 1)]
        if any(len(values) > 1 for values in seen):
            return False
    return True


def least_white_run(tail: int) -> tuple[int, int]:
    """The least white run b, after nine or more 1s, that rules out every tail of `tail` steps: by
    `black_white_tail_column` (a tail of at most 4 floor((b - 1)/9) + 2 steps) and by the kit's Theorem D
    (b at least 1 + 9 ceil((tail + 8)/2))."""
    ours = 1
    while tail > 4 * ((ours - 1) // 9) + 2:
        ours += 1
    return ours, 1 + 9 * ((tail + 9) // 2)


def longest_tail(run: int) -> tuple[int, int]:
    """The longest tail that a black run of `run` steps, at least nine, rules out: by `long_run_tail_column`
    (4 floor(run/9) steps) and by the kit's Theorem B (the longest tail t with 9 ceil((t + 9)/2) at most `run`, or -1
    when there is none)."""
    kit = -1
    while 9 * ((kit + 1 + 10) // 2) <= run:
        kit += 1
    return 4 * (run // 9), kit


def necklaces(period: int) -> list[str]:
    """The primitive binary necklaces of length `period`, each as its least rotation."""
    out = []
    for bits in itertools.product("01", repeat=period):
        word = "".join(bits)
        rotations = [word[i:] + word[:i] for i in range(period)]
        if word == min(rotations) and len(set(rotations)) == period:
            out.append(word)
    return out


def long_runs(block: str) -> bool:
    """Whether every run of 1s of `block`, read cyclically, lasts at least nine steps (the kit's black-runs family)."""
    if "0" not in block:
        return True
    rotated = block[block.index("0"):] + block[:block.index("0")]
    return all(len(run) >= 9 for run in rotated.split("0") if run)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--max-period", type=int, default=20)
    parser.add_argument("--game", action="store_true", help="also run the finite game on the blocks with nine 1s")
    parser.add_argument("--after-ones", action="store_true",
                        help="instead, the windows that runs of 1 to 9 ones leave")
    parser.add_argument("--brute", type=int, default=0,
                        help="instead, the segments up to this length that brute force accepts and the run does not")
    parser.add_argument("--tails", action="store_true",
                        help="instead, the tails that long black runs and white runs after them rule out, against "
                             "the kit's Theorems B and D")
    args = parser.parse_args()

    if args.tails:
        for run in (9, 18, 27, 45, 90):
            ours, kit = longest_tail(run)
            print(f"black run of {run}: tails of at most {ours} steps (kit's Theorem B: {kit})")
        for tail in range(0, 12):
            ours, kit = least_white_run(tail)
            print(f"tail of {tail} after nine 1s and a white run: white run of at least {ours} (kit's Theorem D: {kit})")
        return

    if args.after_ones:
        for ones in range(1, 10):
            windows = windows_after_ones(ones)
            names = sorted("".join(map(str, w)) for w in windows)
            known = "known" if len({w[0] for w in windows}) == 1 else "unknown"
            print(f"after {ones} ones: {len(windows)} windows {names}, first cell {known}")
        return
    if args.brute:
        extra = [u for m in tqdm(range(1, args.brute + 1), desc="lengths", file=sys.stderr)
                 for u in ("".join(bits) for bits in itertools.product("01", repeat=m))
                 if u[0] == "0" and u[-1] == "0" and "1" * 9 not in u and not segment_good(u) and brute_segment(u)]
        print(f"{len(extra)} segments of at most {args.brute} cells that start and end with 0 are determined by brute "
              f"force and not by the three-valued run: {extra}")
        segments = [u for m in range(1, args.brute + 1)
                    for u in ("".join(bits) for bits in itertools.product("01", repeat=m))
                    if u[0] == "0" and u[-1] == "0" and "1" * 9 not in u]
        brute = {u for u in segments if brute_segment(u)}
        for width in (3, 8):
            accepted = {u for u in segments if set_segment_good(u, width)}
            print(f"sets of windows of {width} cells: accept {len(accepted & brute)} of the {len(brute)} segments "
                  f"brute force accepts, and {len(accepted - brute)} it does not")
        return

    total = runs = sets = 0
    for period in tqdm(range(1, args.max_period + 1), desc="periods", file=sys.stderr):
        blocks = necklaces(period)
        family = [b for b in blocks if in_family(b)]
        kit = [b for b in family if long_runs(b)]
        windows = [b for b in blocks if in_set_family(b)]
        total, runs, sets = total + len(family), runs + len(kit), sets + len(windows)
        print(f"period {period}: {len(family)} blocks in the family, {len(kit)} with every run of 1s at least nine "
              f"long, {len(windows)} in the family of sets of windows")
    print(f"up to period {args.max_period}: {total} blocks, {total - runs} beyond the black-runs family; {sets} with "
          f"sets of windows of three cells")
    if args.game:
        from computations import game
        nine = [b for p in range(1, args.max_period + 1) for b in necklaces(p) if "1" * 9 in b + b or b == "1"]
        excluded = {b for b in tqdm(nine, desc="game", file=sys.stderr) if game.least_width(b, 14) is not None}
        family = {b for b in nine if in_family(b)}
        windows = {b for b in nine if in_set_family(b)}
        print(f"sets of windows: {len(windows)} blocks; not excluded by the game: {sorted(windows - excluded)}; "
              f"excluded by the game only: {len(excluded - windows)}; beyond the kit's blocks: "
              f"{len(windows - set(game.kit_blocks(args.max_period)))}")
        kit = game.kit_blocks(args.max_period)
        print(f"{len(nine)} blocks with nine 1s in a row; the game excludes {len(excluded)}, the family {len(family)}; "
              f"in the family but not excluded by the game: {sorted(family - excluded)}; excluded by the game only: "
              f"{len(excluded - family)}; in the family and beyond the kit's blocks: {len(family - set(kit))}")


if __name__ == "__main__":
    main()
