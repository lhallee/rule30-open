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
    parser.add_argument("--brute", type=int, default=0,
                        help="instead, the segments up to this length that brute force accepts and the run does not")
    args = parser.parse_args()

    if args.brute:
        extra = [u for m in tqdm(range(1, args.brute + 1), desc="lengths", file=sys.stderr)
                 for u in ("".join(bits) for bits in itertools.product("01", repeat=m))
                 if u[0] == "0" and u[-1] == "0" and "1" * 9 not in u and not segment_good(u) and brute_segment(u)]
        print(f"{len(extra)} segments of at most {args.brute} cells that start and end with 0 are determined by brute "
              f"force and not by the three-valued run: {extra}")
        return

    total = runs = 0
    for period in tqdm(range(1, args.max_period + 1), desc="periods", file=sys.stderr):
        blocks = necklaces(period)
        family = [b for b in blocks if in_family(b)]
        kit = [b for b in family if long_runs(b)]
        total, runs = total + len(family), runs + len(kit)
        print(f"period {period}: {len(family)} blocks in the family, {len(kit)} with every run of 1s at least nine "
              f"long")
    print(f"up to period {args.max_period}: {total} blocks, {total - runs} beyond the black-runs family")
    if args.game:
        from computations import game
        nine = [b for p in range(1, args.max_period + 1) for b in necklaces(p) if "1" * 9 in b + b or b == "1"]
        excluded = {b for b in tqdm(nine, desc="game", file=sys.stderr) if game.least_width(b, 14) is not None}
        family = {b for b in nine if in_family(b)}
        kit = game.kit_blocks(args.max_period)
        print(f"{len(nine)} blocks with nine 1s in a row; the game excludes {len(excluded)}, the family {len(family)}; "
              f"in the family but not excluded by the game: {sorted(family - excluded)}; excluded by the game only: "
              f"{len(excluded - family)}; in the family and beyond the kit's blocks: {len(family - set(kit))}")


if __name__ == "__main__":
    main()
