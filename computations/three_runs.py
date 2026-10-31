"""The rank certificate of `Rule30Open.Columns.ThreeRuns`: beside a center repeating 001, column 1 read at the second
white step of each period avoids 010, 101 and 1001 from a bounded time on, whatever the right half.

A state is a phase p = (t + ph) % 3 (the center reads 001[p], so p = 2 is the black step and p = 1 the second white
step), the last three readings (newest in bit 0) and the window of columns 1..W (bit i is column i + 1). One step moves
the window with column W + 1 free, as the kit's `stripStep`. The good set is the greatest set of states that both
successors keep without a reading completing a forbidden word; the rank of a state is the most steps any choice of
column W + 1 needs to reach it. At width 13 every state has a rank, at most 46, and the tables of `ThreeRuns.lean` pack
the rank of window w in bits 6w to 6w + 5 of entry 8p + s.

    python -m computations.three_runs            # the good set and the largest rank at width 13
    python -m computations.three_runs --check    # the tables in ThreeRuns.lean are these ranks
    python -m computations.three_runs --lean     # print the tables as Lean
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

import numpy as np

BLOCK = "001"
FREE_PHASE = 1
WORDS = ("010", "101", "1001")
LEAN_FILE = Path(__file__).resolve().parent.parent / "Rule30Open" / "Columns" / "ThreeRuns.lean"


def step(w: np.ndarray, width: int, c: int, x: int) -> np.ndarray:
    """One step of windows of columns 1..width with the center c and column width + 1 equal to x."""
    # w: (n,) int64 -> (n,) int64
    mask = (1 << width) - 1
    return (((w << 1) | c) ^ (w | (w >> 1) | (x << (width - 1)))) & mask


def completes(s: int, b: int) -> bool:
    """Whether the reading b after the last three readings s (newest in bit 0) completes a forbidden word."""
    text = format(s, "03b") + str(b)
    return any(text.endswith(word) for word in WORDS)


def ranks(width: int) -> tuple[np.ndarray, np.ndarray]:
    """The good set and the rank of every state, -1 where no rank exists."""
    n = 1 << width
    win = np.arange(n, dtype=np.int64)  # (n,)
    nxt = [[step(win, width, int(BLOCK[p]), x) for x in (0, 1)] for p in range(3)]  # 3 x 2 x (n,)
    suf = np.arange(8)  # (8,)
    snext = np.zeros((3, n, 8), dtype=np.int64)  # (3, n, 8): the readings after the step
    bad = np.zeros((3, n, 8), dtype=bool)  # (3, n, 8): a forbidden word completes at this step
    for p in range(3):
        if p == FREE_PHASE:
            snext[p] = ((suf[None, :] << 1) | (win & 1)[:, None]) & 7
            for s in range(8):
                for b in (0, 1):
                    bad[p, (win & 1) == b, s] = completes(s, b)
        else:
            snext[p] = suf[None, :]
    good = np.ones((3, n, 8), dtype=bool)  # (3, n, 8)
    while True:
        new = good & ~bad
        for p in range(3):
            q = (p + 1) % 3
            for x in (0, 1):
                new[p] &= good[q][nxt[p][x][:, None], snext[p]]
        if np.array_equal(new, good):
            break
        good = new
    rank = np.where(good, 0, -1)  # (3, n, 8)
    k = 0
    while True:
        done = rank >= 0
        add = np.zeros_like(done)  # (3, n, 8)
        for p in range(3):
            q = (p + 1) % 3
            add[p] = done[q][nxt[p][0][:, None], snext[p]] & done[q][nxt[p][1][:, None], snext[p]]
        add &= ~done
        if not add.any():
            return good, rank
        k += 1
        rank[add] = k


def tables(rank: np.ndarray) -> list[int]:
    """The 24 packed rank tables, entry 8p + s holding the rank of window w in bits 6w to 6w + 5."""
    out = []
    for p in range(3):
        for s in range(8):
            value = 0
            for w in range(rank.shape[1] - 1, -1, -1):
                value = (value << 6) | int(rank[p, w, s])
            out.append(value)
    return out


def lean_tables() -> list[int]:
    """The tables written in ThreeRuns.lean."""
    source = LEAN_FILE.read_text(encoding="utf-8")
    body = source.split("def rankTabs : List Nat := [", 1)[1].split("]", 1)[0]
    return [int(h, 16) for h in re.findall(r"0x[0-9a-f]+", body)]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--width", type=int, default=13)
    parser.add_argument("--check", action="store_true", help="compare with the tables in ThreeRuns.lean")
    parser.add_argument("--lean", action="store_true", help="print the tables as Lean")
    args = parser.parse_args()
    good, rank = ranks(args.width)
    forced = bool((rank >= 0).all())
    print(f"width {args.width}: good set of {int(good.sum())} of {good.size} states; entry "
          + (f"forced within {int(rank.max())} steps" if forced else f"not forced from {int((rank < 0).sum())} states"),
          file=sys.stderr)
    if args.check:
        same = forced and tables(rank) == lean_tables()
        print("the tables of ThreeRuns.lean are these ranks" if same else "the tables differ", file=sys.stderr)
        sys.exit(0 if same else 1)
    if args.lean:
        print("def rankTabs : List Nat := [")
        print(",\n".join(f"  {hex(v)}" for v in tables(rank)))
        print("]")


if __name__ == "__main__":
    main()
