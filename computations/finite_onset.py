"""Rows finite on both sides at the onset: the one left half that keeps the center on a block, for small right halves.

Suppose a finite row has a center column that repeats a block b from time 0 (the onset; any eventually periodic center
is one in a later row, which is again finite). Its right half R drives column 1 whatever the left half holds, and Rule
30 is permutive in its left input, so exactly one left half keeps the center on b against R: Psi_b(R) of
`computations.coupled` (the kit's `Psi_unique`). A left half of width W keeps the center on b through time d - 1 and
leaves it at time d, where d is the first depth at which it differs from Psi_b(R) (the kit's `exact_death_center`). So a
finite onset row with right half R exists exactly when Psi_b(R) is white beyond some depth, and a left half of width W
below the last black depth of Psi_b(R) leaves b by time W + r + 1, r being the longest white run of Psi_b(R).

`census` computes Psi_b(R) to a depth for every primitive block of the given periods, every phase and every right half
of at most k cells (bit i of R is column i + 1), all right halves of a block at once as NumPy bit slices, and sorts each
into three classes: locked (its outer half repeats with a period up to `max_period`), white tail (no black cell in its
outer half) and aperiodic. `block` does one block, and `empty` the white right half alone to a large depth.

    python -m computations.finite_onset census --depth 1024 --more 2              # the 92 blocks, about 3 min
    python -m computations.finite_onset census --depth 1024                       # two cells fewer, 30 s
    python -m computations.finite_onset block 011 --cells 14 --depth 4096         # one block
    python -m computations.finite_onset empty 011 --depth 32768                   # Psi of the white right half
"""

from __future__ import annotations

import argparse
import sys
import time
from dataclasses import dataclass

import numpy as np
from tqdm.auto import tqdm

from computations.coupled import drive_column, eventual_period, psi, white_runs
from computations.game import necklaces
from computations.periodic_columns import initial_rows

U64 = np.uint64
ALL = U64(0xFFFFFFFFFFFFFFFF)
# The right half widths of the census: 2^k right halves per phase, so that every period costs about the same.
PLAN = {2: 12, 3: 12, 5: 12, 6: 11, 7: 10, 9: 9}


def psi_slices(word: str, phase: int, cells: int, depth: int, first_lane: int = 0, lanes: int | None = None
               ) -> np.ndarray:
    """Psi_b(R) at depths 1 .. `depth` for the right halves R = 64 first_lane .. 64 (first_lane + lanes) - 1 of at
    most `cells` cells, as bit slices: bit i of lane l of row j is the cell at depth j + 1 of Psi(64 (first_lane + l)
    + i). With fewer than six cells the right halves repeat across the 64 bits of a lane."""
    if lanes is None:
        lanes = max(1, (1 << cells) // 64) - first_lane
    period = len(word)
    c = [ALL if word[(t + phase) % period] == "1" else U64(0) for t in range(depth + 1)]
    # The driven right half: index x is column x + 1. Column 1 at time t needs columns up to depth - t + 1 at time t.
    rows = initial_rows(min(cells, depth + 1), first_lane, lanes, depth + 1, 0)  # (depth + 1, lanes)
    column = np.empty((depth + 1, lanes), dtype=U64)  # (depth + 1, lanes), column 1 at times 0 .. depth
    for t in range(depth + 1):
        column[t] = rows[0]
        if t == depth:
            break
        left = np.empty_like(rows[:-1])  # (depth - t, lanes), the cell left of each kept cell
        left[0] = c[t]
        left[1:] = rows[:-2]
        rows = left ^ (rows[:-1] | rows[1:])  # (depth - t, lanes)
    center = np.array(c, dtype=U64)[:, None]  # (depth + 1, 1), column 0
    a = center[1:] ^ (center[:-1] | column[:-1])  # (depth, lanes), column -1 at times 0 .. depth - 1
    b = np.broadcast_to(center[:-1], a.shape)  # (depth, lanes), column 0 at the same times
    out = np.empty((depth, lanes), dtype=U64)  # (depth, lanes)
    for j in range(depth):
        out[j] = a[0]  # column -j - 1 at time 0
        a, b = a[1:] ^ (a[:-1] | b[:-1]), a[:-1]  # column -j - 2 from columns -j - 1 and -j
    return out


def unpack(slices: np.ndarray, count: int) -> np.ndarray:
    """Bit slices (depth, lanes) as a boolean array (depth, count), column r being right half r."""
    bits = np.unpackbits(np.ascontiguousarray(slices).view(np.uint8), axis=1, bitorder="little")  # (depth, 64 lanes)
    return bits[:, :count].astype(bool)


def as_int(rows: np.ndarray) -> int:
    """One Psi row given as booleans by depth (depth 1 first) as an integer, bit j being depth j + 1."""
    # rows: (depth,)
    return int.from_bytes(np.packbits(rows, bitorder="little").tobytes(), "little")


@dataclass
class Census:
    """The census of one block and phase over every right half of at most `cells` cells, to `depth`."""

    word: str
    phase: int
    cells: int
    depth: int
    halves: int  # right halves
    locked: list[tuple[int, int, int]]  # (right half, start depth, period) of each locked Psi
    white_tail: list[int]  # right halves whose Psi is white on its outer half
    aperiodic: int
    longest_run: int  # over every right half: the longest white run that ends in a black cell
    longest_witness: int  # a right half that attains it
    last_black: int  # over every right half: the least last black depth
    last_witness: int


def classify(word: str, phase: int, cells: int, depth: int, max_period: int = 128) -> Census:
    """Psi_b(R) for every right half R of at most `cells` cells, sorted into locked (the outer half repeats with a
    period up to `max_period` and a quarter of the outer half), white tail and aperiodic."""
    count = 1 << cells
    slices = psi_slices(word, phase, cells, depth)  # (depth, lanes)
    half = depth // 2
    outer = slices[half:]  # (depth - half, lanes)
    tail_white = ~np.bitwise_or.reduce(outer, axis=0)  # (lanes,), bit set where the outer half is white
    repeats = np.zeros_like(tail_white)  # (lanes,), bit set where the outer half repeats with some period
    for p in range(1, min(max_period, (depth - half) // 4) + 1):  # each period checked over three quarters of it
        repeats |= ~np.bitwise_or.reduce(outer[p:] ^ outer[:-p], axis=0)
    rows = unpack(slices, count)  # (depth, count)
    white = unpack(tail_white[None, :], count)[0]  # (count,)
    locked_mask = unpack(repeats[None, :], count)[0] & ~white  # (count,)
    aperiodic = ~white & ~locked_mask  # (count,)
    run = np.zeros(count, dtype=np.int64)  # (count,), the current white run
    longest = np.zeros(count, dtype=np.int64)  # (count,), the longest white run ending in a black cell
    for j in range(depth):
        longest = np.where(rows[j], np.maximum(longest, run), longest)
        run = np.where(rows[j], 0, run + 1)
    last = np.where(rows.any(axis=0), depth - np.argmax(rows[::-1], axis=0), 0)  # (count,), the last black depth
    locked = []
    for r in np.flatnonzero(locked_mask):
        start, p = eventual_period(as_int(rows[:, r]), depth, max_period)
        locked.append((int(r), start, p))
    return Census(word=word, phase=phase, cells=cells, depth=depth, halves=count, locked=locked,
                  white_tail=[int(r) for r in np.flatnonzero(white)], aperiodic=int(aperiodic.sum()),
                  longest_run=int(longest.max()), longest_witness=int(np.argmax(longest)),
                  last_black=int(last.min()), last_witness=int(np.argmin(last)))


def column_repeats(word: str, phase: int, right: int, depth: int, max_period: int = 256) -> tuple[int, int] | None:
    """Whether column 1 of the right half driven by the block repeats over the outer half of times 0 .. depth: its
    (start time + 1, period), as `eventual_period` gives them, or None."""
    return eventual_period(drive_column(word, phase, right, depth + 1), depth + 1, max_period)


def lock_fate(word: str, phase: int, right: int, start: int, period: int, depth: int) -> int | None:
    """For a locked case, Psi_b(R) to `depth`: the first depth at which it stops repeating with `period` from depth
    `start`, or None when it repeats to `depth` and column 1 repeats over the outer half of the times too."""
    bits = format(psi(word, phase, right, depth), "b").zfill(depth)[::-1]  # depth 1 first
    for j in range(start - 1, depth - period):
        if bits[j] != bits[j + period]:
            return j + period + 1
    return None if column_repeats(word, phase, right, depth) is not None else depth + 1


def block_summary(word: str, cells: int, depth: int, confirm: int = 4) -> dict[str, object]:
    """Every phase of one block: right halves, locked, white tails, aperiodic, and over every right half the longest
    white run and the least last black depth, with witnesses. Each locked case is followed to `confirm` times the
    depth: it persists, or its repetition breaks at a depth that is recorded."""
    results = [classify(word, phase, cells, depth) for phase in range(len(word))]
    locked = [(c.phase, *entry) for c in results for entry in c.locked]
    fates = [lock_fate(word, phase, r, start, p, confirm * depth) for phase, r, start, p in locked]
    run = max(results, key=lambda c: c.longest_run)
    last = min(results, key=lambda c: c.last_black)
    return {"word": word, "cells": cells, "halves": sum(c.halves for c in results), "locked": len(locked),
            "confirmed": sum(f is None for f in fates), "breaks": sorted(f for f in fates if f is not None),
            "periods": sorted({p for _, _, _, p in locked}), "locked_cases": locked,
            "white_tail": sum(len(c.white_tail) for c in results), "aperiodic": sum(c.aperiodic for c in results),
            "longest_run": run.longest_run, "run_witness": (run.phase, run.longest_witness),
            "last_black": last.last_black, "last_witness": (last.phase, last.last_witness)}


def run_census(periods: list[int], depth: int, cells: int | None, more: int = 0) -> list[dict[str, object]]:
    """The census of every primitive block of the given periods, with `cells` cells or the widths of PLAN plus
    `more`."""
    words = [w for p in periods for w in necklaces(p)]
    out = []
    for word in tqdm(words, desc="blocks", file=sys.stderr, leave=False):
        out.append(block_summary(word, cells if cells is not None else PLAN[len(word)] + more, depth))
    return out


def report(rows: list[dict[str, object]], depth: int) -> None:
    """Print the census as Markdown table rows and the totals."""
    print(f"Psi_b(R) to depth {depth}; per block: cells k of the right halves, right halves times phases, locked (of "
          f"them still locked at depth {4 * depth}, Psi and column 1), white tails, longest white run and least last "
          "black depth over every case")
    print("| block | k | cases | locked | white tail | longest white run | least last black depth |")
    print("|---|---|---|---|---|---|---|")
    for r in rows:
        print(f"| {r['word']} | {r['cells']} | {r['halves']:,} | {r['locked']} ({r['confirmed']}) | "
              f"{r['white_tail']} | {r['longest_run']} | {r['last_black']:,} |")
    total = sum(int(r["halves"]) for r in rows)
    locked = sum(int(r["locked"]) for r in rows)
    print(f"blocks {len(rows)}, cases {total:,}, locked {locked} (still locked at depth {4 * depth}: "
          f"{sum(int(r['confirmed']) for r in rows)}), white tails {sum(int(r['white_tail']) for r in rows)}, "
          f"aperiodic {sum(int(r['aperiodic']) for r in rows):,}; longest white run "
          f"{max(int(r['longest_run']) for r in rows)}, least last black depth "
          f"{min(int(r['last_black']) for r in rows)}")
    print("| block | locked | periods | persist | repetition broken at depth |")
    print("|---|---|---|---|---|")
    for r in rows:
        if r["locked"]:
            breaks = list(r["breaks"])  # type: ignore[call-overload]
            periods = ", ".join(str(p) for p in r["periods"])  # type: ignore[attr-defined]
            span = f"{breaks[0]:,} to {breaks[-1]:,}" if breaks else "none"
            print(f"| {r['word']} | {r['locked']} | {periods} | {r['confirmed']} | {span} |")
    by_period: dict[int, list[dict[str, object]]] = {}
    for r in rows:
        by_period.setdefault(len(str(r["word"])), []).append(r)
    for p, rs in by_period.items():
        runs = [int(r["longest_run"]) for r in rs]
        lasts = [int(r["last_black"]) for r in rs]
        print(f"period {p}: {len(rs)} blocks, longest white run {min(runs)} to {max(runs)}, least last black depth "
              f"{min(lasts)} to {max(lasts)}, locked {sum(int(r['locked']) for r in rs)}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("mode", choices=["census", "block", "empty"])
    parser.add_argument("word", nargs="?", help="block and empty: the block, as a word of 0s and 1s")
    parser.add_argument("--periods", default="2,3,5,6,7,9", help="census: the periods")
    parser.add_argument("--cells", type=int, default=None, help="right halves of at most this many cells "
                        "(census: the widths of PLAN when left out)")
    parser.add_argument("--more", type=int, default=0, help="census: cells added to each width of PLAN")
    parser.add_argument("--depth", type=int, default=1024, help="depths of Psi computed")
    args = parser.parse_args()

    started = time.perf_counter()
    if args.mode == "census":
        report(run_census([int(p) for p in args.periods.split(",")], args.depth, args.cells, args.more), args.depth)
    elif args.mode == "block":
        row = block_summary(args.word, args.cells if args.cells is not None else 12, args.depth)
        report([row], args.depth)
        for phase, r, start, p in row["locked_cases"]:  # type: ignore[union-attr]
            print(f"  locked: phase {phase}, right half {r:b} (column 1 first: {format(r, 'b')[::-1]}), period {p} "
                  f"from depth {start}")
        print(f"  longest run at (phase, right half) {row['run_witness']}, least last black at {row['last_witness']}")
    else:
        for phase in range(len(args.word)):
            row = psi(args.word, phase, 0, args.depth)
            ev = eventual_period(row, args.depth, 256)
            runs = white_runs(row, args.depth)
            print(f"{args.word} phase {phase}: {row.bit_count()} black cells at depths 1 to {args.depth}, the last "
                  f"at {row.bit_length()}; longest white run {runs[-1][0] if runs else 0}; record white runs "
                  f"(length, first depth) {runs}; repeating outer half: "
                  f"{'none' if ev is None else f'period {ev[1]} from depth {ev[0]}'}")
    print(f"({time.perf_counter() - started:.0f} s)")


if __name__ == "__main__":
    main()
