"""Rule 30 configurations periodic in time and in space, as cycles of the leftward column map.

A column of Rule 30 is a function of the two columns to its right: column j - 1 reads, at step t, column j at step
t + 1 xor (column j or column j + 1) at step t. For columns that repeat a word of length `period`, held as integers with
bit `ph` the letter at phase `ph`, this is the map (a, b) -> (rot(a) xor (a or b), a) on pairs of adjacent columns,
rot(a) reading a one phase later (`left_column` in `computations/lock_chain.py`). The map is not invertible, but on its
cycles it is: a cycle of length S is a configuration on the ring of S cells whose every column repeats with period
dividing `period`, so a background periodic in time and space, and every such background is one. This module finds
every cycle for a given period, by repeated squaring of the map, and the blocks that appear as columns in them.

    python -m computations.space_time_periodic 1,2,3,4,5,6,7,8,9,10,11,12,13   # every background, under a minute
    python -m computations.space_time_periodic 14   # about two minutes and 6 GB
    python -m computations.space_time_periodic 8,10,12,14 --witnesses   # blocks whose game fails at every width
    python -m computations.space_time_periodic 1,2,3,4,5,6,7,8,9,10,11,12,13,14 --table   # the finding's table
    python -m computations.space_time_periodic 8,9,10,11,12,13 --walls 16   # walls the backgrounds seed, a minute
"""

from __future__ import annotations

import argparse
import sys
from collections import Counter

import numpy as np
from tqdm.auto import tqdm


def column_map(period: int) -> np.ndarray:
    """The leftward map on pairs of adjacent columns of words of length `period`, state a 2^period + b for the column a
    and the column b right of it."""
    # out: (4^period,)
    mask = (1 << period) - 1
    kind = np.int32 if 2 * period < 31 else np.int64  # halves the memory of periods up to 15
    states = np.arange(1 << (2 * period), dtype=kind)  # (4^P,)
    a, b = states >> period, states & mask  # (4^P,) each
    rot = (a >> 1) | ((a & 1) << (period - 1))  # (4^P,), bit ph is a at phase ph + 1
    return ((rot ^ (a | b)) << period) | a  # (4^P,)


def cycles(period: int) -> tuple[np.ndarray, np.ndarray]:
    """The states on cycles of `column_map`, and for each the least state of its cycle, which labels the cycle."""
    # out: (c,), (c,)
    f = column_map(period)  # (4^P,)
    g = f.copy()  # (4^P,), f^(2^k) after k squarings
    for _ in tqdm(range(2 * period), desc=f"squarings, period {period}", file=sys.stderr, leave=False):
        g = g[g]  # f^(2^(2P)) takes every state onto its cycle, since no tail is longer than 4^P
    nodes = np.unique(g)  # (c,), the image of f^(2^(2P)): exactly the states on cycles
    index = np.full(f.size, -1, dtype=f.dtype)  # (4^P,)
    index[nodes] = np.arange(nodes.size, dtype=f.dtype)
    step = index[f[nodes]]  # (c,), position of each state's successor
    label = nodes.copy()  # (c,), least state among the first 2^k states from each
    reach = 1
    while reach < nodes.size:
        label = np.minimum(label, label[step])
        step = step[step]
        reach *= 2
    return nodes, label  # (c,), (c,)


def necklace(word: str) -> str:
    """The least rotation of a word."""
    return min(word[i:] + word[:i] for i in range(len(word)))


def least_period(word: str) -> int:
    """The least period of a word read cyclically."""
    return min(p for p in range(1, len(word) + 1) if len(word) % p == 0 and word == word[p:] + word[:p])


def word_of(column: int, period: int) -> str:
    """The column as a word, letter `ph` its bit `ph`."""
    return "".join(str((column >> ph) & 1) for ph in range(period))


def temporal_periods(period: int) -> dict[int, int]:
    """For each cycle label of `cycles`, the temporal period of its background: the least common multiple of the least
    periods of its columns."""
    from math import lcm
    nodes, label = cycles(period)  # (c,), (c,)
    found: dict[int, int] = {}
    for lab, state in zip(label.tolist(), nodes.tolist()):
        found[lab] = lcm(found.get(lab, 1), least_period(word_of(state >> period, period)))
    return found


def table(periods: list[int]) -> list[tuple[int, int, list[int], int, int]]:
    """For each period: the number of backgrounds up to a shift in time, the spatial periods of those whose temporal
    period is exactly that period, the number of blocks of least period that period among their columns, and the
    number of primitive blocks of that period."""
    from computations.game import necklaces
    rows = []
    for period in periods:
        found = backgrounds(period)
        nodes, label = cycles(period)  # (c,), (c,)
        exact = temporal_periods(period)
        lengths = Counter(label.tolist())
        spatial = sorted({lengths[lab] for lab, t in exact.items() if t == period})
        blocks = set().union(*(b for _, _, b in found))
        rows.append((period, len(found), spatial, len(blocks), len(necklaces(period))))
    return rows


def backgrounds(period: int) -> list[tuple[int, int, set[str]]]:
    """The backgrounds for `period`, each the cycles of `column_map` that differ by a shift in time: the length of the
    cycles, the spatial period of the background; how many cycles the class holds; and the blocks of least period
    `period` among the columns, each as its least rotation. Sorted by length."""
    nodes, label = cycles(period)  # (c,), (c,)
    mask = (1 << period) - 1
    cycle_of = dict(zip(nodes.tolist(), label.tolist()))
    sizes = Counter(label.tolist())

    def shifted(state: int, shift: int) -> int:
        a, b = state >> period, state & mask
        a = ((a >> shift) | (a << (period - shift))) & mask
        b = ((b >> shift) | (b << (period - shift))) & mask
        return (a << period) | b

    classes: dict[int, set[int]] = {}
    for lab in sizes:
        members = {cycle_of[shifted(lab, shift)] for shift in range(period)}
        classes.setdefault(min(members), members)
    found = []
    for members in classes.values():
        blocks = {necklace(word_of(int(state) >> period, period)) for state in nodes[np.isin(label, list(members))]}
        found.append((sizes[min(members)], len(members), {b for b in blocks if least_period(b) == period}))
    return sorted(found, key=lambda item: (item[0], sorted(item[2])))


def witnesses(period: int) -> set[tuple[str, int]]:
    """The blocks that a background of `period` shows the finite game cannot exclude: a column of least period p whose
    left neighbor's least period does not divide p, so that the left neighbor takes both values at one phase of the
    block while the cells to the right repeat (negative-results/columns/ring-orbits.md). Each as (block as its least
    rotation, p)."""
    nodes, _ = cycles(period)  # (c,)
    left = column_map(period)[nodes] >> period  # (c,), the column left of each state's first column
    found = set()
    for state, column in zip(nodes.tolist(), left.tolist()):
        word, neighbor = word_of(state >> period, period), word_of(column, period)
        p = least_period(word)
        if p % least_period(neighbor):
            found.add((necklace(word[:p]), p))
    return found


def background_walls(period: int, cells: int, cap: int = 100000) -> list[tuple[int, int, int]]:
    """For each background of `period` and each of its columns whose block has least period `period`: whether the
    background's own window of `cells` cells right of that column, closed under both values of the cell beyond
    (`lock_chain.closure`), fixes column 1 at the white phases, a trap whose chain to the left is the background: a wall
    at its edge. Returns, for each background up to a shift in time that has such columns, its spatial period, the
    number of those columns, and how many of them carry a wall."""
    from computations.lock_chain import closure, escapes, fixes_left
    nodes, label = cycles(period)  # (c,), (c,)
    f = column_map(period)  # (4^P,)
    mask = (1 << period) - 1
    found = []
    for length, count, blocks in backgrounds(period):
        if not blocks:
            continue
        lab = next(int(lab) for lab in set(label.tolist()) if (label == lab).sum() == length and
                   necklace(word_of(lab >> period, period)) in blocks | {necklace(word_of(lab >> period, period))}
                   and {necklace(word_of(int(st) >> period, period)) for st in nodes[label == lab]
                        if least_period(word_of(int(st) >> period, period)) == period} == blocks)
        states = [lab]
        while (nxt := int(f[states[-1]])) != lab:
            states.append(nxt)
        columns = [state >> period for state in states]  # column at position -k is columns[k]
        size = len(columns)
        positions = walls = 0
        for k in tqdm(range(size), desc=f"background of {size} cells", file=sys.stderr, leave=False):
            word = word_of(columns[k], period)
            if least_period(word) != period:
                continue
            positions += 1
            window = sum(((columns[(k - i) % size] >> 0) & 1) << (i - 1) for i in range(1, cells + 1))
            if escapes(word, period, cells, 0, window):
                continue
            trap = closure(word, period, cells, 0, window, cap, locked=True)
            walls += trap is not None and fixes_left(word, trap)
        found.append((size, positions, walls))
    return found


def ring_period(cells: list[int], limit: int) -> int | None:
    """The least number of steps, up to `limit`, after which the ring of cells returns to itself under Rule 30, a
    direct run, or None."""
    row = np.array(cells, dtype=np.uint8)  # (S,)
    start = row.copy()  # (S,)
    for t in range(1, limit + 1):
        row = np.roll(row, 1) ^ (row | np.roll(row, -1))  # cell i reads cells i - 1, i, i + 1 on the ring
        if np.array_equal(row, start):
            return t
    return None


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("periods", type=str, help="temporal periods, comma separated")
    parser.add_argument("--witnesses", action="store_true", help="the blocks each period's backgrounds witness")
    parser.add_argument("--table", action="store_true", help="a markdown table of the backgrounds of each period")
    parser.add_argument("--walls", type=int, default=0, help="with a width, the walls seeded by each background")
    args = parser.parse_args()
    if args.walls:
        for period in [int(p) for p in args.periods.split(",")]:
            print(f"period {period}, width {args.walls}: (spatial period, columns of the period, walls) "
                  f"{background_walls(period, args.walls)}", flush=True)
        return
    if args.table:
        print("| Period | Backgrounds | Of exactly this period, by spatial period | Blocks among their columns |")
        print("|---:|---:|---|---:|")
        for period, count, spatial, blocks, total in table([int(p) for p in args.periods.split(",")]):
            print(f"| {period} | {count} | {', '.join(f'{s:,}' for s in spatial) or 'none'} | {blocks} of {total} |",
                  flush=True)
        return
    for period in [int(p) for p in args.periods.split(",")]:
        if args.witnesses:
            print(f"period {period}: witnesses {sorted(witnesses(period), key=lambda w: (w[1], w[0]))}", flush=True)
            continue
        found = backgrounds(period)
        blocks = set().union(*(b for _, _, b in found))
        lengths = [length for length, _, _ in found]
        cycle_count = sum(count for _, count, _ in found)
        print(f"period {period}: {cycle_count} cycles in {len(found)} backgrounds up to a shift "
              f"in time, of spatial periods {lengths}; {len(blocks)} blocks of least period {period} appear as "
              f"columns", flush=True)
        for length, count, b in found:
            if b:
                print(f"  spatial period {length} ({count} shifts): {len(b)} blocks: {' '.join(sorted(b))}", flush=True)


if __name__ == "__main__":
    main()
