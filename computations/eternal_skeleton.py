"""The limit set of rule 30 in the frame of a left edge: every row white left of a black cell, read on its first n
left diagonals, ends on one cycle, the single cell's, for n up to 22.

A row white left of a cell, read from that cell rightward, is a sequence R with R_d the cell on left diagonal d. One
step of rule 30 with the frame moved one cell left is

    leftStep(R)_d = R_{d-2} xor (R_{d-1} or R_d),   R_{-1} = R_{-2} = 0,

so the first n coordinates of the image depend only on the first n coordinates: on n-bit states (bit d is R_d) the
step is ((s << 2) xor ((s << 1) or s)) mod 2^n, a map G_n of a finite set. The limit set of G_n on the states with a
black edge cell (bit 0 set) is the eventual image, the union of its cycles; it is the projection of the rows of the
eternal orbits (`Rule30Open.Diagonals.EternalSkeleton`).

- `left_step`: G_n on an array of states.
- `limit_set`: the eventual image of the states with bit 0 set, and the number of steps after which every state is in
  it (the uniform settling time of the first n diagonals over every row with a black edge cell).
- `cycle_lengths`: the cycles of the permutation G_n induces on the limit set.
- `seed_cycle`: the eventual cycle of the single cell (state 1) and its length.
- `table`: for each n, the size of the limit set, the cycle lengths, the seed's cycle length, and whether the limit
  set is exactly the seed's cycle.

    python -m computations.eternal_skeleton --nmax 22   # about 2 s
"""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass

import numpy as np
from tqdm.auto import tqdm


def left_step(s: np.ndarray, n: int) -> np.ndarray:
    """G_n on states s (shape (k,), int64, bit d is diagonal d); returns shape (k,)."""
    mask = (1 << n) - 1
    return ((s << 2) ^ ((s << 1) | s)) & mask


def limit_set(n: int) -> tuple[np.ndarray, int]:
    """The eventual image of the n-bit states with bit 0 set (sorted, shape (m,)) and the number of steps to reach it."""
    cur = np.arange(1 << (n - 1), dtype=np.int64) * 2 + 1  # (2^(n-1),) every state with a black edge cell
    steps = 0
    while True:
        nxt = np.unique(left_step(cur, n))  # (m',) the image is a subset of cur, since bit 0 is kept
        if len(nxt) == len(cur):
            return nxt, steps
        cur = nxt
        steps += 1


def cycle_lengths(states: np.ndarray, n: int) -> list[int]:
    """Cycle lengths of G_n on its limit set `states` (sorted, shape (m,)), which it permutes."""
    nxt = np.searchsorted(states, left_step(states, n))  # (m,) index of the image of each state
    if not np.array_equal(states[nxt], left_step(states, n)):
        raise ValueError("not closed under the step")
    seen = np.zeros(len(states), dtype=bool)  # (m,)
    lengths: list[int] = []
    for i in range(len(states)):
        if seen[i]:
            continue
        j, length = i, 0
        while not seen[j]:
            seen[j] = True
            j = int(nxt[j])
            length += 1
        if j != i:
            raise ValueError("the step is not a permutation of the limit set")
        lengths.append(length)
    return sorted(lengths)


def seed_cycle(n: int) -> tuple[set[int], int]:
    """The single cell's eventual cycle in G_n (as a set of states) and the step at which it is first on it."""
    x = np.array([1], dtype=np.int64)  # (1,)
    orbit = [1]
    seen: dict[int, int] = {1: 0}  # state -> first step it occurs
    while True:  # the orbit of a map of a finite set is eventually periodic, so this ends
        x = left_step(x, n)
        v = int(x[0])
        if v in seen:
            first = seen[v]  # the orbit is on its cycle from this step on
            return set(orbit[first:]), first
        seen[v] = len(orbit)
        orbit.append(v)


@dataclass
class Level:
    n: int
    size: int
    settle: int
    cycles: list[int]
    seed_length: int
    seed_onset: int
    single: bool


def table(nmax: int, progress: bool = True) -> list[Level]:
    rows: list[Level] = []
    for n in tqdm(range(2, nmax + 1), desc="levels", unit="n", file=sys.stderr, disable=not progress):
        states, settle = limit_set(n)
        cyc = cycle_lengths(states, n)
        seed, onset = seed_cycle(n)
        single = len(cyc) == 1 and set(int(v) for v in states) == seed
        rows.append(Level(n, len(states), settle, cyc, len(seed), onset, single))
    return rows


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--nmax", type=int, default=22)
    args = ap.parse_args()
    print("| n | limit set | cycles | seed cycle | steps to the limit set, every row | seed's | one cycle, the seed's |")
    print("|---:|---:|---|---:|---:|---:|---|")
    for r in table(args.nmax):
        print(f"| {r.n} | {r.size} | {r.cycles} | {r.seed_length} | {r.settle} | {r.seed_onset} | {r.single} |")


if __name__ == "__main__":
    main()
