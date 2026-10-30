"""Words in one column right of the center that bring every window into the kit's ether-and-wall trap.

Drive a right half with the center repeating 0001, 0011 or 0111, as in `lock_certificate.py`: the center at time t is
`word[(t + phase) % 4]`. A window is columns 1 .. W as a number, bit j for column j + 1, and one step of it needs column
W + 1. The kit's family (`Rule30Ether.InFamily`) holds a window at depth k when columns 1 .. k carry the ether aligned
with the center, column k is a B3 column, and columns k + 1 .. k + 13 are one of the kit's 109 wall states; it fits a
window when k + 13 <= W, and the least such widths are 16 for 0001 (alignment (6, 0), k = 3), 14 for 0011 ((1, 3),
k = 1) and 13 for 0111 ((2, 2), k = 0). At those widths

- `trap` marks the windows in the family at each phase, 109 in all over the four phases;
- `universal_word` finds one sequence of values of column W + 1 that brings every window, started at any phase, into
  the trap, greedily: it follows a shortest path from the window closest to the trap and moves every window along;
- `slice_run` runs a sequence on all 4 * 2^W windows at once, one integer per column with one bit per window, and
  `slice_check` asks every window to end in the trap: the computation `Rule30Open.Columns.LockWord` makes in the
  kernel.

    python -m computations.lock_word   # the three words at the least widths, about 10 s
    python -m computations.lock_word --lean   # the words as Lean literals
    python -m computations.lock_word --reach 19 20 21   # windows that no sequence brings in, about 3 min
    python -m computations.lock_word --entropy   # how fast the sequences that keep a window out grow, about 20 s
    python -m computations.lock_word --entropy 13 14 15 16   # the same at wider windows, about 1 min

`unreachable` marks the windows from which no values of column W + 1 lead into the trap. Under the three words of
period four there are none up to width 20; beside an alternating center, 0101, about half the windows at widths 19 and
20 can never enter.
"""

from __future__ import annotations

import argparse

import numpy as np

from computations.absorption import ALIGNMENTS, WALL_CELLS, ether, kit_wall
from computations.coin_lock import UNREACHED, decay_rate, entry_paths
from computations.lock_certificate import successor_table

# The least window width at which the kit's family fits, with the alignment (j0, shift) and depth k used there.
LEAST = {"0001": (16, 6, 0, 3), "0011": (14, 1, 3, 1), "0111": (13, 2, 2, 0)}


def trap(word: str, width: int, wall: np.ndarray) -> np.ndarray:
    """member[ph, s]: whether window s at drive phase ph is in the kit's family at some depth k with k + 13 <= width,
    for some alignment of the word."""
    # wall: (4, 2^13), the kit's wall states per ether phase
    states = np.arange(1 << width, dtype=np.int64)  # (2^W,)
    member = np.zeros((4, 1 << width), dtype=bool)  # (4, 2^W)
    for j0, shift in ALIGNMENTS[word]:
        for k in range(width - WALL_CELLS + 1):
            if (j0 + k) % 7 != 2:
                continue
            for ph in range(4):
                psi = (ph + shift) % 4  # the ether phase at drive phase ph
                prefix = sum(ether(j0 + p, psi) << (p - 1) for p in range(1, k + 1))
                strip = (states >> k) & ((1 << WALL_CELLS) - 1)  # (2^W,)
                member[ph] |= ((states & ((1 << k) - 1)) == prefix) & wall[psi][strip]
    return member  # (4, 2^W)


def unreachable(word: str, width: int, wall: np.ndarray) -> np.ndarray:
    """out[ph, s]: whether no values of column W + 1 bring window s at drive phase ph into the trap, with the most
    steps any window needs to enter."""
    # wall: (4, 2^13)
    dist, _ = entry_paths(word, trap(word, width, wall))  # (4, 2^W)
    return dist >= UNREACHED  # (4, 2^W)


def avoid_growth(word: str, member: np.ndarray) -> float:
    """The growth rate per step of the number of sequences of column W + 1 that keep a window out of the trap: twice
    the factor by which a fair coin's chance of staying out decays (`coin_lock.decay_rate`), in floating point."""
    # member: (4, 2^W)
    return 2 * decay_rate(word, member)


def universal_word(word: str, member: np.ndarray) -> list[int]:
    """Values of column W + 1 that bring every window, started at each of the four phases, into the trap."""
    # member: (4, 2^W)
    period, size = member.shape
    dist, first = entry_paths(word, member)  # (4, 2^W) each
    if (dist >= UNREACHED).any():
        raise ValueError("some window cannot enter the trap")
    successors = successor_table(word, size.bit_length() - 1)  # (4, 2, 2^W)
    groups = [np.arange(size, dtype=np.int64) for _ in range(period)]  # windows of each start phase, (n,) each
    values: list[int] = []
    while True:
        step = len(values)
        best: tuple[int, int, int] | None = None
        for start, windows in enumerate(groups):
            ph = (start + step) % period
            outside = windows[~member[ph][windows]]  # (m,)
            if outside.size:
                window = int(outside[np.argmin(dist[ph][outside])])
                if best is None or dist[ph][window] < best[0]:
                    best = (int(dist[ph][window]), start, window)
        if best is None:
            return values
        _, start, window = best
        while not member[(start + len(values)) % period][window]:
            ph = (start + len(values)) % period
            value = int(first[ph][window])
            groups = [np.unique(successors[(s + len(values)) % period, value][g]) for s, g in enumerate(groups)]
            window = int(successors[ph, value][window])
            values.append(value)


def pack(bits: np.ndarray) -> int:
    """The integer with bit i set where `bits[i]`; `bits` has shape (n,)."""
    return int.from_bytes(np.packbits(bits.astype(np.uint8), bitorder="little").tobytes(), "little")


def slice_run(word: str, width: int, values: list[int]) -> list[int]:
    """Column j + 1 of every window after column W + 1 reads `values`, as one integer: bit p * 2^W + r is the window
    that was r at start phase p. The step is Rule 30 on whole integers, with the center and the column beyond as
    masks."""
    size = 1 << width
    ones = (1 << (4 * size)) - 1
    block = (1 << size) - 1
    windows = np.arange(4 * size, dtype=np.int64) % size  # (4 2^W,), the window of each bit at the start
    slices = [pack((windows >> j & 1).astype(bool)) for j in range(width)]
    for step, value in enumerate(values):
        center = sum(block << (p * size) for p in range(4) if word[(p + step) % 4] == "1")
        beyond = ones if value else 0
        slices = [(center if j == 0 else slices[j - 1]) ^ (slices[j] | (beyond if j == width - 1 else slices[j + 1]))
                  for j in range(width)]
    return slices


def slice_check(word: str, width: int, values: list[int], member: np.ndarray) -> bool:
    """Whether every window ends in the trap of its final phase, by matching the slices against each trap window."""
    # member: (4, 2^W)
    size = 1 << width
    ones = (1 << (4 * size)) - 1
    block = (1 << size) - 1
    slices = slice_run(word, width, values)
    inside = 0
    for ph in range(4):
        group = sum(block << (p * size) for p in range(4) if (p + len(values)) % 4 == ph)
        for state in np.flatnonzero(member[ph]).tolist():
            match = group
            for j in range(width):
                match &= slices[j] if state >> j & 1 else ones ^ slices[j]
            inside |= match
    return inside == ones


def lean_literal(values: list[int]) -> str:
    """The word as a number, value i at bit i, in hexadecimal."""
    return hex(sum(v << i for i, v in enumerate(values)))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--lean", action="store_true", help="print the words as Lean literals")
    parser.add_argument("--reach", type=int, nargs="*", help="instead, the windows that can never enter, at these widths")
    parser.add_argument("--entropy", type=int, nargs="*",
                        help="instead, the growth of the sequences that keep out, at the least widths or these")
    args = parser.parse_args()
    wall = kit_wall()  # (4, 2^13)
    if args.entropy is not None:
        for word, (least, _, _, _) in LEAST.items():
            for width in [w for w in args.entropy if w >= least] if args.entropy else [least]:
                growth = avoid_growth(word, trap(word, width, wall))
                print(f"{word}: sequences of column {width + 1} that keep a window out grow by {growth:.6f} per step, "
                      f"so at most {np.log2(growth):.5f} bits per step")
        return
    if args.reach:
        for word in ("0001", "0011", "0111", "0101"):
            for width in args.reach:
                out = unreachable(word, width, wall)  # (4, 2^W)
                print(f"{word} at width {width}: windows that can never enter, by phase: "
                      f"{[round(float(f), 4) for f in out.mean(axis=1)]}")
        return
    for word, (width, j0, shift, k) in LEAST.items():
        member = trap(word, width, wall)  # (4, 2^W)
        values = universal_word(word, member)
        ok = slice_check(word, width, values, member)
        if args.lean:
            print(f"-- {word}: column {width + 1}, {len(values)} values\n{lean_literal(values)}")
            continue
        print(f"{word}: width {width}, alignment ({j0}, {shift}) at depth {k}, trap {member.sum(axis=1).tolist()}; "
              f"a word of {len(values)} values in column {width + 1} brings every window into it: {ok}")


if __name__ == "__main__":
    main()
