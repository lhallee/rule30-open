"""Right halves beside a column of a background that repeats a word of period four, and whether they enter the family.

A background of period P (`space_time_periodic`) that has a column repeating 0001, 0011 or 0111 gives an infinite
right half, the columns right of that column, which the drive keeps in the background forever: the half repeats with
period P in time. If it is in the kit's ether-and-wall family (`absorption.family_depth`) at none of its P phases, it
never enters. The ether, of period 4 on 7 cells, is one such half; the background of period 8 on 80 cells is another,
for 0001. A truncation of it to n cells, white or random beyond, does enter, and this module times the entry.
`wall_set` asks whether a background has a wall: strips right of one of its columns that the rule keeps, with that
column on the background, for both values of the cell beyond. For the ether it gives the kit's greatest wall set.

    python -m computations.background_halves 4,8,12   # every background half of a period-four word, seconds
    python -m computations.background_halves 8 --truncate 80,160,320,640 --steps 4000   # truncations of the 80
    python -m computations.background_halves 8 --walls 20   # walls of up to 20 cells beside every column, 13 min
"""

from __future__ import annotations

import argparse

import numpy as np
from tqdm.auto import tqdm

from computations import absorption
from computations import space_time_periodic as stp

MASK64 = (1 << 64) - 1


def rings(period: int) -> list[list[int]]:
    """Every background of `period` as its ring of columns, left to right, each column a word with bit `ph` the cell at
    phase `ph` (`space_time_periodic.cycles`)."""
    _, label = stp.cycles(period)  # (c,), (c,)
    f = stp.column_map(period)  # (4^P,)
    found = []
    for lab in sorted(set(label.tolist())):
        states = [int(lab)]
        while (nxt := int(f[states[-1]])) != states[0]:
            states.append(nxt)
        found.append([state >> period for state in reversed(states)])  # the map steps one column left
    return found


def word_columns(period: int, word: str) -> list[tuple[list[int], int, int]]:
    """The columns of the backgrounds of `period` that repeat `word`: (ring, column index, the background phase at
    which the column reads word[0] and the word follows)."""
    found = []
    for ring in rings(period):
        for x, column in enumerate(ring):
            read = stp.word_of(column, period)
            for ph in range(len(word)):
                if all(read[(ph + s) % period] == word[s % len(word)] for s in range(period)):
                    found.append((ring, x, ph))
                    break
    return found


def background_half(ring: list[int], x: int, phase: int, cells: int) -> int:
    """Columns x + 1 .. x + cells of the ring at background phase `phase`, bit j the column x + 1 + j."""
    size = len(ring)
    return sum(((ring[(x + 1 + j) % size] >> phase) & 1) << j for j in range(cells))


def ether_prefix(word: str, half: int, phase: int, cells: int) -> int:
    """The most columns 1 .. k of the half (bit j column j + 1) that carry the ether aligned with the drive at `phase`,
    over the kit's alignments, counted up to `cells`."""
    best = 0
    for j0, shift in absorption.ALIGNMENTS[word]:
        k = 0
        while k < cells and ((half >> k) & 1) == absorption.ether(j0 + k + 1, phase + shift):
            k += 1
        best = max(best, k)
    return best


def never_enters(word: str, ring: list[int], x: int, phase: int, period: int, wall: np.ndarray) -> str | None:
    """How the half beside column x, driven by `word` from the background phase `phase`, stays out of the family at all
    `period` phases: "ether" when it is the aligned ether, which no wall state follows; "outside" when its ether prefix
    is below 51 columns at every phase, so that the 64 columns `family_depth` reads decide membership at every depth,
    and it is in the family at none; None when it is in the family at some phase."""
    span = len(ring) * 7 + 64  # past a common period of the ring and the ether
    prefixes = [ether_prefix(word, background_half(ring, x, (phase + s) % period, span), s % 4, span)
                for s in range(period)]
    if min(prefixes) == span:
        return "ether"
    assert max(prefixes) < 51, "a long ether prefix needs a wider check"
    for s in range(period):
        low = background_half(ring, x, (phase + s) % period, 64)
        if absorption.family_depth(word, np.array([low], dtype=np.uint64), s % 4, wall)[0] >= 0:
            return None
    return "outside"


def wall_set(ring: list[int], period: int, column: int, width: int) -> np.ndarray:
    """The greatest set of strips of `width` cells right of `column` of the background, one set per phase, that the
    rule maps into itself for both values of the cell beyond while `column` keeps its background values: where that
    column is white, the strip's first cell must be the background's. Bit j of a strip is column `column` + 1 + j."""
    size, n = len(ring), 1 << width
    strips = np.arange(n, dtype=np.int64)  # (2^w,)
    alive = np.ones((period, n), dtype=bool)  # (P, 2^w)
    after = np.zeros((period, 2, n), dtype=np.int64)  # (P, 2, 2^w)
    for ph in range(period):
        left = (ring[column % size] >> ph) & 1
        if not left:
            alive[ph] = (strips & 1) == ((ring[(column + 1) % size] >> ph) & 1)
        for beyond in (0, 1):
            shifted = ((strips << 1) | left) & (n - 1)  # (2^w,), each cell's left neighbor
            right = (strips >> 1) | (beyond << (width - 1))  # (2^w,), each cell's right neighbor
            after[ph, beyond] = shifted ^ (strips | right)
    while True:
        kept = alive.copy()  # (P, 2^w)
        for ph in range(period):
            nxt = alive[(ph + 1) % period]  # (2^w,)
            kept[ph] &= nxt[after[ph, 0]] & nxt[after[ph, 1]]
        if (kept == alive).all():
            return alive  # (P, 2^w)
        alive = kept


def entry_time(word: str, half: int, cells: int, steps: int, wall: np.ndarray) -> int:
    """The first step at which the half of `cells` columns (white beyond) is in the family, or -1 (`absorption.absorb`)."""
    words = (cells + steps) // 64 + 3
    rows = np.array([[(half >> (64 * i)) & MASK64 for i in range(words)]], dtype=np.uint64)  # (1, words)
    return int(absorption.absorb(word, rows, 0, steps, wall, cells)[0])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("periods", help="comma-separated temporal periods, multiples of 4")
    parser.add_argument("--truncate", default="", help="comma-separated lengths of truncations to time")
    parser.add_argument("--steps", type=int, default=4000)
    parser.add_argument("--walls", type=int, default=0, help="widest strip for the wall search, 0 for none")
    args = parser.parse_args()
    wall = absorption.kit_wall()
    if args.walls:
        for period in [int(p) for p in args.periods.split(",")]:
            for ring in {tuple(r): r for r in rings(period) if len(r) > 1}.values():
                widths = [w for w in range(1, args.walls + 1)
                          if any(wall_set(ring, period, a, w).any() for a in range(len(ring)))]
                print(f"period {period}, background of {len(ring)} cells: strip widths up to {args.walls} with a "
                      f"wall: {widths or 'none'}")
        return
    cuts = [int(n) for n in args.truncate.split(",")] if args.truncate else []
    for period in [int(p) for p in args.periods.split(",")]:
        for word in absorption.WORDS:
            summary: dict[int, tuple[int, set[str | None], dict[int, set[int]]]] = {}  # ring length: columns, verdicts, entries
            for ring, x, phase in tqdm(word_columns(period, word), desc=f"{word} at {period}", leave=False):
                count, verdicts, entries = summary.setdefault(len(ring), (0, set(), {n: set() for n in cuts}))
                verdicts.add(never_enters(word, ring, x, phase, period, wall))
                if len(ring) != 7:
                    for cells in cuts:
                        entries[cells].add(entry_time(word, background_half(ring, x, phase, cells), cells, args.steps,
                                                      wall))
                summary[len(ring)] = (count + 1, verdicts, entries)
            for size, (count, verdicts, entries) in sorted(summary.items()):
                print(f"period {period}, {word}: background of {size} cells, {count} columns repeating the word "
                      f"(time shifts counted apart), halves: {sorted(str(v) for v in verdicts)}")
                for cells, times in entries.items():
                    if times:
                        print(f"  truncated to {cells} cells, white beyond: first step in the family {sorted(times)}")


if __name__ == "__main__":
    main()
