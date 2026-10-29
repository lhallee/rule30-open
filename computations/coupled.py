"""The one left half that keeps a prescribed center column against a given right half.

Fix the center column c and the right half R at time 0. The right half then evolves as the half driven by c (the kit's
`Rule30Ether.drv`), so its column 1 is known. The center's update c(t + 1) = x(t, -1) xor (c(t) or x(t, 1)) forces
column -1, and Rule 30 is permutive in its left input, so columns 0 and -1 rebuild every column to the left:
x(t, -j - 1) = x(t + 1, -j) xor (x(t, -j) or x(t, -j + 1)). The row at time 0 that results, Psi(R), is the only left
half, finite or not, that keeps the center on c at every time against R; for the alternating column it is the kit's
`Rule30PeriodTwoSideways.Psi`. A left half that first differs from Psi(R) at depth d keeps the center on c through time
d - 1 and leaves it at time d (the kit's `exact_death_center`), so a white run of Psi(R) is exactly how far a finite
left half can outlast its own width against R.

`empty` computes Psi of the empty right half for the alternating center, whose black cells the kit's open milestone
`CQ01Empty` asks to be infinitely many, and for the three period-four words, where it is eventually periodic. `all` does
the alternating center for every right half of at most `--cells` cells.

    python -m computations.coupled empty --depth 1048576   # about 2.5 min
    python -m computations.coupled all --cells 14 --depth 4096   # about 2 min
"""

from __future__ import annotations

import argparse
import sys
import time

from tqdm.auto import tqdm

from computations.absorption import ETHER


WORDS = ("01", "0001", "0011", "0111")


def center(word: str, phase: int, steps: int) -> int:
    """The center column c(t) = word[(t + phase) mod len(word)] for t < steps, bit t being time t."""
    return sum(int(word[(t + phase) % len(word)]) << t for t in range(steps))


def drive_column(word: str, phase: int, right: int, steps: int) -> int:
    """Column 1 at times 0 .. steps - 1 of the right half `right` (bit i is column i + 1) driven by that center, bit t
    being time t."""
    column, row = 0, right
    for t in range(steps):
        column |= (row & 1) << t
        row = ((row << 1) | int(word[(t + phase) % len(word)])) ^ (row | (row >> 1))
    return column


def psi(word: str, phase: int, right: int, depth: int) -> int:
    """Psi(R) at depths 1 .. `depth`, bit j being the cell at depth j + 1 (column -j - 1) at time 0. Column -j is known
    at the times below depth + 1 - j, so its cell at time 0 is known for every j up to `depth`."""
    c = center(word, phase, depth + 1)
    a = ((c >> 1) ^ (c | drive_column(word, phase, right, depth + 1))) & ((1 << depth) - 1)  # column -1, times < depth
    b, row = c, 0
    for j in range(depth):
        row |= (a & 1) << j
        a, b = (a >> 1) ^ (a | b), a  # column -j - 2 from columns -j - 1 and -j
    return row


def white_literals(depth: int) -> tuple[int, int]:
    """The numbers that `Rule30Open.PeriodTwo.WhiteRightHalf` checks: column -1 of the row that keeps the center
    alternating against the white right half at times 0 .. depth - 1 (`yLoop`), and that row at depths 1 .. depth as
    bits 1 .. depth (`psiLoop`), rebuilt column by column beside a white wall."""
    column = drive_column("10", 0, 0, depth)  # column 1, bit t being time t
    y = sum(1 << t for t in range(depth) if t % 2 == 0 or not (column >> t) & 1)
    prev, cur, bits = 0, y, 0
    for k in range(1, depth + 1):
        bits |= (cur & 1) << k
        prev, cur = cur, (cur >> 1) ^ (cur | prev)
    return y, bits


def white_runs(row: int, depth: int) -> list[tuple[int, int]]:
    """The record white runs of a row read from depth 1 outward, as (length, first depth), among the runs that end in
    a black cell at depth at most `depth`."""
    bits = format(row, "b").zfill(depth)[::-1]  # depth 1 first
    records: list[tuple[int, int]] = []
    position = 1
    for run in bits.split("1")[:-1]:
        if not records or len(run) > records[-1][0]:
            records.append((len(run), position))
        position += len(run) + 1
    return records


def eventual_period(row: int, depth: int, max_period: int = 64) -> tuple[int, int] | None:
    """The least period p <= max_period with which the row repeats over its outer half, and the least depth from which
    it repeats with p (both up to `depth`), or None."""
    bits = format(row, "b").zfill(depth)[::-1]  # depth 1 first
    half = depth // 2
    for p in range(1, max_period + 1):
        if bits[half + p:] == bits[half:depth - p]:
            start = half
            while start > 0 and bits[start - 1] == bits[start - 1 + p]:
                start -= 1
            return start + 1, p
    return None


def ether_after(word: str, max_steps: int = 32) -> int | None:
    """The first step at which the infinite row repeating `word` (its letter j at depth j + 1) is a row of the kit's
    ether, or None within `max_steps`."""
    rows = {tuple(int(ETHER[(j + r) % 7][phase]) for j in range(7)) for phase in range(4) for r in range(7)}
    n = 7 * len(word)
    cells = [int(word[(n - 1 - i) % len(word)]) for i in range(n)]  # positions left to right, a whole number of periods
    for steps in range(max_steps + 1):
        if all(cells[i] == cells[i + 7] for i in range(n - 7)) and tuple(cells[:7]) in rows:
            return steps
        cells = [cells[i - 1] ^ (cells[i] | cells[(i + 1) % n]) for i in range(n)]
    return None


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("mode", choices=["empty", "all"])
    parser.add_argument("--depth", type=int, default=65536, help="depths of Psi computed")
    parser.add_argument("--cells", type=int, default=8, help="all: every right half of up to this many cells")
    args = parser.parse_args()

    started = time.perf_counter()
    if args.mode == "empty":
        for word in WORDS:
            for phase in range(len(word)):
                depth = args.depth if word == "01" else 4096
                row = psi(word, phase, 0, depth)
                if word != "01":
                    start, p = eventual_period(row, depth)
                    repeat = format(row, "b").zfill(depth)[::-1][start - 1:start - 1 + p]
                    print(f"{word} phase {phase}: periodic with period {p} from depth {start}, repeating {repeat}, "
                          f"a row of the ether after {ether_after(repeat)} steps")
                    continue
                runs = white_runs(row, args.depth)
                print(f"{word} phase {phase}: {row.bit_count()} black cells at depths 1 to {args.depth}, the last at "
                      f"{row.bit_length()}; record white runs (length, first depth): {runs}")
    else:
        for phase in range(2):
            longest, last = (0, 0), args.depth
            for right in tqdm(range(1 << args.cells), desc=f"phase {phase}", file=sys.stderr, leave=False):
                row = psi("01", phase, right, args.depth)
                runs = white_runs(row, args.depth)
                longest = max(longest, (runs[-1][0], right))
                last = min(last, row.bit_length())
            print(f"01 phase {phase}: over the right halves of at most {args.cells} cells, the longest white run of "
                  f"Psi is {longest[0]} (right half {longest[1]:b}), and every Psi has a black cell at depth "
                  f"{last} or beyond, so every left half of width W < {last} leaves the alternation by time "
                  f"W + {longest[0] + 1}")
    print(f"({time.perf_counter() - started:.0f} s)")


if __name__ == "__main__":
    main()
