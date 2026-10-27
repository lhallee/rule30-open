"""Rows that are periodic to the left and white to the right: which have an eventually periodic column?

In the frame of `computations.frames`, such a row is a rational 2-adic integer y, held as (prefix, period word), and
the column under the frame's starting position is Psi(y). This survey takes every period word up to `max_period`
cells with every prefix up to `max_prefix` cells, and reports the rows whose column repeats with a period up to 64 over
the second half of `bits` steps. A periodic column does not make the row's orbit eventually periodic in the frame:
`prefix_growth` follows the prefix of Phi^n(y), which keeps growing for the ether backgrounds.

    python -m computations.backgrounds 9 2 2048   # backgrounds of period up to 9, prefixes up to 2 cells
"""

from __future__ import annotations

import argparse
import sys
import numpy as np

from itertools import product
from tqdm.auto import tqdm

from computations.frames import Bits, minimal, phi_rational, psi, to_int


def column_period(column: np.ndarray, max_period: int) -> int | None:
    """The least period up to `max_period` with which the second half of the column repeats, or None."""
    # column: (n,)
    tail = column[len(column) // 2:]  # (n / 2,)
    return next((p for p in range(1, max_period + 1) if np.array_equal(tail[p:], tail[:-p])), None)


def background_column(prefix: Bits, period: Bits, bits: int) -> np.ndarray:
    """The first `bits` cells of the column of the row (prefix, period)."""
    value = psi(to_int(prefix, period, bits), bits)
    return np.array([(value >> t) & 1 for t in range(bits)], dtype=np.uint8)  # (bits,)


def periodic_columns(max_period: int, max_prefix: int, bits: int) -> list[tuple[Bits, Bits, int]]:
    """Every row with a period word up to `max_period` and a prefix up to `max_prefix` cells whose column is eventually
    periodic, as (prefix, period word, column period), each row once in its minimal form."""
    rows = {}
    for p in range(1, max_period + 1):
        for word in product((0, 1), repeat=p):
            for length in range(max_prefix + 1):
                for prefix in product((0, 1), repeat=length):
                    small = minimal(list(prefix), list(word))
                    rows[(tuple(small[0]), tuple(small[1]))] = small
    found = []
    for prefix, period in tqdm(rows.values(), desc="rows", file=sys.stderr, mininterval=5):
        p = column_period(background_column(prefix, period, bits), 64)
        if p is not None:
            found.append((prefix, period, p))
    return found


def prefix_growth(prefix: Bits, period: Bits, steps: int) -> list[int]:
    """The prefix length of Phi^n(y) for n = 0 .. steps: bounded if the orbit is eventually periodic in the frame."""
    lengths = [len(prefix)]
    for _ in range(steps):
        prefix, period = phi_rational(prefix, period)
        lengths.append(len(prefix))
    return lengths


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("max_period", type=int)
    parser.add_argument("max_prefix", type=int)
    parser.add_argument("bits", type=int)
    args = parser.parse_args()

    found = periodic_columns(args.max_period, args.max_prefix, args.bits)
    backgrounds: dict[str, set[int]] = {}
    for _, period, p in found:
        word = "".join(map(str, period))
        backgrounds.setdefault(min(word[i:] + word[:i] for i in range(len(word))), set()).add(p)
    for word, periods in sorted(backgrounds.items(), key=lambda item: (len(item[0]), item[0])):
        print(f"background {word}: column periods {sorted(periods)}")
    for prefix, period, p in found:
        if len(period) == 7:
            growth = prefix_growth(prefix, period, 200)
            print(f"ether row {''.join(map(str, prefix))}|{''.join(map(str, period))}: column period {p}, "
                  f"prefix of Phi^n(y) at n = 0, 50, 100, 200: {growth[0]}, {growth[50]}, {growth[100]}, {growth[200]}")
            break


if __name__ == "__main__":
    main()
