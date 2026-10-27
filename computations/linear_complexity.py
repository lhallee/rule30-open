"""The linear complexity of the center column: the order of the shortest GF(2) linear recurrence that produces it.

Berlekamp-Massey on Python integers: the connection polynomial and the reversed window of recent cells are integers, so
each discrepancy is the parity of one AND. A random sequence of n cells has linear complexity close to n / 2, an
eventually periodic one at most its preperiod plus its period.

    python -m computations.linear_complexity 65536   # the profile of the first 2^16 cells, with its largest gap from n / 2
"""

from __future__ import annotations

import argparse
import sys
import numpy as np

from tqdm.auto import tqdm

from computations.rule30 import center_column


def complexity_profile(cells: np.ndarray, progress: bool = False) -> np.ndarray:
    """The linear complexity of every prefix of `cells`."""
    # cells: (n,)
    connection, previous = 1, 1  # polynomials, bit i the coefficient of x^i
    order, gap = 0, 1
    window = 0  # bit i is the cell i places before the current one
    profile = np.zeros(len(cells), dtype=np.int64)  # (n,)
    for n, cell in enumerate(tqdm(cells.tolist(), desc="Berlekamp-Massey", file=sys.stderr, disable=not progress)):
        window = (window << 1) | cell
        if (connection & window).bit_count() & 1:
            if 2 * order <= n:
                connection, previous = connection ^ (previous << gap), connection
                order, gap = n + 1 - order, 1
            else:
                connection ^= previous << gap
                gap += 1
        else:
            gap += 1
        profile[n] = order
    return profile  # (n,)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("cells", type=int)
    n = parser.parse_args().cells

    profile = complexity_profile(center_column(n), progress=True)  # (n,)
    gaps = np.abs(profile - (np.arange(1, n + 1) / 2))  # (n,)
    print(f"linear complexity of the first {n} cells: {profile[-1]}; largest gap from n / 2 over all prefixes: "
          f"{gaps.max():.1f}")


if __name__ == "__main__":
    main()
