"""<What this module computes, and which entries quote its numbers.>

<How it computes it, in a few sentences: the algorithm and why it is exact, or what it samples.>

    python -m computations.<module> 4096   # <what this command prints, and how long it takes>
"""

from __future__ import annotations

import argparse
import sys
import numpy as np

from tqdm.auto import tqdm

from computations.rule30 import center_column


def running_density(cells: np.ndarray, progress: bool = False) -> np.ndarray:
    """<What the function returns.> Here: the fraction of black cells in every prefix of `cells`."""
    # cells: (n,)
    counts = np.zeros(len(cells), dtype=np.int64)  # (n,)
    total = 0
    for i, cell in enumerate(tqdm(cells.tolist(), desc="prefixes", file=sys.stderr, disable=not progress)):
        total += cell
        counts[i] = total
    return counts / np.arange(1, len(cells) + 1)  # (n,)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("cells", type=int, help="how many cells of the center column")
    n = parser.parse_args().cells

    density = running_density(center_column(n), progress=True)  # (n,)
    print(f"density of black cells in the first {n} cells: {density[-1]:.6f}")


if __name__ == "__main__":
    main()
