"""The space that tree evaluation uses on the block tree of the center column, and the thresholds a lower bound beats.

The block tree of the kit's `Rule30LightCone` has fan-in d = 3, nodes of b bits and height h = ceil(n / b) for the cell
at time n. Cook and Mertz's algorithm, as Williams states it (Theorem 2.2 of "Simulating time with square-root space",
from Theorem 7 of the STOC 2024 paper), uses space O(d b + h log2(d b)). This module reads the O as equality, to compare
choices of b: it has no constant of the algorithm, so its ratios show growth rates, not bit counts.

    python -m computations.space_window            # the table of the finding
"""

from __future__ import annotations

import argparse
import math

FAN_IN = 3  # the block tree of Rule 30 has fan-in 3


def tree_space(n: int, block: int, fan_in: int = FAN_IN) -> float:
    """d b + h log2(d b) with h = ceil(n / b): the Cook-Mertz space, read as an equality, for blocks of `block` cells."""
    assert 1 <= block <= n
    height = -(-n // block)  # ceil(n / block)
    return fan_in * block + height * math.log2(fan_in * block)


def weak_tree_space(n: int, block: int, fan_in: int = FAN_IN) -> float:
    """(h + d b) log2(d b): the weaker form (h + b) log b that earlier entries used."""
    assert 1 <= block <= n
    height = -(-n // block)
    return (height + fan_in * block) * math.log2(fan_in * block)


def best_block(n: int, weak: bool = False) -> tuple[int, float]:
    """A block size that nearly minimizes the space, and that space, by ternary search. The ceiling in the height makes the
    curve ragged on a scale of a few blocks, so the result is within 0.1% of the true minimum, which
    `tests/test_space_window.py` checks against the full minimum for small n."""
    space = weak_tree_space if weak else tree_space
    low, high = 1, n
    while high - low > 3:
        third = (high - low) // 3
        left, right = low + third, high - third
        if space(n, left) <= space(n, right):
            high = right
        else:
            low = left
    best = min(range(low, high + 1), key=lambda block: space(n, block))
    return best, space(n, best)


def table(exponents: list[int]) -> list[dict[str, float]]:
    """For n = 2^k: the best block, the space, and its ratio to sqrt(n), to sqrt(n log2 n), to n^(2/5) and to the weak
    form's space."""
    rows = []
    for k in exponents:
        n = 1 << k
        block, space = best_block(n)
        _, weak = best_block(n, weak=True)
        rows.append({"k": k, "block": block, "space": space, "over_sqrt_n": space / math.sqrt(n),
                     "over_sqrt_n_log_n": space / math.sqrt(n * k), "over_n_two_fifths": space / n**0.4,
                     "weak_over_space": weak / space})
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--exponents", type=int, nargs="+", default=[10, 20, 30, 40, 60, 80, 120, 160, 240])
    args = parser.parse_args()
    print("   k      best b          space   /sqrt(n)  /sqrt(n log n)  /n^(2/5)  weak/space")
    for row in table(args.exponents):
        print(f"{row['k']:4d} {row['block']:11.3e} {row['space']:14.4e} {row['over_sqrt_n']:10.3f} "
              f"{row['over_sqrt_n_log_n']:14.3f} {row['over_n_two_fifths']:9.3g} {row['weak_over_space']:10.3f}")


if __name__ == "__main__":
    main()
