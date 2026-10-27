"""Rule 30 deformed to Rule 150: the center cell as a polynomial in a parameter T.

The local rule p + q + r + T q r over GF(2)[T] (p, q, r the left, center and right cells) is Rule 150 at T = 0 and
Rule 30, p + (q or r), at T = 1. From the single black cell every cell is a polynomial in T. Interpolating the center
cell in T from its values at the two endpoints needs as many conditions as its degree plus one, so a shortcut through
the deformation needs the degree to grow slowly. It grows like about 1.63^t.

A polynomial is an integer whose bit i is the coefficient of T^i.

    python -m computations.deformation 16
"""

from __future__ import annotations

import argparse
import sys

from tqdm.auto import tqdm


def multiply(a: int, b: int) -> int:
    """The product of two polynomials over GF(2), carry-less."""
    product = 0
    while a:
        low = a & -a
        product ^= b << (low.bit_length() - 1)
        a ^= low
    return product


def deformed_rows(steps: int) -> list[dict[int, int]]:
    """Rows 0 .. steps of the deformed rule from the single cell, each a map from position to nonzero polynomial."""
    rows = [{0: 1}]
    for _ in tqdm(range(steps), desc="steps", file=sys.stderr, leave=False):
        row = rows[-1]
        new = {}
        for x in range(min(row) - 1, max(row) + 2):
            p, q, r = row.get(x - 1, 0), row.get(x, 0), row.get(x + 1, 0)
            cell = p ^ q ^ r ^ (multiply(q, r) << 1)
            if cell:
                new[x] = cell
        rows.append(new)
    return rows


def center_degrees(steps: int) -> list[tuple[int, int]]:
    """For t = 1 .. steps, the T-degree of the center cell and its number of nonzero coefficients."""
    return [(row.get(0, 0).bit_length() - 1, row.get(0, 0).bit_count()) for row in deformed_rows(steps)[1:]]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("steps", type=int)
    args = parser.parse_args()

    table = center_degrees(args.steps)
    print(" t  degree  terms  ratio")
    for t, (degree, terms) in enumerate(table, start=1):
        previous = table[t - 2][0] if t >= 2 else 0
        ratio = f"{degree / previous:.3f}" if previous > 0 and degree > 0 else ""
        print(f"{t:>2}  {degree:>6}  {terms:>5}  {ratio}")


if __name__ == "__main__":
    main()
