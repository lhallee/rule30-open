"""The center cell as a polynomial over GF(2), and the center column as a sum over adjacent black pairs.

`center_anf` evaluates cell 0 at time t on all 2^(2t + 1) rows of its backward cone and takes the Moebius transform,
which gives the coefficient of every monomial in the cone cells. `duhamel_center` computes the center column from the
identity Rule 30 = Rule 150 + (x and x_(+1)) over GF(2): unrolled, the center cell is the central trinomial coefficient
(always odd) plus the Rule 150 kernel applied to every earlier adjacent black pair.

    python -m computations.algebra 9   # degree and top monomials of the center cell for t = 2 .. 9
"""

from __future__ import annotations

import argparse
import numpy as np

from computations.rule30 import center_column, step


def center_truth_table(t: int) -> np.ndarray:
    """Cell 0 at time t for every row of cells -t .. t; entry r is the row whose cell -t + i is bit i of r."""
    n = 2 * t + 1
    rows = np.arange(1 << n, dtype=np.int64)  # (2^n,), bit i is cell -t + i
    cells = [(rows >> i) & 1 for i in range(n)]  # n arrays (2^n,), cells -t .. t
    for _ in range(t):
        cells = [cells[i - 1] ^ (cells[i] | cells[i + 1]) for i in range(1, len(cells) - 1)]  # each (2^n,)
    (center,) = cells  # (2^n,)
    return center.astype(np.uint8)  # (2^n,)


def moebius(table: np.ndarray) -> np.ndarray:
    """The algebraic normal form of a truth table over GF(2): entry m is the coefficient of the monomial whose variables
    are the set bits of m."""
    # table: (2^n,)
    anf = table.copy()  # (2^n,)
    n = anf.size.bit_length() - 1
    for i in range(n):
        anf = anf.reshape(-1, 2, 1 << i)  # (2^(n - i - 1), 2, 2^i)
        anf[:, 1, :] ^= anf[:, 0, :]
        anf = anf.reshape(-1)  # (2^n,)
    return anf  # (2^n,)


def center_anf(t: int) -> np.ndarray:
    """The coefficients of the center cell at time t as a polynomial in cells -t .. t (variable i is cell -t + i)."""
    return moebius(center_truth_table(t))  # (2^(2t + 1),)


def degree_and_top(anf: np.ndarray) -> tuple[int, list[int]]:
    """The degree of a polynomial in algebraic normal form, and its monomials of that degree as bit masks."""
    # anf: (2^n,)
    monomials = np.flatnonzero(anf)  # (terms,)
    sizes = np.array([int(m).bit_count() for m in monomials])  # (terms,)
    degree = int(sizes.max())
    return degree, [int(m) for m in monomials[sizes == degree]]


def trinomial_row(n: int) -> dict[int, int]:
    """The odd coefficients of (x^-1 + 1 + x)^n, as the support {offset: 1}: the Rule 150 kernel after n steps."""
    support = {0}
    for _ in range(n):
        image: dict[int, int] = {}
        for x in support:
            for neighbor in (x - 1, x, x + 1):
                image[neighbor] = image.get(neighbor, 0) ^ 1
        support = {x for x, odd in image.items() if odd}
    return dict.fromkeys(support, 1)


def duhamel_center(n: int) -> np.ndarray:
    """The first `n` cells of the center column from c(t) = 1 + sum over s < t and y of T_(t-1-s)(y) a_s(y) a_s(y + 1),
    mod 2, with T_m the Rule 150 kernel and a_s the single cell's rows."""
    origin = n + 1
    row = 1 << origin  # bit origin + x is cell x
    pairs = []  # pairs[s]: the cells y with a_s(y) = a_s(y + 1) = 1
    for _ in range(n):
        both = row & (row >> 1)  # bit origin + y is a_s(y) a_s(y + 1)
        pairs.append({i - origin for i in range(both.bit_length()) if (both >> i) & 1})
        row = step(row)
    kernels = [trinomial_row(m) for m in range(n)]
    column = np.ones(n, dtype=np.uint8)  # (n,), the central trinomial coefficients are odd
    for t in range(n):
        for s in range(t):
            kernel = kernels[t - 1 - s]
            column[t] ^= sum(kernel.get(y, 0) for y in pairs[s]) & 1
    return column  # (n,)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("t_max", type=int)
    t_max = parser.parse_args().t_max

    for t in range(2, t_max + 1):
        anf = center_anf(t)  # (2^(2t + 1),)
        degree, top = degree_and_top(anf)
        cells = [[i - t for i in range(2 * t + 1) if (m >> i) & 1] for m in top]
        print(f"t = {t}: {int(anf.sum())} monomials, degree {degree} = 2t - 1: {degree == 2 * t - 1}; "
              f"top monomials over cells {cells}")
    assert np.array_equal(duhamel_center(128), center_column(128))
    print("the Duhamel form gives the first 128 cells of the center column")


if __name__ == "__main__":
    main()
