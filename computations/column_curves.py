"""Eventually periodic columns of linear automata over a finite field, and the Galois group of the column curve.

A linear rule x'_i = sum_k a_k x_(i+k) over F_q (k from -r to r', a_(-r) a_(r') != 0) multiplies the row
X(z) = sum_i x_i z^i by A(z) = sum_k a_k z^(-k). The generating function of column p is the constant term in z of
z^(-p) X(z) z^(r') / Q(z), with Q(z) = z^(r') - s B(z) and B(z) = z^(r') A(z), and it is the sum of
Psi(z) = z^(-p) X(z) B(z) / (r' B(z) - z B'(z)) over the r' small roots of Q plus a polynomial in 1/s
([the column curves](../findings/analogs/column-curves.md)). This module checks the two consequences the entry states.

* `frobenius_pattern`: for a radius-2 rule over F_2 and an irreducible pi(s) other than s, the numbers of roots of Q
  modulo pi in the extensions of F_2[s]/pi of degrees 1 to 4. A quartic with 4 distinct roots in the extension of
  degree 3 and one in the base has a Frobenius element of cycle type (1, 3); one with 4 distinct roots in degree 4 and
  none in degree 2 has a 4-cycle (Dedekind).
* `certificates`: for each of the four radius-2 rules x_(i-2) + a x_(i-1) + b x_i + c x_(i+1) + x_(i+2) with a != c,
  the first places of degree at most 3 that give a 3-cycle and a 4-cycle, so that the Galois group is S_4.
* `ep_columns`: every nonzero row of width at most w up to translation, every column within `reach` cells of the row,
  run for T steps; the columns that repeat with a period of at most `pmax` on [T/4, T).
* `twisted_symmetric`: the criterion at radius 1, x_(p+m) = -(a/c)^m x_(p-m) for every m.

    python -m computations.column_curves --certificates        # the S_4 certificates (seconds)
    python -m computations.column_curves --radius-two 9        # radius 2 over F_2, rows of up to 9 cells (about 1 min)
    python -m computations.column_curves --radius-one 3 5      # radius 1 over F_3, rows of up to 5 cells (about 1 min)
"""

from __future__ import annotations

import argparse
from itertools import product

import numpy as np
from tqdm.auto import tqdm

ASYMMETRIC = [(0, 0, 1), (0, 1, 1), (1, 0, 0), (1, 1, 0)]  # (a, b, c) with a != c


def clmul(x: int, y: int) -> int:
    """Product of two polynomials over F_2 held as bit masks."""
    r = 0
    while y:
        if y & 1:
            r ^= x
        x <<= 1
        y >>= 1
    return r


def poly_mod(x: int, m: int) -> int:
    """Remainder of the F_2 polynomial x modulo m (bit masks)."""
    dm = m.bit_length() - 1
    while x and x.bit_length() - 1 >= dm:
        x ^= m << (x.bit_length() - 1 - dm)
    return x


def is_irreducible(m: int) -> bool:
    """Whether the F_2 polynomial m (bit mask, degree >= 1) is irreducible, by trial division."""
    d = m.bit_length() - 1
    return all(poly_mod(m, f) != 0 for f in range(2, 1 << (d // 2 + 1)) if f.bit_length() - 1 >= 1)


def irreducibles(k: int) -> list[int]:
    """The irreducible polynomials of degree k over F_2, as bit masks."""
    return [m for m in range(1 << k, 1 << (k + 1)) if is_irreducible(m)]


class Field:
    """F_(2^m) as F_2[x]/mu, for the first irreducible mu of degree m."""

    def __init__(self, m: int) -> None:
        self.m = m
        self.mu = irreducibles(m)[0]

    def mul(self, x: int, y: int) -> int:
        """Product of two field elements."""
        return poly_mod(clmul(x, y), self.mu)

    def poly_at(self, coeffs: list[int], z: int) -> int:
        """Value at z of the polynomial with the given field coefficients (lowest degree first), by Horner."""
        v = 0
        for c in reversed(coeffs):
            v = self.mul(v, z) ^ c
        return v


def quartic(a: int, b: int, c: int, theta: int, F: Field) -> list[int]:
    """Coefficients (lowest first) of Q(z) = s z^4 + a s z^3 + (1 + b s) z^2 + c s z + s at s = theta in F."""
    return [theta, theta if c else 0, 1 ^ (theta if b else 0), theta if a else 0, theta]


def frobenius_pattern(a: int, b: int, c: int, pi: int) -> tuple[int, int, int, int]:
    """Numbers of roots of Q modulo pi in the extensions of degrees 1, 2, 3, 4 of F_2[s]/pi (pi irreducible, not s)."""
    k = pi.bit_length() - 1
    counts = []
    for d in (1, 2, 3, 4):
        F = Field(k * d)
        thetas = [x for x in range(1 << F.m) if F.poly_at([(pi >> i) & 1 for i in range(k + 1)], x) == 0]  # (k,)
        theta = thetas[0]  # every root of pi gives the same counts, the roots being conjugate
        P = quartic(a, b, c, theta, F)
        counts.append(sum(1 for z in range(1 << F.m) if F.poly_at(P, z) == 0))
    return counts[0], counts[1], counts[2], counts[3]


def cycle_type(counts: tuple[int, int, int, int]) -> str | None:
    """'3-cycle' or '4-cycle' when the root counts certify that Frobenius type with Q modulo pi separable, else None."""
    n1, n2, n3, n4 = counts
    if n1 == 1 and n3 == 4:
        return "3-cycle"
    if n2 == 0 and n4 == 4:
        return "4-cycle"
    return None


def certificates(kmax: int = 3) -> dict[tuple[int, int, int], dict[str, int]]:
    """For each asymmetric radius-2 rule, the first place (by degree, then bit mask) that certifies each cycle type."""
    out: dict[tuple[int, int, int], dict[str, int]] = {}
    for rule in ASYMMETRIC:
        found: dict[str, int] = {}
        for k in range(1, kmax + 1):
            for pi in irreducibles(k):
                if pi == 0b10:
                    continue  # the place s = 0, where the leading coefficient vanishes
                kind = cycle_type(frobenius_pattern(*rule, pi))
                if kind and kind not in found:
                    found[kind] = pi
        out[rule] = found
    return out


def run_row(coeffs: list[int], left: int, row: list[int], q: int, steps: int) -> tuple[np.ndarray, int]:
    """Rows 0 .. steps - 1 of the linear rule with coefficients a_(-left) .. a_(right) on a finite row over F_q.

    Returns the rows padded to a common width and the cell index of their column 0."""
    r = left
    rp = len(coeffs) - 1 - left
    width = len(row) + (r + rp) * steps
    origin = rp * steps  # cell 0 of the row sits at this column; the support grows by r' to the left, r to the right
    rows = np.zeros((steps, width), dtype=np.int64)  # (steps, width)
    rows[0, origin:origin + len(row)] = row
    kernel = np.array(coeffs[::-1], dtype=np.int64)  # (r + r' + 1,): new x_i = sum_k a_k x_(i+k)
    for t in range(1, steps):
        full = np.convolve(rows[t - 1], kernel)  # (width + r + r',)
        rows[t] = full[rp:rp + width] % q
    return rows, origin


def is_eventually_periodic(column: np.ndarray, pmax: int) -> bool:
    """Whether the column repeats with some period at most pmax on its last three quarters.

    A column of a linear rule over F_2 copies (or, with b = 0, nearly clears) its first 2^k values after time 2^k,
    so a window of a single dyadic scale can repeat although the column does not; three quarters of the run spans
    several scales and a short period has to hold across all of them."""
    # column: (T,)
    T = column.size
    tail = column[T // 4:]  # (T - T // 4,)
    return any(np.array_equal(tail[P:], tail[:-P]) for P in range(1, pmax + 1))


def rows_up_to_translation(width: int, q: int) -> list[list[int]]:
    """Every row over F_q with nonzero end cells and at most `width` cells, once up to translation and scaling of
    the first cell to 1."""
    out = []
    for w in range(1, width + 1):
        for middle in product(range(q), repeat=max(w - 2, 0)):
            ends = [[1]] if w == 1 else [[1, *middle, e] for e in range(1, q)]
            out.extend(ends)
    return out


def ep_columns(coeffs: list[int], left: int, q: int, width: int, reach: int, steps: int,
               pmax: int) -> list[tuple[list[int], int, np.ndarray]]:
    """The (row, column, column values) whose column repeats with period at most pmax on [steps/4, steps), for every
    row of `rows_up_to_translation` and every column from -reach to width - 1 + reach."""
    found = []
    for row in tqdm(rows_up_to_translation(width, q), desc=f"q={q} coeffs={coeffs}", leave=False):
        rows, origin = run_row(coeffs, left, row, q, steps)
        for p in range(-reach, len(row) + reach):
            col = rows[:, origin + p]  # (steps,)
            if is_eventually_periodic(col, pmax):
                found.append((row, p, col))
    return found


def twisted_symmetric(row: list[int], p: int, a: int, c: int, q: int) -> bool:
    """x_(p+m) = -(a/c)^m x_(p-m) for every integer m, with negative powers taken in F_q."""
    ratio = (a * pow(c, q - 2, q)) % q
    inv_ratio = pow(ratio, q - 2, q)
    cell = lambda i: row[i] if 0 <= i < len(row) else 0  # noqa: E731
    span = len(row) + abs(p) + 1
    for m in range(-span, span + 1):
        power = pow(ratio, m, q) if m >= 0 else pow(inv_ratio, -m, q)
        if (cell(p + m) + power * cell(p - m)) % q != 0:
            return False
    return True


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--certificates", action="store_true")
    parser.add_argument("--radius-two", type=int, metavar="WIDTH")
    parser.add_argument("--radius-one", nargs=2, type=int, metavar=("Q", "WIDTH"))
    parser.add_argument("--steps", type=int, default=1024)
    parser.add_argument("--pmax", type=int, default=64)
    parser.add_argument("--reach", type=int, default=6)
    args = parser.parse_args()
    if args.certificates:
        for rule, found in certificates().items():
            print(f"(a, b, c) = {rule}: " + ", ".join(f"{kind} at pi = {bin(pi)[2:]}" for kind, pi in sorted(found.items())))
    if args.radius_two:
        for a, b, c in ASYMMETRIC:
            found = ep_columns([1, a, b, c, 1], 2, 2, args.radius_two, args.reach, args.steps, args.pmax)
            bad = [(row, p) for row, p, col in found if col[1:].any()]
            print(f"(a, b, c) = ({a}, {b}, {c}): {len(found)} eventually periodic columns, "
                  f"{len(bad)} not white from time 1 on")
    if args.radius_one:
        q, width = args.radius_one
        mismatches = total = 0
        for a, b, c in product(range(1, q), range(q), range(1, q)):
            found = {(tuple(row), p) for row, p, _ in ep_columns([a, b, c], 1, q, width, args.reach, args.steps // 2,
                                                                args.pmax)}
            for row in rows_up_to_translation(width, q):
                for p in range(-args.reach, len(row) + args.reach):
                    total += 1
                    mismatches += ((tuple(row), p) in found) != twisted_symmetric(row, p, a, c, q)
        print(f"q = {q}, rows of up to {width} cells: {total} columns, {mismatches} where periodicity and the "
              "twisted symmetry disagree")


if __name__ == "__main__":
    main()
