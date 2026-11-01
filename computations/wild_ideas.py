"""Three tests of hidden algebraic structure in Rule 30, each against a random control and a positive control.

* **Ore equations over GF(2)(x).** With f = sum c(n) x^n the center column's generating series, look for polynomials
  P_{-1}, P_0, ..., P_k over GF(2), of degree at most D and not all zero, with
  P_{-1} + P_0 f + P_1 f^2 + P_2 f^4 + ... + P_k f^(2^k) = 0 modulo x^n. In characteristic 2, f^(2^i) = f(x^(2^i)),
  so these are the Mahler-type equations, and by Christol's theorem f satisfies one exactly when c is 2-automatic.
  `ore_profile` returns, for each D, the dimension of the space of solutions modulo x^n; for a random series it is
  0 until the (k + 2)(D + 1) unknowns outnumber the n equations.
* **Short integer relations by LLL.** The column read as the 2-adic integer z = sum c(n) 2^n and as the real number
  r = sum c(n) 2^(-n-1). `two_adic_lattice` is the lattice of integer vectors (a_0, ..., a_d) with
  sum a_i z^i = 0 modulo 2^m; `real_lattice` embeds sum a_i r^i, scaled by 2^(m - 8), as one more coordinate; and
  `constants_lattice` does the same for a linear relation among r, 1, sqrt 2, sqrt 3, sqrt 5, pi, e and log 2. `lll`
  is an exact integer LLL (delta = 3/4), so the first reduced vector b_1 is at most 2^((N - 1)/2) times the shortest
  one, N the lattice dimension: every nonzero vector, and so every relation, has norm at least |b_1| 2^(-(N - 1)/2).
* **Communication rank of the cone.** c_t, the cell at time t under column 0 as a function of the 2t + 1 cells
  x_{-t} .. x_t of row 0, split into the a leftmost cells and the rest. `cut_rank` is the GF(2) rank of the
  2^(2t+1-a) x 2^a matrix of values. The control `structured_control` keeps the two facts about Rule 30 that cap the
  rank: c_t = x_{-t} xor g, and the cells x_{t-1}, x_t enter only through x_{t-1} or x_t; g is random. The rules
  45, 120 (left-permutive like Rule 30, other classes) and 150 (linear) are run through `rule_cone_table` beside it.

    python -m computations.wild_ideas ore --cells 8192 --max-k 5     # Ore equations, center column and controls
    python -m computations.wild_ideas lll --bits 4096 --max-degree 8  # 2-adic, real and constant relations
    python -m computations.wild_ideas rank --max-t 11                 # cut ranks of c_t and of the control
"""

from __future__ import annotations

import argparse
import math
import sys

import numpy as np

from tqdm.auto import tqdm

from computations.cone_screening import cone_table, variable_slices
from computations.rule30 import center_column


# ---------------------------------------------------------------------------------------------------------------------
# GF(2) linear algebra on Python integers


def bits_to_int(bits: np.ndarray) -> int:
    """The integer whose bit i is bits[i]."""
    # bits: (n,)
    packed = np.packbits(bits.astype(np.uint8), bitorder="little")  # (ceil(n / 8),)
    return int.from_bytes(packed.tobytes(), "little")


def insert(basis: dict[int, int], vector: int) -> bool:
    """Reduce `vector` by the GF(2) basis (keyed by each member's lowest set bit) and add what is left. True when the
    vector was independent of the basis."""
    while vector:
        low = (vector & -vector).bit_length()
        pivot = basis.get(low)
        if pivot is None:
            basis[low] = vector
            return True
        vector ^= pivot
    return False


def gf2_rank(rows: list[int]) -> int:
    """The GF(2) rank of the vectors held as integers."""
    basis: dict[int, int] = {}
    return sum(insert(basis, row) for row in rows)


# ---------------------------------------------------------------------------------------------------------------------
# Ore (Mahler-type) equations over GF(2)(x)


def frobenius_power(cells: np.ndarray, i: int, n: int) -> int:
    """f(x^(2^i)) = f^(2^i) modulo x^n, for f = sum cells[j] x^j, as an integer (bit j the coefficient of x^j)."""
    # cells: (len,)
    spread = np.zeros(n, dtype=np.uint8)  # (n,)
    positions = np.nonzero(cells)[0] << i  # (black cells,)
    spread[positions[positions < n]] = 1
    return bits_to_int(spread)


def ore_profile(cells: np.ndarray, k: int, n: int, max_degree: int, progress: bool = False) -> np.ndarray:
    """Entry D is the dimension of the space of (P_{-1}, P_0, ..., P_k), each of degree at most D, with
    P_{-1} + sum_i P_i f^(2^i) = 0 modulo x^n, where f = sum cells[j] x^j."""
    # cells: (>= n,)
    mask = (1 << n) - 1
    series = [1] + [frobenius_power(cells[:n], i, n) for i in range(k + 1)]  # k + 2 integers
    basis: dict[int, int] = {}
    nullity = 0
    profile = np.zeros(max_degree + 1, dtype=np.int64)  # (max_degree + 1,)
    for degree in tqdm(range(max_degree + 1), desc=f"Ore k={k}", file=sys.stderr, disable=not progress):
        for s in series:
            if not insert(basis, (s << degree) & mask):
                nullity += 1
        profile[degree] = nullity
    return profile  # (max_degree + 1,)


def first_relation(profile: np.ndarray) -> int | None:
    """The least degree bound D with a nonzero solution, or None."""
    # profile: (max_degree + 1,)
    hits = np.nonzero(profile)[0]  # (hits,)
    return int(hits[0]) if hits.size else None


def thue_morse(n: int) -> np.ndarray:
    """Parity of the binary digit sum of 0 .. n - 1, a 2-automatic sequence."""
    index = np.arange(n, dtype=np.int64)  # (n,)
    parity = np.zeros(n, dtype=np.uint8)  # (n,)
    while index.any():
        parity ^= (index & 1).astype(np.uint8)
        index >>= 1
    return parity  # (n,)


def period_doubling(n: int) -> np.ndarray:
    """The period-doubling sequence, a 2-automatic sequence: the 2-adic valuation of n + 1 modulo 2."""
    index = np.arange(1, n + 1, dtype=np.int64)  # (n,)
    valuation = np.zeros(n, dtype=np.int64)  # (n,)
    while (index % 2 == 0).any():
        even = index % 2 == 0  # (n,)
        valuation[even] += 1
        index[even] //= 2
    return (valuation % 2).astype(np.uint8)  # (n,)


def random_bits(n: int, seed: int) -> np.ndarray:
    """n independent fair bits from numpy's PCG64."""
    return np.random.default_rng(seed).integers(0, 2, n, dtype=np.uint8)  # (n,)


# ---------------------------------------------------------------------------------------------------------------------
# Exact integer LLL and the relation lattices


def lll(basis: list[list[int]]) -> list[list[int]]:
    """LLL reduction with delta = 3/4 in exact integer arithmetic (Cohen, A Course in Computational Algebraic Number
    Theory, Algorithm 2.6.7). The rows must be linearly independent."""
    b = [list(row) for row in basis]
    size = len(b)
    d = [1] + [0] * size  # d[i + 1] is the Gram determinant of the first i + 1 rows
    lam = [[0] * size for _ in range(size)]
    known = 0

    def dot(u: list[int], v: list[int]) -> int:
        return sum(x * y for x, y in zip(u, v))

    def reduce(k: int, l: int) -> None:
        if 2 * abs(lam[k][l]) > d[l + 1]:
            q = (2 * lam[k][l] + d[l + 1]) // (2 * d[l + 1])
            b[k] = [x - q * y for x, y in zip(b[k], b[l])]
            lam[k][l] -= q * d[l + 1]
            for i in range(l):
                lam[k][i] -= q * lam[l][i]

    def swap(k: int) -> None:
        b[k], b[k - 1] = b[k - 1], b[k]
        for j in range(k - 1):
            lam[k][j], lam[k - 1][j] = lam[k - 1][j], lam[k][j]
        mu = lam[k][k - 1]
        new = (d[k - 1] * d[k + 1] + mu * mu) // d[k]
        for i in range(k + 1, known + 1):
            t = lam[i][k]
            lam[i][k] = (d[k + 1] * lam[i][k - 1] - mu * t) // d[k]
            lam[i][k - 1] = (new * t + mu * lam[i][k]) // d[k + 1]
        d[k] = new

    d[1] = dot(b[0], b[0])
    k = 1
    while k < size:
        if k > known:
            known = k
            for j in range(k + 1):
                u = dot(b[k], b[j])
                for i in range(j):
                    u = (d[i + 1] * u - lam[k][i] * lam[j][i]) // d[i]
                if j < k:
                    lam[k][j] = u
                else:
                    d[k + 1] = u
        reduce(k, k - 1)
        if 4 * d[k + 1] * d[k - 1] < 3 * d[k] * d[k] - 4 * lam[k][k - 1] ** 2:
            swap(k)
            k = max(1, k - 1)
        else:
            for l in range(k - 2, -1, -1):
                reduce(k, l)
            k += 1
    return b


def log2_int(value: int) -> float:
    """log2 of a positive integer of any size."""
    excess = max(value.bit_length() - 60, 0)
    return excess + math.log2(value >> excess)


def log2_norm(vector: list[int]) -> float:
    """log2 of the Euclidean norm of an integer vector."""
    return 0.5 * log2_int(sum(x * x for x in vector))


def column_integer(cells: np.ndarray) -> int:
    """sum cells[n] 2^n: the first len(cells) bits of the 2-adic integer z, or 2^m r for the real r."""
    return bits_to_int(cells)


def two_adic_lattice(z: int, degree: int, bits: int) -> list[list[int]]:
    """A basis of the vectors (a_0, ..., a_degree) with sum a_i z^i = 0 modulo 2^bits; determinant 2^bits."""
    modulus = 1 << bits
    basis = [[modulus] + [0] * degree]
    for i in range(1, degree + 1):
        row = [(-pow(z, i, modulus)) % modulus] + [0] * degree
        row[i] = 1
        basis.append(row)
    return basis


def reversed_integer(cells: np.ndarray) -> int:
    """2^m r truncated, for r = sum cells[n] 2^(-n-1) and m = len(cells): cell 0 is the leading bit."""
    return bits_to_int(cells[::-1].copy())


def real_lattice(numerator: int, degree: int, bits: int) -> list[list[int]]:
    """Rows (e_i, floor(2^(bits-8) r^i)) for i = 0 .. degree, with r = numerator / 2^bits."""
    scale = bits - 8
    basis = []
    for i in range(degree + 1):
        shift = bits * i - scale
        value = (numerator**i) >> shift if shift >= 0 else numerator**i << -shift  # floor(2^scale r^i), error <= i + 1
        row = [0] * (degree + 1) + [value]
        row[i] = 1
        basis.append(row)
    return basis


def pi_scaled(bits: int) -> int:
    """floor(pi 2^bits) up to a few units, by Machin's formula on integers."""
    guard = bits + 20

    def arctan_inv(x: int) -> int:
        total, term, k, sign = 0, (1 << guard) // x, 1, 1
        while term:
            total += sign * (term // k)
            term //= x * x
            k += 2
            sign = -sign
        return total

    return (16 * arctan_inv(5) - 4 * arctan_inv(239)) >> 20


def e_scaled(bits: int) -> int:
    """floor(e 2^bits) up to a few units."""
    guard = bits + 20
    total, term, k = 0, 1 << guard, 0
    while term:
        total += term
        k += 1
        term //= k
    return total >> 20


def log2_scaled(bits: int) -> int:
    """floor(log 2 * 2^bits) up to a few units: log 2 = sum_{k >= 1} 1 / (k 2^k)."""
    guard = bits + 20
    return sum((1 << (guard - k)) // k for k in range(1, guard + 1)) >> 20


def constants_lattice(numerator: int, bits: int) -> tuple[list[list[int]], list[str]]:
    """Rows (e_i, floor(2^(bits-8) v_i)) for v = (r, 1, sqrt 2, sqrt 3, sqrt 5, pi, e, log 2), r = numerator / 2^bits."""
    names = ["r", "1", "sqrt2", "sqrt3", "sqrt5", "pi", "e", "log2"]
    values = [
        numerator,
        1 << bits,
        math.isqrt(2 << (2 * bits)),
        math.isqrt(3 << (2 * bits)),
        math.isqrt(5 << (2 * bits)),
        pi_scaled(bits),
        e_scaled(bits),
        log2_scaled(bits),
    ]
    basis = []
    for i, value in enumerate(values):
        row = [0] * len(values) + [value >> 8]
        row[i] = 1
        basis.append(row)
    return basis, names


def relation_bound(basis: list[list[int]]) -> tuple[float, float]:
    """(log2 of the first LLL vector's norm, log2 of the lower bound 2^(-(N-1)/2) |b_1| on every nonzero vector)."""
    reduced = lll(basis)
    first = min(log2_norm(row) for row in reduced)
    return first, first - (len(basis) - 1) / 2


def two_adic_root(coefficients: list[int], start: int, bits: int) -> int:
    """The root modulo 2^bits of the integer polynomial sum coefficients[i] x^i that lifts `start`, by Hensel
    lifting one bit at a time (the root must be simple modulo 2)."""
    root = start
    for b in range(1, bits):
        modulus = 1 << (b + 1)
        value = sum(c * pow(root, i, modulus) for i, c in enumerate(coefficients)) % modulus
        if value:
            root += 1 << b
    return root % (1 << bits)


def int_to_bits(value: int, bits: int) -> np.ndarray:
    """The lowest `bits` bits of `value`, bit 0 first."""
    return np.array([(value >> i) & 1 for i in range(bits)], dtype=np.uint8)  # (bits,)


# ---------------------------------------------------------------------------------------------------------------------
# Communication rank of the cone function


def cut_rank(table: np.ndarray, t: int, left: int) -> int:
    """GF(2) rank of the matrix of a function of the 2t + 1 cone cells (bit i of the index is x_{-t+i}) with the
    `left` leftmost cells as columns and the rest as rows."""
    # table: (2^(2t+1),)
    matrix = table.reshape(1 << (2 * t + 1 - left), 1 << left)  # (rows, columns)
    if left > 2 * t + 1 - left:
        matrix = matrix.T  # pack the shorter side
    packed = np.packbits(matrix, axis=1, bitorder="little")  # (rows, bytes)
    return gf2_rank([int.from_bytes(row.tobytes(), "little") for row in packed])


def structured_control(t: int, seed: int) -> np.ndarray:
    """x_{-t} xor G(x_{-t+1}, ..., x_{t-2}, x_{t-1} or x_t) with G a uniformly random function: the two facts about
    Rule 30's c_t that cap its cut ranks, and nothing else."""
    n = 2 * t + 1
    index = np.arange(1 << n, dtype=np.int64)  # (2^n,)
    leftmost = index & 1  # (2^n,)
    middle = (index >> 1) & ((1 << (n - 3)) - 1)  # (2^n,), x_{-t+1} .. x_{t-2}
    tail = ((index >> (n - 2)) & 3) != 0  # (2^n,), x_{t-1} or x_t
    g = np.random.default_rng(seed).integers(0, 2, 1 << (n - 2), dtype=np.uint8)  # (2^(n-2),)
    return (leftmost.astype(np.uint8) ^ g[middle | (tail.astype(np.int64) << (n - 3))]).astype(np.uint8)  # (2^n,)


def cap(t: int, left: int) -> int:
    """The rank that the two structural facts allow at a cut: columns pair up into complements (x_{-t} is a column
    variable) and, when x_{t-1} and x_t are both row variables, three of every four rows agree."""
    columns = 1 << left
    if left >= 1:
        columns = (1 << (left - 1)) + 1
    rows_count = 1 << (2 * t + 1 - left)
    if 2 * t + 1 - left >= 2:
        rows_count = (rows_count // 4) * 2
    return min(columns, rows_count)


def rule_cone_table(t: int, rule: int) -> np.ndarray:
    """The cell at time t under column 0, for the elementary rule with Wolfram number `rule`, for all 2^(2t+1)
    assignments of x_{-t} .. x_t; bit i of the index is x_{-t+i}."""
    row: list[np.ndarray] = variable_slices(2 * t + 1)  # (2t + 1) x (2^(2t+1),)
    for _ in range(t):
        new = []
        for i in range(1, len(row) - 1):
            p, q, r = row[i - 1], row[i], row[i + 1]  # each (2^(2t+1),)
            value = np.zeros_like(p)  # (2^(2t+1),)
            for pattern in range(8):
                if rule >> pattern & 1:
                    value |= (p if pattern & 4 else ~p) & (q if pattern & 2 else ~q) & (r if pattern & 1 else ~r)
            new.append(value)
        row = new
    return row[0].astype(np.uint8)  # (2^(2t+1),)


def distinct_lines(table: np.ndarray, t: int, left: int) -> int:
    """The smaller of the numbers of distinct rows and distinct columns of the cut matrix, which bounds its rank."""
    # table: (2^(2t+1),)
    matrix = table.reshape(1 << (2 * t + 1 - left), 1 << left)  # (rows, columns)
    rows = len(np.unique(np.packbits(matrix, axis=1), axis=0))
    columns = len(np.unique(np.packbits(matrix.T, axis=1), axis=0))
    return min(rows, columns)


def jacobsthal(n: int) -> int:
    """J_n = (2^n - (-1)^n) / 3: 0, 1, 1, 3, 5, 11, 21, ..."""
    return (2**n - (-1) ** n) // 3


def left_cut_formula(left: int) -> int:
    """2 + (J_(left+1) - 1) / 2: the rank of c_t at the left cuts with left <= t - 2 for t <= 11. At t = 12 it holds
    for left <= 9 and fails at left = 10 (rank 295)."""
    return 2 + (jacobsthal(left + 1) - 1) // 2


def rank_profile(table: np.ndarray, t: int) -> list[int]:
    """cut_rank for every cut 1 .. 2t."""
    return [cut_rank(table, t, left) for left in range(1, 2 * t + 1)]


# ---------------------------------------------------------------------------------------------------------------------
# Runs


def run_ore(cells_count: int, max_k: int) -> None:
    sources = {
        "center": center_column(cells_count),
        "random": random_bits(cells_count, 1),
        "thue-morse": thue_morse(cells_count),
        "period-doubling": period_doubling(cells_count),
    }
    print(f"n = {cells_count} coefficients; D* = least degree bound with a nonzero solution; "
          "random expectation: (k + 2)(D + 1) just above n")
    for k in range(max_k + 1):
        max_degree = cells_count // (k + 2) + 4
        line = [f"k = {k}: n / (k + 2) - 1 = {cells_count // (k + 2) - 1}"]
        for name, cells in sources.items():
            if name in ("thue-morse", "period-doubling"):
                profile = ore_profile(cells, k, cells_count, min(max_degree, 64))
            else:
                profile = ore_profile(cells, k, cells_count, max_degree, progress=True)
            found = first_relation(profile)
            excess = "none" if found is None else (k + 2) * (found + 1) - cells_count
            line.append(f"{name} D* = {found} (unknowns - n = {excess})")
        print("; ".join(line), flush=True)


def run_lll(bits: int, max_degree: int) -> None:
    sources = {
        "center": center_column(bits),
        "random": random_bits(bits, 2),
        "x^2+x-4": int_to_bits(two_adic_root([-4, 1, 1], 0, bits), bits),
        "cbrt9": int_to_bits(two_adic_root([-9, 0, 0, 1], 1, bits), bits),
    }
    print(f"2-adic, m = {bits} bits: log2 |b1| of the reduced basis, Gaussian heuristic m / (d + 1)")
    for degree in range(2, max_degree + 1):
        parts = [f"d = {degree}: m/(d+1) = {bits / (degree + 1):.1f}"]
        for name, cells in sources.items():
            first, _ = relation_bound(two_adic_lattice(column_integer(cells), degree, bits))
            parts.append(f"{name} {first:.1f}")
        print("; ".join(parts), flush=True)
    real_sources = {
        "center": center_column(bits),
        "random": random_bits(bits, 3),
        "cbrt2-1": int_to_bits(_cube_root_scaled(2, bits) - (1 << bits), bits)[::-1].copy(),
    }
    print(f"real, m = {bits} bits, scale 2^(m-8): log2 |b1|, heuristic (m - 8) / (d + 1)")
    for degree in range(2, max_degree + 1):
        parts = [f"d = {degree}: (m-8)/(d+1) = {(bits - 8) / (degree + 1):.1f}"]
        for name, cells in real_sources.items():
            first, _ = relation_bound(real_lattice(reversed_integer(cells), degree, bits))
            parts.append(f"{name} {first:.1f}")
        print("; ".join(parts), flush=True)
    planted = pi_scaled(bits) + math.isqrt(2 << (2 * bits)) - (4 << bits)  # pi + sqrt 2 - 4, about 0.556
    constant_sources = {**real_sources, "pi+sqrt2-4": int_to_bits(planted, bits)[::-1].copy()}
    for name, cells in constant_sources.items():
        basis, labels = constants_lattice(reversed_integer(cells), bits)
        reduced = lll(basis)
        best = min(reduced, key=lambda row: sum(x * x for x in row))
        print(f"constants {labels}: {name} log2 |b1| = {log2_norm(best):.1f} "
              f"(heuristic {(bits - 8) / len(labels):.1f}), coefficient of r {best[0] != 0}", flush=True)


def _cube_root_scaled(value: int, bits: int) -> int:
    """floor(value^(1/3) 2^bits)."""
    target = value << (3 * bits)
    root = 1 << (bits + 1)
    while True:
        better = (2 * root + target // (root * root)) // 3
        if better >= root:
            break
        root = better
    while root**3 > target:
        root -= 1
    while (root + 1) ** 3 <= target:
        root += 1
    return root


def run_rank(max_t: int, min_t: int, rules: list[int]) -> None:
    for t in range(min_t, max_t + 1):
        table = cone_table(t)  # (2^(2t+1),)
        cuts = range(1, 2 * t + 1)
        center = rank_profile(table, t)
        print(f"t = {t}: cut a = 1 .. {2 * t} (a = leftmost cells on the column side)")
        print(f"  rule 30 rank         {center}")
        print(f"  distinct-line bound  {[distinct_lines(table, t, a) for a in cuts]}")
        print(f"  2 + (J(a+1) - 1)/2   {[left_cut_formula(a) for a in cuts]}")
        print(f"  random-g control     {rank_profile(structured_control(t, t), t)}")
        print(f"  cap of the two facts {[cap(t, a) for a in cuts]}")
        for rule in rules:
            print(f"  rule {rule:3d} rank        {rank_profile(rule_cone_table(t, rule), t)}", flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="test", required=True)
    ore = sub.add_parser("ore")
    ore.add_argument("--cells", type=int, default=8192)
    ore.add_argument("--max-k", type=int, default=4)
    lat = sub.add_parser("lll")
    lat.add_argument("--bits", type=int, default=4096)
    lat.add_argument("--max-degree", type=int, default=8)
    rank = sub.add_parser("rank")
    rank.add_argument("--max-t", type=int, default=11)
    rank.add_argument("--min-t", type=int, default=2)
    rank.add_argument("--rules", type=int, nargs="*", default=[45, 120, 150])
    args = parser.parse_args()
    if args.test == "ore":
        run_ore(args.cells, args.max_k)
    elif args.test == "lll":
        run_lll(args.bits, args.max_degree)
    else:
        run_rank(args.max_t, args.min_t, args.rules)


if __name__ == "__main__":
    main()
