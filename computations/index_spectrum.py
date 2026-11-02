"""The center cell as a Boolean function of the binary digits of its index: algebraic normal form, Walsh spectrum and
correlation with counts of digits modulo 3, against random functions and positive controls.

g_L(n) = c(n) for 1 <= n < 2^L and g_L(0) = 0, a function of the L digits n_0 (least significant) .. n_(L-1) of n.

* `monomial_profile`: the number of monomials of its algebraic normal form over GF(2) and the largest degree, by the
  Moebius transform (`computations.algebra.moebius`). A random function has 2^(L-1) monomials on average.
* `walsh_bias`: the largest |E_n (-1)^(g(n) + sum_(i in S) n_i)| over nonempty sets S of digits, the best correlation
  of g with a parity of digits, by the fast Walsh-Hadamard transform.
* `mod3_bias`: the largest |E_n [(-1)^g(n) (1[|n and S| = r mod 3] - 1/3)]| over nonempty S and r = 0, 1, 2, the best
  correlation of g with the residue modulo 3 of a sum of digits, from the transform with kernel [[1, 1], [1, w]],
  w = exp(2 pi i / 3), which gives T(S) = sum_n (-1)^g(n) w^|n and S| for every S at once.

The controls: Thue-Morse (a parity of all digits, so Walsh bias 1), Rudin-Shapiro (an algebraic normal form of degree
2 with L - 1 monomials) and the indicator of popcount(n) = 0 mod 3 (mod-3 bias 4/9).

    python -m computations.index_spectrum --bits 18 --random 20   # the table of the entry to L = 18 (about 15 s)
"""

from __future__ import annotations

import argparse
import sys

import numpy as np
from tqdm.auto import tqdm

from computations.algebra import moebius
from computations.rule30 import center_column

OMEGA = np.exp(2j * np.pi / 3)


def index_function(cells: np.ndarray, bits: int) -> np.ndarray:
    """g on [0, 2^bits): the center column with cell 0 set white."""
    # cells: (at least 2^bits,)
    table = cells[: 1 << bits].astype(np.uint8).copy()  # (2^bits,)
    table[0] = 0
    return table  # (2^bits,)


def popcounts(size: int) -> np.ndarray:
    """The number of 1 digits of every n < size."""
    n = np.arange(size, dtype=np.int64)  # (size,)
    counts = np.zeros(size, dtype=np.int64)  # (size,)
    while n.any():
        counts += n & 1
        n >>= 1
    return counts  # (size,)


def monomial_profile(table: np.ndarray) -> tuple[int, int]:
    """The number of monomials of the algebraic normal form of a truth table and its degree (-1 for the zero
    function)."""
    # table: (2^L,)
    monomials = np.flatnonzero(moebius(table))  # (terms,)
    if monomials.size == 0:
        return 0, -1
    return int(monomials.size), int(popcounts(table.size)[monomials].max())


def walsh(table: np.ndarray) -> np.ndarray:
    """The Walsh-Hadamard spectrum: entry S is sum_n (-1)^(table(n) + |n and S|)."""
    # table: (2^L,)
    spectrum = 1 - 2 * table.astype(np.int64)  # (2^L,)
    bits = table.size.bit_length() - 1
    for i in range(bits):
        spectrum = spectrum.reshape(-1, 2, 1 << i)  # (2^(L - i - 1), 2, 2^i)
        low, high = spectrum[:, 0, :].copy(), spectrum[:, 1, :].copy()  # each (2^(L - i - 1), 2^i)
        spectrum[:, 0, :], spectrum[:, 1, :] = low + high, low - high
        spectrum = spectrum.reshape(-1)  # (2^L,)
    return spectrum  # (2^L,)


def walsh_bias(table: np.ndarray) -> float:
    """The largest correlation of a truth table with a parity of a nonempty set of digits."""
    # table: (2^L,)
    return float(np.abs(walsh(table)[1:]).max() / table.size)


def mod3_transform(table: np.ndarray) -> np.ndarray:
    """Entry S is sum_n (-1)^table(n) w^|n and S|, w a primitive cube root of unity."""
    # table: (2^L,)
    spectrum = (1 - 2 * table.astype(np.float64)).astype(np.complex128)  # (2^L,)
    bits = table.size.bit_length() - 1
    for i in range(bits):
        spectrum = spectrum.reshape(-1, 2, 1 << i)  # (2^(L - i - 1), 2, 2^i)
        low, high = spectrum[:, 0, :].copy(), spectrum[:, 1, :].copy()  # each (2^(L - i - 1), 2^i)
        spectrum[:, 0, :], spectrum[:, 1, :] = low + high, low + OMEGA * high
        spectrum = spectrum.reshape(-1)  # (2^L,)
    return spectrum  # (2^L,)


def mod3_bias(table: np.ndarray) -> float:
    """The largest |E_n (-1)^table(n) (1[|n and S| = r mod 3] - 1/3)| over nonempty S and r = 0, 1, 2. Since
    1[m = r mod 3] = (1 + w^(m - r) + w^(2(m - r))) / 3, this is (2/3) |Re(w^(-r) T(S))| / 2^L."""
    # table: (2^L,)
    spectrum = mod3_transform(table)[1:]  # (2^L - 1,)
    best = 0.0
    for r in range(3):
        best = max(best, float(np.abs((2 / 3) * np.real(np.conj(OMEGA**r) * spectrum)).max()))
    return best / table.size


def thue_morse_table(bits: int) -> np.ndarray:
    """The parity of the digits of n."""
    return (popcounts(1 << bits) & 1).astype(np.uint8)  # (2^bits,)


def rudin_shapiro_table(bits: int) -> np.ndarray:
    """The parity of the number of adjacent pairs of 1 digits of n, a quadratic form in the digits."""
    n = np.arange(1 << bits, dtype=np.int64)  # (2^bits,)
    return (popcounts(1 << bits)[n & (n >> 1)] & 1).astype(np.uint8)  # (2^bits,)


def mod3_table(bits: int) -> np.ndarray:
    """1 when the number of 1 digits of n is divisible by 3."""
    return (popcounts(1 << bits) % 3 == 0).astype(np.uint8)  # (2^bits,)


def profile(table: np.ndarray) -> tuple[int, int, float, float]:
    """Monomials, degree, Walsh bias and mod-3 bias of a truth table."""
    # table: (2^L,)
    monomials, degree = monomial_profile(table)
    return monomials, degree, walsh_bias(table), mod3_bias(table)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--bits", type=int, default=18)
    parser.add_argument("--random", type=int, default=20)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    cells = center_column(1 << args.bits)  # (2^bits,)
    rng = np.random.default_rng(args.seed)
    print("L  monomials  2^(L-1)  degree | random: monomials mean, sd, min degree | walsh: center, random mean, random max"
          " | mod3: center, random mean, random max")
    for bits in tqdm(range(8, args.bits + 1, 2), desc="L", file=sys.stderr):
        center = profile(index_function(cells, bits))
        rows = [profile(rng.integers(0, 2, 1 << bits, dtype=np.uint8)) for _ in range(args.random)]
        counts = np.array([r[0] for r in rows])  # (random,)
        print(
            f"{bits:2d}  {center[0]:9d}  {1 << (bits - 1):7d}  {center[1]:6d} | {counts.mean():9.1f} {counts.std():6.1f} "
            f"{min(r[1] for r in rows):3d} | {center[2]:.4f} {np.mean([r[2] for r in rows]):.4f} "
            f"{max(r[2] for r in rows):.4f} | {center[3]:.4f} {np.mean([r[3] for r in rows]):.4f} "
            f"{max(r[3] for r in rows):.4f}"
        )
    bits = args.bits
    for name, table in [("Thue-Morse", thue_morse_table(bits)), ("Rudin-Shapiro", rudin_shapiro_table(bits)),
                        ("popcount = 0 mod 3", mod3_table(bits))]:
        monomials, degree, wb, mb = profile(table)
        print(f"control {name}, L = {bits}: monomials {monomials}, degree {degree}, walsh {wb:.4f}, mod3 {mb:.4f}")


if __name__ == "__main__":
    main()
