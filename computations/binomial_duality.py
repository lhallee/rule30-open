"""The binomial transform of the center column over GF(2), and the first rung of Problem 3 on both of its sides.

gamma(n) is the sum mod 2 of c(t) over the t whose binary digits are digits of n (t & n = t); by Lucas's theorem
gamma(n) = sum_t C(n, t) c(t) mod 2. `Rule30Open/Complexity/BinomialDuality.lean` proves that c has period 2^a on
[2^m, oo) iff gamma has period 2^m on [2^a, oo), with the same least witness offset, and that gamma is eventually
periodic iff c is. This module computes the numbers its entry quotes.

* `binomial_transform`: the transform of a 0/1 array on [0, n), by the subset-sum butterfly of
  `computations.algebra.moebius` on the array padded with zeros to a power of two. Entry n of the transform reads only
  entries t <= n, so the padding changes nothing below n.
* `first_mismatch`: the least j >= 0 with x[s + j + P] != x[s + j] inside the data, or None.
* `rung_offset`: for one k, the least witness offsets of "c is not 2^k-periodic from 2^(k-1)" and of the dual
  statement "gamma is not 2^(k-1)-periodic from 2^k".
* `least_eventual_period`: the least p for which the data have period p from some T with at least `confirm` checks
  after T, and that T.
* `multiples_period`: the least eventual period and transient of the transform of the indicator of the multiples of q
  (period q from 0). A power of two q = 2^e gives a transform that vanishes from 2^e on, as the duality says; an odd
  part of q need not survive (q = 5 gives period 15).

    python -m computations.binomial_duality                          # the numbers of the entry (seconds)
    python -m computations.binomial_duality --bits 20 --max-k 20 --cells 1572928   # to L = 20 and k = 20 (5 minutes)
"""

from __future__ import annotations

import argparse
import sys
import time

import numpy as np
from tqdm.auto import tqdm

from computations.algebra import moebius
from computations.rule30 import center_column

MULTIPLES = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 17, 21, 31)


def binomial_transform(values: np.ndarray) -> np.ndarray:
    """The transform over GF(2): entry n is the XOR of values[t] over the t with t & n = t."""
    # values: (n,)
    size = 1 << max(0, (len(values) - 1).bit_length())
    padded = np.zeros(size, dtype=np.uint8)  # (size,)
    padded[: len(values)] = values
    return moebius(padded)[: len(values)]  # (n,)


def first_mismatch(values: np.ndarray, start: int, period: int) -> int | None:
    """The least j >= 0 with values[start + j + period] != values[start + j], or None if there is none in the data."""
    # values: (n,)
    if start + period >= len(values):
        return None
    differ = values[start + period :] != values[start : len(values) - period]  # (n - start - period,)
    hits = np.flatnonzero(differ)  # (h,)
    return int(hits[0]) if hits.size else None


def rung_offset(column: np.ndarray, gamma: np.ndarray, k: int) -> tuple[int | None, int | None]:
    """The offset of the least m >= 2^(k-1) with c(m) != c(m + 2^k), and of the least n >= 2^k with
    gamma(n) != gamma(n + 2^(k-1)); None where the data hold no witness."""
    # column: (n,), gamma: (n,)
    return first_mismatch(column, 1 << (k - 1), 1 << k), first_mismatch(gamma, 1 << k, 1 << (k - 1))


def least_eventual_period(values: np.ndarray, max_period: int, confirm: int) -> tuple[int, int] | None:
    """The least p <= max_period such that the data have period p from some T with at least `confirm` positions
    t >= T checked, and the least such T; None if there is none."""
    # values: (n,)
    for period in range(1, max_period + 1):
        if len(values) - period < confirm:
            break
        differ = np.flatnonzero(values[period:] != values[:-period])  # (d,)
        start = int(differ[-1]) + 1 if differ.size else 0
        if len(values) - period - start >= confirm:
            return period, start
    return None


def multiples_indicator(q: int, size: int) -> np.ndarray:
    """1 at the multiples of q, 0 elsewhere: a sequence with period q from 0."""
    values = np.zeros(size, dtype=np.uint8)  # (size,)
    values[::q] = 1
    return values  # (size,)


def multiples_period(q: int, bits: int) -> tuple[int, int] | None:
    """The least eventual period and transient of the transform of the indicator of the multiples of q, seen on
    2^bits values with a quarter of them as confirmation."""
    gamma = binomial_transform(multiples_indicator(q, 1 << bits))  # (2^bits,)
    return least_eventual_period(gamma, 3 << (bits - 2), 1 << (bits - 2))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--bits", type=int, default=16, help="count the ones of gamma on [0, 2^L) for even L <= bits")
    parser.add_argument("--max-k", type=int, default=14, help="largest rung k for the least witness offsets")
    parser.add_argument("--cells", type=int, default=0,
                        help="cells of the center column to compute (default: enough for --bits and --max-k)")
    parser.add_argument("--period-bits", type=int, default=14, help="length 2^L of the data for the multiples of q")
    args = parser.parse_args()

    need = max(1 << args.bits, (1 << (args.max_k - 1)) + (1 << args.max_k) + 64, args.cells)
    started = time.time()
    column = center_column(need)  # (need,)
    gamma = binomial_transform(column)  # (need,)
    print(f"center column and its transform on {need} cells ({time.time() - started:.1f} s)", file=sys.stderr)

    print("1. ones of gamma on [0, 2^L); index-function-spectrum.md counts the monomials with c(0) set to 0, which"
          " complements gamma, so monomials = 2^L - ones")
    for b in range(8, args.bits + 1, 2):
        ones = int(gamma[: 1 << b].sum())
        print(f"  L = {b:2d}: {ones} ones of {1 << b}; {(1 << b) - ones} monomials with c(0) = 0")

    print(f"2. least witness offsets of the first rung, k = 1 .. {args.max_k}, c side / gamma side")
    rows = []
    for k in tqdm(range(1, args.max_k + 1), desc="k", file=sys.stderr):
        rows.append((k, *rung_offset(column, gamma, k)))
    print("  " + ", ".join(f"k={k}: {oc}/{og}" for k, oc, og in rows))
    print(f"  the two sides agree at every k: {all(oc == og for _, oc, og in rows)};"
          f" a witness exists in the data at every k: {all(oc is not None for _, oc, _ in rows)}")

    print(f"3. the transform of the indicator of the multiples of q, on 2^{args.period_bits} values:"
          " (least eventual period, transient)")
    for q in tqdm(MULTIPLES, desc="q", file=sys.stderr):
        print(f"  q = {q:2d}: {multiples_period(q, args.period_bits)}")


if __name__ == "__main__":
    main()
