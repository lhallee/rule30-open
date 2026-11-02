"""The query complexity of the center cell as a function of its cone: exact for small t, and full real degree.

c_t is a Boolean function of the 2t + 1 cells x_{-t} .. x_t of row 0 (new x_j = x_{j-1} xor (x_j or x_{j+1})). A
decision tree reads cells one at a time, each choice depending on the answers so far; its depth is the most cells it
reads on one row. The kit proves that every tree computing c_t has depth at least 2t - 1 (its GF(2) degree) and that
2t + 1 suffice.

* `exact_depth` finds the least depth of a decision tree for any truth table, by dynamic programming over the 3^n
  subcubes (each cell fixed to 0, fixed to 1, or free). It is used for t <= 6.
* `subcube_sums` computes nu(g) = sum over rows y of (-1)^{|y|} g(y) for g = c_t with x_{-t} = 0, a function of the
  2t cells x_{-t+1} .. x_t, on bit-sliced words, 2^m rows at a time, and the same sums with one more cell fixed. Up to
  sign nu is the coefficient of the product of all variables in the real multilinear polynomial of g, and
  mu(c_t) = 2 nu(g) that of c_t = x_{-t} xor g. A decision tree of depth d is a real polynomial of degree at most d
  (a sum over its leaves of products of at most d factors x_i or 1 - x_i), so mu(c_t) != 0 forces depth 2t + 1.
* `certificate` and `evasive` extend this when mu(c_t) = 0: if for every cell k some fixing of it leaves a function
  with a nonzero top coefficient (or, recursively, with such a certificate), the first query of any tree can be
  answered so that the rest still needs every cell, and the depth is again 2t + 1.
* `rule90_table` is the control: Rule 90's c_t is the parity of the 2^{popcount t} cells x_{-t+2i} with binomial(t, i)
  odd, so its depth is 2^{popcount t}.

    python -m computations.query_depth --exact 6 --max-t 17      # exact depths for t <= 6, certificates for t <= 17
"""

from __future__ import annotations

import argparse
import sys

import numpy as np

from tqdm.auto import tqdm

from computations.cone_screening import cone_table, variable_slices

ALL = np.uint64(0xFFFFFFFFFFFFFFFF)
LOW_PATTERNS = [np.uint64(p) for p in (
    0xAAAAAAAAAAAAAAAA, 0xCCCCCCCCCCCCCCCC, 0xF0F0F0F0F0F0F0F0,
    0xFF00FF00FF00FF00, 0xFFFF0000FFFF0000, 0xFFFFFFFF00000000,
)]  # bit b of word p_i is bit i of b, for the six variables inside a word
ODD_BITS = np.uint64(0x6996966996696996)  # bit b set when b (0 <= b < 64) has odd popcount


def rule90_table(t: int) -> np.ndarray:
    """Rule 90's c_t (new x_j = x_{j-1} xor x_{j+1}) for all 2^(2t+1) cone rows; bit i of the index is x_{-t+i}."""
    row = variable_slices(2 * t + 1)  # (2t + 1) x (2^(2t+1),)
    for _ in range(t):
        row = [row[i - 1] ^ row[i + 1] for i in range(1, len(row) - 1)]  # (len - 2) x (2^(2t+1),)
    return row[0].astype(np.uint8)  # (2^(2t+1),)


def exact_depth(table: np.ndarray, n: int) -> int:
    """The least depth of a decision tree computing the Boolean function with this truth table on n variables (bit i
    of the index is variable i). Subcubes are indexed in base 3, digit 2 meaning free; a subcube costs 0 if the
    function is constant on it, and otherwise 1 + min over free variables i of the max over the two halves."""
    cube = table.astype(np.int8).reshape([2] * n)  # (2,)*n, axis k is variable n - 1 - k
    low, high = cube, cube.copy()
    for axis in range(n):
        l0, l1 = np.take(low, 0, axis=axis), np.take(low, 1, axis=axis)  # (3,)*axis + (2,)*(n-axis-1)
        h0, h1 = np.take(high, 0, axis=axis), np.take(high, 1, axis=axis)
        low = np.stack([l0, l1, np.minimum(l0, l1)], axis=axis)  # (3,)*(axis+1) + (2,)*(n-axis-1)
        high = np.stack([h0, h1, np.maximum(h0, h1)], axis=axis)
    constant = low == high  # (3,)*n
    depth = np.where(constant, 0, n + 1).astype(np.int8)  # (3,)*n
    for _ in range(n):  # after round r every subcube with at most r free variables is final
        new = depth.copy()  # (3,)*n
        for axis in range(n):
            free = [slice(None)] * n
            free[axis] = 2
            candidate = 1 + np.maximum(np.take(depth, 0, axis=axis), np.take(depth, 1, axis=axis))  # (3,)*(n-1)
            new[tuple(free)] = np.minimum(new[tuple(free)], candidate)
        new[constant] = 0
        depth = new
    return int(depth[(2,) * n])


def signed_sum(table: np.ndarray, n: int) -> int:
    """sum over x of (-1)^{|x|} f(x) for a truth table on n variables, directly."""
    index = np.arange(1 << n, dtype=np.int64)  # (2^n,)
    parity = np.zeros(1 << n, dtype=np.int64)  # (2^n,)
    for i in range(n):
        parity ^= (index >> i) & 1
    return int(((1 - 2 * parity) * table.astype(np.int64)).sum())


def inner_slices(m: int) -> list[np.ndarray]:
    """The m inner variables on packed words: bit b of word w is the assignment 64 w + b (m >= 6)."""
    words = 1 << (m - 6)
    index = np.arange(words, dtype=np.uint64)  # (2^(m-6),)
    slices = [np.full(words, p, dtype=np.uint64) for p in LOW_PATTERNS]  # 6 x (2^(m-6),)
    for j in range(m - 6):
        slices.append(np.where((index >> np.uint64(j)) & np.uint64(1), ALL, np.uint64(0)))  # (2^(m-6),)
    return slices  # m x (2^(m-6),)


def restricted_sums(table: np.ndarray, n: int) -> np.ndarray:
    """R[i, b] = sum over x with x_i = b of (-1)^{|x| - b} f(x), directly: the top real coefficient, up to sign, of
    f with variable i fixed to b, as a function of the other n - 1 variables."""
    index = np.arange(1 << n, dtype=np.int64)  # (2^n,)
    parity = np.zeros(1 << n, dtype=np.int64)  # (2^n,)
    for i in range(n):
        parity ^= (index >> i) & 1
    signed = (1 - 2 * parity) * table.astype(np.int64)  # (2^n,)
    sums = np.zeros((n, 2), dtype=np.int64)  # (n, 2)
    for i in range(n):
        bit = (index >> i) & 1  # (2^n,)
        sums[i, 0] = signed[bit == 0].sum()
        sums[i, 1] = -signed[bit == 1].sum()
    return sums


def subcube_sums(t: int, fixed: dict[int, int], inner: int = 24, progress: bool = False) -> tuple[int, np.ndarray]:
    """For g = c_t with x_{-t} = 0, a function of the 2t cells x_{-t+1} .. x_t (variable k is x_{-t+1+k}), restricted
    to the subcube where variable k equals fixed[k]: its signed sum nu = sum over the free y of (-1)^{|y|} g(y), the top
    real coefficient up to sign, and R[k, b], the same sum with free variable k also fixed to b (0 for fixed k). The
    2t cells split into `inner` bit-sliced ones (the rightmost) and the others, fixed in an outer loop."""
    n = 2 * t  # variables of g
    if n < 6:  # too few cells for one word: use the whole table
        g = cone_table(t)[0::2].astype(np.int64)  # (2^(2t),), the rows with x_{-t} = 0
        index = np.arange(1 << n)  # (2^n,)
        free = [k for k in range(n) if k not in fixed]
        sub = np.ones(1 << n, dtype=bool)  # (2^n,)
        for k, b in fixed.items():
            sub &= ((index >> k) & 1) == b
        packed = sum(((index >> k) & 1) << pos for pos, k in enumerate(free))  # (2^n,), the free bits packed
        sums = np.zeros((n, 2), dtype=np.int64)  # (2t, 2)
        table = g[sub][np.argsort(packed[sub])]  # (2^|free|,)
        for pos, k in enumerate(free):
            sums[k] = restricted_sums(table, len(free))[pos]
        return signed_sum(table, len(free)), sums
    m = min(inner, n)
    words = inner_slices(m)  # m x (2^(m-6),)
    word_index = np.arange(len(words[0]))  # (2^(m-6),)
    word_odd = np.zeros(len(words[0]), dtype=bool)  # (2^(m-6),), parity of the word index
    for j in range(m - 6):
        word_odd ^= ((word_index >> j) & 1).astype(bool)
    outer = n - m
    mask = np.full(len(words[0]), ALL, dtype=np.uint64)  # (2^(m-6),), the inner assignments in the subcube
    for k, b in fixed.items():
        if k >= outer:
            mask &= words[k - outer] if b else ~words[k - outer]
    flip = -1 if sum(fixed.values()) % 2 else 1  # count the free weight only

    def signed(bits: np.ndarray) -> int:
        """sum over the inner assignments marked in `bits` of (-1)^{inner weight}."""
        odd_words = np.bitwise_count(bits & ODD_BITS).astype(np.int64)  # (2^(m-6),)
        even_words = np.bitwise_count(bits & ~ODD_BITS).astype(np.int64)  # (2^(m-6),)
        return int(np.where(word_odd, odd_words - even_words, even_words - odd_words).sum())

    total = 0
    sums = np.zeros((n, 2), dtype=np.int64)  # (2t, 2)
    for a in tqdm(range(1 << outer), desc=f"t={t}", file=sys.stderr, disable=not progress, mininterval=5):
        if any(k < outer and (a >> k) & 1 != b for k, b in fixed.items()):
            continue
        cells = [ALL if (a >> i) & 1 else np.uint64(0) for i in range(outer)]  # cells x_{-t+1} .. x_{-t+outer}
        row = [np.uint64(0)] + cells + words  # x_{-t} = 0, then the 2t cells; scalars or (2^(m-6),)
        for _ in range(t):
            row = [row[i - 1] ^ (row[i] | row[i + 1]) for i in range(1, len(row) - 1)]  # (len - 2) entries
        g = np.broadcast_to(row[0], words[0].shape) & mask  # (2^(m-6),)
        sign = flip * (-1 if bin(a).count("1") % 2 else 1)
        chunk = sign * signed(g)
        total += chunk
        for k in range(outer):
            if k not in fixed:
                b = (a >> k) & 1
                sums[k, b] += -chunk if b else chunk
        for j in range(m):
            if outer + j not in fixed:
                sums[outer + j, 0] += sign * signed(g & ~words[j])
                sums[outer + j, 1] -= sign * signed(g & words[j])
    return total, sums


def evasive(t: int, fixed: dict[int, int], level: int, inner: int = 24, progress: bool = False) -> bool:
    """A certificate that g restricted to `fixed` needs all its free variables: its top real coefficient is not 0
    (level 0), or for every free variable k some fixing of k leaves a function with a certificate of level - 1. A
    tree for a function with a certificate reads every free variable on some row, by induction: the first query fixes
    some k, the answer b of the certificate leaves a function that needs the rest. False means no certificate up to
    this level, not that a shorter tree exists."""
    nu, sums = subcube_sums(t, fixed, inner, progress)
    if nu != 0:
        return True
    if level == 0:
        return False
    for k in range(2 * t):
        if k in fixed or sums[k, 0] != 0 or sums[k, 1] != 0:  # a nonzero sum is a certificate of level 0
            continue
        if not any(evasive(t, {**fixed, k: b}, level - 1, inner, progress) for b in (0, 1)):
            return False
    return True


def certificate(t: int, max_level: int = 3, inner: int = 24, progress: bool = False) -> tuple[int, int, list[int]]:
    """The certificate that every decision tree for c_t has depth 2t + 1: returns (mu(c_t), level, hard cells).
    Level 0: mu(c_t) = 2 nu(g) != 0. Level L >= 1: `evasive` at level L for g (variable k is x_{-t+1+k}), so g needs
    all 2t queries and c_t = x_{-t} xor g all 2t + 1; the hard cells are the k with both fixings of top coefficient 0.
    Level -1: no certificate up to `max_level`."""
    nu, sums = subcube_sums(t, {}, inner, progress)
    if nu != 0:
        return 2 * nu, 0, []
    hard = [k for k in range(2 * t) if sums[k, 0] == 0 and sums[k, 1] == 0]
    for level in range(1, max_level + 1):
        if all(any(evasive(t, {k: b}, level - 1, inner, progress) for b in (0, 1)) for k in hard):
            return 0, level, hard
    return 0, -1, hard


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--exact", type=int, default=5, help="exact decision-tree depths for t <= this")
    parser.add_argument("--max-t", type=int, default=12, help="mu(c_t) for t <= this")
    parser.add_argument("--inner", type=int, default=24, help="bit-sliced variables per chunk")
    args = parser.parse_args()

    print("t  depth(Rule 30)  2t+1  depth(Rule 90)  2^popcount(t)")
    for t in range(1, args.exact + 1):
        n = 2 * t + 1
        print(t, exact_depth(cone_table(t), n), n, exact_depth(rule90_table(t), n), 2 ** bin(t).count("1"), flush=True)
    print("t  mu(c_t)  certificate level  cells without a certificate")
    for t in tqdm(range(1, args.max_t + 1), desc="certificates", file=sys.stderr):
        print(t, *certificate(t, args.inner, progress=t >= 15), flush=True)


if __name__ == "__main__":
    main()
