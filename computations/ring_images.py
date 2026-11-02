"""How many rows of a ring of W cells Rule 30 reaches in one step, and how much information one step loses there.

A row of a ring of W cells is an integer whose bit i is cell i, with cell W - 1 beside cell 0. One step of an
elementary rule maps the 2^W rows to `image_size` rows, and the loss of the step is W - log2(image size) bits.

`image_size` counts the image by enumerating all 2^W rows. `missed_rows` gives the number of rows that Rule 30 does not
reach without enumeration, from two transfer matrices:

* `pair_matrix`: the 12 states ((a, b), (a', b')) with (a, b) != (a', b'), two adjacent cells of two rows, and an
  edge to ((b, c), (b', c')) when Rule 30 gives the two rows the same cell over b and b' and (b, c) != (b', c').
  Rule 30 is left permutive, x'_i = x_(i-1) xor (x_i or x_(i+1)), so two rows with the same image that agree on two
  adjacent cells agree on the cell to their left, and around the ring on every cell. So the ordered pairs of distinct
  rows with the same image are exactly the closed walks of length W, and there are trace(N2^W) of them.
* `triple_matrix`: the same for ordered triples of pairwise distinct rows, trace(N3^W).

No row has more than three preimages (the kit's `Rule30Equivalents.Preimages.card_le_three`, for configurations of
Z, of which the rows of a ring are the periodic ones). With n_k the number of rows with exactly k preimages,
trace(N2^W) = 2 n_2 + 6 n_3 and trace(N3^W) = 6 n_3, so the rows reached by no row number
n_2 + 2 n_3 = trace(N2^W) / 2 - trace(N3^W) / 6. `characteristic_polynomial` gives both matrices' characteristic
polynomials exactly (Faddeev-LeVerrier in integers), which fix the traces for every W.

    python -m computations.ring_images --max-width 24   # the table of the finding (about 15 s at width 24)
"""

from __future__ import annotations

import argparse
import itertools
import math
import sys

import numpy as np
from tqdm.auto import tqdm


def ring_step(rows: np.ndarray, width: int, rule: int) -> np.ndarray:
    """One step of the elementary rule `rule` (Wolfram's number) on rows of a ring of `width` cells."""
    # rows: (n,) int64, bit i is cell i
    mask = (1 << width) - 1
    left = ((rows << 1) | (rows >> (width - 1))) & mask  # (n,), bit i is cell i - 1
    right = ((rows >> 1) | (rows << (width - 1))) & mask  # (n,), bit i is cell i + 1
    out = np.zeros_like(rows)  # (n,)
    for pattern in range(8):
        if (rule >> pattern) & 1:
            l_bit, c_bit, r_bit = (pattern >> 2) & 1, (pattern >> 1) & 1, pattern & 1
            out |= (left if l_bit else ~left) & (rows if c_bit else ~rows) & (right if r_bit else ~right)
    return out & mask  # (n,)


def preimage_counts(width: int, rule: int) -> np.ndarray:
    """The number of preimages of every row of a ring of `width` cells, by enumeration of all rows."""
    rows = np.arange(1 << width, dtype=np.int64)  # (2^W,)
    return np.bincount(ring_step(rows, width, rule), minlength=1 << width)  # (2^W,)


def image_size(width: int, rule: int) -> int:
    """The number of rows of a ring of `width` cells that one step of `rule` reaches."""
    return int(np.count_nonzero(preimage_counts(width, rule)))


def rule_cell(left: int, center: int, right: int, rule: int = 30) -> int:
    """The new cell of an elementary rule over the three cells `left`, `center`, `right`."""
    return (rule >> (4 * left + 2 * center + right)) & 1


def tuple_matrix(k: int, rule: int = 30) -> np.ndarray:
    """The transfer matrix of ordered k-tuples of pairwise distinct rows with the same image: a state is the pair of
    adjacent cells (a, b) of each row, held as 2a + b, with the k pairs pairwise distinct."""
    states = [s for s in itertools.product(range(4), repeat=k) if len(set(s)) == k]
    index = {s: i for i, s in enumerate(states)}
    matrix = np.zeros((len(states), len(states)), dtype=np.int64)  # (states, states)
    for s in states:
        for nxt in itertools.product(range(2), repeat=k):
            images = {rule_cell(p >> 1, p & 1, c, rule) for p, c in zip(s, nxt)}
            target = tuple(((p & 1) << 1) | c for p, c in zip(s, nxt))
            if len(images) == 1 and target in index:
                matrix[index[s], index[target]] += 1
    return matrix  # (states, states)


def pair_matrix(rule: int = 30) -> np.ndarray:
    """`tuple_matrix` for ordered pairs: 12 states."""
    return tuple_matrix(2, rule)  # (12, 12)


def triple_matrix(rule: int = 30) -> np.ndarray:
    """`tuple_matrix` for ordered triples: 24 states."""
    return tuple_matrix(3, rule)  # (24, 24)


def walk_traces(matrix: np.ndarray, max_width: int) -> list[int]:
    """trace(matrix^W) for W = 1 .. max_width, in exact integer arithmetic."""
    # matrix: (s, s)
    exact = [[int(v) for v in row] for row in matrix]
    size = len(exact)
    power = [row[:] for row in exact]
    traces = []
    for _ in range(max_width):
        traces.append(sum(power[i][i] for i in range(size)))
        power = [[sum(power[i][m] * exact[m][j] for m in range(size)) for j in range(size)] for i in range(size)]
    return traces


def characteristic_polynomial(matrix: np.ndarray) -> list[int]:
    """The coefficients of det(x I - matrix), leading coefficient first, by Faddeev-LeVerrier. For an integer matrix
    every step stays integral and each division by k is exact, which the function checks."""
    # matrix: (s, s)
    size = matrix.shape[0]
    a = matrix.astype(object)  # (s, s), Python integers
    identity = np.identity(size, dtype=np.int64).astype(object)  # (s, s)
    product = np.zeros((size, size), dtype=object)  # (s, s), A M_(k-1), with M_0 = 0
    coefficients = [1]
    for k in range(1, size + 1):
        m = product + coefficients[-1] * identity  # (s, s), M_k
        product = a.dot(m)  # (s, s)
        trace = int(np.trace(product))
        assert trace % k == 0
        coefficients.append(-trace // k)
    return coefficients


def power_sums(max_width: int) -> list[int]:
    """p_W, the sum of the W-th powers of the roots of x^3 - x^2 - 2, for W = 1 .. max_width: p_1 = 1, p_2 = 1,
    p_3 = 7 and p_W = p_(W-1) + 2 p_(W-3)."""
    sums = [1, 1, 7]
    while len(sums) < max_width:
        sums.append(sums[-1] + 2 * sums[-3])
    return sums[:max_width]


def missed_rows(width: int) -> int:
    """The rows of a ring of `width` >= 3 cells that Rule 30 reaches from no row: (p_W + 1) / 2 - [3 divides W]."""
    p = power_sums(width)[width - 1]
    return (p + 1) // 2 - (1 if width % 3 == 0 else 0)


def loss_bits(width: int, image: int) -> float:
    """W - log2(image), the information one step loses on a ring of `width` cells."""
    return width - math.log2(image)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--max-width", type=int, default=24)
    parser.add_argument("--formula-width", type=int, default=64)
    args = parser.parse_args()

    n2, n3 = pair_matrix(), triple_matrix()
    print("characteristic polynomial of N2:", characteristic_polynomial(n2))
    print("characteristic polynomial of N3:", characteristic_polynomial(n3))
    t2, t3 = walk_traces(n2, args.max_width), walk_traces(n3, args.max_width)
    print("W  rule30-image  missed  formula  max-preimages  loss-30  rule90-image  loss-90  rule150-image  loss-150")
    for width in tqdm(range(3, args.max_width + 1), desc="widths", file=sys.stderr):
        counts = preimage_counts(width, 30)  # (2^W,)
        image = int(np.count_nonzero(counts))
        missed = (1 << width) - image
        by_traces = t2[width - 1] // 2 - t3[width - 1] // 6
        assert missed == missed_rows(width) == by_traces
        i90, i150 = image_size(width, 90), image_size(width, 150)
        print(
            f"{width:2d}  {image:11d}  {missed:6d}  {missed_rows(width):7d}  {int(counts.max()):13d}  "
            f"{loss_bits(width, image):7.4f}  {i90:12d}  {loss_bits(width, i90):7.4f}  {i150:13d}  "
            f"{loss_bits(width, i150):8.4f}"
        )
    for width in (32, 48, args.formula_width):
        image = (1 << width) - missed_rows(width)
        print(f"formula W = {width}: loss {loss_bits(width, image):.3e} bits, missed share {missed_rows(width) / 2**width:.3e}")
    losses = {width: loss_bits(width, (1 << width) - missed_rows(width)) for width in range(3, 401)}
    print(f"formula: largest loss for 13 <= W <= 400 is {max(losses[w] for w in range(13, 401)):.4f} bits")
    summed = {n: n * losses[n + 1] for n in range(2, 80)}  # N steps on the ring of N + 1 cells
    print(
        f"formula: N * loss(N + 1) is at most {max(summed.values()):.4f} bits for 2 <= N <= 79, at most "
        f"{max(summed[n] for n in range(13, 80)):.4f} for 13 <= N <= 79, and {summed[40]:.4f} at N = 40"
    )


if __name__ == "__main__":
    main()
