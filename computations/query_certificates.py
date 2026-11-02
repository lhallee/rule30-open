"""Sensitivity, certificates and fixed answers for the center cell as a function of its cone.

c_t is a Boolean function of the 2t + 1 cells x_{-t} .. x_t of an arbitrary row (new x_j = x_{j-1} xor (x_j or
x_{j+1})); bit i of a row index is x_{-t+i}. Every decision tree that computes c_t reads at least 2t cells on some row
(QueryDepth.md), and all 2t + 1 for t <= 17. This module measures the standard lower-bound methods that could give
2t + 1 for every t, and where they stop.

* `sensitivity_profile`: the most cells whose flip flips c_t at one row (the sensitivity s(c_t)), the rows sensitive
  to all three rightmost cells (none for t >= 2: Lean `right_corner`), and the rows sensitive to every cell but the
  two rightmost.
* `certificate_complexity`: C(c_t), the most cells a row needs fixed before c_t is constant, by a pass over the 3^n
  subcubes (each cell fixed to 0, fixed to 1, or free). D(f) >= C(f) >= s(f), and C(c_t) <= 2t for t >= 2 by
  `right_corner_certificate`.
* `fixed_answer_cells`: the cells at which an adversary can give one answer fixed in advance and still force a tree
  to read the whole cone, by a game over the subcubes. An adversary with fixed answers on a set Z needs a row
  sensitive to every cell of Z: a tree reads the other cells first and leaves any cell of Z for last.
* `lift_failures`: whether one step of Rule 30 preserves evasiveness (a function on m cells that needs all m queries)
  for every function: it does not.

    python -m computations.query_certificates --max-s 12 --max-c 7 --max-fixed 5
"""

from __future__ import annotations

import argparse
import sys

import numpy as np

from tqdm.auto import tqdm

from computations.cone_screening import cone_table


def free_counts(n: int) -> np.ndarray:
    """The number of free cells of each subcube of n cells, indexed (3,)*n with digit 2 meaning free."""
    count = np.zeros([3] * n, dtype=np.int8)  # (3,)*n
    for axis in range(n):
        shape = [1] * n
        shape[axis] = 3
        count += (np.arange(3) == 2).reshape(shape).astype(np.int8)
    return count  # (3,)*n


def subcube_constant(table: np.ndarray, n: int) -> np.ndarray:
    """True for the subcubes on which the function with this truth table (bit i of the index is variable i) is
    constant. Axis k of the result is variable n - 1 - k, with digit 2 meaning free."""
    cube = table.astype(np.int8).reshape([2] * n)  # (2,)*n
    low, high = cube, cube.copy()
    for axis in range(n):
        l0, l1 = np.take(low, 0, axis=axis), np.take(low, 1, axis=axis)  # (3,)*axis + (2,)*(n-axis-1)
        h0, h1 = np.take(high, 0, axis=axis), np.take(high, 1, axis=axis)
        low = np.stack([l0, l1, np.minimum(l0, l1)], axis=axis)  # (3,)*(axis+1) + (2,)*(n-axis-1)
        high = np.stack([h0, h1, np.maximum(h0, h1)], axis=axis)
    return low == high  # (3,)*n


def sensitivity_counts(table: np.ndarray, n: int) -> np.ndarray:
    """For every row, the bit mask of the cells whose flip changes the function."""
    index = np.arange(1 << n, dtype=np.int64)  # (2^n,)
    mask = np.zeros(1 << n, dtype=np.int64)  # (2^n,)
    for i in range(n):
        mask |= (table != table[index ^ (1 << i)]).astype(np.int64) << i
    return mask  # (2^n,)


def sensitivity_profile(t: int) -> tuple[int, int, int]:
    """(s(c_t), rows sensitive to the three rightmost cells x_{t-2}, x_{t-1}, x_t, rows sensitive to every cell but
    x_{t-1} and x_t)."""
    n = 2 * t + 1
    mask = sensitivity_counts(cone_table(t), n)  # (2^n,)
    weight = np.bitwise_count(mask.astype(np.uint64)).astype(np.int64)  # (2^n,)
    corner = (7 << (n - 3)) if n >= 3 else 0
    all_but_two = (1 << (n - 2)) - 1
    return (int(weight.max()), int(((mask & corner) == corner).sum()) if n >= 3 else 0,
            int(((mask & all_but_two) == all_but_two).sum()))


def certificate_complexity(table: np.ndarray, n: int) -> int:
    """max over rows x of the least number of cells whose values at x make the function constant."""
    size = np.where(subcube_constant(table, n), n - free_counts(n), n + 1).astype(np.int8)  # (3,)*n
    for axis in range(n):  # a row's value is the least size over the constant subcubes that contain it
        free = np.take(size, 2, axis=axis)  # (3,)*(n-1)
        parts = [np.minimum(np.take(size, b, axis=axis), free) for b in (0, 1)]  # 2 x (3,)*(n-1)
        size = np.stack(parts + [free], axis=axis)  # (3,)*n
    rows = size[(slice(0, 2),) * n]  # (2,)*n
    return int(rows.max())


def adversary_wins(table: np.ndarray, n: int, fixed: dict[int, int]) -> bool:
    """Whether an adversary that answers variable i with fixed[i] (and any other variable as it likes) forces every
    tree to read all n variables: the game over subcubes, where a subcube with one free variable is won when the
    function is not constant on it."""
    constant = subcube_constant(table, n)  # (3,)*n
    free = free_counts(n)  # (3,)*n
    alive = (free == 0) | ~constant  # (3,)*n
    win = alive.copy()  # (3,)*n
    for _ in range(n):  # after round r every subcube with at most r free variables is final
        new = win.copy()  # (3,)*n
        for variable in range(n):
            axis = n - 1 - variable
            w0, w1 = np.take(win, 0, axis=axis), np.take(win, 1, axis=axis)  # (3,)*(n-1)
            answer = (w1 if fixed[variable] else w0) if variable in fixed else (w0 | w1)  # (3,)*(n-1)
            index = [slice(None)] * n
            index[axis] = 2
            new[tuple(index)] &= answer
        new &= alive
        if (new == win).all():
            break
        win = new
    return bool(win[(2,) * n])


def fixed_answer_cells(t: int) -> dict[int, list[int]]:
    """For each cell j of the cone, the answers b for which the adversary that always answers x_j = b (and anything
    elsewhere) still forces every tree for c_t to read all 2t + 1 cells."""
    n = 2 * t + 1
    table = cone_table(t)  # (2^n,)
    return {j: [b for b in (0, 1) if adversary_wins(table, n, {j + t: b})] for j in range(-t, t + 1)}


def evasive(table: np.ndarray, n: int) -> bool:
    """Whether every decision tree for this truth table reads all n variables on some row."""
    return adversary_wins(table, n, {})


def one_step(table: np.ndarray, m: int) -> np.ndarray:
    """F o Phi for F on m cells y_0 .. y_{m-1}: the function of the m + 2 cells x_0 .. x_{m+1} with
    y_j = x_j xor (x_{j+1} or x_{j+2})."""
    index = np.arange(1 << (m + 2), dtype=np.int64)  # (2^(m+2),)
    cells = [(index >> i) & 1 for i in range(m + 2)]  # (m + 2) x (2^(m+2),)
    image = np.zeros(1 << (m + 2), dtype=np.int64)  # (2^(m+2),)
    for j in range(m):
        image |= (cells[j] ^ (cells[j + 1] | cells[j + 2])) << j
    return table[image]  # (2^(m+2),)


def lift_failures(m: int) -> tuple[int, int]:
    """Over every function F of m cells (m <= 3) that needs all m queries: (how many, how many with F o Phi not
    needing all m + 2)."""
    total = failures = 0
    for code in range(1 << (1 << m)):
        table = np.array([(code >> b) & 1 for b in range(1 << m)], dtype=np.uint8)  # (2^m,)
        if not evasive(table, m):
            continue
        total += 1
        failures += not evasive(one_step(table, m), m + 2)
    return total, failures


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--max-s", type=int, default=12, help="sensitivity profile for t <= this")
    parser.add_argument("--max-c", type=int, default=7, help="certificate complexity for t <= this")
    parser.add_argument("--max-fixed", type=int, default=5, help="fixed-answer cells for t <= this")
    args = parser.parse_args()

    print("t  2t+1  s(c_t)  rows sensitive at x_{t-2}, x_{t-1}, x_t  rows sensitive at x_{-t} .. x_{t-2}")
    for t in tqdm(range(1, args.max_s + 1), desc="sensitivity", file=sys.stderr):
        print(t, 2 * t + 1, *sensitivity_profile(t), flush=True)
    print("t  2t+1  C(c_t)")
    for t in tqdm(range(1, args.max_c + 1), desc="certificates", file=sys.stderr):
        print(t, 2 * t + 1, certificate_complexity(cone_table(t), 2 * t + 1), flush=True)
    print("t  cell: fixed answers that still force 2t + 1 queries")
    for t in tqdm(range(1, args.max_fixed + 1), desc="fixed answers", file=sys.stderr):
        print(t, fixed_answer_cells(t), flush=True)
    total, failures = lift_failures(3)
    print(f"functions of 3 cells needing 3 queries: {total}; after one step of Rule 30, {failures} need fewer than 5")


if __name__ == "__main__":
    main()
