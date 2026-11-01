"""Restricted models for the center cell: strips with white boundaries, forward certificates, and dyadic windows.

Three models in which an algorithm for the center cell c(n) can be charged, each checked here against Rule 90, whose
center column from one black cell is eventually white and so costs nothing to compute.

* **Strips.** Evolve only the columns -w .. w' of the single black cell, with every cell outside held white, and read
  the center. `first_strip_error` returns the first time the strip's center differs from the true one.
* **Forward certificates.** A set S of cells of the spacetime diagram, containing (n, 0), such that each cell of S is
  fixed by the rule from cells of S and free cells (row 0 and the cells outside the light cone of the seed, which are
  white): for Rule 30 its left parent, and either a black one of its two other parents or, when both are white, both of
  them. `min_certificate` finds the least size by integer programming, `lazy_evaluation_count` counts the cells that a
  memoized top-down evaluation touches, and `certificate_lower_bound` is the bound proved in the entry.
* **Dyadic windows.** By the kit's `Rule30Problem3Bounds.period_of_canon_window_time_le`, a one-tape machine that halts
  within k steps on every input of the window [2^(k-1), 2^(k-1) + 2^k) computes a function of period 2^k from 2^(k-1)
  on. `dyadic_witnesses` finds, for each k, the least m >= 2^(k-1) with c(m) != c(m + 2^k).

Run as `python -m computations.restricted_models`.
"""

from __future__ import annotations

import argparse
import time

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix

from computations.rule30 import center_column


def rule_table(rule: int) -> np.ndarray:
    """The elementary rule's new cell for each neighborhood 4 l + 2 c + r."""
    return np.array([(rule >> i) & 1 for i in range(8)], dtype=np.uint8)  # (8,)


def step_row(table: np.ndarray, row: np.ndarray) -> np.ndarray:
    """One step on a finite row with white cells held beyond both ends."""
    padded = np.concatenate(([0], row, [0])).astype(np.uint8)  # (W + 2,)
    index = 4 * padded[:-2] + 2 * padded[1:-1] + padded[2:]  # (W,)
    return table[index]  # (W,)


def strip_center(rule: int, left: int, right: int, steps: int) -> np.ndarray:
    """Center cells at times 0 .. steps of the single black cell evolved on the columns -left .. right only."""
    table = rule_table(rule)  # (8,)
    row = np.zeros(left + right + 1, dtype=np.uint8)  # (W,)
    row[left] = 1
    column = np.zeros(steps + 1, dtype=np.uint8)  # (steps + 1,)
    column[0] = 1
    for t in range(1, steps + 1):
        row = step_row(table, row)
        column[t] = row[left]
    return column  # (steps + 1,)


def true_center(rule: int, steps: int) -> np.ndarray:
    """Center cells at times 0 .. steps of the single black cell; the strip of half-width steps is exact."""
    return strip_center(rule, steps, steps, steps)  # (steps + 1,)


def first_strip_error(rule: int, left: int, right: int, steps: int, truth: np.ndarray | None = None) -> int:
    """The first time at most `steps` where the strip -left .. right gives the wrong center, or -1 if none."""
    if truth is None:
        truth = true_center(rule, steps)  # (steps + 1,)
    strip = strip_center(rule, left, right, steps)  # (steps + 1,)
    wrong = np.nonzero(strip != truth[: steps + 1])[0]  # (k,)
    return int(wrong[0]) if wrong.size else -1


def spacetime_cone(rule: int, n: int) -> np.ndarray:
    """Rows 0 .. n of the single black cell on the columns -n .. n; entry [s, j + n] is cell j at time s."""
    table = rule_table(rule)  # (8,)
    rows = np.zeros((n + 1, 2 * n + 1), dtype=np.uint8)  # (n + 1, 2n + 1)
    rows[0, n] = 1
    for s in range(1, n + 1):
        rows[s] = step_row(table, rows[s - 1])
    return rows  # (n + 1, 2n + 1)


def _is_variable(n: int, s: int, j: int) -> bool:
    """A cell that a certificate must derive: inside the light cone of the seed, after row 0, and within the
    backward cone of (n, 0) widened by one cell on the right, the reach of the right parent."""
    return 1 <= s <= n and abs(j) <= s and -(n - s) <= j <= n - s


def certificate_cells(n: int) -> list[tuple[int, int]]:
    """The cells (s, j) that can appear in a forward certificate of (n, 0)."""
    return [(s, j) for s in range(1, n + 1) for j in range(-s, s + 1) if _is_variable(n, s, j)]


def min_certificate_set(n: int, rule: int = 30) -> set[tuple[int, int]]:
    """A forward certificate of the center cell at time n of least size, by integer programming (rules 30, 90)."""
    if n == 0:
        return set()
    x = spacetime_cone(rule, n)  # (n + 1, 2n + 1)
    cells = certificate_cells(n)
    index = {cell: i for i, cell in enumerate(cells)}
    rows: list[dict[int, float]] = []
    lower: list[float] = []
    for (s, j), i in index.items():
        if s == 1:
            continue
        parents = [(s - 1, j - 1), (s - 1, j), (s - 1, j + 1)]
        if rule == 90:
            needed = [parents[0], parents[2]]
            for p in needed:
                if p in index:
                    rows.append({i: 1.0, index[p]: -1.0})
                    lower.append(-np.inf)
            continue
        left, centre, right = parents
        if left in index:
            rows.append({i: 1.0, index[left]: -1.0})  # y_v - y_left <= 0
            lower.append(-np.inf)
        value = lambda p: int(x[p[0], p[1] + n]) if abs(p[1]) <= n else 0
        if value(centre) == 0 and value(right) == 0:
            for p in (centre, right):
                if p in index:
                    rows.append({i: 1.0, index[p]: -1.0})
                    lower.append(-np.inf)
        else:
            black = [p for p in (centre, right) if value(p) == 1]
            if any(p not in index for p in black):
                continue  # a free black cell certifies the or; free cells in the cone are row 0 only
            constraint = {i: 1.0}
            for p in black:
                constraint[index[p]] = constraint.get(index[p], 0.0) - 1.0
            rows.append(constraint)
            lower.append(-np.inf)
    matrix = lil_matrix((len(rows) + 1, len(cells)))
    for r, constraint in enumerate(rows):
        for col, coefficient in constraint.items():
            matrix[r, col] = coefficient
    matrix[len(rows), index[(n, 0)]] = 1.0
    upper = [0.0] * len(rows) + [1.0]
    lower = lower + [1.0]
    result = milp(
        c=np.ones(len(cells)),
        constraints=LinearConstraint(matrix.tocsr(), lower, upper),
        integrality=np.ones(len(cells)),
        bounds=Bounds(0, 1),
    )
    if not result.success:
        raise RuntimeError(f"integer program failed at n = {n}: {result.message}")
    return {cell for cell, i in index.items() if result.x[i] > 0.5}


def min_certificate(n: int, rule: int = 30) -> int:
    """The least size of a forward certificate of the center cell at time n."""
    return len(min_certificate_set(n, rule))


def is_certificate(n: int, cells: set[tuple[int, int]], rule: int = 30) -> bool:
    """Check a set of cells as a forward certificate of (n, 0), by the definition (an independent check)."""
    x = spacetime_cone(rule, n)  # (n + 1, 2n + 1)

    def known(s: int, j: int) -> bool:
        return s == 0 or abs(j) > s or (s, j) in cells

    def value(s: int, j: int) -> int:
        return int(x[s, j + n]) if abs(j) <= n else 0

    if (n, 0) not in cells and n > 0:
        return False
    for s, j in cells:
        if s == 0 or abs(j) > s:
            continue
        if rule == 90:
            if not (known(s - 1, j - 1) and known(s - 1, j + 1)):
                return False
            continue
        if not known(s - 1, j - 1):
            return False
        if value(s - 1, j) == 0 and value(s - 1, j + 1) == 0:
            if not (known(s - 1, j) and known(s - 1, j + 1)):
                return False
        elif not any(known(s - 1, q) and value(s - 1, q) == 1 for q in (j, j + 1)):
            return False
    return True


def lazy_certificate(n: int, rule: int = 30) -> set[tuple[int, int]]:
    """The cells that a memoized top-down evaluation of (n, 0) derives; for Rule 30 it reads the center parent before
    the right parent and skips the right parent when the center parent is black."""
    x = spacetime_cone(rule, n)  # (n + 1, 2n + 1)
    seen: set[tuple[int, int]] = set()
    stack = [(n, 0)] if n > 0 else []
    while stack:
        s, j = stack.pop()
        if (s, j) in seen or s == 0 or abs(j) > s:
            continue
        seen.add((s, j))
        if rule == 90:
            stack.extend([(s - 1, j - 1), (s - 1, j + 1)])
            continue
        stack.append((s - 1, j - 1))
        stack.append((s - 1, j))
        if abs(j) > s - 1 or x[s - 1, j + n] == 0:
            stack.append((s - 1, j + 1))
    return seen


def lazy_evaluation_count(n: int, rule: int = 30) -> int:
    """The number of cells derived by the lazy evaluation of `lazy_certificate`."""
    return len(lazy_certificate(n, rule))


def certificate_lower_bound(n: int) -> int:
    """The bound of the entry: a forward certificate of (n, 0) for Rule 30 has at least
    sum over n/2 <= s <= n of (n - s + 1) cells, about n^2 / 8."""
    return sum(n - s + 1 for s in range(max(1, (n + 1) // 2), n + 1))


def rule90_certificate_size(n: int) -> int:
    """The forced closure for Rule 90: cells (s, j), 1 <= s <= n, |j| <= min(s, n - s), j = n - s mod 2."""
    return sum(1 for s in range(1, n + 1) for j in range(-s, s + 1) if abs(j) <= n - s and (j - (n - s)) % 2 == 0)


def dyadic_witnesses(max_k: int, column: np.ndarray | None = None) -> list[tuple[int, int]]:
    """For k = 1 .. max_k, the pair (k, m - 2^(k-1)) for the least m >= 2^(k-1) with c(m) != c(m + 2^k)."""
    need = 2 ** (max_k - 1) + 2 ** max_k + 64
    if column is None:
        column = center_column(need)  # (need,)
    out = []
    for k in range(1, max_k + 1):
        low, period = 2 ** (k - 1), 2**k
        m = low
        while m + period < len(column) and column[m] == column[m + period]:
            m += 1
        if m + period >= len(column):
            raise ValueError(f"column too short for k = {k}")
        out.append((k, m - low))
    return out


def ray_flip_depths(max_k: int, column: np.ndarray) -> list[tuple[int, int, int]]:
    """For k = 1 .. max_k, the triple (k, residues whose ray has both colors in the data, deepest first flip).

    The ray of a residue r modulo 2^k is {m >= 2^(k-1) : m = r mod 2^k}. The kit's
    `Rule30Problem3Bounds.computes_const_on_dyadic_ray` makes the function constant on the ray of any input n >= 2^(k-1)
    on which a one-tape machine halts within k steps; so if every ray has both colors, every machine takes at least
    k + 1 steps on every n >= 2^(k-1). The deepest first flip is the largest, over residues, of the index of the first
    ray element whose color differs from the ray's first element."""
    out = []
    for k in range(1, max_k + 1):
        low, period = 2 ** (k - 1), 2**k
        usable = (len(column) - low) // period * period
        block = column[low : low + usable].reshape(-1, period)  # (rays, 2^k): row i holds m = low + i 2^k + r'
        differs = block != block[0]  # (rays, 2^k)
        has_flip = differs.any(axis=0)  # (2^k,)
        first = np.where(has_flip, differs.argmax(axis=0), -1)  # (2^k,)
        out.append((k, int(has_flip.sum()), int(first.max())))
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--max-w", type=int, default=60, help="largest strip half-width")
    parser.add_argument("--right-max", type=int, default=60, help="largest right width with an exact left side")
    parser.add_argument("--max-cert", type=int, default=24, help="largest n for the exact certificate minimum")
    parser.add_argument("--max-lazy", type=int, default=200, help="largest n for the lazy evaluation counts")
    parser.add_argument("--max-k", type=int, default=16, help="largest k for the dyadic windows")
    args = parser.parse_args()

    print("1. Strips with white boundaries: first wrong time")
    horizon = 2 * args.max_w + 8
    for rule in (30, 90, 150):
        truth = true_center(rule, horizon)  # (horizon + 1,)
        exact = all(
            first_strip_error(rule, w, w + 1, horizon, truth) == 2 * w + 2
            and first_strip_error(rule, w, horizon, horizon, truth) == 2 * w + 2
            for w in range(args.max_w + 1)
        )
        symmetric = [first_strip_error(rule, w, w, horizon, truth) for w in range(args.max_w + 1)]
        other = {w: t for w, t in enumerate(symmetric) if t != 2 * w + 2}
        never = sum(1 for t in other.values() if t == -1)
        listed = {w: t for w, t in other.items() if t != -1}
        print(f"  rule {rule}: right width w + 1 or exact, first error at 2w + 2 for all w <= {args.max_w}: {exact};"
              f" symmetric strip w = w': correct up to time {horizon} for {never} widths, first error at another"
              f" time for {listed or 'none'}")

    print("2. Right width alone (left side exact): first wrong time T(w') for Rule 30 and Rule 90")
    steps = 12 * args.right_max + 20
    truth30 = true_center(30, steps)  # (steps + 1,)
    truth90 = true_center(90, steps)  # (steps + 1,)
    started = time.time()
    ratios = []
    for wr in range(0, args.right_max + 1, max(1, args.right_max // 12)):
        t30 = first_strip_error(30, steps, wr, steps, truth30)
        t90 = first_strip_error(90, steps, wr, steps, truth90)
        if wr > 0 and t30 > 0:
            ratios.append(t30 / wr)
        print(f"  w' = {wr:4d}: rule 30 first error {t30:5d}, rule 90 {t90:5d}  ({time.time() - started:5.1f} s)",
              flush=True)
    if ratios:
        print(f"  rule 30 T(w') / w' over w' >= {max(1, args.right_max // 12)}: min {min(ratios):.2f}, max {max(ratios):.2f}")

    print("3. Forward certificates: lower bound, exact minimum, lazy evaluation, Rule 90 closure")
    print("     n  bound  minimum  lazy  rule90  min/n^2")
    for n in range(2, args.max_cert + 1, 2):
        exact_min = min_certificate(n)
        print(f"  {n:4d} {certificate_lower_bound(n):6d} {exact_min:8d} {lazy_evaluation_count(n):5d}"
              f" {rule90_certificate_size(n):7d}  {exact_min / n**2:.3f}", flush=True)
    started = time.time()
    for n in sorted({50, 100, args.max_lazy}):
        lazy = lazy_evaluation_count(n)
        print(f"  n = {n}: lazy {lazy} = {lazy / n**2:.3f} n^2, bound {certificate_lower_bound(n) / n**2:.3f} n^2,"
              f" rule 90 {rule90_certificate_size(n) / n**2:.3f} n^2 ({time.time() - started:.1f} s)", flush=True)

    print(f"4. Dyadic windows: least offset m - 2^(k-1) with c(m) != c(m + 2^k), k = 1 .. {args.max_k}")
    started = time.time()
    column = center_column(2 ** (args.max_k - 1) + 2**args.max_k + 64)  # (N,)
    witnesses = dyadic_witnesses(args.max_k, column)
    print(f"  ({time.time() - started:.1f} s) " + ", ".join(f"k={k}: {d}" for k, d in witnesses))
    print(f"  every offset inside the window of 2^k inputs: {all(d < 2**k for k, d in witnesses)};"
          f" largest offset {max(d for _, d in witnesses)}")

    print("5. Dyadic rays: residues modulo 2^k whose ray from 2^(k-1) has both colors in the same data")
    for k, flipping, deepest in ray_flip_depths(args.max_k, column):
        print(f"  k = {k:2d}: {flipping} of {2**k} residues flip, deepest first flip at ray element {deepest}")


if __name__ == "__main__":
    main()
