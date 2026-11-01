"""The presheaf of Rule 30 patches beside a repeating column, its limit over windows, and its linearization.

A column k repeats a block from some time on. A section over a finite patch of space-time right of the column is an
assignment of 0s and 1s that obeys the rule at every cell whose three parents lie in the patch, with the column read
from the block. Over the slab of `width` cells and the times t - m .. t, a section is a play of the finite game
(`computations.game`) of length m, and its restriction to time t is a window. The windows that extend over every
past, the limit of the presheaf over the slabs, are the sets `limit_windows.limit_sets` computes (`exact_limit`).

Cech cohomology needs coefficients in an abelian group, so the presheaf of sets is linearized: a section over a slab
becomes a formal sum of plays with coefficients in GF(2), and a window y extends over m steps when the vector e_y is
the end of a compatible family of such sums (the cohomological obstruction of Abramsky, Mansfield and Barbosa vanishes).
One step beside a column value is a relation between windows; its linearization is the subspace
{(tail(a), head(a)) : a in GF(2)^moves}, and the windows that extend linearly over every past form the limit
`linear_limit`. Its annihilator is spanned by the indicators of disjoint sets of windows (`linear_step` keeps them as
labels), found by union-find over the connected components of each step's graph of moves: linearization replaces each
step by its connected components, and the direction of the moves is lost. So the linear limit holds the exact limit,
and every test read from it is weaker than the exact one (`linear_good`, `functional_good`), which `game` refines.

`dense_linear_limit` computes the same limit by Gaussian elimination over GF(2), for the tests.

    python -m computations.sheaf_sections --survey 12 --widths 4,6,8,10   # blocks each test excludes, by period
    python -m computations.sheaf_sections --sizes 0001,00000011 --widths 6,8,10   # windows kept by each limit
    python -m computations.sheaf_sections --lemma 12 --widths 3,4,5,6,7,8,9,10    # the lemma one cell short
"""

from __future__ import annotations

import argparse
import sys

import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components
from tqdm.auto import tqdm

from computations import game
from computations import limit_windows as lw


def step_components(moves: np.ndarray, col: int) -> tuple[np.ndarray, np.ndarray, int]:
    """The connected components of the graph of one step beside `col`, with the windows before the step on one side
    and the windows after it on the other. Returns the component of each window before (shape (n,)), of each window
    after (shape (n,), -1 for a window that no move reaches) and the number of components."""
    n = moves.shape[1]
    source = np.concatenate([np.arange(n), np.arange(n)])  # (2n,)
    target = np.concatenate([moves[col, :, 0], moves[col, :, 1]]) + n  # (2n,), windows after at n .. 2n - 1
    graph = csr_matrix((np.ones(2 * n, dtype=np.int8), (source, target)), shape=(2 * n, 2 * n))
    count, label = connected_components(graph, directed=False)  # label: (2n,)
    reached = np.zeros(n, dtype=bool)  # (n,)
    reached[target - n] = True
    after = np.where(reached, label[n:], -1)  # (n,)
    return label[:n], after, int(count)


def canonical(labels: np.ndarray) -> np.ndarray:
    """The labels (shape (n,), -1 for no set) renumbered by first occurrence, so equal families compare equal."""
    out = np.full(labels.shape, -1, dtype=np.int64)  # (n,)
    keep = labels >= 0
    _, first, inverse = np.unique(labels[keep], return_index=True, return_inverse=True)
    rank = np.argsort(np.argsort(first))  # (sets,) order of first occurrence
    out[keep] = rank[inverse]
    return out


def linear_step(labels: np.ndarray, moves: np.ndarray, col: int) -> np.ndarray:
    """One step of the annihilator of the linear limit. `labels` (shape (n,)) gives each window the disjoint set Q of
    the annihilator's basis it lies in (-1 for none); the annihilator is spanned by the indicators of these sets. A
    functional after the step lies in the new annihilator when it equals, on every move, a functional of the old
    annihilator at the move's start: it is constant on each component of the step, zero on the components that meet a
    window in no set, constant across the components that meet one set, and free on a window that no move reaches."""
    n = moves.shape[1]
    before, after, count = step_components(moves, col)
    sets = int(labels.max()) + 1
    zero = count + sets  # one node for 'must vanish'
    other = np.where(labels >= 0, count + labels, zero)  # (n,) the set of each window, or the zero node
    graph = csr_matrix((np.ones(n, dtype=np.int8), (before, other)), shape=(zero + 1, zero + 1))
    _, cls = connected_components(graph, directed=False)  # (zero + 1,)
    dead = cls[zero]
    new = np.full(n, -1, dtype=np.int64)  # (n,)
    reached = after >= 0
    alive = reached.copy()
    alive[reached] = cls[after[reached]] != dead
    new[alive] = cls[after[alive]]
    unreached = np.flatnonzero(~reached)  # (g,) windows with no move into them: each a set of its own
    new[unreached] = cls.max() + 1 + np.arange(unreached.size)
    return canonical(new)


def linear_limit(block: str, moves: np.ndarray) -> list[np.ndarray]:
    """The annihilator of the linear limit at each phase, as labels (shape (n,) each) of disjoint sets of windows: for
    each phase i, before the column reads block[i]. The annihilator grows period by period until the labels at phase
    0 repeat."""
    n = moves.shape[1]
    labels = np.full(n, -1, dtype=np.int64)  # (n,) the annihilator of all windows is zero
    while True:
        after = labels
        for ch in block:
            after = linear_step(after, moves, int(ch))
        if np.array_equal(after, labels):
            break
        labels = after
    out = []
    for ch in block:
        out.append(labels)
        labels = linear_step(labels, moves, int(ch))
    return out


def exact_limit(block: str, moves: np.ndarray) -> list[np.ndarray]:
    """The windows that extend over every past at each phase, as boolean masks (shape (n,) each)."""
    out = []
    for members in lw.limit_sets(block, moves):
        mask = np.zeros(moves.shape[1], dtype=bool)  # (n,)
        mask[members] = True
        out.append(mask)
    return out


def linear_good(block: str, moves: np.ndarray) -> bool:
    """Whether, at every 0 of the block, cell k + 1 is constant on the windows whose obstruction vanishes, those in no
    set of the annihilator. The strongest pointwise test the linearization gives."""
    first = np.arange(moves.shape[1]) & 1  # (n,)
    for ch, labels in zip(block, linear_limit(block, moves)):
        if ch == "0":
            values = first[labels < 0]
            if values.size and values.min() != values.max():
                return False
    return True


def functional_good(block: str, moves: np.ndarray) -> bool:
    """Whether, at every 0 of the block, cell k + 1 plus a constant lies in the annihilator of the linear limit: it is
    constant on every set and equal to the constant off the sets. Every linear section then reads one value."""
    first = np.arange(moves.shape[1]) & 1  # (n,)
    for ch, labels in zip(block, linear_limit(block, moves)):
        if ch != "0":
            continue
        outside = first[labels < 0]
        if outside.size and outside.min() != outside.max():
            return False
        inside = labels >= 0
        if inside.any():
            sets = int(labels.max()) + 1
            ones = np.bincount(labels[inside], weights=first[inside], minlength=sets)  # (sets,)
            sizes = np.bincount(labels[inside], minlength=sets)  # (sets,)
            if ((ones > 0) & (ones < sizes)).any():
                return False
    return True


def exact_good(block: str, moves: np.ndarray) -> bool:
    """`limit_windows.is_good`: cell k + 1 constant on the exact limit at every 0."""
    return lw.is_good(block, moves)


def game_good(block: str, width: int) -> bool:
    """Whether the finite game excludes the block at this width."""
    return game.bad_pairs(block, width) == 0


# Dense GF(2) linear algebra, for the tests.

def row_reduce(rows: np.ndarray) -> np.ndarray:
    """A basis (shape (r, n), uint8) of the span of `rows` (shape (m, n)) over GF(2), in reduced echelon form."""
    a = rows.copy() % 2  # (m, n)
    pivot_row = 0
    for column in range(a.shape[1]):
        hits = np.flatnonzero(a[pivot_row:, column]) + pivot_row
        if hits.size == 0:
            continue
        a[[pivot_row, hits[0]]] = a[[hits[0], pivot_row]]
        others = np.flatnonzero(a[:, column])
        others = others[others != pivot_row]
        a[others] ^= a[pivot_row]
        pivot_row += 1
        if pivot_row == a.shape[0]:
            break
    return a[:pivot_row].astype(np.uint8)


def kernel(matrix: np.ndarray) -> np.ndarray:
    """A basis (shape (d, m)) of the vectors x over GF(2) with x @ matrix = 0, for `matrix` of shape (m, n)."""
    m = matrix.shape[0]
    joined = np.concatenate([matrix % 2, np.eye(m, dtype=np.uint8)], axis=1).astype(np.uint8)  # (m, n + m)
    reduced = row_reduce(joined)  # (r, n + m)
    zero = ~reduced[:, : matrix.shape[1]].any(axis=1)
    return reduced[zero, matrix.shape[1]:]


def dense_step(basis: np.ndarray, moves: np.ndarray, col: int) -> np.ndarray:
    """{head(a) : a in GF(2)^moves, tail(a) in span(basis)} for one step beside `col`, by elimination: the moves'
    combinations whose tails a parity check of the span kills, carried to their heads."""
    n = moves.shape[1]
    tails = np.concatenate([np.arange(n), np.arange(n)])  # (2n,)
    heads = np.concatenate([moves[col, :, 0], moves[col, :, 1]])  # (2n,)
    tail_matrix = np.zeros((2 * n, n), dtype=np.uint8)  # (2n, n) row a = e_tail(a)
    tail_matrix[np.arange(2 * n), tails] = 1
    head_matrix = np.zeros((2 * n, n), dtype=np.uint8)  # (2n, n)
    head_matrix[np.arange(2 * n), heads] = 1
    checks = kernel(basis.T) if basis.size else np.eye(n, dtype=np.uint8)  # (c, n) parity checks of the span
    combos = kernel((tail_matrix.astype(np.int64) @ checks.T.astype(np.int64)) % 2)  # (d, 2n)
    image = (combos.astype(np.int64) @ head_matrix.astype(np.int64)) % 2  # (d, n)
    return row_reduce(image) if image.size else np.zeros((0, n), dtype=np.uint8)


def dense_linear_limit(block: str, moves: np.ndarray) -> list[np.ndarray]:
    """The linear limit at each phase as a basis (shape (r, n) each), by elimination: the image of all of GF(2)^n
    under the block read again and again, until it stops shrinking."""
    n = moves.shape[1]
    basis = np.eye(n, dtype=np.uint8)  # (n, n)
    while True:
        after = basis
        for ch in block:
            after = dense_step(after, moves, int(ch))
        if after.shape == basis.shape and np.array_equal(row_reduce(after), row_reduce(basis)):
            break
        basis = after
    out = []
    for ch in block:
        out.append(basis)
        basis = dense_step(basis, moves, int(ch))
    return out


def annihilator_rows(labels: np.ndarray) -> np.ndarray:
    """The indicators (shape (s, n)) of the sets that `labels` (shape (n,)) names."""
    sets = int(labels.max()) + 1
    rows = np.zeros((sets, labels.size), dtype=np.uint8)  # (s, n)
    keep = labels >= 0
    rows[labels[keep], np.flatnonzero(keep)] = 1
    return rows


# Surveys.

def survey(max_period: int, widths: list[int]) -> dict[tuple[int, int], dict[str, int]]:
    """For each period and width K, the number of primitive blocks that each test excludes: the two linear tests at K,
    the exact limit at K - 1 and at K, and the game at K. The inclusions functional <= pointwise <= exact at K - 1 <=
    exact at K <= game are checked on every block (`one_cell_short` proves the second)."""
    out: dict[tuple[int, int], dict[str, int]] = {}
    for width in widths:
        moves, narrow = lw.window_moves(width), lw.window_moves(width - 1)  # (2, n, 2), (2, n / 2, 2)
        for period in range(1, max_period + 1):
            counts = {"blocks": 0, "functional": 0, "pointwise": 0, "exact_narrow": 0, "exact": 0, "game": 0}
            blocks = game.necklaces(period)
            for block in tqdm(blocks, desc=f"width {width} period {period}", unit="block", file=sys.stderr,
                              mininterval=5, leave=False):
                flags = [functional_good(block, moves), linear_good(block, moves), exact_good(block, narrow),
                         exact_good(block, moves), game_good(block, width)]
                assert all(not a or b for a, b in zip(flags, flags[1:])), (block, flags)
                counts["blocks"] += 1
                for key, flag in zip(list(counts)[1:], flags):
                    counts[key] += flag
            out[(width, period)] = counts
            print(f"width {width:2d} period {period:2d}: {counts}", flush=True)
    return out


def one_cell_short(block: str, width: int) -> bool:
    """Whether every window y' of the exact limit at `width - 1` cells has y' + (cell 1) outside every set of the linear
    limit at `width` cells, and y' + (cell 0) too when the last cell of y' is 0, at every phase: the lemma behind
    'the linear test at K is never stronger than the exact test at K - 1'."""
    moves, narrow = lw.window_moves(width), lw.window_moves(width - 1)  # (2, n, 2), (2, n / 2, 2)
    half = 1 << (width - 1)
    for labels, exact in zip(linear_limit(block, moves), exact_limit(block, narrow)):
        short = np.flatnonzero(exact)  # (s,) windows of width - 1 cells
        if (labels[short | half] >= 0).any():
            return False
        ends_white = short[((short >> (width - 2)) & 1) == 0]  # (s0,)
        if (labels[ends_white] >= 0).any():
            return False
    return True


def sizes(block: str, width: int) -> list[tuple[int, int, int, int]]:
    """For each phase: windows in the exact limit, windows whose linear obstruction vanishes, sets of the
    annihilator, and the largest set."""
    moves = lw.window_moves(width)  # (2, n, 2)
    rows = []
    for exact, labels in zip(exact_limit(block, moves), linear_limit(block, moves)):
        counts = np.bincount(labels[labels >= 0]) if (labels >= 0).any() else np.zeros(1, dtype=np.int64)
        rows.append((int(exact.sum()), int((labels < 0).sum()), int((counts > 0).sum()), int(counts.max())))
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--survey", type=int, default=0, help="every primitive block up to this period")
    parser.add_argument("--widths", default="4,6,8", help="window widths, comma separated")
    parser.add_argument("--lemma", type=int, default=0, help="check `one_cell_short` on every block up to this period")
    parser.add_argument("--sizes", default="", help="blocks, comma separated: the size of each limit by phase")
    args = parser.parse_args()
    widths = [int(value) for value in args.widths.split(",") if value]
    if args.survey:
        survey(args.survey, widths)
    if args.lemma:
        for width in widths:
            blocks = [block for period in range(1, args.lemma + 1) for block in game.necklaces(period)]
            bar = tqdm(blocks, desc=f"lemma at width {width}", unit="block", file=sys.stderr, mininterval=5, leave=False)
            failures = [block for block in bar if not one_cell_short(block, width)]
            print(f"width {width}: the lemma holds for {len(blocks) - len(failures)} of {len(blocks)} blocks of period "
                  f"at most {args.lemma}; failures {failures[:5]}", flush=True)
    for block in (value for value in args.sizes.split(",") if value):
        for width in widths:
            rows = sizes(block, width)
            exact = [r[0] for r in rows]
            linear = [r[1] for r in rows]
            print(f"{block} width {width}: exact limit {min(exact)}..{max(exact)} of {1 << width} windows, "
                  f"linear {min(linear)}..{max(linear)}, sets {min(r[2] for r in rows)}..{max(r[2] for r in rows)}, "
                  f"largest set {max(r[3] for r in rows)}")


if __name__ == "__main__":
    main()
