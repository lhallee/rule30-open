"""The Conley index over GF(2) of the window graphs beside a column that repeats a block.

Two graphs on windows, each with the column held to `block`:

* **The finite game** (`computations.game`): cells 1 .. width right of the column, the cell beyond them free.
* **Two-sided windows** (`two_sided_moves`): cells -radius .. radius, the center held to the block, both edge cells free
  at every step, so a window has up to four successors and keeps those whose center is the block's next value.

The maximal invariant set of a finite directed graph is the union of its components that hold a cycle and the paths
between them, and its Conley index over a field is the shift-equivalence class of the adjacency matrix restricted to it,
which is the class of its non-nilpotent part (the Leray reduction). The matrix is block triangular in an order of the
strongly connected components, so the non-nilpotent part splits over the components: `index_dimension` gives its
dimension over GF(2) for one component, the rank of a high power of its adjacency matrix. Over a field of
characteristic 0 the index is trivial exactly when there is no cycle, since the trace of the k-th power counts closed
walks of length k and a nonnegative matrix with a cycle has one of positive trace; over GF(2) a component with cycles
can have a nilpotent matrix, the count of closed walks of every length being even.

    python -m computations.conley_index --max-period 8 --widths 6,8,10 --radii 3,4,5,6   # about two minutes
    python -m computations.conley_index --max-period 8 --widths 4,6,8,10 --radii "" --transfer   # with multiplicities
"""

from __future__ import annotations

import argparse
import time

import numpy as np

from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components
from tqdm.auto import tqdm

from computations.game import bad_pairs, game_moves, necklaces


def gf2_rank(matrix: np.ndarray) -> int:
    """The rank over GF(2) of a 0/1 matrix, by elimination on rows packed eight bits to a byte."""
    # matrix: (m, n)
    packed = np.packbits(matrix.astype(np.uint8) & 1, axis=1)  # (m, ceil(n / 8))
    rows, columns = matrix.shape
    rank = 0
    for column in range(columns):
        byte, shift = column >> 3, 7 - (column & 7)
        hits = np.flatnonzero((packed[rank:, byte] >> shift) & 1) + rank  # (h,), rows with a 1 in this column
        if hits.size == 0:
            continue
        pivot = int(hits[0])
        if pivot != rank:
            packed[[rank, pivot]] = packed[[pivot, rank]]
        hits = np.where(hits == rank, pivot, hits)[1:]  # (h - 1,), the other rows, after the swap
        packed[hits] ^= packed[rank]
        rank += 1
        if rank == rows:
            break
    return rank


def index_dimension(adjacency: np.ndarray) -> int:
    """The dimension over GF(2) of the non-nilpotent part of `adjacency`: the rank of A^(2^k) once squaring stops
    lowering it (rank(A^m) = rank(A^(2m)) forces rank(A^m) = rank(A^(m+1)), and then every later power has that rank)."""
    # adjacency: (n, n)
    power = (adjacency % 2).astype(np.float32)  # (n, n); entries of a product stay below 2^24, so float32 is exact
    rank = gf2_rank(power.astype(np.uint8))
    while rank > 0:
        power = (power @ power) % 2  # (n, n)
        squared = gf2_rank(power.astype(np.uint8))
        if squared == rank:
            break
        rank = squared
    return rank


def cyclic_components(source: np.ndarray, target: np.ndarray, nodes: int, transfer: bool = False) -> list[np.ndarray]:
    """The 0/1 adjacency matrix of each strongly connected component with a move inside it, in node order: the
    relation of the multivalued map, so two moves between the same windows (two values of a free cell) count once.
    With `transfer`, the transfer matrix instead, which counts such moves with their multiplicity."""
    # source, target: (e,)
    graph = csr_matrix((np.ones(source.size, dtype=np.int8), (source, target)), shape=(nodes, nodes))
    _, label = connected_components(graph, directed=True, connection="strong")  # (nodes,)
    inside = label[source] == label[target]  # (e,)
    out = []
    position = np.zeros(nodes, dtype=np.int64)  # (nodes,), a node's place in its component
    for component in np.unique(label[source[inside]]).tolist():
        members = np.flatnonzero(label == component)  # (m,)
        position[members] = np.arange(members.size)
        moves = inside & (label[source] == component)  # (e,)
        adjacency = np.zeros((members.size, members.size), dtype=np.int64)  # (m, m)
        np.add.at(adjacency, (position[source[moves]], position[target[moves]]), 1)
        out.append(adjacency if transfer else (adjacency > 0).astype(np.int64))
    return out


def component_indices(source: np.ndarray, target: np.ndarray, nodes: int,
                      transfer: bool = False) -> list[tuple[int, int]]:
    """(size, GF(2) index dimension) for each component that holds a cycle, of the relation or, with `transfer`, of the
    transfer matrix."""
    return [(int(a.shape[0]), index_dimension(a)) for a in cyclic_components(source, target, nodes, transfer)]


def two_sided_moves(block: str, radius: int) -> tuple[np.ndarray, np.ndarray, int]:
    """Moves of the two-sided window graph. Node phase * 2^w + x, w = 2 radius + 1, holds the window whose cell i -
    radius is bit i of x; only windows whose center is the block's value at the phase have moves."""
    period, width = len(block), 2 * radius + 1
    n_windows = 1 << width
    windows = np.arange(n_windows, dtype=np.int64)  # (2^w,)
    edges = 1 | (1 << (width - 1))
    sources, targets = [], []
    for phase in range(period):
        here = windows[((windows >> radius) & 1) == int(block[phase])]  # (2^(w-1),)
        # bit i of here << 1 is cell i - 1 and bit i of here >> 1 is cell i + 1: x'_i = x_(i-1) xor (x_i or x_(i+1))
        inner = ((here << 1) ^ (here | (here >> 1))) & (n_windows - 1) & ~edges  # (2^(w-1),), edge cells unknown
        nxt = (phase + 1) % period
        for free in range(4):
            after = inner | (free & 1) | ((free >> 1) << (width - 1))  # (2^(w-1),)
            keep = ((after >> radius) & 1) == int(block[nxt])  # (2^(w-1),)
            sources.append(phase * n_windows + here[keep])
            targets.append(nxt * n_windows + after[keep])
    return np.concatenate(sources), np.concatenate(targets), period * n_windows  # (e,), (e,)


def survey(max_period: int, widths: list[int], radii: list[int],
           transfer: bool = False) -> dict[str, dict[str, object]]:
    """For every primitive block of period at most `max_period`: the game at each width and the two-sided graph at each
    radius, with the blocks whose total index is trivial, those the game excludes, and those with a component that
    holds a cycle and has a trivial index. With `transfer`, the index of the transfer matrix instead of the relation."""
    blocks = [block for period in range(1, max_period + 1) for block in necklaces(period)]
    out: dict[str, dict[str, object]] = {}
    cases = [("game", w) for w in widths] + [("two-sided", r) for r in radii]
    for kind, size in cases:
        trivial, excluded, nilpotent_cycles, acyclic, excluded_dims = [], [], [], [], {}
        for block in tqdm(blocks, desc=f"{kind} {size}", mininterval=5.0, leave=False):
            if kind == "game":
                source, target, column = game_moves(block, size)
                found = component_indices(source, target, column.size, transfer)
                if bad_pairs(block, size) == 0:
                    excluded.append(block)
                    excluded_dims[block] = sum(d for _, d in found)
            else:
                found = component_indices(*two_sided_moves(block, size), transfer)
            if not found:
                acyclic.append(block)
            elif sum(d for _, d in found) == 0:
                trivial.append(block)
            if any(d == 0 for _, d in found):
                nilpotent_cycles.append(block)
        out[f"{kind} {size}"] = {"blocks": len(blocks), "acyclic": acyclic, "trivial": trivial, "excluded": excluded,
                                 "excluded_dims": excluded_dims, "nilpotent_cycles": nilpotent_cycles}
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--max-period", type=int, default=8)
    parser.add_argument("--widths", default="6,8,10")
    parser.add_argument("--radii", default="3,4,5,6")
    parser.add_argument("--transfer", action="store_true", help="the transfer matrix, with multiplicities")
    args = parser.parse_args()
    start = time.time()
    radii = [int(r) for r in args.radii.split(",")] if args.radii else []
    result = survey(args.max_period, [int(w) for w in args.widths.split(",")], radii, args.transfer)
    for case, row in result.items():
        print(f"{case}: {row['blocks']} blocks; no cycle {len(row['acyclic'])}; GF(2) index trivial "
              f"{len(row['trivial'])} {row['trivial']}; game excludes {len(row['excluded'])}, with index dimensions "
              f"{row['excluded_dims']}; a cyclic component of trivial index in {len(row['nilpotent_cycles'])}")
    print(f"{time.time() - start:.0f} s")


if __name__ == "__main__":
    main()
