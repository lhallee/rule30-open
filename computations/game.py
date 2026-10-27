"""The finite game on the cells right of a column that repeats a block, and the certificates Lean checks for it.

The column repeats `pattern`; cells 1 .. width right of it evolve exactly, and cell width + 1 is free at every step.
Node phase * 2^width + r holds the cells whose cell x is bit x - 1 of r. Every real row is one play. Every infinite play
ends inside one strongly connected component of the graph on nodes, and only a component with a move inside it can
hold a play forever. If in each of those the column left of the repeating one, c_(t+1) xor (c_t or cell 1), is a
function of the phase, it is eventually periodic for every row, and Jen's theorem excludes the block in every rotation
(Lean: `game_column` in `Rule30Open.Columns.FiniteGame`).

    python -m computations.game --max-period 14 --widths 6,10,14   # which primitive blocks the game excludes
"""

from __future__ import annotations

import argparse
import sys
import time
import numpy as np

from graphlib import TopologicalSorter
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components
from tqdm.auto import tqdm


def necklaces(period: int) -> list[str]:
    """The primitive binary necklaces of length `period`, each as its least rotation."""
    found = []
    for word in range(1 << period):
        text = format(word, f"0{period}b")
        rotations = {text[i:] + text[:i] for i in range(period)}
        if len(rotations) == period and text == min(rotations):
            found.append(text)
    return found


def game_graph(pattern: str, width: int) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    """The game's moves (source, target), each node's strongly connected component, whether a play can stay in each
    component, and the left column at each node."""
    period, n_cells = len(pattern), 1 << width
    c = np.array([int(bit) for bit in pattern], dtype=np.int64)  # (p,)
    cells = (np.arange(n_cells)[:, None] >> np.arange(width)[None, :]) & 1  # (n, width), cell x at index x - 1
    weights = 1 << np.arange(width, dtype=np.int64)  # (width,)
    sources, targets = [], []
    for phase in range(period):
        left = np.concatenate([np.full((n_cells, 1), c[phase]), cells[:, :-1]], axis=1)  # (n, width)
        for free in (0, 1):
            right = np.concatenate([cells[:, 1:], np.full((n_cells, 1), free)], axis=1)  # (n, width)
            sources.append(phase * n_cells + np.arange(n_cells))  # (n,)
            targets.append(((phase + 1) % period) * n_cells + ((left ^ (cells | right)) * weights).sum(axis=1))  # (n,)
    source, target = np.concatenate(sources), np.concatenate(targets)  # (2 p n,), (2 p n,)
    nodes = period * n_cells
    graph = csr_matrix((np.ones(source.size, dtype=np.int8), (source, target)), shape=(nodes, nodes))
    _, label = connected_components(graph, directed=True, connection="strong")  # (p n,)
    recurrent = np.zeros(label.max() + 1, dtype=bool)  # (components,)
    recurrent[label[source][label[source] == label[target]]] = True  # components a play can stay in
    phase_of, first = np.arange(nodes) // n_cells, np.arange(nodes) % n_cells & 1  # (p n,), (p n,)
    column = (c[(phase_of + 1) % period] ^ (c[phase_of] | first)).astype(bool)  # (p n,), the left column
    return source, target, label, recurrent, column  # (2 p n,), (2 p n,), (p n,), (components,), (p n,)


def bad_pairs(pattern: str, width: int) -> int:
    """The (component, phase) pairs at which a component that can hold a play shows the left column taking both
    values. Zero means the game excludes the block at this width."""
    _, _, label, recurrent, column = game_graph(pattern, width)
    phase_of = np.arange(label.size) >> width  # (p n,)
    keep = recurrent[label]  # (p n,)
    key = label[keep] * len(pattern) + phase_of[keep]  # (kept,)
    count, ones = np.bincount(key), np.bincount(key, weights=column[keep])  # (keys,), (keys,)
    return int(((ones > 0) & (ones < count)).sum())


def game_certificate(pattern: str, width: int) -> dict[str, int]:
    """The packed numbers `ranks`, `transient` and `values` of the Lean `GameCert` for `pattern` at `width`.

    A node's rank is its component's layer in the condensation (the longest path into it) times one more than the
    number of components that can hold a play, plus the component's place among those (0 for the others), so a move
    between components raises the rank and only transient components share a rank. Raises ValueError when the game
    has a bad pair or the ranks do not fit in 8 bits.
    """
    source, target, label, recurrent, column = game_graph(pattern, width)
    period = len(pattern)
    predecessors: dict[int, set[int]] = {component: set() for component in range(label.max() + 1)}
    for a, b in zip(label[source].tolist(), label[target].tolist(), strict=True):
        if a != b:
            predecessors[b].add(a)
    layer: dict[int, int] = {}
    order = list(TopologicalSorter(predecessors).static_order())  # each component after its predecessors
    for component in order:
        layer[component] = max((layer[p] + 1 for p in predecessors[component]), default=0)
    place = {component: i + 1 for i, component in enumerate(c for c in order if recurrent[c])}
    stride = len(place) + 1
    rank = np.array([layer[c] * stride + place.get(c, 0) for c in range(len(layer))])[label]  # (p n,)
    slot = (rank * period + (np.arange(label.size) >> width))[recurrent[label]]  # (recurrent nodes,)
    value = column[recurrent[label]]  # (recurrent nodes,)
    ones = np.zeros(int(rank.max() + 1) * period, dtype=bool)  # (ranks p,)
    ones[slot[value]] = True
    if ones[slot[~value]].any():
        raise ValueError(f"{pattern} at width {width}: the left column is not a function of the phase in a component")
    if rank.max() > 255:
        raise ValueError(f"{pattern} at width {width}: ranks reach {rank.max()}, past 8 bits")
    return {
        "ranks": int.from_bytes(rank.astype(np.uint8).tobytes(), "little"),  # node v's rank at bits 8v .. 8v + 7
        "transient": sum(1 << r for r in range(0, int(rank.max()) + 1, stride)),
        "values": sum(1 << int(i) for i in np.flatnonzero(ones)),
    }


def lean_certificate(pattern: str, width: int) -> str:
    """The Lean definition `cert<pattern>` of `game_certificate(pattern, width)`, as `FiniteGame.lean` has it."""
    block = ", ".join("true" if bit == "1" else "false" for bit in pattern)
    lines = [
        f'/-- The block {pattern} at width {width}, from `game_certificate("{pattern}", {width})` in '
        "`computations/game.py`. -/",
        f"def cert{pattern} : GameCert where",
        f"  block := [{block}]",
        f"  width := {width}",
    ]
    lines += [f"  {name} := 0x{number:x}" for name, number in game_certificate(pattern, width).items()]
    return "\n".join(lines)


def excluded_blocks(max_period: int, widths: list[int]) -> tuple[dict[str, int], int]:
    """Each primitive block of period up to `max_period` that the game excludes, with the first width that does, and
    the number of blocks tried."""
    blocks = [pattern for period in range(1, max_period + 1) for pattern in necklaces(period)]
    excluded = {}
    for pattern in tqdm(blocks, desc="blocks", unit="block", file=sys.stderr, mininterval=5):
        width = next((width for width in widths if bad_pairs(pattern, width) == 0), None)
        if width is not None:
            excluded[pattern] = width
    return excluded, len(blocks)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--max-period", type=int, default=14)
    parser.add_argument("--widths", default="6,10,14", help="widths tried in order, comma separated")
    args = parser.parse_args()

    started = time.perf_counter()
    excluded, tried = excluded_blocks(args.max_period, [int(width) for width in args.widths.split(",")])
    for pattern, width in excluded.items():
        print(f"{pattern:>14}: excluded at width {width}")
    print(f"{len(excluded)} of {tried} primitive blocks of period up to {args.max_period} excluded "
          f"({time.perf_counter() - started:.0f} s)")


if __name__ == "__main__":
    main()
