"""The game with cyclic classes on every primitive block of a range of periods: which blocks it closes that the plain
game does not, and which of those nothing else excludes.

The column repeats `block` of period P; the game keeps the cells 1 .. W right of it, with cell W + 1 free
(`game.moves`). In each strongly connected component with a move inside it, the plain game asks the left column,
c_(t+1) xor (c_t or cell 1), to be a function of the phase, and the class test asks it to be a function of the cyclic
class: the node's distance from a root of the component modulo the gcd d of the component's cycle lengths
(`game.component_periods`, `Rule30Open.Columns.ClassGame`). Passing at W implies passing at W + 1 for both tests, since
dropping cell W + 1 maps a component at W + 1 into one at W, its cycles to cycles, so d at W + 1 is a multiple of d at W
and the class at W is a function of the class at W + 1.

`classify` is one block at one width in a single pass: one search for the components and one breadth-first search from
a node joined to a root of every component that can hold a play, with the levels' gcd taken per component. The survey
runs it over every block with both colors, in up to two processes, and checks each block the class test closes and the
game does not against the other exclusions of the repository and the kit: `game.kit_blocks`, the wall sets
(`wall_segments.in_set_family`) and the limit windows of 14 cells (`limit_windows.is_good`).

    python -m computations.class_survey --periods 13 16 --width 16 --workers 2   # about 18 minutes
    python -m computations.class_survey --periods 3 12 --width 16                # the 744 blocks of class-game.md
    python -m computations.class_survey --block 000000001011 --width 16          # one block
"""

from __future__ import annotations

import argparse
import functools
import json
import multiprocessing
import sys
import time
from dataclasses import asdict, dataclass

import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components, shortest_path
from tqdm.auto import tqdm

from computations import game


@dataclass
class Row:
    """One block at one width: whether the plain game and the class test close it, and every component that can hold a
    play as (size, cyclic period, left column mixed at a phase, mixed in a class), largest first."""

    block: str
    width: int
    game: bool
    classes: bool
    components: list[tuple[int, int, bool, bool]]


def classify(block: str, width: int) -> Row:
    """The plain game and the class test for `block` at `width`."""
    period, n = len(block), 1 << width
    nodes = period * n
    src, tgt = game.moves(block, width)  # (2 P n,), (2 P n,)
    graph = csr_matrix((np.ones(src.size, dtype=np.int8), (src, tgt)), shape=(nodes, nodes))
    _, label = connected_components(graph, directed=True, connection="strong")  # (P n,)
    del graph
    inside = label[src] == label[tgt]  # (2 P n,)
    s_in, t_in = src[inside], tgt[inside]  # (e,), (e,)
    del src, tgt, inside
    recurrent = np.unique(label[s_in])  # (c,), components that can hold a play
    if recurrent.size == 0:
        return Row(block, width, True, True, [])
    on = np.flatnonzero(np.isin(label, recurrent))  # (m,), their nodes
    first = np.unique(label[on], return_index=True)[1]  # (c,), the least node of each
    root = nodes  # a node joined to the least node of every such component
    rows = np.concatenate([s_in, np.full(recurrent.size, root)])  # (e + c,)
    cols = np.concatenate([t_in, on[first]])  # (e + c,)
    inner = csr_matrix((np.ones(rows.size, dtype=np.int8), (rows, cols)), shape=(nodes + 1, nodes + 1))
    dist = shortest_path(inner, directed=True, unweighted=True, indices=root)  # (P n + 1,)
    del inner
    level = np.where(np.isfinite(dist), dist - 1, -1).astype(np.int64)[:nodes]  # (P n,)
    cycle = np.zeros(label.max() + 1, dtype=np.int64)  # (components,)
    np.gcd.at(cycle, label[s_in], np.abs(level[s_in] + 1 - level[t_in]))
    c = np.array([int(ch) for ch in block], dtype=np.int64)  # (P,)
    phase = on >> width  # (m,)
    column = c[(phase + 1) % period] ^ (c[phase] | (on & 1))  # (m,), the left column
    comp = np.searchsorted(recurrent, label[on])  # (m,), the component's place among those that can hold a play

    def mixed(key: np.ndarray) -> set[int]:
        """The components in which some key shows both values of the left column."""
        group = comp * (int(key.max()) + 1) + key  # (m,)
        ones = np.bincount(group, weights=column)  # (groups,)
        count = np.bincount(group)  # (groups,)
        both = np.flatnonzero((ones > 0) & (ones < count))  # (k,)
        return set((both // (int(key.max()) + 1)).tolist())

    periods = cycle[recurrent]  # (c,), the cyclic periods
    by_phase = mixed(phase)
    by_class = mixed(level[on] % periods[comp])
    sizes = np.bincount(comp)  # (c,)
    components = sorted(((int(sizes[k]), int(periods[k]), k in by_phase, k in by_class) for k in range(recurrent.size)),
                        reverse=True)
    return Row(block, width, not by_phase, not by_class, components)


def least_class_width(block: str, width: int) -> int:
    """The least width at which the class test closes `block`, given that it closes it at `width`."""
    while width > 1 and classify(block, width - 1).classes:
        width -= 1
    return width


def elsewhere(block: str) -> list[str]:
    """The other exclusions of the repository and the kit that reach `block`: the kit, the wall sets and the limit
    windows of 14 cells."""
    from computations import limit_windows, wall_segments

    found = []
    if block in game.kit_blocks(len(block)):
        found.append("kit: " + game.kit_blocks(len(block))[block])
    if any(wall_segments.in_set_family(block[i:] + block[:i]) for i in range(len(block))):
        found.append("wall sets")
    if limit_windows.is_good(block, limit_windows.window_moves(14)):
        found.append("limit windows")
    return found


def blocks_of(periods: range) -> list[str]:
    """The primitive blocks with both colors of the given periods, each as its least rotation."""
    return [b for p in periods for b in game.necklaces(p) if "0" in b and "1" in b]


def survey(blocks: list[str], width: int, workers: int) -> list[Row]:
    """`classify` of every block at `width`, over at most two processes, with a progress bar."""
    task = functools.partial(classify, width=width)
    bar = functools.partial(tqdm, total=len(blocks), desc=f"blocks at width {width}", file=sys.stderr,
                            mininterval=10)
    if workers > 1:
        with multiprocessing.get_context("spawn").Pool(min(workers, 2)) as pool:
            return list(bar(pool.imap(task, blocks, chunksize=4)))
    return [task(b) for b in bar(blocks)]


def table(rows: list[Row]) -> dict[int, tuple[int, int, int]]:
    """By period: blocks, closed by the game, closed by the classes only."""
    out: dict[int, list[int]] = {}
    for row in rows:
        entry = out.setdefault(len(row.block), [0, 0, 0])
        entry[0] += 1
        entry[1] += row.game
        entry[2] += row.classes and not row.game
    return {p: (a, b, c) for p, (a, b, c) in sorted(out.items())}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--periods", type=int, nargs=2, metavar=("MIN", "MAX"))
    parser.add_argument("--block", help="one block")
    parser.add_argument("--width", type=int, default=16)
    parser.add_argument("--workers", type=int, default=1, help="processes, at most 2")
    parser.add_argument("--out", help="write every row as a JSON line to this file")
    args = parser.parse_args()
    started = time.perf_counter()
    if args.block:
        print(classify(args.block, args.width))
    if args.periods:
        rows = survey(blocks_of(range(args.periods[0], args.periods[1] + 1)), args.width, args.workers)
        if args.out:
            with open(args.out, "w") as handle:
                for row in rows:
                    handle.write(json.dumps(asdict(row)) + "\n")
        print("period | blocks | closed by the game | closed by classes only")
        for period, (count, by_game, only) in table(rows).items():
            print(f"{period} | {count} | {by_game} | {only}")
        for row in rows:
            if row.classes and not row.game:
                least = least_class_width(row.block, args.width)
                print(f"{row.block}: classes at width {least}; components at {args.width}: {row.components}; "
                      f"elsewhere: {elsewhere(row.block) or 'none'}", flush=True)
    print(f"({time.perf_counter() - started:.0f} s)", file=sys.stderr)


if __name__ == "__main__":
    main()
