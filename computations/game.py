"""The finite game on the cells right of a column that repeats a block, and the certificates Lean checks for it.

The column repeats `pattern`; cells 1 .. width right of it evolve exactly, and cell width + 1 is free at every step.
Node phase * 2^width + r holds the cells whose cell x is bit x - 1 of r. Every real row is one play. Every infinite play
ends inside one strongly connected component of the graph on nodes, and only a component with a move inside it can
hold a play forever. If in each of those the column left of the repeating one, c_(t+1) xor (c_t or cell 1), is a
function of the phase, it is eventually periodic for every row, and Jen's theorem excludes the block in every rotation
(Lean: `game_column` in `Rule30Open.Columns.FiniteGame`).

`--jen` also closes a component when a farther column is eventually periodic along every play that stays in it, which
Jen's theorem forbids as well (`jen_open`), and reports the blocks that this adds.

`--kit` also lists the excluded blocks that the pinned kit does not exclude (`kit_blocks`), each at the least width the
game needs and with the number of nodes there; `lean_mask` writes the certificate Lean checks for one
(`Rule30Open.Columns.GameBlocks`).

    python -m computations.game --max-period 14 --widths 6,10,14   # which primitive blocks the game excludes
    python -m computations.game --max-period 12 --widths 6,10 --jen   # what Jen's theorem on farther columns adds
    python -m computations.game --max-period 14 --widths 6,10,14 --kit   # which of those are new to the kit
    python -m computations.game --max-period 16 --widths 6,10,14 --kit   # the same to period 16, about 20 minutes
    python -m computations.game --min-period 17 --max-period 18 --workers 4   # periods 17 and 18, about 17 minutes
"""

from __future__ import annotations

import argparse
import functools
import multiprocessing
import sys
import time
import numpy as np

from graphlib import TopologicalSorter
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components
from tqdm.auto import tqdm

# The words of the kit's strip-certificate table (`Rule30StripCertificateTable.certTable`) and of its three single strip
# certificates (`Rule30StripCertificates.not_eventually_01111111`, `not_eventually_00000011` and
# `not_eventually_000000000101`), each as its least rotation. tests/test_computations.py reads them from the kit.
KIT_WORDS = (
    "01111111", "0000000011", "0011111111", "0111111111", "00000000001", "00000000011", "00111111111", "01011111111",
    "01111111111", "000000000001", "000000000011", "000111111111", "001111111111", "010111111111", "011111111111",
    "0000000000001", "0000000000011", "0000000000101", "0000000001011", "0000000010011", "0000000101111",
    "0000111111111", "0001011111111", "0001111111111", "0010111111111", "0011111111101", "0011111111111",
    "0101111111111", "0110111111111", "0111111111111", "00000011", "000000000101",
)


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


def jen_open(pattern: str, width: int) -> list[int]:
    """The sizes of the components that `bad_pairs` counts and that Jen's theorem on a farther column does not close
    either. A component is closed when one of columns 1 .. width is a function of the phase on it, when the free cell
    is a function of the phase on the moves inside it, or when for some j the moves inside it, read on the phase and
    columns 1 .. j, are a function of the phase and columns 1 .. j at the start; each makes some column right of the
    repeating one eventually periodic along every play that stays in the component, against Jen's theorem."""
    source, target, label, recurrent, column = game_graph(pattern, width)
    period, n_cells = len(pattern), 1 << width
    phase_of, cells = np.arange(label.size) >> width, np.arange(label.size) & (n_cells - 1)  # (p n,), (p n,)
    free = np.repeat(np.arange(2 * period) % 2, n_cells)  # (2 p n,), the free cell of each move
    sizes = []
    for component in np.flatnonzero(recurrent).tolist():
        members = np.flatnonzero(label == component)  # (m,)
        moves = (label[source] == component) & (label[target] == component)  # (2 p n,)

        def constant(values: np.ndarray, phases: np.ndarray) -> bool:
            seen = np.zeros((period, 2), dtype=bool)  # (p, 2)
            seen[phases, values] = True
            return not seen.all(axis=1).any()

        if constant(column[members].astype(np.int64), phase_of[members]):
            continue
        if any(constant((cells[members] >> j) & 1, phase_of[members]) for j in range(width)):
            continue
        if constant(free[moves], phase_of[source[moves]]):
            continue
        deterministic = False
        for j in range(1, width + 1):
            start = phase_of[source[moves]] * n_cells + (cells[source[moves]] & ((1 << j) - 1))  # (k,)
            end = phase_of[target[moves]] * n_cells + (cells[target[moves]] & ((1 << j) - 1))  # (k,)
            order = np.lexsort((end, start))  # (k,)
            start, end = start[order], end[order]  # (k,), (k,)
            if not ((start[1:] == start[:-1]) & (end[1:] != end[:-1])).any():
                deterministic = True
                break
        if not deterministic:
            sizes.append(int(members.size))
    return sorted(sizes, reverse=True)


def game_ranks(pattern: str, width: int) -> tuple[np.ndarray, int, int]:
    """Each node's rank, the transient ranks as the bits of a number, and the left column at rank r and phase at bit
    r * period + phase of another.

    A node's rank is its component's layer in the condensation (the longest path into it) times one more than the
    number of components that can hold a play, plus the component's place among those (0 for the others), so a move
    between components raises the rank and only transient components share a rank. Raises ValueError when the game
    has a bad pair.
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
    transient = sum(1 << r for r in range(0, int(rank.max()) + 1, stride))
    return rank, transient, sum(1 << int(i) for i in np.flatnonzero(ones))  # (p n,), int, int


def game_certificate(pattern: str, width: int) -> dict[str, int]:
    """The packed numbers `ranks`, `transient` and `values` of the Lean `GameCert` for `pattern` at `width`, from
    `game_ranks`. Raises ValueError when the game has a bad pair or the ranks do not fit in 8 bits."""
    rank, transient, values = game_ranks(pattern, width)  # (p n,), int, int
    if rank.max() > 255:
        raise ValueError(f"{pattern} at width {width}: ranks reach {rank.max()}, past 8 bits")
    return {
        "ranks": int.from_bytes(rank.astype(np.uint8).tobytes(), "little"),  # node v's rank at bits 8v .. 8v + 7
        "transient": transient,
        "values": values,
    }


def game_mask(pattern: str, width: int) -> dict[str, int | list[int]]:
    """The fields `bits`, `ranks`, `transient` and `values` of the Lean `GameMask` for `pattern` at `width`: as
    `game_certificate`, with each rank in `bits` bits, the fewest that hold the largest rank, and one number of ranks
    for each phase, which keeps every number the kernel shifts small."""
    rank, transient, values = game_ranks(pattern, width)  # (p n,), int, int
    bits = max(1, int(rank.max()).bit_length())
    planes = (rank.reshape(len(pattern), -1)[:, :, None] >> np.arange(bits)) & 1  # (p, n, bits), rank bit i at [.., i]
    ranks = [
        int.from_bytes(np.packbits(plane.astype(np.uint8).ravel(), bitorder="little").tobytes(), "little")
        for plane in planes  # plane: (n, bits), the rank of cells r at bits r bits .. r bits + bits - 1
    ]
    return {"bits": bits, "ranks": ranks, "transient": transient, "values": values}


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


def lean_mask(pattern: str, width: int) -> str:
    """The Lean definition `mask<pattern>` of `game_mask(pattern, width)`, as `GameBlocks.lean` has it."""
    mask = game_mask(pattern, width)
    ranks = ",\n    ".join(f"0x{number:x}" for number in mask["ranks"])
    return "\n".join([
        f'/-- The block {pattern} at width {width}, from `game_mask("{pattern}", {width})` in `computations/game.py`. -/',
        f"def mask{pattern} : GameMask where",
        f"  block := wordOf {len(pattern)} 0b{pattern}",
        f"  width := {width}",
        f"  bits := {mask['bits']}",
        f"  ranks := [{ranks}]",
        f"  transient := 0x{mask['transient']:x}",
        f"  values := 0x{mask['values']:x}",
    ])


# The kit's white-padding certificate families, 0^r followed by a tail, with the least r: families A to E of
# `Rule30UniformWhitePadding` and F to I of `Rule30ShortTail` (`certificateA` to `certificateI`).
PADDING_FAMILIES = (("101011", 13), ("1101", 14), ("11101", 23), ("101", 23), ("1111", 31), ("1", 21), ("11", 11),
                    ("1001", 22), ("1011", 13))
# The kit's Theorem B' (`Rule30BlackRunBlocks.no_black_run_block`): 1^r followed by a block u, with the least r.
BLACK_RUN_BLOCKS = (("0", 18), ("00", 18), ("000", 18), ("0000", 18), ("0100", 18), ("010", 27), ("0010", 27),
                    ("0110", 27))


def kit_blocks(max_period: int) -> dict[str, str]:
    """The primitive blocks of period up to `max_period` that the pinned kit excludes as the eventual period of the
    center column, each with the reason: a strip certificate (`KIT_WORDS`), every run of 1s lasting at least 9 steps
    (`Rule30BlackRuns.not_eventuallyPeriodic_of_long_one_runs`, the constant blocks included), a padded word of
    `Rule30PaddedWords`: 0^q 1 with q >= 9, 0^r 11 with r >= 8, or 0^q 10111 with q >= 9, a white-padding certificate
    family (`PADDING_FAMILIES`), or Theorem B' (`BLACK_RUN_BLOCKS`). The kit's other families, its tails of at most
    six cells after at least 69 white cells, its suffix families and its mixtures, need periods above 21."""
    found = {word: "strip certificate" for word in KIT_WORDS if len(word) <= max_period}
    for period in range(1, max_period + 1):
        padded = {least_rotation("0" * (period - len(tail)) + tail)
                  for tail, white in (("1", 9), ("11", 8), ("10111", 9)) if period - len(tail) >= white}
        families = {least_rotation("0" * (period - len(tail)) + tail)
                    for tail, white in PADDING_FAMILIES if period - len(tail) >= white}
        families |= {least_rotation("1" * (period - len(block)) + block)
                     for block, black in BLACK_RUN_BLOCKS if period - len(block) >= black}
        for word in necklaces(period):
            start = word.find("0")  # a 0 to cut the cycle at, -1 for the block 1
            ones = [len(run) for run in (word[start:] + word[:start]).split("0") if run] if start >= 0 else []
            if word not in found and all(run >= 9 for run in ones):
                found[word] = "long runs of 1s"
            elif word not in found and word in padded:
                found[word] = "padded word"
            elif word not in found and word in families:
                found[word] = "padding or black-run family"
    return found


def least_rotation(word: str) -> str:
    """The least rotation of `word`."""
    return min(word[i:] + word[:i] for i in range(len(word)))


def least_width(pattern: str, max_width: int = 14) -> int | None:
    """The least width at which the game excludes `pattern`, or None up to `max_width`."""
    return next((width for width in range(1, max_width + 1) if bad_pairs(pattern, width) == 0), None)


def first_width(pattern: str, widths: list[int], jen: bool = False) -> int | None:
    """The first of `widths` at which the game excludes `pattern`, or None. With `jen`, a component also closes by
    Jen's theorem on a farther column."""
    open_at = (lambda width: len(jen_open(pattern, width))) if jen else (lambda width: bad_pairs(pattern, width))
    return next((width for width in widths if open_at(width) == 0), None)


def excluded_blocks(max_period: int, widths: list[int], jen: bool = False, min_period: int = 1,
                    workers: int = 1) -> tuple[dict[str, int], int]:
    """Each primitive block of period `min_period` to `max_period` that the game excludes, with the first width that
    does, and the number of blocks tried, over `workers` processes."""
    blocks = [pattern for period in range(min_period, max_period + 1) for pattern in necklaces(period)]
    task = functools.partial(first_width, widths=widths, jen=jen)
    progress = functools.partial(tqdm, total=len(blocks), desc="blocks", unit="block", file=sys.stderr, mininterval=5)
    if workers > 1:
        with multiprocessing.get_context("spawn").Pool(workers) as pool:  # no fork of a process that holds threads
            found = list(progress(pool.imap(task, blocks, chunksize=8)))
    else:
        found = [task(pattern) for pattern in progress(blocks)]
    return {pattern: width for pattern, width in zip(blocks, found) if width is not None}, len(blocks)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--max-period", type=int, default=14)
    parser.add_argument("--min-period", type=int, default=1)
    parser.add_argument("--workers", type=int, default=1, help="processes for the survey")
    parser.add_argument("--widths", default="6,10,14", help="widths tried in order, comma separated")
    parser.add_argument("--jen", action="store_true", help="also close components by Jen's theorem on farther columns")
    parser.add_argument("--kit", action="store_true", help="also list the excluded blocks the kit does not exclude")
    args = parser.parse_args()

    started = time.perf_counter()
    widths = [int(width) for width in args.widths.split(",")]
    excluded, tried = excluded_blocks(args.max_period, widths, min_period=args.min_period, workers=args.workers)
    for pattern, width in excluded.items():
        print(f"{pattern:>14}: excluded at width {width}")
    print(f"{len(excluded)} of {tried} primitive blocks of period {args.min_period} to {args.max_period} excluded "
          f"({time.perf_counter() - started:.0f} s)")
    if args.jen:
        extended, _ = excluded_blocks(args.max_period, widths, jen=True)
        print(f"with Jen's theorem on farther columns: {len(extended)} excluded, "
              f"{sorted(set(extended) - set(excluded))} beyond the game")
        for pattern in ("0001", "0011", "0111"):
            print(f"{pattern}: open components at widths 6 to 12 have "
                  + "; ".join(f"{jen_open(pattern, width)} nodes" for width in (6, 8, 10, 12)))
    if args.kit:
        kit = kit_blocks(args.max_period)
        new = [pattern for pattern in excluded if pattern not in kit]
        print(f"the kit excludes {len(kit)} primitive blocks of period up to {args.max_period}, "
              f"{len(set(kit) & set(excluded))} of the game's; {sorted(set(kit) - set(excluded))} only the kit; "
              f"{len(new)} only the game:")
        for pattern in new:
            width = least_width(pattern)
            print(f"{pattern:>14}: least width {width}, {len(pattern) << width} nodes")


if __name__ == "__main__":
    main()
