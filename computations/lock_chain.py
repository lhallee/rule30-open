"""Locked windows carried leftward: the blocks whose locks are one lock seen from farther columns.

Let column m repeat a block s of period P, and let a locked window of s fix column m + 1 at the white phases of s, to
the values v. Then column m - 1 repeats `left_column(s, v)`, since column m at the next phase is column m - 1 xor
(column m or column m + 1), and every column further left repeats a block that the two columns right of it determine
(`chain`). A row whose columns m - d .. m repeat these blocks has, beside column m - d, the d columns of the chain and
then the locked window of s: so the block at distance d in the chain has a locked window d cells wider than that of s.

`frozen_columns` reads the converse off the game: in each bottom component of the locked nodes of a block (a strongly
connected set of locked nodes that no move leaves), the columns 1, 2, .. right of the repeating one that are a
function of the phase. A seed is a block with a bottom component in which column 1 is not; `classify` finds the seeds
among the blocks with a locked node and places every such block in the chain of a seed. `wall_returns` follows the set
of windows beside a column that repeats 0 1^(P-1), from the wall that a long run of 1s leaves, and reports the cell
beside the column at each white phase. `short_scan` follows the chains of many seeds for columns of a shorter period,
`chain_lock` builds the lock such a column gets, `is_lock` checks it with the rule on whole windows, and `lean_trap`
writes it as a trap of `Rule30Open.Columns.WordTraps`. `natural_trap` finds the trap a driven right half has entered,
as the closure of its true window at the least width that works; `entry_steps` measures entry into a trap by the
rule's own halves, `coin_entry` with a fair coin in place of the cells beyond the window, and `white_lock` asks
whether the white right half settles. `lock_backgrounds` sorts the locks of a `survey` by the background their chains
end in, `background_row` gives a row of that background to run on its ring, and `component_tables` carries one bottom
component leftward as a trap, as the census traps (`CENSUS_TRAPS`, `CENSUS_LARGE`) are. `trap_reach` asks whether
every node of the game can reach a trap, which entry needs, and `miss_tables` builds, for a trap that some node cannot
reach, a closed set of windows apart from it (`MISSED_NATURAL`, `MISSED_CENSUS`); `pair_tables` gives the two bottom
components of each block of `PAIRS`, which every node can reach together.

    python -m computations.lock_chain --chain 8,9,10,11,12,13 --depth 12   # the chains of 0 1^(P-1), 15 s
    python -m computations.lock_chain --classify 4,8,10,11,12 --width 13 --workers 3   # every lock's seed, about 2 min
    python -m computations.lock_chain --lock-backgrounds 10,11,12,13,14,15 --width 16 --workers 3   # two hours
    python -m computations.lock_chain --ether   # the chain of 0 1^7, the kit's ether and its wall, about 1 min
    python -m computations.lock_chain --wall 4,5,6,7,8,9,10,11,12,13,14 --width 11   # returns to the wall, 1 s
    python -m computations.lock_chain --t001 --verify   # the kit's trap for 001 and the short-period locks, 1 min
    python -m computations.lock_chain --short 16,18,20,21 --width 9 --depth 3000 --workers 4   # about 40 min
    python -m computations.lock_chain --short 24,27,30 --width 5 --rest 15 --depth 3000 --workers 4   # long-run seeds
    python -m computations.lock_chain --entry trap001011,trap001011101 --cells 8 --steps 50000   # entry by small halves
    python -m computations.lock_chain --natural 3,5,6,7,9 --steps 20000   # traps that driven halves enter
    python -m computations.lock_chain --natural 2,3,5,6,7,9 --steps 20000 --starts 300 --workers 3   # 301 halves
    python -m computations.lock_chain --entry trap001011111,trap001010011 --cells 0 --steps 1000000   # the white half
    python -m computations.lock_chain --entry trap001011111 --cells 8 --steps 500000 --sample 100   # a long sample
    python -m computations.lock_chain --coin trap001011,trap0011101,trap001011111 --cells 8 --steps 50000   # a coin
    python -m computations.lock_chain --lean   # the trap entries of WordTraps and NineTraps
    python -m computations.lock_chain --lean-ten   # the trap entries of TenTraps, the wall of period 10 carried
    python -m computations.lock_chain --ten-entry --cells 8 --steps 50000   # entry into each trap of TenTraps
    python -m computations.lock_chain --lean-ten-gap   # the entries of the halves of 8 cells, TenGap.lean
    python -m computations.lock_chain --ten-coin   # the period-10 wall with a fair coin beyond, about a minute
    python -m computations.lock_chain --lean-walls 11   # the traps of ElevenTraps; 12, 13, 14 for the others
    python -m computations.lock_chain --lean-wall-gaps   # the entries of WallGaps
    python -m computations.lock_chain --lean-far   # the traps of FarWalls, walls carried past WALL_DEPTHS
    python -m computations.lock_chain --far-entry --cells 4 --steps 20000   # entry into each of them
    python -m computations.lock_chain --lean-census 13   # the traps of CensusTraps13; 14 for CensusTraps14
    python -m computations.lock_chain --census-entry 13 --cells 4 --steps 20000   # entry into each of them
    python -m computations.lock_chain --lean-census-large 14   # the traps of CensusTrapsLarge, in parts; 15 too
    python -m computations.lock_chain --lean-long-large   # the traps of NaturalTrapsLongLarge, in parts
    python -m computations.lock_chain --reach 18   # which traps every window of 18 cells can reach, cut to 18 cells
    python -m computations.lock_chain --wide-reach 2   # the test of reach at 22 cells: natural traps, pairs, sets
    python -m computations.lock_chain --wide-reach-carried 3   # the same for the traps carried along a chain
    python -m computations.lock_chain --halves-apart   # halves of the natural scans apart from NaturalTrapsWalls' traps
    python -m computations.lock_chain --apart-census 3   # the same for every trap that passes the test of reach, APART
    python -m computations.lock_chain --lean-refuted   # closed sets refuting entry into traps of UNREACHED, in Lean
    python -m computations.lock_chain --lean-back   # the windows that can reach a trap, refuting entry, in Lean
    python -m computations.lock_chain --lean-wide-walls   # walls of 22 cells beside traps carried far, in Lean
    python -m computations.lock_chain --apart-pairs   # traps of one block that refute each other
    python -m computations.lock_chain --chain-apart   # chain locks of long-run seeds apart from traps in Lean
    python -m computations.lock_chain --chain-family 01111   # a block's traps from those chains, pairwise apart
    python -m computations.lock_chain --lean-apart-traps   # their refutations and pair reductions, in Lean
    python -m computations.lock_chain --scan001   # long-run seeds whose chains reach 001, about 11 min
    python -m computations.lock_chain --scan001-wider   # periods 36 to 48, and 27 to 33 at width 9
    python -m computations.lock_chain --lean-traps001   # four traps for 001 pairwise apart, in Lean
    python -m computations.lock_chain --lean-trap-sets   # the natural traps of TrapSets
    python -m computations.lock_chain --lean-fifteen   # the traps of FifteenWalls, two walls of period 15 carried
    python -m computations.lock_chain --lean-missed   # the traps of MissedTraps, with closed sets apart from them
    python -m computations.lock_chain --lean-pairs   # the traps of TrapPairs, two for each block
    python -m computations.lock_chain --lean-wall-natural   # the traps of NaturalTrapsWalls
    python -m computations.lock_chain --t001-reach 26   # every node of the game of 001 can reach t001, about 11 min
    python -m computations.lock_chain --t001-coin   # a fair coin beyond the window against t001, widths 12 to 20
    python -m computations.lock_chain --lean-extra   # the traps of NaturalTraps
    python -m computations.lock_chain --lean-large   # the trap of NaturalTrapsLarge, checked in parts
    python -m computations.lock_chain --lean-long   # the traps of NaturalTrapsLong, periods 13 and 14
    python -m computations.lock_chain --long-entry --cells 4 --steps 20000   # entry into each of them
    python -m computations.lock_chain --extra-entry --cells 4 --steps 20000   # entry into each of them
    python -m computations.lock_chain --natural-coin   # those of 16 cells against a fair coin in column 17
    python -m computations.lock_chain --walls-entry 11 --cells 6 --steps 20000   # entry into each trap of ElevenTraps
    python -m computations.lock_chain --natural 10,11,12 --steps 20000 --workers 4   # periods 10 to 12
    python -m computations.lock_chain --natural 13,14 --steps 20000 --max-width 16 --workers 4   # traps of 16 cells
    python -m computations.lock_chain --natural-from saved.txt   # the per-period summary of a saved --natural run
"""

from __future__ import annotations

import argparse
import functools
import multiprocessing
import re
import sys
from collections.abc import Iterator
from pathlib import Path

import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components
from tqdm.auto import tqdm

from computations import absorption, game, locks

# Seeds, the width of their lock, a distance at which their chain holds a block of a shorter period, the shortest found
# for each such block (`short_scan`), and the seed's lock values when it has more than one bottom component without a
# fixed column; `--verify` checks each lock on whole windows.
VERIFIED = [("01111111", 5, 8, None), ("01111111", 5, 14, None), ("0111111111", 5, 30, None),
            ("000010111111111", 5, 47, None), ("00000000001111111111", 9, 98, "01111111110000000000"),
            ("000111111111", 5, 24, None), ("00001111111111", 5, 30, None), ("00011111111111", 5, 38, None),
            ("000001100111111111", 9, 21, "011110011000000000"), ("000110010111111111", 9, 38, "011001100000000000"),
            ("000101101111111111", 9, 62, "011000000000000000"), ("000010101111111111", 9, 135, "011100000000000000"),
            ("000000111111111011", 9, 162, "111111000000000000")]


def necklace(word: str) -> str:
    """The least rotation of a word."""
    return min(word[i:] + word[:i] for i in range(len(word)))


def least_period(word: str) -> int:
    """The least period of a word read cyclically."""
    return min(p for p in range(1, len(word) + 1) if len(word) % p == 0 and word == word[p:] + word[:p])


def left_column(column: str, right: str) -> str:
    """The block that the column left of one repeating `column` repeats, when the column right of it reads `right` at
    the same phases; only the letters of `right` at the white phases of `column` matter."""
    period = len(column)
    return "".join(str(int(column[(ph + 1) % period]) ^ (int(column[ph]) | int(right[ph]))) for ph in range(period))


def chain(seed: str, values: str, depth: int) -> list[str]:
    """The blocks of columns m, m - 1, .., m - depth when column m repeats `seed` and column m + 1 reads `values` at
    the same phases (only its letters at the white phases of `seed` matter), each at the phases of `seed`."""
    columns = [seed, left_column(seed, values)]
    while len(columns) <= depth:
        columns.append(left_column(columns[-1], columns[-2]))
    return columns[:depth + 1]


def chain_cycle(seed: str, values: str, limit: int = 100000) -> tuple[int, list[str]]:
    """Where the chain becomes periodic in the distance, and one period of its columns: the chain is a function of the
    last two columns, so it repeats once a pair of adjacent columns does."""
    columns = chain(seed, values, 1)
    seen: dict[tuple[str, str], int] = {}
    while (columns[-2], columns[-1]) not in seen:
        if len(columns) > limit:
            raise ValueError("no period within the limit")
        seen[(columns[-2], columns[-1])] = len(columns) - 2
        columns.append(left_column(columns[-1], columns[-2]))
    start = seen[(columns[-2], columns[-1])]
    return start, columns[start:len(columns) - 2]


def bottom_components(block: str, width: int) -> list[np.ndarray]:
    """The bottom components of the locked nodes of the game at this width: each a strongly connected set of locked
    nodes that no move leaves."""
    period, size = len(block), 1 << width
    source, target, _, _, _ = game.game_graph(block, width)  # (2 p n,), (2 p n,)
    locked, _ = locks.lock_info(block, width)  # (p n,)
    keep = locked[source]  # (2 p n,), moves from locked nodes, which stay locked
    start, end = source[keep], target[keep]  # (k,), (k,)
    nodes = period * size
    graph = csr_matrix((np.ones(start.size, dtype=np.int8), (start, end)), shape=(nodes, nodes))
    _, label = connected_components(graph, directed=True, connection="strong")  # (p n,)
    leaves = np.zeros(label.max() + 1, dtype=bool)  # (components,)
    leaves[label[start][label[start] != label[end]]] = True
    return [np.flatnonzero(label == c) for c in np.unique(label[locked]) if not leaves[c]]  # each (members,)


def phase_columns(members: np.ndarray, width: int, period: int) -> list[str]:
    """The blocks of columns 1, 2, .. on a set of nodes, as long as each is a function of the phase there."""
    # members: (m,)
    phase = members >> width  # (m,)
    columns = []
    for j in range(width):
        bit = (members >> j) & 1  # (m,)
        low = np.full(period, 2)  # (p,)
        high = np.full(period, -1)  # (p,)
        np.minimum.at(low, phase, bit)
        np.maximum.at(high, phase, bit)
        if (low != high).any():
            break
        columns.append("".join(str(int(v)) for v in low))
    return columns


def frozen_columns(block: str, width: int) -> list[tuple[int, list[str]]]:
    """For each bottom component of the locked nodes, its size and `phase_columns` there."""
    return [(int(members.size), phase_columns(members, width, len(block)))
            for members in bottom_components(block, width)]


def lock_values(block: str, width: int) -> list[tuple[list[str], str]]:
    """For each bottom component of the locked nodes, `phase_columns` there and column 1 right of the last of them at
    each phase (of the block itself when there is none): its one value at the white phases of that column, which the
    lock fixes, and 0 at the black phases, where it does not matter."""
    period = len(block)
    found = []
    for members in bottom_components(block, width):
        columns = phase_columns(members, width, period)
        last, beyond = (columns[-1] if columns else block), len(columns)
        phase, cell = members >> width, (members >> beyond) & 1  # (m,), (m,)
        values = ""
        for ph in range(period):
            seen = set(cell[phase == ph].tolist())
            values += str(seen.pop()) if last[ph] == "0" and len(seen) == 1 else "0"
        found.append((columns, values))
    return found


def survey(periods: list[int], width: int, workers: int = 1) -> dict[str, list[tuple[list[str], str]]]:
    """`lock_values` for every primitive block of these periods that has a locked node at this width."""
    blocks = [block for period in periods for block in game.necklaces(period)]
    task = functools.partial(lock_values, width=width)
    progress = functools.partial(tqdm, total=len(blocks), desc="blocks", file=sys.stderr, mininterval=5)
    if workers > 1:
        with multiprocessing.get_context("spawn").Pool(workers) as pool:
            found = list(progress(pool.imap(task, blocks, chunksize=2)))
    else:
        found = [task(block) for block in progress(blocks)]
    return {block: result for block, result in zip(blocks, found) if result}


def classify(found: dict[str, list[tuple[list[str], str]]], depth: int) -> tuple[dict[str, list[str]],
                                                                                    dict[str, list[tuple[str, int]]]]:
    """The seeds of a `survey`, the blocks with a bottom component in which column 1 is not a function of the phase,
    with their lock values; and for each block, one (seed, distance) per bottom component: the least distance at which
    the chain of a seed, from its lock values, holds the block, and the block's last column a function of the phase
    at that distance less the number of such columns ("", -1 when no chain holds both)."""
    seeds = {block: [values for columns, values in result if not columns]
             for block, result in found.items() if any(not columns for columns, _ in result)}
    tables = [(seed, [necklace(column) for column in chain(seed, values, depth)])
              for seed, options in seeds.items() for values in options]
    placed: dict[str, list[tuple[str, int]]] = {}
    for block, result in found.items():
        for columns, _ in result:
            last, frozen = necklace(columns[-1] if columns else block), len(columns)
            spots = [(distance, seed) for seed, steps in tables for distance in range(frozen, len(steps))
                     if steps[distance] == block and steps[distance - frozen] == last]
            placed.setdefault(block, []).append(min(spots)[::-1] if spots else ("", -1))
    return seeds, placed


def trap_reach(*traps: dict, width: int | None = None) -> float:
    """The share of the nodes of the finite game of the traps' block at `width` cells (the widest trap's width if None),
    with the phase counted modulo the block's period as `WTrap.Absorption` compares labels, from which some values of
    the cell beyond the window lead into the traps' states: each trap cut to its first `width` cells when it is wider,
    and when it is narrower, the windows whose first cells form a state, whatever the cells after them. Every finitely
    supported right half enters one of the traps only if this is 1 at every width: the nodes that cannot reach the
    states form a set that no move leaves, so a half whose first cells start there never has them in a state, and such
    a set at one width gives one at every larger width, the windows that begin with its nodes."""
    width = max(t["cells"] for t in traps) if width is None else width
    return float(reach_nodes(traps, width).mean())


def reach_nodes(traps: tuple[dict, ...], width: int) -> np.ndarray:
    """The nodes of the game of `width` cells that can reach the traps' nodes (`trap_nodes`), found backward from them
    (`locks.back_search`)."""
    word = traps[0]["word"]
    assert all(t["word"] == word for t in traps), "one block"
    return locks.back_search(word, width, trap_nodes(traps, width))  # (p n,)


def successors(word: str, width: int, keys: np.ndarray) -> np.ndarray:
    """The nodes of the game of `width` cells that the nodes `keys` (phase * 2^width + window) move to, under each value
    of the cell beyond: an array of shape (2, k)."""
    # keys: (k,)
    period, low = len(word), np.uint64((1 << width) - 1)
    window = keys & low  # (k,)
    phase = (keys >> np.uint64(width)).astype(np.int64)  # (k,)
    column = np.array([int(bit) for bit in word], dtype=np.uint64)[phase]  # (k,)
    after = (((phase + 1) % period).astype(np.uint64) << np.uint64(width))  # (k,)
    out = []
    for beyond in (0, 1):
        wide = column | window << np.uint64(1) | np.uint64(beyond << (width + 1))  # (k,), the column at bit 0
        out.append(after | (((wide << np.uint64(1)) ^ (wide | (wide >> np.uint64(1)))) >> np.uint64(1) & low))
    return np.stack(out)  # (2, k)


def trap_nodes(traps: tuple[dict, ...], width: int) -> np.ndarray:
    """The nodes of the game of `width` cells, a label modulo the block's period and a window, that are in one of the
    traps: whose first cells, as many as the trap has up to `width`, form a state of it with that label."""
    period = len(traps[0]["word"])
    inside = np.zeros(period << width, dtype=bool)  # (p n,)
    for t in traps:
        cut = min(width, t["cells"])
        mine = np.zeros((period, 1 << cut), dtype=bool)  # (p, 2^cut), a label and the first `cut` cells
        for label, window in t["states"]:
            mine[label % period, window & ((1 << cut) - 1)] = True
        inside |= np.tile(mine, (1, 1 << (width - cut))).reshape(-1)  # (p n,), any cells after the first `cut`
    return inside


def module_entries() -> list[tuple[str, str, functools.partial]]:
    """Every trap of the trap modules and the seven of `Rule30Open.Columns.MissedTraps`, as (module, the name of its
    declaration in Lean, a function that builds its tables), in the order of `coverage.trap_blocks`; the pairs of
    `PAIRS` and `WALL_SPLIT` are left to `pair_tables` and `split_tables`, and the walls of `WIDE_WALLS`, each one of a
    pair, to `wide_wall`. The wall of period 9 at distance 0 is `trap001011111` of `Rule30Open.Columns.WordTraps`."""
    found = [("WordTraps", name, functools.partial(tables, name)) for name, *_ in TRAPS]
    found.append(("WordTraps", "trap001011111", functools.partial(tables, "trap001011111")))
    found += [("NineTraps", f"nine{d}" if d else "trap001011111", functools.partial(carried, "trap001011111", d))
              for d in nine_distances()]
    found.append(("NineTraps", "trap001010011", functools.partial(tables, "trap001010011")))
    found += [("TenTraps", f"ten{d}", functools.partial(carried, "trap0000010001", d)) for d in ten_distances()]
    for period, module, prefix in ((11, "ElevenTraps", "el"), (12, "TwelveTraps", "tw"), (13, "ThirteenTraps", "th"),
                                   (14, "FourteenTraps", "fo")):
        walls = {name: k for k, name in enumerate(WALLS[period])}
        found += [(module, f"{prefix}{walls[name]}_{d}", functools.partial(carried, name, d))
                  for name, d, _ in wall_distances(period, WALL_DEPTHS[period])]
    naturals = (("NaturalTraps", EXTRA_TRAPS, "nat"), ("NaturalTrapsLarge", LARGE_TRAPS, "nat"),
                ("NaturalTrapsLong", LONG_TRAPS, "nat"), ("NaturalTrapsLongLarge", LONG_LARGE, "nat"),
                ("NaturalTrapsWalls", WALL_NATURAL, "natw"), ("MissedTraps", MISSED_NATURAL, "nat"))
    for module, entries, prefix in naturals:
        found += [(module, f"{prefix}{word}", functools.partial(extra_tables, word)) for word, *_ in entries]
    found += [("FarWalls", f"far{period}_{d}", functools.partial(carried, name, d))
              for period, entries in FAR_WALLS.items() for name, d in entries]
    found += [("FifteenWalls", f"fw{wall}_{d}", functools.partial(fifteen_tables, wall, d))
              for wall, d in FIFTEEN_DISTANCES]
    for period, entries in CENSUS_TRAPS.items():
        found += [(f"CensusTraps{period}", f"cen{entry[0]}", functools.partial(census_tables, entry))
                  for entry in entries]
    for module, entries in (("CensusTrapsLarge", CENSUS_LARGE), ("CensusTrapsLarge15", CENSUS_LARGE15),
                            ("MissedTraps", MISSED_CENSUS)):
        found += [(module, f"cen{entry[0]}", functools.partial(census_tables, entry)) for entry in entries]
    return found


def module_traps() -> list[tuple[str, dict]]:
    """Every trap of the trap modules, as (module, tables), in the order of `coverage.trap_blocks`, and the seven of
    `Rule30Open.Columns.MissedTraps` (`module_entries`); the pairs of `PAIRS` are left to `pair_tables`."""
    return [(module, build()) for module, _, build in module_entries()]


def reach_census(width: int = 18) -> list[tuple[str, str, int, float]]:
    """`trap_reach` at `width` cells for every trap of the trap modules (`module_traps`), each cut to its first `width`
    cells when it is wider and taken as the windows that begin with its states when it is narrower, and for the two
    traps of each block of `PAIRS` or `WALL_SPLIT` together: (module, block, cells, share)."""
    rows = [(module, t["word"], t["cells"], trap_reach(t, width=width))
            for module, t in tqdm(module_traps(), desc="traps", file=sys.stderr, mininterval=10)]
    for block in PAIRS:
        pair = pair_tables(block)
        rows.append(("TrapPairs", block, pair[0]["cells"], trap_reach(*pair, width=width)))
    for block, _ in WALL_SPLIT:
        pair = split_tables(block)
        rows.append(("NaturalTrapsWalls", block, max(t["cells"] for t in pair), trap_reach(*pair, width=width)))
    return rows


def miss_tables(t: dict, max_width: int = 20) -> dict:
    """A closed set of windows apart from the trap, as tables (`relabeled_tables`): at the least width w, up to
    `max_width`, at which some node of the game cannot reach the trap's nodes (`trap_nodes`), with the phase counted
    modulo the block's period, the least strongly connected component of those nodes that no move leaves. A right half
    whose first w cells are in it keeps them in it, whatever the cells beyond do, so it never enters the trap."""
    word = t["word"]
    for width in range(1, max_width + 1):
        low = (1 << width) - 1
        source, target, label, _, _ = game.game_graph(word, width)  # (2 p n,), (2 p n,), (p n,)
        out = ~locks.back_closure(trap_nodes((t,), width), source, target)  # (p n,), a set no move leaves
        if out.any():
            leaves = np.zeros(label.max() + 1, dtype=bool)  # (components,)
            leaves[label[source][label[source] != label[target]]] = True
            sizes = np.bincount(label)  # (components,)
            best = min(set(label[out & ~leaves[label]].tolist()), key=lambda c: (sizes[c], c))
            members = np.flatnonzero(label == best)  # (m,)
            return relabeled_tables(word, width, {(x >> width, x & low) for x in members.tolist()})
    raise ValueError(f"every node of the game of {word} can reach its trap up to width {max_width}")


def reach_job(job: tuple[str, str, list[dict], int]) -> tuple[str, str, float]:
    """`trap_reach` of one trap, or of the traps of a pair or set together, at a width: (module, name, share)."""
    module, name, traps, width = job
    return module, name, trap_reach(*traps, width=width)


def wide_reach(width: int = 22, workers: int = 1) -> list[tuple[str, str, float]]:
    """The test of reach in a wider game for the hypotheses that pass both tests at `REACH_WIDTH` cells and are not
    carried along a chain: the traps of the natural and large census modules, the pairs of `PAIRS` and `WALL_SPLIT`,
    and the sets of `TRAP_SETS`, in `workers` processes; those below 1 are the hypotheses of `UNREACHED_WIDE`."""
    keep = {"NaturalTraps", "NaturalTrapsLarge", "NaturalTrapsLong", "NaturalTrapsLongLarge", "NaturalTrapsWalls",
            "CensusTrapsLarge", "CensusTrapsLarge15"}
    jobs = []
    for module, name, build in module_entries():
        if module in keep:
            t = build()
            if t["word"] not in UNREACHED.get(module, ()) and t["word"] not in APART.get(module, ()):
                jobs.append((module, name, [t], width))
    jobs += [("TrapPairs", f"pair{block}", pair_tables(block), width) for block in PAIRS
             if block not in APART.get("TrapPairs", ())]
    jobs += [("NaturalTrapsWalls", f"natw{block}", split_tables(block), width) for block, _ in WALL_SPLIT]
    jobs += [("TrapSets", f"set{block}", [t for *_, t in set_tables(block)], width) for block, *_ in TRAP_SETS]
    jobs.sort(key=lambda job: len(job[2][0]["word"]))
    with multiprocessing.get_context("spawn").Pool(workers) as pool:
        return list(tqdm(pool.imap(reach_job, jobs), total=len(jobs), desc="hypotheses", file=sys.stderr,
                         mininterval=30))


def wide_reach_carried(width: int = 22, workers: int = 1) -> list[tuple[str, str, float]]:
    """The test of reach in a wider game for the traps that `wide_reach` leaves out, those carried along a chain: every
    trap of `module_entries` outside the natural and large census modules and `Rule30Open.Columns.MissedTraps` that
    passes both tests at `REACH_WIDTH` cells, in `workers` processes; those below 1 are the carried traps of
    `UNREACHED_WIDE`. About five hours in three processes at 22 cells."""
    skip = {"NaturalTraps", "NaturalTrapsLarge", "NaturalTrapsLong", "NaturalTrapsLongLarge", "NaturalTrapsWalls",
            "CensusTrapsLarge", "CensusTrapsLarge15", "MissedTraps"}
    jobs = []
    for module, name, build in module_entries():
        if module not in skip:
            t = build()
            if t["word"] not in UNREACHED.get(module, ()) and t["word"] not in APART.get(module, ()):
                jobs.append((module, name, [t], width))
    with multiprocessing.get_context("spawn").Pool(workers) as pool:
        return list(tqdm(pool.imap(reach_job, jobs), total=len(jobs), desc="carried traps", file=sys.stderr,
                         mininterval=30))


def block_apart(job: tuple[str, list[tuple[str, str, list[dict]]]]) -> list[
        tuple[str, str, int, list[tuple[int, int, int]]]]:
    """For one block and its traps or pairs, as (module, name, tables): the halves of the block's natural scan
    (`natural_scan`, windows of 16 to 64 cells) and, for each trap or pair, those inside a natural trap apart from it or
    from both traps of the pair, as (module, name, halves inside some natural trap, [(half, cells, states)])."""
    from computations import right_half
    block, entries = job
    starts = right_half.random_starts(30, 64)
    period = len(block)
    halves = [(k, natural_tables(block, starts[k], time, cells, modulus)) for k, time, cells, modulus, _ in
              natural_scan(block, 20000)[1]]

    def apart(t: dict, u: dict) -> bool:
        cut = (1 << min(t["cells"], u["cells"])) - 1
        mine = {(label % period, window & cut) for label, window in t["states"]}
        return not mine & {(label % period, window & cut) for label, window in u["states"]}

    return [(module, name, len(halves), [(k, u["cells"], len(u["states"])) for k, u in halves
                                         if all(apart(t, u) for t in traps)]) for module, name, traps in entries]


def apart_census(workers: int = 1) -> list[tuple[str, str, int, list[tuple[int, int, int]]]]:
    """`block_apart` for every trap of the trap modules that passes the test of reach (`module_entries` less
    `UNREACHED` and `Rule30Open.Columns.MissedTraps`), and for the pairs of `PAIRS` and `WALL_SPLIT`, one scan per
    block, in `workers` processes: the entries with some half apart are the traps of `APART`."""
    jobs: dict[str, list[tuple[str, str, list[dict]]]] = {}
    for module, name, build in module_entries():
        if module == "MissedTraps" or (name.startswith("cen") and name[3:] in UNREACHED.get(module, ())):
            continue
        t = build()
        if t["word"] not in UNREACHED.get(module, ()):
            jobs.setdefault(t["word"], []).append((module, name, [t]))
    for block in PAIRS:
        jobs.setdefault(block, []).append(("TrapPairs", f"pair{block}", pair_tables(block)))
    for block, _ in WALL_SPLIT:
        jobs.setdefault(block, []).append(("NaturalTrapsWalls", f"natw{block}", split_tables(block)))
    items = sorted(jobs.items(), key=lambda job: (len(job[0]), job[0]))
    with multiprocessing.get_context("spawn").Pool(workers) as pool:
        rows = list(tqdm(pool.imap(block_apart, items), total=len(items), desc="blocks", file=sys.stderr,
                         mininterval=30))
    return [row for found in rows for row in found]


def refuted_entries(max_width: int = 17, max_states: int = 2000, max_pairs: int = 300_000) -> list[
        tuple[str, str, dict, dict]]:
    """The traps of `UNREACHED` whose refutation `Rule30Open.Columns.RefutedTraps` checks in Lean, as (module, name,
    tables, closed set): those that fail the test of reach at a width up to `max_width`, where `miss_tables` gives a
    closed set apart from the trap of at most `max_states` states, with at most `max_pairs` pairs of a state of the trap
    and one of the set for the kernel to compare."""
    out = []
    for module, name, build in tqdm(module_entries(), desc="refuted", file=sys.stderr, mininterval=10):
        if module not in UNREACHED or (name.startswith("cen") and name[3:] not in UNREACHED[module]):
            continue
        t = build()
        if t["word"] not in UNREACHED[module]:
            continue
        try:
            s = miss_tables(t, max_width)
        except ValueError:
            continue
        if len(s["states"]) <= max_states and len(s["states"]) * len(t["states"]) <= max_pairs:
            out.append((module, name, t, s))
    return out


def lean_refuted(entries: list[tuple[str, str, dict, dict]] | None = None) -> str:
    """The closed sets of `Rule30Open.Columns.RefutedTraps`, one per entry of `refuted_entries`: each with the checks
    that it is closed and apart from the trap, and the refutation of entry into the trap, by `not_absorption`, or by
    `not_absorption_wide` when the set is wider than the trap."""
    out = []
    for module, name, t, s in refuted_entries() if entries is None else entries:
        away, wide = f"away_{name}", s["cells"] > t["cells"]
        body = lean_entry(s, away).split("\n", 1)[1]
        apart, refute = ("apartWide", "not_absorption_wide") if wide else ("apart", "not_absorption")
        out.append(f"/-- A closed set apart from `{name}` of {module}: windows of {s['cells']} cells, labels modulo "
                   f"{s['modulus']}, {len(s['states'])} states. -/\n{body}\n"
                   f"theorem {away}_closed : {away}.closedCheck = true := by decide +kernel\n\n"
                   f"theorem {away}_apart : {away}.{apart} {name} = true := by decide +kernel\n\n"
                   f"/-- **Some finitely supported right half driven by `{t['word']}` never enters `{name}`.** -/\n"
                   f"theorem {name}_not_absorption : ¬ {name}.Absorption :=\n"
                   f"  {refute} _ {away} {away}_closed rfl (by decide) {away}_apart (by decide)\n")
    return "\n".join(out)


def pair_tables(block: str) -> list[dict]:
    """The bottom components of the locked windows of 16 cells of a block, each as a trap (`component_tables`)."""
    return [component_tables(block, 16, index, 0) for index in range(len(cached_components(block, 16)))]


def lean_pairs(part: int = 1024, piece: int = 1 << 16) -> str:
    """The traps of `Rule30Open.Columns.TrapPairs`, the two of each block of `PAIRS` (`pair_tables`), each with its
    kernel check, in parts (`lean_parts`) when it has more than 3,000 states."""
    out = []
    for block in PAIRS:
        for index, t in enumerate(pair_tables(block)):
            name = f"pair{block}_{index}"
            if len(t["states"]) > 3000:
                out.append(lean_parts(t, name, part, piece))
            else:
                out.append(lean_entry(t, name) + f"\ntheorem {name}_check : {name}.check = true := by decide +kernel\n")
    return "\n".join(out)


def lean_missed() -> str:
    """The traps of `Rule30Open.Columns.MissedTraps`, those of `MISSED_NATURAL` and `MISSED_CENSUS`, each with its kernel
    check, the closed set of `miss_tables` with the checks that it is closed and apart from the trap, and the refutation
    of entry into the trap."""
    traps = [(f"nat{word}", extra_tables(word)) for word, *_ in MISSED_NATURAL]
    traps += [(f"cen{entry[0]}", census_tables(entry)) for entry in MISSED_CENSUS]
    out = []
    for name, t in traps:
        s, miss = miss_tables(t), f"miss{t['word']}"
        body = lean_entry(s, miss).split("\n", 1)[1]
        out.append(lean_entry(t, name) + f"\ntheorem {name}_check : {name}.check = true := by decide +kernel\n\n"
                   f"/-- A closed set apart from `{name}`: windows of {s['cells']} cells, labels modulo "
                   f"{s['modulus']}, {len(s['states'])} states. -/\n{body}\n"
                   f"theorem {miss}_closed : {miss}.closedCheck = true := by decide +kernel\n\n"
                   f"theorem {miss}_apart : {miss}.apart {name} = true := by decide +kernel\n\n"
                   f"/-- **Some finitely supported right half driven by `{t['word']}` never enters `{name}`.** -/\n"
                   f"theorem {name}_not_absorption : ¬ {name}.Absorption :=\n"
                   f"  not_absorption {name} {miss} {miss}_closed rfl (by decide) {miss}_apart\n    (by decide)\n")
    return "\n".join(out)


def background_row(seed: str, values: str) -> list[int]:
    """One row of the background that the chain of a lock ends in: the cells of one spatial period of the chain's cycle
    at the seed's phase 0, from left to right, to be run on its ring (`space_time_periodic.ring_period`)."""
    _, cycle = chain_cycle(seed, values)
    return [int(column[0]) for column in reversed(cycle)]


def lock_backgrounds(found: dict[str, list[tuple[list[str], str]]]) -> dict[int, dict[int, tuple[set[str], set[str]]]]:
    """For a `survey`, by period and by the spatial period of a background: the blocks with a bottom component whose
    chain, from its last column that is a function of the phase and its lock values, becomes periodic in the distance in
    that background (`chain_cycle`); and the blocks of that least period among the columns of those chains, up to one
    spatial period past where they repeat, which the locks carried leftward give traps."""
    result: dict[int, dict[int, tuple[set[str], set[str]]]] = {}
    for block, entries in found.items():
        period = len(block)
        for columns, values in entries:
            seed = columns[-1] if columns else block
            start, cycle = chain_cycle(seed, values)
            ends, reach = result.setdefault(period, {}).setdefault(len(cycle), (set(), set()))
            ends.add(block)
            reach |= {necklace(column) for column in chain(seed, values, start + len(cycle))
                      if least_period(column) == period}
    return result


@functools.lru_cache(maxsize=64)
def cached_components(block: str, width: int) -> tuple[np.ndarray, ...]:
    """`bottom_components`, kept for the blocks asked again."""
    return tuple(bottom_components(block, width))


def component_tables(block: str, width: int, index: int, distance: int) -> dict:
    """Bottom component `index` of the locked nodes of `block` at `width` (`bottom_components`) carried `distance`
    columns left by its chain, as a labelled trap (`relabeled_tables`): each node keeps its phase, and the `distance`
    columns of the chain go in front of its window. The chain starts at the last column the component fixes as a
    function of the phase, with the lock values of the column right of it (`lock_values`)."""
    period, low = len(block), (1 << width) - 1
    members = cached_components(block, width)[index]  # (m,)
    columns = phase_columns(members, width, period)
    seed, frozen = (columns[-1] if columns else block), len(columns)
    phase, cell = members >> width, (members >> frozen) & 1  # (m,), (m,)
    values = "".join(str(int(cell[phase == ph][0])) if seed[ph] == "0" else "0" for ph in range(period))
    steps = chain(seed, values, frozen + distance)  # columns frozen, frozen - 1, .., -distance of the block's row
    nodes = set()
    for x in members.tolist():
        ph = x >> width
        near = sum(int(steps[frozen + distance - 1 - j][ph]) << j for j in range(distance))
        nodes.add((ph, near | (x & low) << distance))
    return relabeled_tables(steps[frozen + distance], distance + width, nodes)


def chain_lock(seed: str, width: int, distance: int, want: str | None = None) -> tuple[str, list[tuple[int, int]]]:
    """The lock that `chain` carries `distance` columns left of a seed with a locked window of `width` cells: the block
    at that distance, at the phases of the seed, and the nodes (phase, window of distance + width cells) whose first
    `distance` cells are the chain and whose last `width` cells are a node of a bottom component of the seed with no
    column fixed by the phase: the first such component, or the first with lock values `want`."""
    period = len(seed)
    for members in bottom_components(seed, width):
        if phase_columns(members, width, period):
            continue
        phase, cell = members >> width, members & 1  # (m,), (m,)
        values = "".join(str(int(cell[phase == ph][0])) if seed[ph] == "0" else "0" for ph in range(period))
        if want is not None and values != want:
            continue
        columns = chain(seed, values, distance)  # columns m, m - 1, .., m - distance
        nodes = []
        for x in members.tolist():
            ph, window = x >> width, x & ((1 << width) - 1)
            near = sum(int(columns[distance - 1 - j][ph]) << j for j in range(distance))  # cells 1 .. distance
            nodes.append((ph, near | window << distance))
        return columns[distance], nodes
    raise ValueError(f"{seed} has no such bottom component at width {width}")


def is_lock(block: str, nodes: list[tuple[int, int]], width: int) -> bool:
    """Whether a set of nodes (phase of `block`, window of `width` cells) is closed under both values of the cell
    beyond the window and shows one value of the column left of the block at each phase: a direct check with the
    rule on whole windows."""
    period, full = len(block), (1 << width) - 1
    present = set(nodes)
    left: dict[int, int] = {}
    for ph, window in nodes:
        here, after = int(block[ph]), int(block[(ph + 1) % period])
        if left.setdefault(ph, after ^ (here | (window & 1))) != after ^ (here | (window & 1)):
            return False
        for free in (0, 1):
            wide = here | window << 1 | free << (width + 1)  # bit 0 the block's column, bit width + 1 the cell beyond
            nxt = ((wide << 1) ^ (wide | (wide >> 1))) >> 1 & full  # one step of the rule, cells 1 .. width
            if ((ph + 1) % period, nxt) not in present:
                return False
    return True


def short_columns(seed: str, values: str, periods: set[int], depth: int) -> dict[int, tuple[int, str]]:
    """For each least period in `periods`, the first distance up to `depth` at which a column of the chain has it,
    and that column's word of that length, as its least rotation."""
    found: dict[int, tuple[int, str]] = {}
    for distance, column in enumerate(chain(seed, values, depth)):
        p = least_period(column)
        if p in periods and p not in found:
            found[p] = (distance, necklace(column[:p]))
    return found


def seed_short_columns(block: str, width: int, depth: int) -> list[tuple[str, dict[int, tuple[int, str]]]]:
    """For each bottom component of `block` at this width with no column fixed by the phase, its lock values and
    `short_columns` of their chain for the proper divisors of the period."""
    period = len(block)
    if not locks.has_lock(block, width):
        return []
    divisors = {p for p in range(1, period) if period % p == 0}
    found = []
    for columns, values in lock_values(block, width):
        if not columns:
            found.append((values, short_columns(block, values, divisors, depth)))
    return found


def long_run_blocks(period: int, rest: int) -> list[str]:
    """The primitive blocks of this period, as least rotations, made of a run of at least nine 1s and at most `rest`
    other cells: every seed found but 0 1^7 has this form."""
    found = set()
    for others in range(1, min(rest, period - 9) + 1):
        for w in range(1 << others):
            block = "1" * (period - others) + format(w, f"0{others}b")
            if least_period(block) == period:
                found.add(necklace(block))
    return sorted(found)


def short_scan(periods: list[int], width: int, depth: int, workers: int = 1,
               rest: int | None = None) -> dict[str, list[tuple[str, dict]]]:
    """`seed_short_columns` for every primitive block of these periods, or only those of `long_run_blocks` when `rest`
    is given, keeping the seeds whose chain has a column of a shorter period within `depth`."""
    if rest is None:
        blocks = [block for period in periods for block in game.necklaces(period)]
    else:
        blocks = [block for period in periods for block in long_run_blocks(period, rest)]
    task = functools.partial(seed_short_columns, width=width, depth=depth)
    progress = functools.partial(tqdm, total=len(blocks), desc="seeds", file=sys.stderr, mininterval=10)
    if workers > 1:
        with multiprocessing.get_context("spawn").Pool(workers) as pool:
            found = list(progress(pool.imap(task, blocks, chunksize=64)))
    else:
        found = [task(block) for block in progress(blocks)]
    return {block: [(values, hits) for values, hits in result if hits]
            for block, result in zip(blocks, found) if any(hits for _, hits in result)}


# The chain locks that `Rule30Open.Columns.WordTraps` checks: name, seed, the seed's lock width, the distance and the
# seed's lock values (None for its first bottom component).
TRAPS = [("trap01", "01111111", 5, 14, None), ("trap001fifteen", "000010111111111", 5, 47, None),
         ("trap01111", "00000000001111111111", 9, 98, "01111111110000000000"),
         ("trap001011", "000111111111", 5, 24, None), ("trap0011101", "00001111111111", 5, 30, None),
         ("trap001011101", "000001100111111111", 9, 21, "011110011000000000")]


def trap_tables(seed: str, width: int, distance: int, want: str | None = None) -> dict:
    """A chain lock as a labelled trap (`relabeled_tables`)."""
    full, nodes = chain_lock(seed, width, distance, want)
    return relabeled_tables(full, distance + width, set(nodes))


def natural_tables(word: str, start: int, time: int, cells: int, modulus: int) -> dict:
    """The closure of the true window of the right half `start` (bit i is column i + 1), driven by `word` from phase 0,
    at `time`, as a labelled trap (`relabeled_tables`); the closure must be locked."""
    row = start
    for t in range(time):
        row = ((row << 1) | int(word[t % len(word)])) ^ (row | (row >> 1))
    nodes = closure(word, modulus, cells, time, row & ((1 << cells) - 1), 10 ** 6)
    assert nodes is not None and fixes_left(word, nodes)
    return relabeled_tables(word * (modulus // len(word)), cells, nodes)


def relabeled_tables(full: str, cells: int, nodes: set[tuple[int, int]]) -> dict:
    """Locked nodes (phase, window) beside a column that reads `full` at the phases, as a labelled trap: the block as
    its least rotation `word`, the window width, the labels' modulus (the length of `full`), and the states, sorted,
    each a label and a window, with label l reading the block at phase l modulo its period; for each state the index of
    its successor under each value of the cell beyond, and the bits of column 1 at the white labels."""
    modulus, period = len(full), least_period(full)
    word = necklace(full[:period])
    turn = next(r for r in range(period) if (full + full)[r:r + period] == word)  # full[r + l] = word[l]
    states = sorted({((ph - turn) % modulus, window) for ph, window in nodes})
    index = {state: i for i, state in enumerate(states)}
    mask = (1 << cells) - 1
    successors, first = [], 0
    for label, window in states:
        here = int(word[label % period])
        if not here:
            first |= (window & 1) << label
        for free in (0, 1):
            wide = here | window << 1 | free << (cells + 1)
            successors.append(index[((label + 1) % modulus, ((wide << 1) ^ (wide | (wide >> 1))) >> 1 & mask)])
    return {"word": word, "cells": cells, "modulus": modulus, "states": states, "successors": successors,
            "first": first}


def carried(name: str, distance: int) -> dict:
    """The trap of `NATURAL` named `name` carried `distance` columns left by its chain (`carry`)."""
    return carry(tables(name), distance)


def carry(t: dict, distance: int) -> dict:
    """A trap carried `distance` columns left by its chain: the block at that distance, read with the trap's labels, and
    as tables (`relabeled_tables`). The trap's lock values are its first cells at its white labels; the d columns of
    the chain go in front of each state's window."""
    word, period, cells, modulus = t["word"], len(t["word"]), t["cells"], t["modulus"]
    full = word * (modulus // period)  # the trap's block at its labels
    values = "".join(str((t["first"] >> label) & 1) if full[label] == "0" else "0" for label in range(modulus))
    columns = chain(full, values, distance)  # columns m, m - 1, .., m - distance at the labels
    nodes = set()
    for label, window in t["states"]:
        near = sum(int(columns[distance - 1 - j][label]) << j for j in range(distance))
        nodes.add((label, near | window << distance))
    return relabeled_tables(columns[distance], distance + cells, nodes)


# Natural traps: name, word, a right half that a run of the word drives into the trap (bit i is column i + 1;
# `right_half.random_starts(300, 64)[13]`, `[2]` and `[79]`, the white half, and `random_starts(30, 64)[4]`), the time,
# the width and the modulus. The first is checked in `Rule30Open.Columns.WordTraps`, the second in
# `Rule30Open.Columns.NineTraps`; the third, a second trap for 01, is the chain of the lock of 0^4 1 0 1^8
# (`test_period_two_fourteen`); the fourth, the wall of period 10, is carried by its chain in
# `Rule30Open.Columns.TenTraps`, and the last six, the walls of periods 11 and 12, in `ElevenTraps` and `TwelveTraps`.
NATURAL = [("trap001011111", "001011111", 18202347099481127113, 12000, 43, 9),
           ("trap001010011", "001010011", 12828593127923856452, 12000, 41, 27),
           ("trap01fourteen", "01", 18368822234183756340, 12000, 31, 14),
           ("trap0000010001", "0000010001", 0, 12000, 16, 10),
           ("trap00000011011", "00000011011", 0, 12000, 16, 11),
           ("trap00110100111", "00110100111", 0, 12000, 16, 11),
           ("trap00001101001", "00001101001", 0, 12000, 16, 11),
           ("trap001011100111", "001011100111", 0, 12000, 16, 12),
           ("trap000110110011", "000110110011", 0, 12000, 16, 12),
           ("trap000010011111", "000010011111", 6991680298694716019, 12000, 16, 12),
           ("trap0001110010011", "0001110010011", 0, 12000, 16, 13),
           ("trap0000000000001", "0000000000001", 0, 12000, 16, 13),
           ("trap0000000000011", "0000000000011", 0, 12000, 16, 13),
           ("trap00011100101011", "00011100101011", 0, 12000, 16, 14)]

# The walls of periods 11 to 14 that `ElevenTraps`, `TwelveTraps`, `ThirteenTraps` and `FourteenTraps` carry: the
# narrowest of the commonest traps that the natural scan finds there (`wall_chains`), each the trap of a white or random
# half at step 12,000. At periods 13 and 14 only the smallest wall, carried until its chain has shown every block it
# holds (`WALL_DEPTHS`); carried 40 columns, the walls of 5,088 and 13,904 states of period 13 take 4 MB of tables.
WALLS = {11: ["trap00000011011", "trap00110100111", "trap00001101001"],
         12: ["trap001011100111", "trap000110110011", "trap000010011111"],
         13: ["trap0001110010011"],
         14: ["trap00011100101011"]}
WALL_DEPTHS = {11: 40, 12: 40, 13: 53, 14: 103}
# Blocks that the walls of `WALLS` reach only beyond `WALL_DEPTHS` and that no other trap module holds and nothing
# excludes, which the census of locked windows of 16 cells finds (`lock_backgrounds`): the wall and the least distance,
# checked in `Rule30Open.Columns.FarWalls`.
FAR_WALLS = {12: [("trap001011100111", d) for d in (41, 42, 43, 44, 45, 46, 47, 48, 49, 51, 53, 54)]}
# Census traps: for the blocks that the chains of the locked windows of 16 cells hold (`lock_backgrounds`) and that no
# other trap module has and nothing excludes, the lock that carries to each at the least cost (states times cells), when
# it has at most 3,000 states: the block, the block whose bottom component it is, the component's index in
# `bottom_components`, and the distance it is carried (`component_tables`); checked in
# `Rule30Open.Columns.CensusTraps13`, `CensusTraps14` and `CensusTraps15`.
CENSUS_TRAPS = {13: [("0000000000111", "0001100011011", 0, 17), ("0000000100011", "0001100011011", 0, 15),
                    ("0000000111011", "0001100011011", 0, 9), ("0000000111111", "0011001111011", 0, 7),
                    ("0000001000011", "0001100011011", 0, 7), ("0000001000111", "0000001101111", 0, 2),
                    ("0000001011011", "0010110101011", 0, 21), ("0000001011101", "0000111001101", 0, 91),
                    ("0000001100101", "0001100011011", 0, 13), ("0000001100111", "0001100011011", 0, 55),
                    ("0000001101001", "0000010111001", 0, 12), ("0000001110101", "0001100011011", 0, 25),
                    ("0000010000011", "0001100011011", 0, 23), ("0000010000111", "0000111001101", 0, 90),
                    ("0000010010101", "0010110101111", 0, 30), ("0000010011001", "0011001111011", 0, 1),
                    ("0000010100111", "0001100011011", 0, 41), ("0000010101011", "0001100011011", 0, 39),
                    ("0000010111011", "0000000010011", 0, 4),
                    ("0000010111101", "0000001101111", 0, 3), ("0000010111111", "0000000010011", 0, 3),
                    ("0000011000101", "0001100011011", 0, 5), ("0000011001011", "0010110101111", 0, 28),
                    ("0000011001111", "0001100011011", 0, 43), ("0000100010001", "0001100011011", 0, 2),
                    ("0000100101011", "0001100011011", 0, 61), ("0000101000011", "0001100011011", 0, 21),
                    ("0000101010001", "0001100011011", 0, 19), ("0000101010011", "0001100011011", 0, 53),
                    ("0000101100111", "0000111001101", 0, 92), ("0000101101001", "0001100011011", 0, 48),
                    ("0000101101011", "0000111001101", 0, 70), ("0000101110011", "0001100011011", 0, 44),
                    ("0000110000111", "0010110101111", 0, 33), ("0000110001111", "0010110101011", 0, 7),
                    ("0000110011011", "0000111001101", 0, 82), ("0000110111001", "0001100011011", 0, 59),
                    ("0000110111101", "0010110101011", 0, 16), ("0000111000101", "0010110101011", 0, 17),
                    ("0000111100111", "0010110101011", 0, 8), ("0000111101011", "0000111001101", 0, 68),
                    ("0000111110001", "0001100011011", 0, 18), ("0000111111001", "0000010111001", 0, 11),
                    ("0000111111101", "0001100011011", 0, 16), ("0001000101011", "0000010111001", 0, 9),
                    ("0001000110011", "0001100011011", 0, 56), ("0001001000111", "0001100011011", 0, 38),
                    ("0001001001101", "0011001111011", 0, 2), ("0001001101011", "0010110101011", 0, 18),
                    ("0001010001101", "0001100011011", 0, 31), ("0001010010101", "0001100011011", 0, 11),
                    ("0001010010111", "0001100011011", 0, 34), ("0001010100101", "0001100011011", 0, 3),
                    ("0001010101001", "0011001111011", 0, 5), ("0001010101101", "0010110101111", 0, 25),
                    ("0001011000111", "0000001101111", 0, 4), ("0001011001001", "0000010111001", 0, 4),
                    ("0001011001011", "0010110101111", 0, 34), ("0001011010101", "0000111001101", 0, 85),
                    ("0001011010111", "0011001111011", 0, 3), ("0001011011001", "0001100011011", 0, 45),
                    ("0001011111001", "0001100011011", 0, 60), ("0001011111101", "0001100011011", 0, 40),
                    ("0001100011111", "0000111001101", 0, 89), ("0001100101001", "0000111001101", 0, 87),
                    ("0001100101101", "0010110101011", 0, 12), ("0001101001101", "0010110101011", 0, 2),
                    ("0001101001111", "0001100011011", 0, 10), ("0001101011001", "0000010111001", 0, 17),
                    ("0001101011011", "0000111001101", 0, 77), ("0001101011101", "0001100011011", 0, 50),
                    ("0001101011111", "0010110101011", 0, 14), ("0001101101101", "0001100011011", 0, 46),
                    ("0001101101111", "0001100011011", 0, 36), ("0001110100101", "0001100011011", 0, 27),
                    ("0001110100111", "0001100011011", 0, 26), ("0001110110011", "0001100011011", 0, 30),
                    ("0001110111101", "0010110101011", 0, 29), ("0001111001111", "0010110101111", 0, 32),
                    ("0001111011101", "0001100011011", 0, 28), ("0001111100111", "0010110101011", 0, 4),
                    ("0001111101101", "0001100011011", 0, 58), ("0010010110011", "0000111001101", 0, 83),
                    ("0010011011111", "0010110101111", 0, 29), ("0010011100101", "0001100011011", 0, 47),
                    ("0010011100111", "0001100011011", 0, 33), ("0010011111101", "0001100011011", 0, 8),
                    ("0010100101101", "0000111001101", 0, 78), ("0010100101111", "0010110101011", 0, 24),
                    ("0010100111101", "0000010111001", 0, 6), ("0010101001011", "0001100011011", 0, 51),
                    ("0010101111011", "0001100011011", 0, 35), ("0010110011011", "0000010111001", 0, 1),
                    ("0010110101011", "0010110101011", 0, 0), ("0010110101101", "0010110101011", 0, 10),
                    ("0010110111011", "0001100011011", 0, 49), ("0011001111101", "0001100011011", 0, 24),
                    ("0011010100111", "0000111001101", 0, 79), ("0011010110101", "0000111001101", 0, 74),
                    ("0011010111111", "0010110101111", 0, 27), ("0011011010101", "0010110101011", 0, 13),
                    ("0011011011111", "0001100011011", 0, 52), ("0011011100111", "0001100011011", 0, 1),
                    ("0011011111111", "0001100011011", 0, 14), ("0011101010111", "0000010111001", 0, 10),
                    ("0011101101011", "0000111001101", 0, 76), ("0011101101111", "0000010111001", 0, 13),
                    ("0011101110111", "0000111001101", 0, 86), ("0011101111111", "0001100011011", 0, 6),
                    ("0011110111011", "0000111001101", 0, 81), ("0011110111111", "0001100011011", 0, 22),
                    ("0011111011101", "0001100011011", 0, 42), ("0011111011111", "0001100011011", 0, 20),
                    ("0011111101111", "0001100011011", 0, 4), ("0011111110111", "0001100011011", 0, 12),
                    ("0101010111011", "0010110101111", 0, 26), ("0101011010111", "0000111001101", 0, 75),
                    ("0101011011011", "0000010111001", 0, 2), ("0101011111111", "0011001111011", 0, 6),
                    ("0101101110111", "0010110101011", 0, 11), ("0101110101111", "0010110101111", 0, 31),
                    ("0101111101111", "0010110101011", 0, 6), ("0110110110111", "0010110101011", 0, 1),
                    ("0110110111111", "0010110101011", 0, 22)],
                14: [("00000000010101", "00000100000101", 0, 5), ("00000001100011", "00101101011101", 0, 51),
                    ("00000001110111", "00111110111101", 0, 20), ("00000001111101", "00101101011101", 0, 62),
                    ("00000001111111", "00101101011101", 0, 88), ("00000010000101", "00111110111101", 0, 18),
                    ("00000010010111", "00101101101101", 0, 40), ("00000010100001", "00101101010011", 0, 24),
                    ("00000010100101", "00111110111101", 0, 7), ("00000010110111", "00101101010011", 0, 37),
                    ("00000011000101", "00111110111101", 0, 1), ("00000011010001", "00101101101101", 0, 77),
                    ("00000011010011", "00011111001111", 0, 40), ("00000011010111", "00101101011101", 0, 58),
                    ("00000011101001", "00011111001111", 0, 26), ("00000011101011", "00011111001111", 0, 17),
                    ("00000011110101", "00011111001111", 0, 45), ("00000011110111", "00101101101101", 0, 68),
                    ("00000011111001", "00101101101101", 0, 51), ("00000100010011", "00011111001111", 0, 70),
                    ("00000100011111", "00101101010011", 0, 6), ("00000100101011", "00101101011101", 0, 26),
                    ("00000100101101", "00101101011101", 0, 39), ("00000100101111", "00011111001111", 0, 62),
                    ("00000100110011", "00101101101101", 0, 49), ("00000100110101", "00101101101101", 0, 6),
                    ("00000100110111", "00101101101101", 0, 36), ("00000100111001", "00111110111101", 0, 15),
                    ("00000100111101", "00101101011101", 0, 48), ("00000101000011", "00101101101101", 0, 47),
                    ("00000101000111", "00011111001111", 0, 1), ("00000101001101", "00111110111101", 0, 13),
                    ("00000101010001", "00101101010011", 0, 3), ("00000101100011", "00101101011101", 0, 56),
                    ("00000101100101", "00011111001111", 0, 66), ("00000101101011", "00101101010011", 0, 15),
                    ("00000110001001", "00011111001111", 0, 5), ("00000110101111", "00101101101101", 0, 34),
                    ("00000110110011", "00101101011101", 0, 34), ("00000110110101", "00101101101101", 0, 72),
                    ("00000110111001", "00101101101101", 0, 63), ("00000111001111", "00101101011101", 0, 63),
                    ("00000111010011", "00101101010011", 0, 22), ("00000111100001", "00000100000101", 0, 9),
                    ("00000111100011", "00101101010011", 0, 35), ("00000111110101", "00101101010011", 0, 4),
                    ("00000111111011", "00101101101101", 0, 39), ("00001000010011", "00101101011101", 0, 53),
                    ("00001000011011", "00101101101101", 0, 55), ("00001000011111", "00101101010011", 0, 5),
                    ("00001000101011", "00011111001111", 0, 14), ("00001000101101", "00011111001111", 0, 24),
                    ("00001001000011", "00000100000101", 0, 7), ("00001001000101", "00011111001111", 0, 57),
                    ("00001001000111", "00101101011101", 0, 68), ("00001001010101", "00011110110011", 0, 5),
                    ("00001001100101", "00011110110011", 0, 1), ("00001001110101", "00101101101101", 0, 61),
                    ("00001010001001", "00101101101101", 0, 11), ("00001010001111", "00101101101101", 0, 21),
                    ("00001010011101", "00101101011101", 0, 71), ("00001010011111", "00101101010011", 0, 36),
                    ("00001010110011", "00011111001111", 0, 3), ("00001010110101", "00101101101101", 0, 58),
                    ("00001011000101", "00011111001111", 0, 19), ("00001011001101", "00101101010011", 0, 17),
                    ("00001011001111", "00101101101101", 0, 14), ("00001011011011", "00101101101101", 0, 15),
                    ("00001011011101", "00101101101101", 0, 22), ("00001011101111", "00011111001111", 0, 46),
                    ("00001100010011", "00101101011101", 0, 74), ("00001100101001", "00101101101101", 0, 2),
                    ("00001100101011", "00101101101101", 0, 30), ("00001100101101", "00101101101101", 0, 5),
                    ("00001101000111", "00101101010011", 0, 2), ("00001101100011", "00101101010011", 0, 9),
                    ("00001101101111", "00101101011101", 0, 66), ("00001110001101", "00111110111101", 0, 6),
                    ("00001110101011", "00000100000101", 0, 11), ("00001110110101", "00011111001111", 0, 7),
                    ("00001110111011", "00011111001111", 0, 29), ("00001110111111", "00101101010011", 0, 34),
                    ("00001111000101", "00011111001111", 0, 28), ("00001111001101", "00101101101101", 0, 29),
                    ("00001111010011", "00000100000101", 0, 10), ("00001111010111", "00101101101101", 0, 13),
                    ("00001111011001", "00101101101101", 0, 8), ("00001111100101", "00011111001111", 0, 36),
                    ("00001111101101", "00101101101101", 0, 62), ("00001111110001", "00011111001111", 0, 16),
                    ("00010001000101", "00101101101101", 0, 44), ("00010001101101", "00101101101101", 0, 9),
                    ("00010001111011", "00101101101101", 0, 60), ("00010001111111", "00000100000101", 0, 4),
                    ("00010010010011", "00011111001111", 0, 54), ("00010010011111", "00011111001111", 0, 23),
                    ("00010010100101", "00101101010011", 0, 20), ("00010010101001", "00101101011101", 0, 77),
                    ("00010010101111", "00101101010011", 0, 32), ("00010010111101", "00101101011101", 0, 81),
                    ("00010011001111", "00101101011101", 0, 28), ("00010011010111", "00011111001111", 0, 32),
                    ("00010011100011", "00011111001111", 0, 42), ("00010011100111", "00101101011101", 0, 83),
                    ("00010011101101", "00011110110011", 0, 2), ("00010011111001", "00011110110011", 0, 4),
                    ("00010100010111", "00101101011101", 0, 64), ("00010100011011", "00101101011101", 0, 43),
                    ("00010100100101", "00101101101101", 0, 25), ("00010100110111", "00011110110011", 0, 3),
                    ("00010100111001", "00101101010011", 0, 31), ("00010101001101", "00111110111101", 0, 16),
                    ("00010101010011", "00101101011101", 0, 84), ("00010101011001", "00011111001111", 0, 33),
                    ("00010101011011", "00101101011101", 0, 21), ("00010101011111", "00101101010011", 0, 33),
                    ("00010101110101", "00101101101101", 0, 45), ("00010101111101", "00011111001111", 0, 71),
                    ("00010110011101", "00101101011101", 0, 75), ("00010110100011", "00101101011101", 0, 46),
                    ("00010110110011", "00011111001111", 0, 47), ("00010110111001", "00101101101101", 0, 64),
                    ("00010110111101", "00101101011101", 0, 70), ("00010111000111", "00111110111101", 0, 14),
                    ("00010111001001", "00101101011101", 0, 35), ("00010111010101", "00101101101101", 0, 37),
                    ("00010111011111", "00011111001111", 0, 2), ("00010111100101", "00011111001111", 0, 41),
                    ("00010111101001", "00011111001111", 0, 11), ("00011000111011", "00111110111101", 0, 5),
                    ("00011001000111", "00111110111101", 0, 12), ("00011001011101", "00101101011101", 0, 24),
                    ("00011001101011", "00101101101101", 0, 4), ("00011001101101", "00011111001111", 0, 21),
                    ("00011010011101", "00011111001111", 0, 35), ("00011010110101", "00000100000101", 0, 13),
                    ("00011011010011", "00101101101101", 0, 24), ("00011011100101", "00011111001111", 0, 10),
                    ("00011011100111", "00101101010011", 0, 30), ("00011011101001", "00011111001111", 0, 8),
                    ("00011100100111", "00101101101101", 0, 26), ("00011100110101", "00000100000101", 0, 3),
                    ("00011100110111", "00101101101101", 0, 43), ("00011101001111", "00101101101101", 0, 20),
                    ("00011101011011", "00101101101101", 0, 42), ("00011101100111", "00101101011101", 0, 42),
                    ("00011101101001", "00011111001111", 0, 9), ("00011101101011", "00000100000101", 0, 12),
                    ("00011101101101", "00101101101101", 0, 71), ("00011101110011", "00111110111101", 0, 11),
                    ("00011110010011", "00101101011101", 0, 67), ("00011110011001", "00101101010011", 0, 27),
                    ("00011110011111", "00101101010011", 0, 23), ("00011110110111", "00011111001111", 0, 56),
                    ("00011111001011", "00101101101101", 0, 35), ("00011111011111", "00000100000101", 0, 6),
                    ("00011111101011", "00011111001111", 0, 44), ("00011111110101", "00101101011101", 0, 87),
                    ("00100100101101", "00101101101101", 0, 27), ("00100101001111", "00101101010011", 0, 10),
                    ("00100101010011", "00011111001111", 0, 22), ("00100101011011", "00101101101101", 0, 65),
                    ("00100101011101", "00101101011101", 0, 44), ("00100101101011", "00101101101101", 0, 56),
                    ("00100101110101", "00011111001111", 0, 43), ("00100110011101", "00011111001111", 0, 6),
                    ("00100110011111", "00101101011101", 0, 25), ("00100110101101", "00101101010011", 0, 12),
                    ("00100110110101", "00101101011101", 0, 60), ("00100110111011", "00101101101101", 0, 3),
                    ("00100110111101", "00111110111101", 0, 4), ("00100111001011", "00101101011101", 0, 59),
                    ("00100111001111", "00101101101101", 0, 10), ("00100111011101", "00101101101101", 0, 1),
                    ("00100111100111", "00101101011101", 0, 45), ("00100111101011", "00000100000101", 0, 2),
                    ("00100111101101", "00101101010011", 0, 19), ("00100111111101", "00101101101101", 0, 79),
                    ("00101001101101", "00101101101101", 0, 17), ("00101001110101", "00101101101101", 0, 18),
                    ("00101010100111", "00101101101101", 0, 78), ("00101011001101", "00101101101101", 0, 70),
                    ("00101011011011", "00101101010011", 0, 18), ("00101011011101", "00101101011101", 0, 72),
                    ("00101011011111", "00101101011101", 0, 47), ("00101011101101", "00101101011101", 0, 22),
                    ("00101011111011", "00101101011101", 0, 65), ("00101101011011", "00101101011101", 0, 37),
                    ("00101101110101", "00011111001111", 0, 38), ("00101110101101", "00101101101101", 0, 53),
                    ("00101110101111", "00101101011101", 0, 27), ("00101110111111", "00101101101101", 0, 48),
                    ("00101111010011", "00101101101101", 0, 41), ("00101111100111", "00101101011101", 0, 52),
                    ("00101111101011", "00101101101101", 0, 12), ("00101111110011", "00011111001111", 0, 69),
                    ("00101111111101", "00111110111101", 0, 19), ("00110011010101", "00011111001111", 0, 68),
                    ("00110011011101", "00101101010011", 0, 26), ("00110011111011", "00101101011101", 0, 33),
                    ("00110101001111", "00101101011101", 0, 23), ("00110101100111", "00101101011101", 0, 20),
                    ("00110101111101", "00101101101101", 0, 66), ("00110110110101", "00011111001111", 0, 52),
                    ("00110111011111", "00011111001111", 0, 59), ("00111001110111", "00111110111101", 0, 2),
                    ("00111001111111", "00111110111101", 0, 17), ("00111010101111", "00011111001111", 0, 64),
                    ("00111011101101", "00101101010011", 0, 25), ("00111011111011", "00101101010011", 0, 8),
                    ("00111011111101", "00101101010011", 0, 21), ("00111101011111", "00000100000101", 0, 8),
                    ("00111101101011", "00101101011101", 0, 38), ("00111101101101", "00011111001111", 0, 34),
                    ("00111101111011", "00011111001111", 0, 4), ("00111110101011", "00101101101101", 0, 38),
                    ("00111110110101", "00101101011101", 0, 57), ("00111110110111", "00101101101101", 0, 76),
                    ("00111111010101", "00101101011101", 0, 61), ("00111111011011", "00011111001111", 0, 39),
                    ("00111111101111", "00101101011101", 0, 50), ("01010101101011", "00101101101101", 0, 75),
                    ("01010101110111", "00101101011101", 0, 32), ("01010110111011", "00101101011101", 0, 78),
                    ("01010111010111", "00101101011101", 0, 41), ("01010111101111", "00101101010011", 0, 13),
                    ("01010111111011", "00101101101101", 0, 33), ("01011011010111", "00011111001111", 0, 55),
                    ("01011011110111", "00101101101101", 0, 59), ("01011101101111", "00101101010011", 0, 16),
                    ("01011111111011", "00011110110011", 0, 10), ("01101101110111", "00011111001111", 0, 20)],
                15: [("000000000000111", "000000000000111", 0, 0), ("000000000001001", "001111101101101", 0, 13),
                     ("000000000010101", "000001001010101", 0, 5), ("000000000100011", "000000000100011", 0, 0),
                     ("000000000110001", "000110010110101", 0, 13), ("000000000111001", "000110010110101", 0, 9),
                     ("000000000111011", "000101100110111", 0, 109), ("000000000111111", "001101011110101", 0, 15),
                     ("000000001001101", "000000001101011", 0, 2), ("000000001010111", "000000111001101", 0, 2),
                     ("000000001100101", "000101100110111", 0, 113), ("000000001110101", "000000000000111", 0, 8),
                     ("000000001111101", "001111101101101", 0, 56), ("000000010000011", "000000000000111", 0, 6),
                     ("000000010001001", "000111101001111", 0, 25), ("000000010010011", "000111101001111", 0, 45),
                     ("000000010100101", "000111101001111", 0, 11), ("000000010110111", "001001011010111", 0, 27),
                     ("000000010111001", "001001011010111", 0, 43), ("000000011000101", "000111101001111", 0, 5),
                     ("000000011001011", "000101100110111", 0, 8), ("000000011001101", "001011001101101", 0, 38),
                     ("000000011010111", "001111101101101", 0, 52), ("000000011011001", "000100111101101", 0, 9),
                     ("000000011101001", "001001111010111", 0, 17), ("000000011110001", "001001111010111", 0, 8),
                     ("000000011110111", "001011001101101", 0, 34), ("000000100001001", "000101100110111", 0, 60),
                     ("000000100001101", "000000100001101", 0, 0), ("000000100001111", "000110010110101", 0, 15),
                     ("000000100010001", "001111101101101", 0, 84), ("000000100010111", "001101011110101", 0, 6),
                     ("000000100011101", "001101011010111", 0, 33), ("000000100100101", "001111101101101", 0, 74),
                     ("000000100101001", "000101111111011", 0, 3), ("000000100110111", "001101011110101", 0, 2),
                     ("000000100111011", "000000100111011", 0, 0), ("000000100111111", "000000100111111", 0, 0),
                     ("000000101000001", "001001011010111", 0, 17), ("000000101000111", "000111101001111", 0, 17),
                     ("000000101001011", "000011010101111", 0, 19), ("000000101010001", "000000000000111", 0, 2),
                     ("000000101011001", "000101100110111", 0, 99), ("000000101011011", "000111101001111", 0, 3),
                     ("000000101100011", "001101011010111", 0, 39), ("000000101100111", "001111101101101", 0, 6),
                     ("000000101101001", "001001111010111", 0, 56), ("000000101101111", "001111101101101", 0, 17),
                     ("000000101110001", "000101100110111", 0, 56), ("000000110000101", "000000000000111", 0, 4),
                     ("000000110001001", "001101011010111", 0, 15), ("000000110001111", "000000110001111", 0, 0),
                     ("000000110010101", "000011010101111", 0, 21), ("000000110011101", "001011001101101", 0, 24),
                     ("000000110100101", "001111101101101", 0, 1), ("000000110100111", "001111101101101", 0, 19),
                     ("000000110101111", "001011001101101", 0, 45), ("000000110110101", "001101011010111", 0, 13),
                     ("000000110111011", "000101111111011", 0, 1), ("000000111001101", "000000111001101", 0, 0),
                     ("000000111011011", "000110010110101", 0, 17), ("000000111101001", "000001100011011", 0, 10),
                     ("000001000001111", "000001001010101", 0, 9), ("000001000010001", "000001100011011", 0, 2),
                     ("000001000010011", "001011001101101", 0, 32), ("000001000010101", "000110010110101", 0, 3),
                     ("000001000101001", "001101011010111", 0, 26), ("000001000110011", "000111101001111", 0, 37),
                     ("000001000111001", "001001111010111", 0, 36), ("000001000111101", "001001011010111", 0, 16),
                     ("000001001000111", "001111101101101", 0, 62), ("000001001001101", "000101100110111", 0, 102),
                     ("000001001010101", "000001001010101", 0, 0), ("000001001011011", "000011010101111", 0, 29),
                     ("000001001011101", "000101100110111", 0, 81), ("000001001110111", "000001001110111", 0, 0),
                     ("000001010001001", "000001001010101", 0, 21), ("000001010010011", "000101100110111", 0, 6),
                     ("000001010010101", "000101100110111", 0, 111), ("000001010100101", "001001111010111", 0, 51),
                     ("000001010111101", "000011010101111", 0, 5),
                     ("000001011000101", "001011001101101", 0, 43), ("000001011000111", "000011010101111", 0, 25),
                     ("000001011011011", "000001011011011", 0, 0), ("000001011100001", "001001111010111", 0, 40),
                     ("000001011100101", "000111101001111", 0, 21), ("000001011100111", "000001011100111", 0, 0),
                     ("000001011101011", "001111101101101", 0, 63), ("000001100001001", "000001001010101", 0, 7),
                     ("000001100011011", "000001100011011", 0, 0), ("000001100011111", "000001100011111", 0, 0),
                     ("000001100100111", "001001011010111", 0, 31), ("000001100101001", "000101100110111", 0, 25),
                     ("000001100101101", "001011001101101", 0, 5), ("000001101001101", "001001111010111", 0, 3),
                     ("000001101010001", "000011010101111", 0, 26), ("000001101011001", "001001011010111", 0, 3),
                     ("000001101011101", "001001111010111", 0, 12), ("000001101100101", "000001010110101", 0, 7),
                     ("000001101101111", "001111101101101", 0, 60), ("000001101110111", "000111101001111", 0, 35),
                     ("000001101111001", "000001101111001", 0, 0), ("000001110000101", "001001011010111", 0, 22),
                     ("000001110011101", "001101011010111", 0, 34), ("000001110011111", "001111101101101", 0, 57),
                     ("000001110101001", "000001010110101", 0, 5), ("000001110101011", "000001001010101", 0, 11),
                     ("000001110110001", "000101100110111", 0, 46), ("000001111010001", "000011010101111", 0, 14),
                     ("000001111011011", "001001011010111", 0, 52), ("000001111011111", "001001111010111", 0, 39),
                     ("000001111101011", "001001111010111", 0, 38), ("000001111101111", "000001111101111", 0, 0),
                     ("000001111110011", "000001111110011", 0, 0), ("000001111110101", "000101100110111", 0, 55),
                     ("000001111110111", "001101011110101", 0, 5), ("000010000101001", "001111101101101", 0, 78),
                     ("000010000101101", "000101100110111", 0, 30), ("000010000111111", "001001111010111", 0, 55),
                     ("000010001000101", "001001011010111", 0, 40), ("000010001000111", "001011001101101", 0, 35),
                     ("000010001001111", "001011001101101", 0, 40), ("000010001010101", "000110010110101", 0, 7),
                     ("000010001010111", "001001111010111", 0, 30), ("000010001011101", "000111101001111", 0, 38),
                     ("000010001011111", "000111101001111", 0, 48), ("000010001100111", "000111101001111", 0, 39),
                     ("000010001110001", "001001111010111", 0, 50), ("000010010010111", "000100111101101", 0, 11),
                     ("000010010011011", "000101100110111", 0, 75), ("000010010111001", "000010010111001", 0, 0),
                     ("000010010111101", "000010010111101", 0, 0), ("000010011000111", "000011010101111", 0, 2),
                     ("000010011001011", "000011110110011", 0, 1), ("000010011001111", "000011010101111", 0, 13),
                     ("000010011010111", "001101011010111", 0, 5), ("000010011111001", "001001111010111", 0, 60),
                     ("000010100001011", "000101100110111", 0, 18), ("000010100011101", "000000000000111", 0, 10),
                     ("000010100011111", "001001011010111", 0, 26), ("000010100100111", "000101100110111", 0, 90),
                     ("000010100111001", "000011010101111", 0, 9), ("000010100111011", "001111101101101", 0, 65),
                     ("000010101000111", "000111101001111", 0, 1), ("000010101001111", "000010101001111", 0, 0),
                     ("000010101010011", "001111101101101", 0, 96), ("000010101010111", "001011001101101", 0, 12),
                     ("000010101011001", "001101011010111", 0, 6), ("000010101011101", "000111101001111", 0, 33),
                     ("000010101101011", "000011010101111", 0, 32), ("000010101101111", "000001100011011", 0, 11),
                     ("000010101110101", "000011010101111", 0, 27), ("000010101110111", "000001001010101", 0, 17),
                     ("000010101111011", "000111101001111", 0, 29), ("000010101111111", "001111101101101", 0, 16),
                     ("000010110001101", "000001100011011", 0, 19), ("000010110010101", "001011001101101", 0, 8),
                     ("000010110101011", "000111101001111", 0, 49), ("000010110110111", "000101100110111", 0, 95),
                     ("000010110111001", "000101100110111", 0, 91), ("000010110111111", "000010110111111", 0, 0),
                     ("000010111000101", "001111101101101", 0, 58), ("000010111001101", "000101100110111", 0, 100),
                     ("000010111010001", "000111101001111", 0, 18), ("000010111010101", "001001011010111", 0, 50),
                     ("000010111011001", "000001011100111", 0, 1), ("000010111011101", "000101100110111", 0, 11),
                     ("000010111100011", "000101100110111", 0, 63), ("000010111100101", "001101011010111", 0, 9),
                     ("000010111101001", "001101011010111", 0, 18), ("000010111101101", "001111101101101", 0, 7),
                     ("000010111111001", "001001011010111", 0, 59), ("000011000011101", "000011010101111", 0, 24),
                     ("000011000100111", "000001100011011", 0, 7), ("000011000110111", "001001011010111", 0, 18),
                     ("000011000111001", "000111101001111", 0, 31), ("000011000111111", "001111101101101", 0, 5),
                     ("000011001001001", "001011001101101", 0, 2), ("000011001001101", "001001111010111", 0, 43),
                     ("000011001010001", "000111101001111", 0, 7), ("000011001010011", "000101100110111", 0, 84),
                     ("000011001100111", "000101100110111", 0, 12), ("000011001101011", "000001010110101", 0, 10),
                     ("000011001101101", "000101100110111", 0, 20), ("000011001110001", "000110010110101", 0, 5),
                     ("000011001110011", "001001111010111", 0, 28), ("000011001111001", "000011001111001", 0, 0),
                     ("000011010000111", "000101100110111", 0, 28), ("000011010010101", "000101100110111", 0, 105),
                     ("000011010011001", "000101100110111", 0, 96), ("000011010011101", "000001100011011", 0, 14),
                     ("000011010101111", "000011010101111", 0, 0), ("000011011001001", "000101100110111", 0, 35),
                     ("000011011010101", "000111101001111", 0, 43), ("000011011010111", "001001011010111", 0, 45),
                     ("000011011011011", "001101011010111", 0, 24), ("000011011011101", "001011001101101", 0, 9),
                     ("000011011100111", "000111101001111", 0, 12), ("000011011110011", "000011011110011", 0, 0),
                     ("000011011110111", "000101100110111", 0, 52), ("000011011111011", "000011011111011", 0, 0),
                     ("000011100010011", "000011010101111", 0, 15), ("000011100011101", "000111101001111", 0, 16),
                     ("000011100100101", "000001100011011", 0, 15), ("000011100100111", "001011001101101", 0, 28),
                     ("000011100101001", "001111101101101", 0, 94), ("000011100110101", "000001001010101", 0, 3),
                     ("000011100110111", "000101100110111", 0, 98), ("000011100111111", "001011001101101", 0, 42),
                     ("000011101000111", "000101100110111", 0, 70), ("000011101001111", "001001111010111", 0, 9),
                     ("000011101010011", "001111101101101", 0, 68), ("000011101011001", "000101100110111", 0, 16),
                     ("000011101100011", "000111101001111", 0, 9), ("000011101100101", "000101100110111", 0, 4),
                     ("000011101100111", "000101111111011", 0, 6), ("000011101101011", "000011101101011", 0, 0),
                     ("000011101101111", "000101100110111", 0, 88), ("000011101111111", "001101011010111", 0, 38),
                     ("000011110001011", "000011110001011", 0, 0), ("000011110001101", "000111101001111", 0, 10),
                     ("000011110011001", "000001001010101", 0, 18), ("000011110100111", "000001001010101", 0, 23),
                     ("000011110101001", "001101011010111", 0, 17), ("000011110101111", "000011110101111", 0, 0),
                     ("000011110110011", "000011110110011", 0, 0), ("000011111010001", "000001010110101", 0, 4),
                     ("000011111010011", "000001001010101", 0, 10), ("000011111011101", "000110010110101", 0, 4),
                     ("000011111100101", "000011111100101", 0, 0), ("000011111101001", "000110010110101", 0, 16),
                     ("000011111101011", "000001100011011", 0, 9), ("000011111110001", "000000000000111", 0, 1),
                     ("000011111111101", "000011111111101", 0, 0), ("000100010010011", "001111101101101", 0, 91),
                     ("000100010011011", "000011010101111", 0, 34), ("000100010011111", "001111101101101", 0, 83),
                     ("000100010100011", "001011001101101", 0, 26), ("000100010100111", "001101011010111", 0, 35),
                     ("000100010101001", "001001011010111", 0, 57), ("000100010101011", "001001111010111", 0, 34),
                     ("000100010101101", "000101100110111", 0, 1), ("000100010110011", "000101100110111", 0, 13),
                     ("000100010110111", "001001011010111", 0, 23), ("000100010111101", "001101011110101", 0, 10),
                     ("000100011001011", "000111101001111", 0, 40), ("000100011001101", "000001001010101", 0, 19),
                     ("000100011001111", "000011010101111", 0, 23), ("000100011010111", "000100011010111", 0, 0),
                     ("000100011011101", "000101100110111", 0, 47), ("000100011101011", "000001010110101", 0, 2),
                     ("000100011111111", "000001001010101", 0, 4), ("000100100010011", "001001111010111", 0, 23),
                     ("000100100010111", "001011001101101", 0, 29), ("000100100011001", "000101100110111", 0, 43),
                     ("000100100111101", "000101100110111", 0, 22), ("000100101010101", "000001100011011", 0, 22),
                     ("000100101010111", "000100101010111", 0, 0), ("000100101011101", "001111101101101", 0, 71),
                     ("000100101100111", "000111101001111", 0, 32), ("000100110011001", "001111101101101", 0, 10),
                     ("000100110100011", "001011001101101", 0, 11), ("000100110101001", "001001011010111", 0, 32),
                     ("000100110101011", "000011010101111", 0, 16), ("000100110101101", "000011110110011", 0, 2),
                     ("000100110101111", "001101011010111", 0, 36), ("000100110110101", "001011001101101", 0, 6),
                     ("000100111001011", "001101011010111", 0, 10), ("000100111011011", "000001100011011", 0, 13),
                     ("000100111011111", "001111101101101", 0, 95), ("000100111101101", "000100111101101", 0, 0),
                     ("000100111110011", "000110010110101", 0, 6), ("000100111110111", "001101011110101", 0, 12),
                     ("000100111111101", "000000000010001", 0, 1), ("000101000101101", "000101100110111", 0, 23),
                     ("000101000110011", "001111101101101", 0, 88), ("000101000110101", "001001111010111", 0, 26),
                     ("000101000111001", "001001011010111", 0, 36), ("000101000111101", "001011001101101", 0, 41),
                     ("000101001001001", "001101011010111", 0, 21), ("000101001001011", "000110010110101", 0, 19),
                     ("000101001011001", "001001011010111", 0, 19), ("000101001011111", "000111101001111", 0, 28),
                     ("000101001100011", "000001100011011", 0, 5), ("000101001100111", "001011001101101", 0, 10),
                     ("000101001111011", "000101100110111", 0, 64), ("000101010001101", "000101100110111", 0, 97),
                     ("000101010010111", "000101010010111", 0, 0), ("000101010011001", "000101100110111", 0, 14),
                     ("000101010011011", "001111101101101", 0, 92), ("000101010100011", "000001001010101", 0, 16),
                     ("000101010101111", "001101011010111", 0, 37), ("000101010110111", "000011110110011", 0, 3),
                     ("000101011000111", "001101011110101", 0, 11), ("000101011001001", "001001111010111", 0, 44),
                     ("000101011011111", "000011010101111", 0, 4), ("000101011100101", "001001111010111", 0, 4),
                     ("000101011100111", "000101100110111", 0, 103), ("000101011101001", "001001111010111", 0, 24),
                     ("000101011101111", "000011010101111", 0, 6), ("000101011110011", "001001111010111", 0, 29),
                     ("000101011110101", "000101100110111", 0, 2), ("000101011110111", "000001001010101", 0, 1),
                     ("000101011111011", "000101011111011", 0, 0), ("000101011111111", "000000111001101", 0, 1),
                     ("000101100011011", "000101111111011", 0, 7), ("000101100011101", "001001111010111", 0, 10),
                     ("000101100100111", "000101100110111", 0, 85), ("000101100101001", "000111101001111", 0, 13),
                     ("000101100101101", "001001111010111", 0, 1), ("000101100110111", "000101100110111", 0, 0),
                     ("000101100111001", "000001100011011", 0, 16), ("000101100111101", "000111101001111", 0, 26),
                     ("000101101010111", "000011010101111", 0, 3), ("000101101111011", "000001100011011", 0, 12),
                     ("000101101111111", "000111101001111", 0, 2), ("000101110001111", "000101111111011", 0, 5),
                     ("000101110010111", "001101011010111", 0, 29), ("000101110011111", "000101100110111", 0, 3),
                     ("000101110100101", "000001100011011", 0, 3), ("000101110110011", "000101100110111", 0, 33),
                     ("000101110110101", "000101100110111", 0, 72), ("000101110111011", "001001111010111", 0, 20),
                     ("000101111001101", "001001111010111", 0, 33), ("000101111010101", "001101011110101", 0, 3),
                     ("000101111010111", "000101100110111", 0, 50), ("000101111011101", "001001011010111", 0, 37),
                     ("000101111101011", "000001001010101", 0, 22), ("000101111101111", "001001111010111", 0, 52),
                     ("000101111110101", "001001111010111", 0, 37), ("000101111111011", "000101111111011", 0, 0),
                     ("000110001100111", "000011010101111", 0, 8), ("000110001101111", "001001111010111", 0, 48),
                     ("000110001110101", "000111101001111", 0, 15), ("000110001111001", "000101100110111", 0, 27),
                     ("000110010011001", "000101100110111", 0, 66), ("000110010011011", "001001111010111", 0, 14),
                     ("000110010011111", "000001001010101", 0, 2), ("000110010110011", "000110010110011", 0, 0),
                     ("000110010110101", "000110010110101", 0, 0), ("000110010111101", "000110010111101", 0, 0),
                     ("000110011001001", "000001010110101", 0, 9), ("000110011011001", "001111101101101", 0, 81),
                     ("000110011101011", "001001011010111", 0, 38), ("000110011110011", "000101100110111", 0, 83),
                     ("000110100011011", "001001111010111", 0, 58), ("000110100011111", "000110010110101", 0, 2),
                     ("000110100101001", "000101100110111", 0, 86), ("000110100111001", "001101011010111", 0, 8),
                     ("000110100111111", "000101100110111", 0, 110), ("000110101000111", "001111101101101", 0, 70),
                     ("000110101001001", "001001111010111", 0, 6), ("000110101001011", "001111101101101", 0, 8),
                     ("000110101010101", "000100111101101", 0, 1), ("000110101100101", "000001001010101", 0, 13),
                     ("000110101101011", "000110101101011", 0, 0), ("000110101110011", "001011001101101", 0, 7),
                     ("000110101111111", "000011010101111", 0, 18), ("000110110001111", "000101100110111", 0, 89),
                     ("000110110011111", "000011010101111", 0, 28), ("000110110101011", "000101100110111", 0, 58),
                     ("000110110101111", "000110010110101", 0, 18), ("000110110110111", "001101011010111", 0, 20),
                     ("000110110111001", "001001111010111", 0, 32), ("000110110111111", "000101100110111", 0, 5),
                     ("000110111001101", "001001011010111", 0, 56), ("000110111100111", "001111101101101", 0, 77),
                     ("000110111101111", "000111101001111", 0, 30), ("000110111111001", "000101111111011", 0, 2),
                     ("000111000111001", "000101100110111", 0, 101), ("000111000111101", "001001111010111", 0, 18),
                     ("000111001001011", "000101100110111", 0, 71), ("000111001001101", "000111001001101", 0, 0),
                     ("000111001011011", "000111001011011", 0, 0), ("000111001101001", "000101100110111", 0, 48),
                     ("000111001101101", "000101100110111", 0, 9), ("000111001110011", "001001111010111", 0, 49),
                     ("000111001110101", "000001010110101", 0, 3), ("000111001111001", "000001001010101", 0, 20),
                     ("000111010001111", "001001011010111", 0, 35), ("000111010011101", "001011001101101", 0, 27),
                     ("000111010011111", "000000000000111", 0, 9), ("000111010100101", "000101100110111", 0, 31),
                     ("000111010100111", "000101100110111", 0, 79), ("000111010101101", "000101100110111", 0, 54),
                     ("000111010101111", "000101100110111", 0, 45), ("000111010111101", "001001011010111", 0, 21),
                     ("000111011001101", "001101011010111", 0, 27), ("000111011001111", "001001111010111", 0, 25),
                     ("000111011010011", "001111101101101", 0, 76), ("000111011010101", "000101100110111", 0, 41),
                     ("000111011010111", "000001001010101", 0, 12), ("000111011011001", "001001011010111", 0, 28),
                     ("000111011011011", "001101011010111", 0, 19), ("000111011100101", "001001011010111", 0, 30),
                     ("000111011101011", "001011001101101", 0, 4), ("000111011101111", "001111101101101", 0, 87),
                     ("000111011110011", "000011010101111", 0, 7), ("000111100100111", "001001111010111", 0, 5),
                     ("000111100101011", "000101100110111", 0, 51), ("000111100101101", "001001111010111", 0, 31),
                     ("000111100101111", "000011010101111", 0, 1), ("000111101001011", "001001111010111", 0, 45),
                     ("000111101001111", "000111101001111", 0, 0), ("000111101011111", "000101100110111", 0, 17),
                     ("000111101101101", "001101011010111", 0, 7), ("000111101110011", "001001011010111", 0, 39),
                     ("000111110010011", "000111101001111", 0, 20), ("000111110010101", "001001011010111", 0, 58),
                     ("000111110100111", "001001111010111", 0, 16), ("000111110101001", "000101100110111", 0, 15),
                     ("000111110101011", "001101011110101", 0, 4), ("000111110101101", "001011001101101", 0, 33),
                     ("000111110101111", "000101100110111", 0, 68), ("000111110110101", "001001111010111", 0, 11),
                     ("000111110110111", "000001010110101", 0, 6), ("000111110111001", "000101100110111", 0, 7),
                     ("000111111001011", "001101011110101", 0, 1), ("000111111010011", "001001011010111", 0, 33),
                     ("000111111011001", "001101011010111", 0, 12), ("000111111011011", "001111101101101", 0, 18),
                     ("000111111011101", "001011001101101", 0, 23), ("000111111011111", "000001001010101", 0, 6),
                     ("000111111101011", "001111101101101", 0, 14), ("000111111111001", "001111101101101", 0, 12),
                     ("000111111111101", "000110010110101", 0, 8), ("001001001010111", "001101011010111", 0, 22),
                     ("001001001011011", "000101100110111", 0, 39), ("001001001011111", "000100111101101", 0, 10),
                     ("001001001110101", "000001100011011", 0, 8), ("001001010110011", "000101100110111", 0, 21),
                     ("001001010110101", "001001010110101", 0, 0), ("001001010110111", "000011010101111", 0, 11),
                     ("001001011010101", "001011001101101", 0, 36), ("001001011010111", "001001011010111", 0, 0),
                     ("001001011011011", "000101100110111", 0, 37), ("001001011011101", "001111101101101", 0, 66),
                     ("001001011101011", "000011010101111", 0, 30), ("001001011101111", "000101100110111", 0, 32),
                     ("001001011111011", "001001011010111", 0, 44), ("001001011111111", "000111101001111", 0, 44),
                     ("001001100101011", "001101011010111", 0, 30), ("001001100101101", "001001011010111", 0, 54),
                     ("001001100111101", "001001011010111", 0, 4), ("001001101001011", "001011001101101", 0, 3),
                     ("001001101001101", "001001011010111", 0, 29), ("001001101010111", "001101011010111", 0, 28),
                     ("001001101011011", "001001011010111", 0, 24), ("001001101110111", "001001101110111", 0, 0),
                     ("001001101111011", "000101100110111", 0, 57), ("001001101111101", "000111101001111", 0, 8),
                     ("001001101111111", "001001011010111", 0, 42), ("001001110010101", "001001111010111", 0, 59),
                     ("001001110100101", "001111101101101", 0, 3), ("001001110111011", "001011001101101", 0, 1),
                     ("001001110111101", "001111101101101", 0, 75), ("001001111001011", "001111101101101", 0, 53),
                     ("001001111001101", "001101011010111", 0, 25), ("001001111001111", "001001011010111", 0, 46),
                     ("001001111100111", "000101100110111", 0, 59),
                     ("001001111101111", "001101011010111", 0, 14), ("001001111110011", "000111101001111", 0, 24),
                     ("001001111111101", "000101100110111", 0, 108), ("001010010111111", "000111101001111", 0, 34),
                     ("001010011010011", "000101100110111", 0, 44), ("001010011010101", "001001111010111", 0, 15),
                     ("001010011100111", "001111101101101", 0, 2), ("001010011101111", "000001100011011", 0, 6),
                     ("001010100101011", "000111101001111", 0, 41), ("001010100101101", "000101100110111", 0, 76),
                     ("001010101101011", "001101011010111", 0, 1), ("001010101111101", "000101100110111", 0, 87),
                     ("001010101111111", "001010101111111", 0, 0), ("001010110011101", "000101100110111", 0, 61),
                     ("001010110110111", "000001100011011", 0, 20), ("001010111001111", "001010111001111", 0, 0),
                     ("001010111101011", "001010111101011", 0, 0), ("001010111101111", "001001111010111", 0, 47),
                     ("001010111110011", "001011001101101", 0, 39), ("001010111111011", "001111101101101", 0, 59),
                     ("001011001011011", "000101100110111", 0, 92), ("001011001101101", "001011001101101", 0, 0),
                     ("001011001110111", "001001111010111", 0, 13), ("001011001111011", "000101100110111", 0, 74),
                     ("001011010010111", "001111101101101", 0, 79), ("001011010110011", "001001011010111", 0, 48),
                     ("001011010110101", "001011010110101", 0, 0), ("001011010111011", "001001111010111", 0, 41),
                     ("001011011011101", "000001001010101", 0, 14), ("001011011011111", "001101011010111", 0, 23),
                     ("001011011110111", "000011010101111", 0, 33), ("001011011111111", "000000001101011", 0, 1),
                     ("001011101110101", "001101011010111", 0, 11), ("001011101110111", "001111101101101", 0, 9),
                     ("001011110101011", "001101011110101", 0, 7), ("001011110101111", "000101111111011", 0, 4),
                     ("001011110110011", "001001111010111", 0, 22), ("001011111011101", "001001111010111", 0, 27),
                     ("001011111101111", "000000111001101", 0, 3), ("001100110011101", "001111101101101", 0, 85),
                     ("001100110011111", "000111101001111", 0, 36), ("001100110101011", "001001111010111", 0, 21),
                     ("001100110101101", "001101011010111", 0, 3), ("001100110110101", "000111101001111", 0, 23),
                     ("001100110111101", "000111101001111", 0, 14), ("001100111001101", "000001001010101", 0, 15),
                     ("001100111011101", "001111101101101", 0, 89), ("001100111110101", "001100111110101", 0, 0),
                     ("001100111111101", "000000000000111", 0, 7), ("001100111111111", "000000000110011", 0, 1),
                     ("001101001101011", "001001011010111", 0, 20), ("001101010101011", "001111101101101", 0, 11),
                     ("001101010111101", "001001011010111", 0, 25), ("001101011010111", "001101011010111", 0, 0),
                     ("001101011101011", "000101100110111", 0, 73), ("001101011101111", "001001011010111", 0, 1),
                     ("001101011110101", "001101011110101", 0, 0), ("001101011111011", "000011010101111", 0, 12),
                     ("001101100111011", "000101100110111", 0, 34), ("001101100111101", "001111101101101", 0, 67),
                     ("001101101011101", "000101100110111", 0, 93), ("001101101101111", "001001111010111", 0, 42),
                     ("001101101110101", "000110010110101", 0, 1), ("001101110101111", "000011010101111", 0, 22),
                     ("001101110111101", "000101100110111", 0, 77), ("001101111010101", "001001011010111", 0, 49),
                     ("001101111010111", "000101100110111", 0, 26), ("001101111011101", "000001010110101", 0, 1),
                     ("001101111100111", "000001100011011", 0, 1), ("001101111110111", "000011010101111", 0, 20),
                     ("001101111111011", "000100111101101", 0, 8), ("001101111111111", "001101111111111", 0, 0),
                     ("001110011101011", "001101011010111", 0, 16), ("001110011101111", "000001100011011", 0, 4),
                     ("001110101001111", "001001111010111", 0, 54), ("001110101010101", "000011010101111", 0, 35),
                     ("001110101011011", "001111101101101", 0, 72), ("001110101111111", "000110010110101", 0, 14),
                     ("001110111001111", "000111101001111", 0, 6), ("001110111010111", "000101100110111", 0, 82),
                     ("001110111110101", "000101100110111", 0, 62), ("001110111110111", "000101100110111", 0, 24),
                     ("001111010110111", "000100111101101", 0, 12), ("001111010111111", "000001001010101", 0, 8),
                     ("001111011110101", "001111101101101", 0, 4), ("001111011111111", "000000000000111", 0, 5),
                     ("001111101011011", "001001011010111", 0, 51), ("001111101101101", "001111101101101", 0, 0),
                     ("001111110101111", "001001111010111", 0, 7), ("001111110110101", "001101011010111", 0, 40),
                     ("001111110111101", "000111101001111", 0, 4), ("001111111010101", "001111101101101", 0, 55),
                     ("001111111011111", "000000000000111", 0, 3), ("001111111110111", "000101100110111", 0, 112),
                     ("010101010111011", "000011010101111", 0, 17), ("010101010111111", "000000001101011", 0, 3),
                     ("010101101111011", "001101011010111", 0, 31), ("010101111111011", "001011001101101", 0, 44),
                     ("010101111111111", "000100111101101", 0, 4), ("010110101111111", "000111101001111", 0, 46),
                     ("010110110111011", "001101011010111", 0, 2), ("010110111011011", "000101100110111", 0, 38),
                     ("010111101101111", "000001100011011", 0, 18), ("011011011011111", "001001111010111", 0, 2),
                     ("011011011110111", "000101100110111", 0, 19), ("011011101101111", "001001111010111", 0, 57),
                     ("011011111101111", "001011001101101", 0, 31), ("011011111110111", "001011001101101", 0, 37),
                     ("011110111111111", "000110010110101", 0, 12)]}
# The census traps of more than 3,000 states, of the blocks of periods 13 and 14 that no smaller component reaches, in
# the same form; checked in parts in `Rule30Open.Columns.CensusTrapsLarge`.
CENSUS_LARGE = [("0000000110001", "0000000110001", 0, 0), ("0000001001111", "0000001001111", 0, 0),
                ("0000001011111", "0000001011111", 0, 0), ("0000101111011", "0000101111011", 0, 0),
                ("0001001011001", "0001001011001", 0, 0), ("0001101111011", "0001101111011", 0, 0),
                ("0001111110101", "0001111110101", 0, 0), ("0011101011111", "0011101011111", 0, 0),
                ("0101111111011", "0101111111011", 0, 0), ("0111101111111", "0111101111111", 0, 0),
                ("00000000110001", "00000000110001", 0, 0), ("00000010010001", "00000010010001", 0, 0),
                ("00000010010011", "00000010010011", 0, 0), ("00000010111011", "00000010111011", 0, 0),
                ("00000011011011", "00000011011011", 0, 0), ("00000101111111", "00000101111111", 0, 0),
                ("00100101111111", "00100101111111", 0, 0), ("00101111111011", "00101111111011", 0, 0),
                ("00111010111111", "00111010111111", 0, 0), ("01010111111111", "01010111111111", 0, 0),
                ("01011010111111", "01011010111111", 0, 0), ("01111011111111", "01111011111111", 0, 0)]
# The census traps of more than 3,000 states of period 15, in the same form; checked in parts in
# `Rule30Open.Columns.CensusTrapsLarge15`.
CENSUS_LARGE15 = [("000000001010101", "000000001010101", 0, 0), ("000000001101001", "000000001101001", 0, 0),
                  ("000000001111111", "000000001111111", 0, 0), ("000000010010001", "000000010010001", 0, 0),
                  ("000000100011011", "000000100011011", 0, 0), ("000000100101011", "000000100101011", 0, 0),
                  ("000000110010111", "000000110010111", 0, 0), ("000000110111001", "000000110111001", 0, 0),
                  ("000000111100001", "000000111100001", 0, 0), ("000001001011001", "000001001011001", 0, 0),
                  ("000001101000101", "000001101000101", 0, 0), ("000001101111011", "000001101111011", 0, 0),
                  ("000010011111111", "000010011111111", 0, 0), ("000011011111001", "000011011111001", 0, 0),
                  ("000100101111001", "000100101111001", 0, 0), ("000101111111001", "000101111111001", 0, 0),
                  ("000110111111011", "000110111111011", 0, 0), ("000111111110101", "000111111110101", 0, 0),
                  ("001011101011101", "001011101011101", 0, 0), ("001011111110111", "001011111110111", 0, 0),
                  ("001101100111111", "001101100111111", 0, 0), ("001111110110111", "001111110110111", 0, 0),
                  ("010111110111111", "010111110111111", 0, 0), ("011011011111111", "011011011111111", 0, 0)]


def tables(name: str) -> dict:
    """The tables of a trap of `TRAPS` or `NATURAL`."""
    for entry in TRAPS:
        if entry[0] == name:
            return trap_tables(*entry[1:])
    entry = next(entry for entry in NATURAL if entry[0] == name)
    return natural_tables(*entry[1:])


def lean_number(x: int, piece: int = 0) -> str:
    """A natural number as a Lean term: its literal, or with `piece` > 0 the sum of its pieces of `piece` bits, each
    shifted into place, since Lean reads a literal digit by digit, in time quadratic in its length."""
    digits = sys.get_int_max_str_digits()
    sys.set_int_max_str_digits(0)  # the packed tables have up to hundreds of thousands of digits
    try:
        if not piece or x >> piece == 0:
            return str(x)
        parts = [(x >> (piece * k)) & ((1 << piece) - 1) for k in range((x.bit_length() + piece - 1) // piece)]
        return " +\n      ".join([str(parts[0])] + [f"{part} <<< {piece * k}" for k, part in enumerate(parts) if k])
    finally:
        sys.set_int_max_str_digits(digits)


def lean_entry(t: dict, name: str, piece: int = 0) -> str:
    """The Lean definition of a trap `WTrap` from its tables, packed as the kit packs `t001`, with the packed numbers
    in pieces of `piece` bits when `piece` > 0 (`lean_number`)."""
    n = len(t["states"])
    lb, ib = max(1, (t["modulus"] - 1).bit_length()), max(1, (n - 1).bit_length())
    windows = sum(window << (t["cells"] * i) for i, (_, window) in enumerate(t["states"]))
    labels = sum(label << (lb * i) for i, (label, _) in enumerate(t["states"]))
    nexts = sum(j << (ib * e) for e, j in enumerate(t["successors"]))
    block = ", ".join("true" if c == "1" else "false" for c in t["word"])
    windows, labels, nexts = lean_number(windows, piece), lean_number(labels, piece), lean_number(nexts, piece)
    return (f"/-- The block `{t['word']}`: {t['cells']} cells, labels modulo {t['modulus']}, {n} states. -/\n"
            f"def {name} : WTrap :=\n"
            f"  {{ b := [{block}], K := {t['cells']}, m := {t['modulus']}, n := {n}, lb := {lb}, ib := {ib},\n"
            f"    u := {t['first']},\n    R := {windows},\n    L := {labels},\n    S := {nexts} }}\n")


def back_tables(traps: tuple[dict, ...], width: int) -> dict:
    """The nodes of the game of `width` cells that can reach the traps (`reach_nodes`), by label modulo the block's
    period, each label's windows in increasing order, and the least node outside them: the set that
    `Rule30Open.Columns.ReachRefuted` checks closed under predecessors."""
    word = traps[0]["word"]
    reach = reach_nodes(traps, width).reshape(len(word), 1 << width)  # (p, n)
    rows = [np.flatnonzero(reach[label]).tolist() for label in range(len(word))]
    l0, w0 = divmod(int(np.flatnonzero(~reach.reshape(-1))[0]), 1 << width)
    return {"word": word, "cells": width, "rows": rows, "miss": (l0, w0)}


def lean_back(name: str, trap: str, s: dict, piece: int = 0, part: int = 512) -> str:
    """The declarations of `Rule30Open.Columns.ReachRefuted` for one trap of another module: the set `name` of
    `back_tables`, the check of each label's windows in parts of `part`, one kernel check each, that the set holds the
    trap's states, and the refutation of entry into the trap `trap`."""
    block = ", ".join("true" if c == "1" else "false" for c in s["word"])
    cells, period = s["cells"], len(s["word"])
    sizes = ", ".join(str(len(row)) for row in s["rows"])
    rows = ",\n      ".join(lean_number(sum(w << (cells * i) for i, w in enumerate(row)), piece) for row in s["rows"])
    total = sum(len(row) for row in s["rows"])
    l0, w0 = s["miss"]
    out = [f"/-- The windows of {cells} cells from which the trap `{trap}` can be reached, by label: {total:,} of the "
           f"{period << cells:,} nodes of the game. -/\n"
           f"def {name} : WinSet :=\n  {{ b := [{block}], K := {cells},\n    sizes := [{sizes}],\n"
           f"    rows := [{rows}] }}\n"]
    for label, row in enumerate(s["rows"]):
        full, rest = divmod(len(row), part)
        for k in range(full):
            out.append(f"theorem {name}_{label}_{k} : WinSet.allRangeT ({name}.backOK {label}) ({part} * {k}) {part} = "
                       f"true := by\n  decide +kernel\n")
        out.append(f"theorem {name}_{label}_{full} : WinSet.allRangeT ({name}.backOK {label}) ({part} * {full}) {rest} "
                   f"= true := by\n  decide +kernel\n")
        cases = "".join(f"      | {k}, _ => {name}_{label}_{k}\n" for k in range(full))
        out.append(f"theorem {name}_{label} : Rule30EtherThree.allBelowT ({name}.backOK {label}) "
                   f"({name}.cnt {label}) = true :=\n  WinSet.allBelowT_of_forall fun i hi => WinSet.allRange_cover "
                   f"(c := {part}) "
                   f"(q := {full}) (r := {rest}) (by decide)\n"
                   f"    (fun k hk =>\n      match k, hk with\n{cases}"
                   f"      | _ + {full}, h => absurd h (by omega))\n"
                   f"    {name}_{label}_{full} i (by have h : i < {len(row)} := hi; omega)\n")
    out.append(f"theorem {name}_check : {name}.check = true :=\n"
               f"  WinSet.check_of_labels _ (by decide) (by decide) fun l hl =>\n"
               f"    match l, hl with\n" + "".join(f"    | {label}, _ => {name}_{label}\n" for label in range(period)) +
               f"    | _ + {period}, h => absurd h (by show ¬ _ < {period}; omega)\n")
    out.append(f"theorem {name}_holds : {name}.holds {trap} = true := by decide +kernel\n")
    out.append(f"/-- **Some finitely supported right half driven by `{s['word']}` never enters `{trap}`.** -/\n"
               f"theorem {trap}_not_absorption_back : ¬ {trap}.Absorption :=\n"
               f"  not_absorption_back _ {name} rfl (by decide) {name}_check {name}_holds {l0} {w0} "
               f"(by decide +kernel)\n")
    return "\n".join(out)


def cut_rows(traps: tuple[dict, ...], width: int) -> list[list[int]]:
    """The traps' states cut to their first `width` cells, by label modulo the block's period, each label's windows in
    increasing order: the set `WinSet.holds` checks in `Rule30Open.Columns.ReachRefuted`."""
    period = len(traps[0]["word"])
    rows = [set() for _ in range(period)]
    for t in traps:
        for label, window in t["states"]:
            rows[label % period].add(window & ((1 << width) - 1))
    return [sorted(row) for row in rows]


def fwd_tables(traps: tuple[dict, ...], width: int) -> dict:
    """A closed set apart from the traps when they fail the test of reach at `width` cells: the least strongly connected
    component that no move leaves among the nodes that cannot reach them (`reach_nodes`), as tables
    (`relabeled_tables`), with labels modulo the block's period."""
    word = traps[0]["word"]
    away = np.flatnonzero(~reach_nodes(traps, width)).astype(np.uint64)  # (a,)
    target = np.searchsorted(away, successors(word, width, away).reshape(-1))  # (2 a,), into `away`: no move leaves
    source = np.tile(np.arange(away.size), 2)  # (2 a,)
    graph = csr_matrix((np.ones(source.size, dtype=np.int8), (source, target)), shape=(away.size, away.size))
    _, label = connected_components(graph, directed=True, connection="strong")  # (a,)
    leaves = np.zeros(label.max() + 1, dtype=bool)  # (components,)
    leaves[label[source][label[source] != label[target]]] = True
    sizes = np.bincount(label)  # (components,)
    best = min((c for c in range(label.max() + 1) if not leaves[c]), key=lambda c: (sizes[c], c))
    low = (1 << width) - 1
    return relabeled_tables(word, width, {(int(k) >> width, int(k) & low) for k in away[label == best].tolist()})


def kit_t001() -> dict:
    """The kit's trap `t001` for 001 as tables (`relabeled_tables`): 815 states of 47 cells, labels modulo 21."""
    return relabeled_tables("001" * 7, 47, {(label, strip) for strip, label in t001_states()})


# Two more traps for 001, chain locks of seeds of period 21 with a long run of 1s that `short_scan` finds (`rest` 15 at
# width 9 and `rest` 12 at width 5, periods 15 to 33): name in `Rule30Open.Columns.Traps001`, seed, the seed's lock
# width, the distance and the seed's lock values. With the kit's `t001` and `trap001fifteen` they are four traps
# pairwise apart (`apart_closed`); the scans' other traps for 001 lie inside the lift of the one of 304 cells.
TRAPS_001 = [("trap001b", "010111111111111110111", 9, 135, "000000000000000000000"),
             ("trap001c", "000000101110111111111", 5, 299, "011111000000000000000")]


def traps001_tables() -> list[tuple[str, dict]]:
    """The four traps for 001 pairwise apart, by their names in `Rule30Open.Columns.Traps001`: the kit's `t001`
    (`t001W`), `trap001fifteen` and the two of `TRAPS_001`."""
    out = [("t001W", kit_t001()), ("trap001fifteen", tables("trap001fifteen"))]
    return out + [(name, trap_tables(seed, width, distance, values)) for name, seed, width, distance, values in TRAPS_001]


# The seeds that `scan001` tries: periods, the width of the locked window and the most cells outside the run of 1s; the
# second list goes on to longer periods, and wider windows, and takes about an hour.
SCAN001 = (([15, 18, 21, 24, 27, 30, 33], 5, 12), ([15, 18, 21, 24], 9, 15))
SCAN001_WIDER = (([36, 39, 42, 45, 48], 5, 12), ([27, 30, 33], 9, 15))


def scan001(depth: int = 3000, plans: tuple = SCAN001) -> list[tuple[str, str, int, int]]:
    """The seeds with a long run of 1s whose chain has a column 001 within `depth` (`short_scan` with each `rest` and
    width of `plans`, by default 12 at width 5 for periods 15 to 33 and 15 at width 9 for periods 15 to 24): (seed, lock
    values, lock width, distance), each seed and its values once, with the narrower lock when both widths find it."""
    found = {}
    for periods, width, rest in plans:
        for seed, entries in short_scan(periods, width, depth, rest=rest).items():
            for values, hits in entries:
                if 3 in hits and hits[3][1] == "001":
                    found.setdefault((seed, values), (width, hits[3][0]))
    return [(seed, values, width, distance) for (seed, values), (width, distance) in found.items()]


def lean_winset(name: str, word: str, width: int, rows: list[list[int]], piece: int = 0) -> str:
    """A set of windows of `Rule30Open.Columns.ReachRefuted` (`WinSet`): each label's windows in increasing order."""
    block = ", ".join("true" if c == "1" else "false" for c in word)
    sizes = ", ".join(str(len(row)) for row in rows)
    packed = ", ".join(lean_number(sum(w << (width * i) for i, w in enumerate(row)), piece) for row in rows)
    return (f"def {name} : WinSet :=\n  {{ b := [{block}], K := {width},\n    sizes := [{sizes}],\n"
            f"    rows := [{packed}] }}\n")


def apart_traps(pairs: list[tuple[str, tuple[str, str], tuple[str, str], int]] | None = None) -> list[
        tuple[str, str, str, str, str]]:
    """The traps of the trap modules that pass the test of reach (not in `UNREACHED` or `UNREACHED_WIDE`) and of
    halves apart (not in `APART`), outside `MissedTraps`, the pairs and the sets, that another trap of their block
    refutes with all of its states (`apart_pairs`): (block, module, name, the other's module, its name), the first
    such other, in the order of `block_traps`; from `pairs` when given, the result of `apart_pairs`."""
    lists = (UNREACHED, APART, UNREACHED_WIDE)
    found = {}
    for block, (ma, na), (mb, nb), size in apart_pairs() if pairs is None else pairs:
        if ma in ("MissedTraps", "TrapPairs", "TrapSets", "Traps001") or (ma, na) in found:
            continue
        if any(block in refuted.get(ma, ()) for refuted in lists) or re.fullmatch(r"natw[01]+_\d", na):
            continue
        other = named_tables(mb, nb) if mb != "Traps001" else kit_t001()
        if size == len(other["states"]):
            found[(ma, na)] = (block, mb, nb)
    return [(block, ma, na, mb, nb) for (ma, na), (block, mb, nb) in found.items()]


def apart_refuted() -> dict[str, list[str]]:
    """The traps of `APART_TRAPS` by module, as the blocks of their traps, in the form of `UNREACHED`."""
    found: dict[str, list[str]] = {}
    for block, module, *_ in APART_TRAPS:
        found.setdefault(module, []).append(block)
    return found


def chain_apart(periods: tuple[int, ...] = (16, 20, 24, 28, 32, 36, 40), width: int = 5, rest: int = 12,
                depth: int = 3000) -> list[tuple[str, str, int, str, str, int]]:
    """The chain locks of the seeds with a long run of 1s (`short_scan` with `rest`) whose chain reaches a block with a
    trap in Lean (`block_traps`), each a trap of that block (`trap_tables`), that are apart as a whole from a trap of
    the block in Lean (`apart_closed`), so that entry into that trap is false: (block, seed, distance, module, name,
    cells of the chain trap)."""
    blocks = block_traps()
    out = []
    for seed, entries in short_scan(list(periods), width, depth, rest=rest).items():
        for values, hits in entries:
            for distance, word in hits.values():
                if word not in blocks:
                    continue
                t = trap_tables(seed, width, distance, values)
                for module, name, lean in blocks[word]:
                    if apart_closed(lean, t).all():
                        out.append((word, seed, distance, module, name, t["cells"]))
    return out


def chain_family(block: str, periods: tuple[int, ...] = (16, 20, 24, 28, 32, 36, 40), width: int = 5, rest: int = 12,
                 depth: int = 3000, lean: list[tuple[str, dict]] | None = None) -> tuple[list[tuple[str, dict]],
                                                                                         list[int]]:
    """The traps of `block` in Lean (`lean`, or those of `block_traps`) and the chain locks of the seeds with a long run
    of 1s that reach it (`short_scan` with `rest`), each as (name, tables); and a family of them pairwise apart as
    wholes (`apart_closed` both ways), chosen greedily from those apart from the most others, as indices."""
    if lean is None:
        lean = [(name, t) for _, name, t in block_traps().get(block, [])]
    traps = list(lean)
    traps += [(f"chain{seed}@{distance}", trap_tables(seed, width, distance, values))
              for seed, entries in short_scan(list(periods), width, depth, rest=rest).items()
              for values, hits in entries for distance, word in hits.values() if word == block]
    n = len(traps)
    apart = [[i != j and bool(apart_closed(traps[j][1], traps[i][1]).all()) for j in range(n)] for i in range(n)]
    mutual = [[apart[i][j] and apart[j][i] for j in range(n)] for i in range(n)]
    family: list[int] = []
    for i in sorted(range(n), key=lambda i: (-sum(mutual[i]), i)):
        if all(mutual[i][j] for j in family):
            family.append(i)
    return traps, family


def lean_check_names() -> set[str]:
    """The names `x` of the traps with a theorem `x_check` in the Lean modules of `Rule30Open/Columns`."""
    root = Path(__file__).resolve().parents[1] / "Rule30Open" / "Columns"
    found = set()
    for path in root.glob("*.lean"):
        found |= set(re.findall(r"^theorem (\w+)_check :", path.read_text(encoding="utf-8"), re.M))
    return found


def lean_apart_traps(piece: int = 1 << 16) -> str:
    """The declarations of `Rule30Open.Columns.ApartTraps`: for each entry of `APART_TRAPS`, that the other trap is
    closed, the refuted trap's states cut to the narrower width (`cut_rows`), that they hold its states and that the
    other trap avoids them, the refutation of entry (`not_absorption_fwd`), and the reduction of the block to entry
    into one of the two (`absorption_some_excludes`)."""
    entries = {(m, n): b for m, n, b in module_entries()}
    checks = lean_check_names()
    out = []
    for block, module, name, other_module, other in APART_TRAPS:
        c, s = entries[(module, name)](), entries[(other_module, other)]()
        assert c["word"] == block and apart_closed(c, s).all()
        word, width, cert = c["word"], min(c["cells"], s["cells"]), f"apart_{name}"
        block = ", ".join("true" if ch == "1" else "false" for ch in word)
        closed = f"WTrap.closedCheck_of_check _ {other}_check" if other in checks else "by decide +kernel"
        check_other = f"exact {other}_check" if other in checks else "decide +kernel"
        check_name = f"exact {name}_check" if name in checks else "decide +kernel"
        out.append(f"theorem {cert}_closed : {other}.closedCheck = true :=\n  {closed}\n\n"
                   f"/-- The states of `{name}` cut to {width} cells, by label. -/\n"
                   + lean_winset(cert, word, width, cut_rows((c,), width), piece)
                   + f"\ntheorem {cert}_holds : {cert}.holds {name} = true := by\n  decide +kernel\n\n"
                   f"theorem {cert}_avoids : {cert}.avoids {other} = true := by\n  decide +kernel\n\n"
                   f"/-- **Entry into `{name}` is false**: the right half of state 0 of `{other}` never enters it. "
                   f"-/\ntheorem {name}_not_absorption_apart : ¬ {name}.Absorption :=\n"
                   f"  not_absorption_fwd _ {other} {cert} {cert}_closed rfl rfl (by decide)\n"
                   f"    (by decide) {cert}_holds {cert}_avoids (by decide)\n\n"
                   f"/-- The two traps of `{word}`. -/\ndef pair_{word} : List WTrap := [{other}, {name}]\n\n"
                   f"/-- **`{word}` reduced to entry into one of its two traps.** -/\n"
                   f"theorem pair_{word}_excludes (hA : WTrap.AbsorptionSome pair_{word}) :\n"
                   f"    ¬ Rule30StripCertificates.EventuallyWord\n      [{block}] := by\n"
                   f"  refine absorption_some_excludes _ pair_{word} ?_ ?_ hA <;>\n"
                   f"    simp only [pair_{word}, List.mem_cons, List.not_mem_nil, or_false] <;> rintro C (rfl | rfl)\n"
                   f"  · rfl\n  · rfl\n  · {check_other}\n  · {check_name}\n")
    return "\n".join(out)


def lean_traps001(piece: int = 1 << 16) -> str:
    """The declarations of `Rule30Open.Columns.Traps001` for the two traps of `TRAPS_001`: each with its kernel check;
    for each of the four traps for 001 and each other, the other's states cut to the narrower width (`cut_rows`), that
    they hold its states and that the first trap avoids them; and, for each of the four, the refutation of entry into
    one of the other three (`not_absorption_some_fwd`)."""
    traps = traps001_tables()
    out = []
    for name, t in traps[2:]:
        out.append(lean_entry(t, name, piece) + f"\ntheorem {name}_check : {name}.check = true := by decide +kernel\n")
    for name, t in traps:
        if name not in ("t001W", "trap001fifteen"):
            out.append(f"theorem {name}_closed : {name}.closedCheck = true := by decide +kernel\n")
    for s_name, s in traps:
        others = [(c_name, c) for c_name, c in traps if c_name != s_name]
        for c_name, c in others:
            width = min(s["cells"], c["cells"])
            cert = f"cert_{s_name}_{c_name}"
            out.append(f"/-- The states of `{c_name}` cut to {width} cells, by label. -/\n"
                       + lean_winset(cert, c["word"], width, cut_rows((c,), width), piece)
                       + f"\ntheorem {cert}_holds : {cert}.holds {c_name} = true := by\n  decide +kernel\n\n"
                       f"theorem {cert}_avoids : {cert}.avoids {s_name} = true := by\n  decide +kernel\n")
        names = ", ".join(c_name for c_name, _ in others)
        cases = "\n".join(f"  · exact ⟨cert_{s_name}_{c_name}, rfl, rfl, by decide, by decide,\n"
                          f"      cert_{s_name}_{c_name}_holds, cert_{s_name}_{c_name}_avoids⟩" for c_name, _ in others)
        listed = ", ".join(f"`{c_name}`" for c_name, _ in others)
        out.append(f"/-- **Entry into one of {listed} is false**: the right half of state 0 of\n"
                   f"`{s_name}` never enters any. -/\n"
                   f"theorem {s_name}_not_absorption_some : ¬ WTrap.AbsorptionSome [{names}] := by\n"
                   f"  refine not_absorption_some_fwd _ {s_name} {s_name}_closed (by decide) ?_\n"
                   f"  simp only [List.mem_cons, List.not_mem_nil, or_false]\n"
                   f"  rintro C (rfl | rfl | rfl)\n{cases}\n")
    return "\n".join(out)


def block_traps() -> dict[str, list[tuple[str, str, dict]]]:
    """Every trap checked in Lean, by block, as (module, name of its declaration, tables): the traps of
    `module_entries`, the two of each block of `PAIRS` (`Rule30Open.Columns.TrapPairs`) and of `WALL_SPLIT`
    (`Rule30Open.Columns.NaturalTrapsWalls`), the natural traps of `TRAP_SETS` (`Rule30Open.Columns.TrapSets`), and the
    kit's `t001` (`t001W` of `Rule30Open.Columns.Traps001`)."""
    found: dict[str, list[tuple[str, str, dict]]] = {}
    entries = [(module, name, build()) for module, name, build in module_entries()]
    entries += [("TrapPairs", f"pair{block}_{k}", t) for block in PAIRS for k, t in enumerate(pair_tables(block))]
    entries += [("NaturalTrapsWalls", f"natw{word}_{k}", t) for word, _ in WALL_SPLIT
                for k, t in enumerate(split_tables(word))]
    entries += [entry for block, *_ in TRAP_SETS for entry in set_tables(block) if entry[0] == "TrapSets"]
    entries.append(("Traps001", "t001W", kit_t001()))
    for module, name, t in tqdm(entries, desc="traps", file=sys.stderr, leave=False):
        found.setdefault(t["word"], []).append((module, name, t))
    return found


def apart_closed(a: dict | list[dict], b: dict) -> np.ndarray:
    """The states of the trap `b` in its largest subset that every move, under both values of the cell beyond, keeps
    inside, among the states whose windows, cut to the narrower of the two traps, are not those of a state of the trap
    `a` whose label reads the same phase, or of any trap of `a` when it is a list: a mask over b's states. When it is
    not empty, a right half started in one of them stays in the subset and never enters `a`, or any of them."""
    period = len(b["word"])
    alive = np.ones(len(b["states"]), dtype=bool)  # (n,)
    for other in a if isinstance(a, list) else [a]:
        mask = (1 << min(other["cells"], b["cells"])) - 1
        cut = {(label % period, window & mask) for label, window in other["states"]}
        alive &= np.array([(label % period, window & mask) not in cut for label, window in b["states"]])  # (n,)
    moves = np.array(b["successors"]).reshape(-1, 2)  # (n, 2)
    while True:
        kept = alive & alive[moves[:, 0]] & alive[moves[:, 1]]  # (n,)
        if (kept == alive).all():
            return alive  # (n,)
        alive = kept


def apart_pairs() -> list[tuple[str, tuple[str, str], tuple[str, str], int]]:
    """For every two traps of one block among `block_traps`, a closed set of states of one apart from the other
    (`apart_closed`), which refutes entry into the other: (block, (module, name) refuted, (module, name) of the trap
    that holds the set, its number of states) for each such ordered pair."""
    out = []
    for block, traps in sorted(block_traps().items()):
        for ma, na, a in traps:
            for mb, nb, b in traps:
                if (ma, na) != (mb, nb):
                    size = int(apart_closed(a, b).sum())
                    if size:
                        out.append((block, (ma, na), (mb, nb), size))
    return out


def lean_fwd(name: str, trap: str, s: dict, rows: list[list[int]], piece: int = 0) -> str:
    """The declarations of `Rule30Open.Columns.ReachRefuted` for a closed set `s` apart from the trap `trap` of another
    module (`fwd_tables`): the set with its check that it is closed, the trap's states cut to its width (`cut_rows`),
    that they hold the trap's states and that the closed set avoids them, and the refutation of entry."""
    block = ", ".join("true" if c == "1" else "false" for c in s["word"])
    cells = s["cells"]
    sizes = ", ".join(str(len(row)) for row in rows)
    packed = ", ".join(lean_number(sum(w << (cells * i) for i, w in enumerate(row)), piece) for row in rows)
    body = lean_entry(s, f"{name}", piece).split("\n", 1)[1]
    return (f"/-- A closed set apart from `{trap}`: windows of {cells} cells, labels modulo {s['modulus']}, "
            f"{len(s['states'])} states. -/\n{body}\n"
            f"theorem {name}_closed : {name}.closedCheck = true := by decide +kernel\n\n"
            f"/-- The states of `{trap}` cut to {cells} cells, by label. -/\n"
            f"def {name}_cut : WinSet :=\n  {{ b := [{block}], K := {cells},\n    sizes := [{sizes}],\n"
            f"    rows := [{packed}] }}\n\n"
            f"theorem {name}_holds : {name}_cut.holds {trap} = true := by decide +kernel\n\n"
            f"theorem {name}_avoids : {name}_cut.avoids {name} = true := by decide +kernel\n\n"
            f"/-- **Some finitely supported right half driven by `{s['word']}` never enters `{trap}`.** -/\n"
            f"theorem {trap}_not_absorption_fwd : ¬ {trap}.Absorption :=\n"
            f"  not_absorption_fwd _ {name} {name}_cut {name}_closed rfl rfl (by decide) (by decide)\n"
            f"    {name}_holds {name}_avoids (by decide)\n")


@functools.lru_cache(maxsize=None)
def wide_wall(module: str, name: str) -> dict:
    """The wall of `WIDE_WALLS` found for the carried trap `name` of `module`: the least closed set among the nodes of
    the game of `WIDE_WIDTH` cells that cannot reach it (`fwd_tables`), on which column 1 is fixed at the white phases,
    so a trap of the same block."""
    t = next(build() for m, n, build in module_entries() if (m, n) == (module, name))
    return fwd_tables((t,), WIDE_WIDTH)


def lean_wide_walls(piece: int = 1 << 16) -> str:
    """The declarations of `Rule30Open.Columns.WideWalls` after its header: for each entry of `WIDE_WALLS`, the wall
    with its kernel check and the refutation of entry into the carried trap from it (`lean_fwd`); the refutation of
    entry into the wall from the carried trap, which is apart from it as a whole (`apart_closed`); and the reduction of
    the block to entry into one of the two. Then the list of the walls, its check and its blocks."""
    entries = {(m, n): b for m, n, b in module_entries()}
    checks = lean_check_names()
    out, names = [], []
    for module, name in WIDE_WALLS:
        t, wall = entries[(module, name)](), wide_wall(module, name)
        assert apart_closed(wall, t).all()
        word, cert, wide = t["word"], f"wide_{name}_apart", f"wide_{name}"
        names.append(wide)
        block = ", ".join("true" if c == "1" else "false" for c in word)
        closed = f"WTrap.closedCheck_of_check _ {name}_check" if name in checks else "by decide +kernel"
        check_name = f"exact {name}_check" if name in checks else "decide +kernel"
        out.append(lean_fwd(wide, name, wall, cut_rows((t,), WIDE_WIDTH), piece)
                   + f"\ntheorem {wide}_check : {wide}.check = true := by decide +kernel\n\n"
                   f"theorem {name}_closed_wide : {name}.closedCheck = true :=\n  {closed}\n\n"
                   f"/-- The states of `{wide}`, by label. -/\n"
                   + lean_winset(cert, word, WIDE_WIDTH, cut_rows((wall,), WIDE_WIDTH), piece)
                   + f"\ntheorem {cert}_holds : {cert}.holds {wide} = true := by\n  decide +kernel\n\n"
                   f"theorem {cert}_avoids : {cert}.avoids {name} = true := by\n  decide +kernel\n\n"
                   f"/-- **Entry into `{wide}` is false**: the right half of state 0 of `{name}` never enters it. -/\n"
                   f"theorem {wide}_not_absorption : ¬ {wide}.Absorption :=\n"
                   f"  not_absorption_fwd _ {name} {cert} {name}_closed_wide rfl rfl (by decide)\n"
                   f"    (by decide) {cert}_holds {cert}_avoids (by decide)\n\n"
                   f"/-- The carried trap and the wall of `{word}`. -/\n"
                   f"def widePair_{word} : List WTrap := [{name}, {wide}]\n\n"
                   f"/-- **`{word}` reduced to entry into the carried trap or its wall.** -/\n"
                   f"theorem widePair_{word}_excludes (hA : WTrap.AbsorptionSome widePair_{word}) :\n"
                   f"    ¬ Rule30StripCertificates.EventuallyWord\n      [{block}] := by\n"
                   f"  refine absorption_some_excludes _ widePair_{word} ?_ ?_ hA <;>\n"
                   f"    simp only [widePair_{word}, List.mem_cons, List.not_mem_nil, or_false] <;> "
                   f"rintro C (rfl | rfl)\n"
                   f"  · rfl\n  · rfl\n  · {check_name}\n  · exact {wide}_check\n")
    blocks = ",\n     ".join("[" + ", ".join("true" if c == "1" else "false" for c in wide_wall(m, n)["word"]) + "]"
                               for m, n in WIDE_WALLS)
    checks_list = ", ".join(f"{wall}_check" for wall in names)
    out.append(f"/-- The walls. -/\ndef wideWalls : List WTrap :=\n  [{', '.join(names)}]\n\n"
               f"theorem wideWalls_check : wideWalls.all WTrap.check = true := by\n"
               f"  simp only [wideWalls, List.all_cons, List.all_nil, Bool.and_true, {checks_list}]\n\n"
               f"theorem wideWalls_blocks : wideWalls.map WTrap.b =\n    [{blocks}] := rfl\n")
    return "\n".join(out)


def lean_back_module(piece: int = 1 << 16, part: int = 1024) -> str:
    """The declarations of `Rule30Open.Columns.ReachRefuted` after its general part: for each entry of
    `REACH_REFUTED`, the windows that can reach the trap (`back_tables`, `lean_back`) or a closed set apart from it
    (`fwd_tables`, `lean_fwd`), at its width, and the refutation of entry into it."""
    entries = {(module, name): build for module, name, build in module_entries()}
    out = []
    for module, name, width, kind in REACH_REFUTED:
        t = entries[(module, name)]()
        if kind == "back":
            out.append(lean_back(f"back_{name}", name, back_tables((t,), width), piece, part))
        else:
            out.append(lean_fwd(f"fwd_{name}", name, fwd_tables((t,), width), cut_rows((t,), width), piece))
    return "\n".join(out)


def lean_trap(name: str) -> str:
    """The Lean entry `WTrap` for a trap of `TRAPS` or `NATURAL`, with its kernel check."""
    return lean_entry(tables(name), name) + f"\ntheorem {name}_check : {name}.check = true := by decide +kernel\n"


def chain_distances(name: str, period: int, depth: int) -> list[int]:
    """The least distance below `depth` at which the chain of the natural trap `name` holds each block of `period`."""
    seen, found = set(), []
    for distance in range(depth):
        word = carried(name, distance)["word"]
        if len(word) == period and word not in seen:
            seen.add(word)
            found.append(distance)
    return found


def nine_distances() -> list[int]:
    """The least distance at which the chain of the period-9 wall `001011111` holds each block of period 9."""
    return chain_distances("trap001011111", 9, 30)


def ten_distances() -> list[int]:
    """The least distance at which the chain of the period-10 wall `0000010001` holds each block of period 10 that
    the kit does not exclude; the chain repeats with period 155 in the distance, and every block in it appears by
    distance 30."""
    return [d for d in chain_distances("trap0000010001", 10, 31)
            if carried("trap0000010001", d)["word"] not in game.KIT_WORDS]


def ten_entry(cells: int, steps: int) -> list[tuple[int, str, int, np.ndarray]]:
    """For each trap of `TenTraps`, by its distance along the chain of the period-10 wall: its block, its width, and the
    entry step (`entry_steps`) of each right half with support in cells 1 .. `cells`, driven from each phase, or -1."""
    halves = list(range(1 << cells))
    found = []
    for distance in tqdm(ten_distances(), desc="distances", file=sys.stderr):
        t = carried("trap0000010001", distance)
        times = np.concatenate([entry_steps(t, halves, phase, steps) for phase in range(10)])  # (10 2^cells,)
        found.append((distance, t["word"], t["cells"], times))
    return found


def trap_member(t: dict) -> np.ndarray:
    """The states of a labelled trap as membership masks by phase of its block, for `coin_lock`: a label counts by its
    phase, as entry (`WTrap.Absorption`) does."""
    # out: (period, 2^cells)
    member = np.zeros((len(t["word"]), 1 << t["cells"]), dtype=bool)  # (period, 2^cells)
    for label, window in t["states"]:
        member[label % len(t["word"]), window] = True
    return member


def ten_member() -> np.ndarray:
    """The states of the period-10 wall `ten0` as membership masks by phase, for `coin_lock`."""
    # out: (10, 2^16)
    return trap_member(carried("trap0000010001", 0))


def trap_coin(word: str, member: np.ndarray, steps: int = 12000, limit: int | None = None) -> dict:
    """A trap against a fair coin in the column beyond its window (`coin_lock`): the longest of the shortest entry
    paths, the largest and the mean (at phase 0) expected entry time, the decay factor per step, the largest chance of
    staying out after `steps` steps, the length of a word of the column beyond that brings every window at phase 0 in,
    and for each value the number of windows that a constant column beyond leaves outside after 3,000 steps from phase
    0. When some window cannot enter, the expected entry, the decay and the word are left out (None). `limit` caps the
    power iteration of `coin_lock.decay_rate`."""
    from computations import coin_lock
    from computations.lock_certificate import successor_table
    # member: (period, 2^W)
    width = member.shape[1].bit_length() - 1
    dist, _ = coin_lock.entry_paths(word, member)  # (period, 2^W)
    reachable = bool((dist < coin_lock.UNREACHED).all())
    successors = successor_table(word, width)  # (period, 2, 2^W)
    constant = []
    for value in (0, 1):
        windows = np.arange(1 << width)  # (2^W,)
        for t in range(3000):
            windows = successors[t % len(word), value][windows]
        constant.append(int((~member[3000 % len(word)][windows]).sum()))
    found = {"reachable": reachable, "longest_path": int(dist[dist < coin_lock.UNREACHED].max()),
             "stay_out": float(coin_lock.stay_out(word, member, steps).max()), "constant": constant,
             "expected_max": None, "expected_mean": None, "decay": None, "word": None}
    if reachable:
        expected = coin_lock.expected_entry(word, member)  # (period, 2^W)
        found.update(expected_max=float(expected.max()), expected_mean=float(expected[0].mean()),
                     decay=coin_lock.decay_rate(word, member, limit=limit),
                     word=len(coin_lock.universal_word(word, member)))
    return found


def ten_coin(steps: int = 12000) -> dict:
    """The period-10 wall against a fair coin in column 17 (`trap_coin`)."""
    return trap_coin("0000010001", ten_member(), steps)


def natural_coin(steps: int = 12000, limit: int = 2000) -> Iterator[tuple[str, dict]]:
    """`trap_coin` for each trap of 16 cells of `EXTRA_TRAPS`, with a fair coin in column 17, the power iteration
    capped at `limit` periods; yields (block, results) one trap at a time."""
    for word, _, cells, _ in tqdm(EXTRA_TRAPS, desc="natural traps", file=sys.stderr):
        if cells == 16:
            yield word, trap_coin(word, trap_member(extra_tables(word)), steps, limit)


def natural_coin_widths(widths: tuple[tuple[int, int], ...] = ((16, 5000), (18, 2000), (20, 600))) -> Iterator[
        tuple[str, list[float]]]:
    """For each trap of 16 cells of `EXTRA_TRAPS`, the factor per step by which the chance of staying out falls with a
    fair coin in the column after a game of each width, the trap taken as the windows that begin with its states
    (`trap_nodes`): `coin_lock.period_rate`, an upper bound wherever its iteration stops, capped at the paired number
    of steps. Yields (block, factors) one trap at a time."""
    from computations import coin_lock
    for word, _, cells, _ in tqdm(EXTRA_TRAPS, desc="natural traps", file=sys.stderr):
        if cells == 16:
            t = extra_tables(word)
            yield word, [coin_lock.period_rate(word, trap_nodes((t,), width).reshape(len(word), 1 << width),
                                               tolerance=1e-10, limit=limit) for width, limit in widths]


def ten_lengths(lengths: list[int], count: int = 60, steps: int = 100000) -> list[tuple[int, np.ndarray]]:
    """Entry steps into the period-10 wall of `count` random right halves of each length (from
    `numpy.random.default_rng(30)`, the last cell black), driven from phases 0 and 5."""
    rng = np.random.default_rng(30)
    t = carried("trap0000010001", 0)
    found = []
    for length in lengths:
        halves = [int("".join(str(b) for b in rng.integers(0, 2, length)), 2) | (1 << (length - 1))
                  for _ in range(count)]
        found.append((length, np.concatenate([entry_steps(t, halves, phase, steps) for phase in (0, 5)])))
    return found


def gap_entries(name: str, cells: int = 8, steps: int = 50000) -> list[list[tuple[int, int]]]:
    """For each phase of the natural trap `name` and each right half r with support in cells 1 .. `cells` (bit i is
    column i + 1), the first step T at which the run of r driven from that phase has its first cells in a state of the
    trap with the label of its phase, and that state's index in the sorted states of the trap's Lean definition."""
    t = carried(name, 0)
    word, period, width = t["word"], len(t["word"]), t["cells"]
    index = {state: k for k, state in enumerate(t["states"])}
    out = []
    for phase in range(period):
        row_entries = []
        for r in range(1 << cells):
            row = r
            for step in range(steps + 1):
                k = index.get(((step + phase) % period, row & ((1 << width) - 1)))
                if k is not None:
                    row_entries.append((step, k))
                    break
                row = ((row << 1) | int(word[(step + phase) % period])) ^ (row | (row >> 1))
            else:
                raise ValueError(f"half {r} from phase {phase} does not enter by step {steps}")
        out.append(row_entries)
    return out


def ten_gap_entries(cells: int = 8, steps: int = 50000) -> list[list[tuple[int, int]]]:
    """`gap_entries` for the period-10 wall `ten0`."""
    return gap_entries("trap0000010001", cells, steps)


def lean_gap(name: str, trap: str, bound: int, prefix: str) -> str:
    """The entry data of a gap module for the natural trap `name`, whose Lean definition is `trap`: for each phase, the
    step and the state of each half of `gap_entries`, with the kernel check of the phase against the bound."""
    blocks = []
    for phase, entries in enumerate(gap_entries(name)):
        items = [f"({step}, {k})" for step, k in entries]
        lines, line = [], "    "
        for j, item in enumerate(items):
            piece = item + (", " if j + 1 < len(items) else "]")
            if len(line) + len(piece.rstrip()) > 120:
                lines.append(line.rstrip())
                line = "    "
            line += piece
        lines.append(line)
        blocks.append(f"/-- The entry step and state of each right half of at most eight cells, from phase {phase}. -/\n"
                      f"def {prefix}{phase} : List (Nat × Nat) := [\n" + "\n".join(lines) + "\n\n"
                      f"set_option maxHeartbeats 0 in\ntheorem {prefix}{phase}_ok : gapEntriesOk {trap} {phase} {bound} "
                      f"{prefix}{phase} = true := by\n  decide +kernel\n\ntheorem {prefix}{phase}_len : {prefix}{phase}.length = "
                      f"2 ^ 8 := by decide +kernel\n")
    return "\n".join(blocks)


def lean_ten_gap() -> str:
    """The entry data of `Rule30Open.Columns.TenGap`."""
    return lean_gap("trap0000010001", "ten0", 3058, "tenGap")


# The walls of `Rule30Open.Columns.WallGaps`: the trap, its Lean definition, the bound (the latest entry plus 16) and
# the prefix of the entry lists.
WALL_GAPS = [("trap00000011011", "el0_0", 1610, "elGap"), ("trap001011100111", "tw0_0", 2357, "twGap")]


# Natural traps of periods 10 to 12 for blocks that the kit and the finite game do not exclude and no wall of TenTraps,
# ElevenTraps or TwelveTraps carries, for `Rule30Open.Columns.NaturalTraps`: the block, a right half that a run of it
# drives into the trap at step 12,000 (the white half, or one of `right_half.random_starts(30, 64)`), the width and the
# modulus. For each block the natural scan of periods 10 to 12 finds one trap, the same for every start that enters
# one up to a shift of the labels by a multiple of the period. `LARGE_TRAPS` holds the 35th, of 61,857 states, for
# `Rule30Open.Columns.NaturalTrapsLarge` (`lean_large`).
EXTRA_TRAPS = [("0001010101", 6991680298694716019, 31, 20), ("0010010101", 15376576670725646791, 40, 30),
               ("0011010101", 18202347099481127113, 26, 20), ("00000000101", 0, 16, 11), ("00000010001", 0, 16, 11),
               ("00000011101", 0, 16, 11), ("00000110011", 0, 16, 11), ("00000110101", 0, 16, 22),
               ("00001111011", 2921701138199145236, 22, 22), ("00010011101", 0, 16, 11), ("00011111111", 0, 16, 11),
               ("00110011111", 0, 16, 11), ("00111111011", 0, 16, 11), ("00111111101", 0, 16, 11),
               ("01101111111", 0, 16, 22), ("01110111111", 0, 16, 11), ("000000001011", 0, 16, 12),
               ("000001001101", 0, 16, 12), ("000001100011", 0, 16, 12), ("000001101011", 0, 16, 12),
               ("000001111011", 0, 16, 12), ("000010010001", 0, 16, 12), ("000010101001", 0, 16, 12),
               ("000011011011", 0, 16, 12), ("000011111111", 0, 16, 12), ("000101001001", 12475343592431589197, 44, 24),
               ("000101101011", 0, 16, 12), ("001001101111", 0, 16, 12), ("001011011111", 0, 16, 12),
               ("001011111011", 0, 16, 12), ("001110111101", 0, 16, 12), ("001111101111", 0, 16, 12),
               ("010101010111", 0, 16, 12), ("010111111011", 0, 16, 12)]
LARGE_TRAPS = [("00010001011", 0, 30, 22)]
# Natural traps of periods 13 and 14 for blocks that the kit and the game do not exclude and that the walls of
# `ThirteenTraps` and `FourteenTraps` do not carry, for `Rule30Open.Columns.NaturalTrapsLong`: as `EXTRA_TRAPS`, from
# the natural scan with windows of 16 cells, the smallest trap of each block, those of at most 3,000 states.
LONG_TRAPS = [("0000000010001", 0, 16, 13), ("0000000110011", 0, 16, 13), ("0000001000101", 0, 16, 13),
              ("0000001010111", 0, 16, 13), ("0000001101011", 0, 16, 13),
              ("0000001101111", 6648364488764846871, 16, 13), ("0000011011001", 0, 16, 13),
              ("0000100001111", 0, 16, 13), ("0000100101001", 0, 16, 13), ("0000110111011", 0, 16, 13),
              ("0000111001101", 0, 16, 13), ("0000111011001", 0, 16, 13), ("0000111101001", 0, 16, 13),
              ("0001001111101", 0, 16, 13), ("0001010111111", 0, 16, 13), ("0001011101111", 0, 16, 13),
              ("0001011111011", 0, 16, 13), ("0001100011011", 0, 16, 13),
              ("0001101111001", 0, 16, 13), ("0001111110011", 0, 16, 13),
              ("0010010110101", 0, 16, 13),
              ("0010011010111", 0, 16, 13), ("0010101011101", 0, 16, 13),
              ("0010110101111", 0, 16, 13),
              ("0010111101111", 0, 16, 13), ("0011001110101", 0, 16, 13), ("0011001111011", 0, 16, 13),
              ("0011001111111", 0, 16, 13), ("0011010110111", 0, 16, 13), ("0011011111011", 0, 16, 13),
              ("0111011111111", 0, 16, 13), ("00000001001101", 0, 16, 14), ("00000001101011", 0, 16, 14),
              ("00000010001101", 0, 16, 14), ("00000011011001", 0, 16, 14), ("00000100000101", 0, 16, 14),
              ("00000101011011", 0, 16, 14), ("00000110001111", 0, 16, 14), ("00000111011011", 0, 16, 14),
              ("00001000101111", 0, 16, 14), ("00001001011001", 0, 16, 14), ("00001010100111", 0, 16, 14),
              ("00001011011001", 0, 16, 14), ("00001011100111", 0, 16, 14), ("00001011111011", 0, 16, 14),
              ("00001101111011", 0, 16, 14), ("00001111101001", 0, 16, 14),
              ("00001111101111", 0, 16, 14), ("00010010010111", 0, 16, 14), ("00010110101011", 0, 16, 14),
              ("00010110111111", 0, 16, 14), ("00010111101011", 0, 16, 14), ("00011010110011", 0, 16, 14),
              ("00011011010111", 0, 16, 14), ("00011100111101", 0, 16, 14), ("00011110100111", 0, 16, 14),
              ("00011110110011", 0, 16, 14), ("00011111001111", 6648364488764846871, 16, 14),
              ("00100100101111", 0, 16, 14), ("00100110110111", 0, 16, 14), ("00101011101111", 0, 16, 14),
              ("00101011110101", 0, 16, 14), ("00101101010011", 0, 16, 14), ("00101101011101", 0, 16, 14),
              ("00101101111111", 0, 16, 14), ("00110111111011", 0, 16, 14), ("00111010110111", 0, 16, 14),
              ("00111110111101", 0, 16, 14), ("01010101011111", 0, 16, 14), ("01101111110111", 0, 16, 14)]
# The natural traps of periods 13 and 14 of more than 3,000 states that `LONG_TRAPS` leaves out and that the census of
# locked windows does not already hold as a component (`CENSUS_LARGE` holds the other 22): every sampled half is
# inside each at step 12,000. Checked in parts in `Rule30Open.Columns.NaturalTrapsLongLarge`.
LONG_LARGE = [("0000001011011", 0, 16, 13), ("0000001101001", 0, 16, 13), ("0000010111011", 0, 16, 13),
              ("0000010111111", 0, 16, 13), ("0000110111001", 0, 16, 13), ("0010100101111", 0, 16, 13),
              ("0101011111111", 0, 16, 13), ("0110110111111", 0, 16, 13), ("00000001111111", 0, 16, 14),
              ("00000011110111", 0, 16, 14), ("00011111110101", 0, 16, 14), ("01011111111011", 0, 16, 14)]


# Traps that some finitely supported right half never enters, since some node of the game cannot reach them
# (`trap_reach`), taken out of the lists above and below: the natural traps of four blocks of periods 13 and 14, in the
# form of `LONG_TRAPS`, and the census traps of three blocks of periods 13 and 15, in that of `CENSUS_TRAPS`.
# `Rule30Open.Columns.MissedTraps` checks each and refutes its entry with a closed set of windows apart from it
# (`miss_tables`).
MISSED_NATURAL = [("0001101101011", 0, 16, 13), ("0010010010111", 6648364488764846871, 16, 13),
                  ("0010101111111", 6991680298694716019, 16, 13), ("00001101111001", 0, 16, 14)]
MISSED_CENSUS = [("0000010111001", "0000010111001", 0, 0), ("000001010110101", "000001010110101", 0, 0),
                 ("001001111010111", "001001111010111", 0, 0)]
# The traps of the modules that the test of reach refutes (`reach_census` at `REACH_WIDTH` cells): some node of the
# finite game of that width cannot reach a window whose first cells form a state of the trap, cut to that width when
# the trap is wider, so a right half whose first cells start there never enters the trap, and entry, the hypothesis of
# the trap's reduction, is false. By module, the blocks of those traps; the seven of `MISSED_NATURAL` and
# `MISSED_CENSUS`, refuted in Lean, are not repeated.
REACH_WIDTH = 20
UNREACHED = {
    "CensusTraps13": ["0000001100111", "0000001101001", "0000010100111", "0000011001011", "0000110011011",
                      "0000110111001", "0000111111001", "0001000110011", "0001010100101", "0001011010101",
                      "0001011010111", "0001011111001", "0001100011111", "0001100101001", "0001101011011",
                      "0010100111101", "0011010100111", "0011010111111", "0011101101011", "0011101110111",
                      "0011110111011", "0011111101111", "0101010111011", "0101011010111", "0101011111111"],
    "CensusTraps14": ["00000001111111", "00000011010001", "00000011110111", "00000100111001", "00000110110101",
                      "00001000011111", "00001000101101", "00001010001001", "00001010001111", "00001011000101",
                      "00001011101111", "00001100101001", "00001100101011", "00010011100011", "00010011111001",
                      "00010100110111", "00010101011001", "00011011010011", "00011111110101", "00100110101101",
                      "00100111001111", "00100111101011", "00100111111101", "00101010100111", "00101011001101",
                      "00110011011101", "00111001111111", "00111011111011", "01010111111011", "01011011010111"],
    "CensusTraps15": ["000000000001001", "000000010001001", "000000010010011", "000000010111001", "000000011110111",
                      "000000100010111", "000000101011001", "000000101110001", "000000110001001", "000000110110101",
                      "000001000010011", "000001111110101", "000010000101001", "000010001011111", "000010011000111",
                      "000010101011001", "000010101101111", "000010110010101", "000010110101011", "000010111100101",
                      "000010111101001", "000010111111001", "000011110011001", "000011110100111", "000100100011001",
                      "000101001011001", "000101100111001", "000101100111101", "000101111101011", "000101111101111",
                      "000110010110101", "000110100111001", "000110110011111", "000110110110111", "000111010101111",
                      "000111010111101", "000111011011001", "000111011011011", "000111011100101", "000111101101101",
                      "000111101110011", "001001001011011", "001001011111111", "001001101111111", "001001111101111",
                      "001010010111111", "001010011010011", "001011010010111", "001011011011111", "001100110110101",
                      "001110011101011", "001110101111111", "001110111110101", "010110101111111", "011011101101111",
                      "011011111101111"],
    "ElevenTraps": ["00000001011", "00000101111", "00000110001", "00001000111", "00001001101", "00001100101",
                    "00001101001", "00001101011", "00001101101", "00001111001", "00001111111", "00010100101",
                    "00011010011", "00011011001", "00011100111", "00011110011", "00011111001", "00100111011",
                    "00101101111", "00110111011", "00110111111", "00111010111", "00111011011", "01010101011",
                    "01011101111", "01011111011", "01111011111"],
    "FarWalls": ["000000011111", "010101111111"],
    "FourteenTraps": ["00000000010001", "00000000110011", "00000001010111", "00000100001111", "00000101010111",
                      "00000111001101", "00001000010001", "00001000011101", "00001100011011", "00001111010101",
                      "00001111101011", "00010011111101", "00010101111111", "00010110010101", "00010110100101",
                      "00011011011101", "00011110111001", "00100101100101", "00100110111111", "00101101101101",
                      "00101110011111", "00101111101111", "00110011111111", "00110111100111", "00111001110101",
                      "00111010011111", "00111011011101", "00111011101111", "01110111111111"],
    "NaturalTrapsLong": ["0001111110011", "0010011010111"],
    "NineTraps": ["000001101", "000011001", "000100101", "000110011", "001101111", "001110111", "011101111"],
    "TenTraps": ["0000000001", "0000000101", "0000011101", "0000100111", "0000110011", "0000111111", "0001010111",
                 "0001011111", "0001111111", "0011001111", "0011111101", "0111011111"],
    "ThirteenTraps": ["0000000100001", "0000001001101", "0000001111111", "0000011000111", "0000100101101",
                      "0000101001001", "0000101011001", "0000101110111", "0000110011101", "0000111011011",
                      "0000111101111", "0001001110111", "0001010001011", "0001011100111", "0001011101011",
                      "0001110010011", "0001111101111", "0010010100111", "0010011110101", "0010110111111",
                      "0010111101101", "0101010101111"],
    "TwelveTraps": ["000000010001", "000000011101", "000000101101", "000000110011", "000001000111", "000001010111",
                    "000001011011", "000010011111", "000100101111", "000100111011", "000100111101", "000101001111",
                    "000101011111", "000110011001", "000110110101", "000111001101", "000111110011", "001001100101",
                    "001001101011", "001011010111", "001011101111", "001100111111", "001101101111", "001111111101",
                    "010110111111", "011101111111"],
    "WordTraps": ["01", "001"],
}
# Blocks of periods 13 and 14 whose locked windows of 16 cells have two bottom components, with different values of
# column 1 at the white phases, neither of which every node of the game can reach, while every node can reach one of
# the two (`trap_reach` on both): the natural traps of `MISSED_NATURAL` are one of each pair.
# `Rule30Open.Columns.TrapPairs` reduces each block to entry into one of its two components (`pair_tables`).
PAIRS = ["0001101101011", "0010010010111", "0010101111111", "00001101111001"]


# Traps that fail the test of reach and whose refutation `Rule30Open.Columns.ReachRefuted` checks: module, the trap's
# name in Lean, the width, and the kind, "back" from the windows that can reach the trap (`back_tables`) or "fwd" from
# a closed set apart from it (`fwd_tables`).
REACH_REFUTED = [("MissedTraps", "cen000001010110101", 8, "back"), ("TwelveTraps", "tw0_40", 22, "back"),
                 ("ElevenTraps", "el1_22", 22, "back"), ("CensusTraps14", "cen00000110101111", 22, "back"),
                 ("CensusTraps13", "cen0000010000111", 22, "back"), ("FourteenTraps", "fo0_46", 22, "back"),
                 ("CensusTraps15", "cen000011110101001", 22, "back"), ("CensusTraps15", "cen000011011110111", 22, "back"),
                 ("CensusTraps15", "cen000100101010101", 22, "back"), ("CensusTraps13", "cen0000001011101", 22, "back"),
                 ("ElevenTraps", "el1_23", 22, "back"), ("TwelveTraps", "tw1_30", 22, "back"),
                 ("ThirteenTraps", "th0_18", 22, "back")]
WIDE_WIDTH = 22
# Walls of 22 cells: traps carried along a background's columns that fail the test of reach at `WIDE_WIDTH` cells
# while most nodes can reach them, by module and name in Lean. For each, the least closed set among the nodes that
# cannot (`wide_wall`) has column 1 fixed at the white phases, every node can reach it, and it and the carried trap
# are apart as wholes; `Rule30Open.Columns.WideWalls` checks it and reduces the block to entry into one of the two.
WIDE_WALLS = [("ElevenTraps", "el0_33"), ("FourteenTraps", "fo0_30"), ("FourteenTraps", "fo0_31")]
# The hypotheses that pass both tests at `REACH_WIDTH` cells but fail the test of reach in the game of `WIDE_WIDTH`
# cells (`wide_reach`, which tries the natural traps, the large census components, the pairs and the sets, and
# `wide_reach_carried`, which tries the traps carried along a chain): by module, the blocks of those traps, or of the
# pair of `WALL_SPLIT` for 00101101111.
UNREACHED_WIDE = {
    "CensusTraps13": ["0000001011101", "0000010000111", "0001101011001", "0010100101101"],
    "CensusTraps14": ["00000110101111", "00000110111001", "00111010101111", "00111110110111", "00111111011011"],
    "CensusTraps15": ["000010001000101", "000011011110111", "000011110101001", "000100101010101", "000101001001001",
                      "000111000111001", "001001011011011", "001001111001111", "010110111011011"],
    "ElevenTraps": ["00001011001", "00001100111", "00100100101"],
    "FifteenWalls": ["000010101011001", "000010110010101"],
    "FourteenTraps": ["00010100100011", "00111011110101", "01010101111011"],
    "NaturalTrapsLongLarge": ["0101011111111"],
    "NaturalTrapsWalls": ["00101101111", "0010011110101"],
    "TenTraps": ["0101111011"],
    "ThirteenTraps": ["0010010011101"],
    "TwelveTraps": ["000010101011", "000100110101", "000101100111"],
    "WordTraps": ["001011"],
}

# The traps of the modules, and the pairs, that pass the test of reach but that a half of their block's natural scan,
# closing windows of 16 to 64 cells, never enters: at step 12,000 the half is inside a closed set apart from the trap,
# or from both traps of a pair (`halves_apart`), so entry is false. By module, the blocks of those traps.
APART = {
    "CensusTraps13": ["0001010101001"],
    "CensusTraps14": ["00100110111101"],
    "CensusTraps15": ["000000110011101", "000000111101001", "000001101011101", "000010001000111", "000011100100111",
                      "000100010100011", "000100100010111", "000100101100111", "000100111001011", "000110101001001",
                      "000111010011101", "000111011110011", "000111110101101", "000111111011101"],
    "ElevenTraps": ["00001000101", "00110100111"],
    "FourteenTraps": ["00000100100111", "00001011101001"],
    "NaturalTrapsLong": ["00001011100111"],
    "ThirteenTraps": ["0000010101101", "0000100001011", "0000110110001", "0001011110111", "0001110101101",
                      "0011011011011"],
    "TrapPairs": ["0001101101011"],
    "TwelveTraps": ["000001110101"],
}

# Traps that pass the tests of reach and of halves apart while another trap of their block, wider than the games
# tested, holds a closed set apart from them, all of its states (`apart_closed`), so entry into each is false, and the
# block comes down to entry into one of the two, in `Rule30Open.Columns.ApartTraps`: (block, module, name, the other
# trap's module, its name), from `apart_traps`.
APART_TRAPS = [
    ("0000000001", "NaturalTrapsWalls", "natw0000000001", "TenTraps", "ten23"),
    ("0000011101", "NaturalTrapsWalls", "natw0000011101", "TenTraps", "ten25"),
    ("0001111111", "NaturalTrapsWalls", "natw0001111111", "TenTraps", "ten26"),
    ("0011111101", "NaturalTrapsWalls", "natw0011111101", "TenTraps", "ten24"),
    ("00000001011", "NaturalTrapsWalls", "natw00000001011", "ElevenTraps", "el0_20"),
    ("00001001101", "NaturalTrapsWalls", "natw00001001101", "ElevenTraps", "el0_24"),
    ("00001101011", "NaturalTrapsWalls", "natw00001101011", "ElevenTraps", "el0_22"),
    ("00001111111", "NaturalTrapsWalls", "natw00001111111", "ElevenTraps", "el0_19"),
    ("00111010111", "NaturalTrapsWalls", "natw00111010111", "ElevenTraps", "el0_11"),
    ("01010101011", "NaturalTrapsWalls", "natw01010101011", "ElevenTraps", "el0_25"),
    ("01011111011", "NaturalTrapsWalls", "natw01011111011", "ElevenTraps", "el0_21"),
    ("01111011111", "NaturalTrapsWalls", "natw01111011111", "ElevenTraps", "el0_26"),
    ("000000010001", "NaturalTrapsWalls", "natw000000010001", "TwelveTraps", "tw1_40"),
    ("000000011101", "NaturalTrapsWalls", "natw000000011101", "TwelveTraps", "tw1_34"),
    ("000000110011", "NaturalTrapsWalls", "natw000000110011", "TwelveTraps", "tw1_38"),
    ("000100111101", "NaturalTrapsWalls", "natw000100111101", "TwelveTraps", "tw2_13"),
    ("000111001101", "NaturalTrapsWalls", "natw000111001101", "TwelveTraps", "tw2_14"),
    ("001100111111", "NaturalTrapsWalls", "natw001100111111", "TwelveTraps", "tw1_39"),
    ("001111111101", "NaturalTrapsWalls", "natw001111111101", "TwelveTraps", "tw1_33"),
    ("010110111111", "NaturalTrapsWalls", "natw010110111111", "TwelveTraps", "tw1_20"),
    ("011101111111", "NaturalTrapsWalls", "natw011101111111", "TwelveTraps", "tw1_37"),
    ("0000001001101", "NaturalTrapsWalls", "natw0000001001101", "ThirteenTraps", "th0_50"),
    ("0000011000111", "NaturalTrapsWalls", "natw0000011000111", "ThirteenTraps", "th0_53"),
    ("0000111011011", "NaturalTrapsWalls", "natw0000111011011", "ThirteenTraps", "th0_15"),
    ("0001111101111", "NaturalTrapsWalls", "natw0001111101111", "ThirteenTraps", "th0_52"),
    ("0010110111111", "NaturalTrapsWalls", "natw0010110111111", "ThirteenTraps", "th0_49"),
    ("0101010101111", "NaturalTrapsWalls", "natw0101010101111", "ThirteenTraps", "th0_51"),
    ("00000000010001", "NaturalTrapsWalls", "natw00000000010001", "FourteenTraps", "fo0_19"),
    ("00000000110011", "NaturalTrapsWalls", "natw00000000110011", "FourteenTraps", "fo0_17"),
    ("00000001010111", "NaturalTrapsWalls", "natw00000001010111", "FourteenTraps", "fo0_23"),
    ("00000100001111", "NaturalTrapsWalls", "natw00000100001111", "FourteenTraps", "fo0_57"),
    ("00000111001101", "NaturalTrapsWalls", "natw00000111001101", "FourteenTraps", "fo0_21"),
    ("00001100011011", "NaturalTrapsWalls", "natw00001100011011", "FourteenTraps", "fo0_25"),
    ("00010011111101", "NaturalTrapsWalls", "natw00010011111101", "FourteenTraps", "fo0_20"),
    ("00010101111111", "NaturalTrapsWalls", "natw00010101111111", "FourteenTraps", "fo0_22"),
    ("00100101100101", "NaturalTrapsWalls", "natw00100101100101", "FourteenTraps", "fo0_66"),
    ("00100110111111", "NaturalTrapsWalls", "natw00100110111111", "FourteenTraps", "fo0_69"),
    ("00101111101111", "NaturalTrapsWalls", "natw00101111101111", "FourteenTraps", "fo0_24"),
    ("00110011111111", "NaturalTrapsWalls", "natw00110011111111", "FourteenTraps", "fo0_18"),
    ("01110111111111", "NaturalTrapsWalls", "natw01110111111111", "FourteenTraps", "fo0_16"),
    ("0000001101001", "NaturalTrapsLongLarge", "nat0000001101001", "CensusTraps13", "cen0000001101001"),
    ("0000110111001", "NaturalTrapsLongLarge", "nat0000110111001", "CensusTraps13", "cen0000110111001"),
    ("00000001111111", "NaturalTrapsLongLarge", "nat00000001111111", "CensusTraps14", "cen00000001111111"),
    ("00000011110111", "NaturalTrapsLongLarge", "nat00000011110111", "CensusTraps14", "cen00000011110111"),
    ("00011111110101", "NaturalTrapsLongLarge", "nat00011111110101", "CensusTraps14", "cen00011111110101"),
    ("000000101011001", "FifteenWalls", "fw1_11", "CensusTraps15", "cen000000101011001"),
    ("001001111101111", "FifteenWalls", "fw1_106", "CensusTraps15", "cen001001111101111"),
    ("000010000101001", "FifteenWalls", "fw1_109", "CensusTraps15", "cen000010000101001"),
]

# Blocks whose every trap in the trap modules, and pair, is refuted by a half apart (`APART`), reduced instead to entry
# into one of a set of traps: the block's traps in the modules by name (`named_tables`), and the natural traps its
# halves are inside that none of those is, each as (start, cells, modulus) of `EXTRA_TRAPS`. Every node of the game of
# 20 cells can reach one of them, and every half of the scan is inside one. Checked in `Rule30Open.Columns.TrapSets`.
TRAP_SETS = [("00001000101", [("ElevenTraps", "el0_5")], [(18429370810410311795, 22, 11)]),
             ("00110100111", [("ElevenTraps", "el1_0")], [(4728953243656014532, 21, 11)]),
             ("000001110101", [("TwelveTraps", "tw0_22")], [(4728953243656014532, 22, 12)]),
             ("0000010101101", [("ThirteenTraps", "th0_41")], [(4728953243656014532, 23, 13)]),
             ("0000100001011", [("ThirteenTraps", "th0_21")], [(12828593127923856452, 25, 13)]),
             ("0000110110001", [("ThirteenTraps", "th0_45")], [(13784866300695777546, 30, 13)]),
             ("0001010101001", [("CensusTraps13", "cen0001010101001")], [(6648364488764846871, 22, 13)]),
             ("0001011110111", [("ThirteenTraps", "th0_31")], [(4728953243656014532, 30, 26)]),
             ("0001101101011", [("TrapPairs", "pair0001101101011_0"), ("TrapPairs", "pair0001101101011_1")],
              [(18429370810410311795, 21, 13)]),
             ("0001110101101", [("ThirteenTraps", "th0_8")], [(12828593127923856452, 21, 13)]),
             ("0011011011011", [("ThirteenTraps", "th0_12")], [(8432205463714238596, 25, 13)]),
             ("00000100100111", [("FourteenTraps", "fo0_33")], [(0, 22, 14), (6648364488764846871, 27, 14)]),
             ("00001011100111", [("NaturalTrapsLong", "nat00001011100111")], [(13505850817731016314, 24, 14)]),
             ("00001011101001", [("FourteenTraps", "fo0_58")], [(4728953243656014532, 23, 14)]),
             ("00100110111101", [("CensusTraps14", "cen00100110111101")], [(0, 26, 14)]),
             ("000000110011101", [("CensusTraps15", "cen000000110011101")],
              [(0, 28, 15), (12131907666976161055, 42, 15)]),
             ("000000111101001", [("CensusTraps15", "cen000000111101001")],
              [(12828593127923856452, 24, 15), (16965863739456413490, 30, 15)]),
             ("000001101011101", [("CensusTraps15", "cen000001101011101")], [(6648364488764846871, 37, 15)]),
             ("000010001000111", [("CensusTraps15", "cen000010001000111")], [(6117052809311358181, 39, 15)]),
             ("000011100100111", [("CensusTraps15", "cen000011100100111")], [(0, 32, 15)]),
             ("000100010100011", [("CensusTraps15", "cen000100010100011")], [(12828593127923856452, 30, 15)]),
             ("000100100010111", [("CensusTraps15", "cen000100100010111")], [(6648364488764846871, 33, 15)]),
             ("000100101100111", [("CensusTraps15", "cen000100101100111")], [(4728953243656014532, 38, 15)]),
             ("000100111001011", [("CensusTraps15", "cen000100111001011")], [(16492533075233650793, 36, 15)]),
             ("000110101001001", [("CensusTraps15", "cen000110101001001")], [(17333691585517767718, 26, 15)]),
             ("000111010011101", [("CensusTraps15", "cen000111010011101")], [(12828593127923856452, 31, 15)]),
             ("000111011110011", [("CensusTraps15", "cen000111011110011")], [(4728953243656014532, 29, 15)]),
             ("000111110101101", [("CensusTraps15", "cen000111110101101")], [(12828593127923856452, 37, 15)]),
             ("000111111011101", [("CensusTraps15", "cen000111111011101")], [(0, 27, 15)])]

# Natural traps for blocks of periods 10 to 14 whose only traps, walls carried to them, fail the test of reach
# (`UNREACHED`): from the natural scans, the smallest closed set of windows that a sampled half driven by the block is
# inside at step 12,000, when it passes the test at 20 cells and no half of the scan is inside a closed set apart from
# it, in the form of `EXTRA_TRAPS`. Checked in `Rule30Open.Columns.NaturalTrapsWalls`, those of more than 3,000 states
# in parts.
WALL_NATURAL = [("0000000001", 0, 16, 10), ("0000000101", 0, 16, 10), ("0000011101", 0, 16, 10),
                ("0000110011", 0, 16, 10), ("0001111111", 0, 16, 10), ("0011001111", 0, 16, 10),
                ("0011111101", 0, 16, 10), ("0111011111", 0, 16, 10), ("00000001011", 0, 16, 11),
                ("00001001101", 0, 16, 11), ("00001101001", 0, 16, 11), ("00001101011", 0, 16, 11),
                ("00001101101", 0, 18, 11), ("00001111001", 12475343592431589197, 16, 11), ("00001111111", 0, 16, 11),
                ("00111010111", 0, 16, 11), ("00111011011", 12828593127923856452, 17, 11), ("01010101011", 0, 16, 11),
                ("01011111011", 0, 16, 11), ("01111011111", 0, 16, 11), ("000000010001", 0, 16, 12),
                ("000000011101", 0, 16, 12), ("000000110011", 0, 16, 12), ("000001010111", 0, 16, 12),
                ("000100111101", 4728953243656014532, 16, 12), ("000101011111", 0, 16, 12), ("000111001101", 0, 16, 12),
                ("001011101111", 0, 16, 12), ("001100111111", 0, 16, 12), ("001111111101", 0, 16, 12),
                ("010110111111", 0, 16, 12), ("011101111111", 0, 16, 12), ("0000001001101", 0, 16, 13),
                ("0000011000111", 0, 16, 13), ("0000111011011", 0, 16, 13), ("0001111101111", 0, 16, 13),
                ("0010011110101", 0, 16, 13), ("0010110111111", 0, 16, 13), ("0101010101111", 0, 16, 13),
                ("00000000010001", 0, 16, 14), ("00000000110011", 0, 16, 14), ("00000001010111", 0, 16, 14),
                ("00000100001111", 0, 16, 14), ("00000111001101", 0, 16, 14), ("00001000010001", 0, 16, 14),
                ("00001100011011", 0, 16, 14), ("00010011111101", 0, 16, 14), ("00010101111111", 0, 16, 14),
                ("00100101100101", 0, 16, 14), ("00100110111111", 0, 16, 14), ("00101111101111", 0, 16, 14),
                ("00110011111111", 0, 16, 14), ("00110111100111", 0, 16, 14), ("01110111111111", 0, 16, 14)]

# Blocks of the same kind whose sampled halves settle into two closed sets apart from each other, so that entry into
# either alone is false, while every node of the game of 20 cells can reach one of the two: the block and its two
# traps, the narrower first, each as (start, cells, modulus) of `EXTRA_TRAPS`. `NaturalTrapsWalls` reduces each block
# to entry into one of the two (`split_tables`).
WALL_SPLIT = [("0001010111", [(6648364488764846871, 19, 10), (0, 20, 10)]),
              ("00101101111", [(0, 16, 11), (12828593127923856452, 19, 11)]),
              ("000000101101", [(0, 17, 12), (12828593127923856452, 26, 12)]),
              ("000010011111", [(6991680298694716019, 16, 12), (0, 18, 24)]),
              ("0000001111111", [(0, 16, 13), (15376576670725646791, 25, 13)]),
              ("00101101101101", [(0, 16, 14), (1252019101295043734, 32, 14)])]


# Two walls of the background of 2,145 cells at period 15, wider than the 16 cells of the census of locked windows: the
# natural traps of 000111111011101 (27 cells, 193 states) and 000001101011101 (37 cells, 652 states), in the form of
# `EXTRA_TRAPS`. `Rule30Open.Columns.FifteenWalls` carries them, as (wall, distance), to the blocks of period 15 that no
# other trap that passes reaches, where the carried trap passes the test of reach at 20 cells and no half of the
# block's natural scan is apart from it.
FIFTEEN_WALLS = [("000111111011101", 0, 27, 15), ("000001101011101", 6648364488764846871, 37, 15)]
FIFTEEN_DISTANCES = [(0, 110), (1, 2), (1, 3), (1, 4), (1, 6), (1, 7), (1, 8), (1, 9), (1, 11), (1, 12), (1, 13),
                     (1, 14), (1, 15), (1, 16), (1, 18), (1, 19), (1, 20), (1, 22), (1, 23), (1, 24), (1, 25), (1, 28),
                     (1, 29), (1, 30), (1, 33), (1, 34), (1, 37), (1, 39), (1, 40), (1, 42), (1, 43), (1, 45), (1, 47),
                     (1, 48), (1, 50), (1, 51), (1, 52), (1, 55), (1, 56), (1, 57), (1, 59), (1, 60), (1, 61), (1, 62),
                     (1, 63), (1, 64), (1, 66), (1, 67), (1, 68), (1, 71), (1, 74), (1, 75), (1, 76), (1, 77), (1, 78),
                     (1, 80), (1, 81), (1, 82), (1, 84), (1, 85), (1, 86), (1, 87), (1, 88), (1, 90), (1, 91), (1, 92),
                     (1, 94), (1, 95), (1, 97), (1, 98), (1, 99), (1, 100), (1, 101), (1, 102), (1, 103), (1, 104),
                     (1, 105), (1, 106), (1, 107), (1, 109), (1, 110), (1, 111), (1, 116), (1, 117), (1, 119), (1, 120)]


@functools.lru_cache(maxsize=2)
def fifteen_wall(wall: int) -> dict:
    """The wall of `FIFTEEN_WALLS` as tables (`natural_tables`)."""
    word, start, cells, modulus = FIFTEEN_WALLS[wall]
    return natural_tables(word, start, 12000, cells, modulus)


def fifteen_tables(wall: int, distance: int) -> dict:
    """A wall of `FIFTEEN_WALLS` carried `distance` columns left by its chain (`carry`)."""
    return carry(fifteen_wall(wall), distance)


def lean_fifteen(piece: int = 1 << 16) -> str:
    """The traps of `Rule30Open.Columns.FifteenWalls`, one per entry of `FIFTEEN_DISTANCES`, named by the wall and the
    distance, each with its own kernel check."""
    out = []
    for wall, distance in FIFTEEN_DISTANCES:
        label = f"fw{wall}_{distance}"
        out.append(lean_entry(fifteen_tables(wall, distance), label, piece)
                   + f"\ntheorem {label}_check : {label}.check = true := by decide +kernel\n")
    return "\n".join(out)


def extra_tables(word: str) -> dict:
    """The trap of `EXTRA_TRAPS`, `LARGE_TRAPS`, `LONG_TRAPS`, `LONG_LARGE`, `MISSED_NATURAL` or `WALL_NATURAL` for
    the block, as tables (`natural_tables`)."""
    _, start, cells, modulus = next(entry for entry in EXTRA_TRAPS + LARGE_TRAPS + LONG_TRAPS + LONG_LARGE
                                    + MISSED_NATURAL + WALL_NATURAL if entry[0] == word)
    return natural_tables(word, start, 12000, cells, modulus)


def split_tables(word: str) -> list[dict]:
    """The two traps of `WALL_SPLIT` for the block, as tables (`natural_tables`)."""
    _, traps = next(entry for entry in WALL_SPLIT if entry[0] == word)
    return [natural_tables(word, start, 12000, cells, modulus) for start, cells, modulus in traps]


def halves_apart(t: dict, steps: int = 20000) -> list[tuple[int, int, int, int, bool]]:
    """For each half of the natural scan of the trap's block (`natural_scan`) that is inside a natural trap, that trap
    and whether it is apart from `t`: no state of it, cut to the narrower of the two widths, with its label modulo the
    period, is a state of `t` so cut. A half inside a trap apart from `t` never enters `t`. As (half, cells, modulus,
    size, apart)."""
    from computations import right_half
    word, period = t["word"], len(t["word"])
    starts = right_half.random_starts(30, 64)
    out = []
    for k, time, cells, modulus, size in natural_scan(word, steps)[1]:
        other = natural_tables(word, starts[k], time, cells, modulus)
        cut = (1 << min(cells, t["cells"])) - 1
        mine = {(label % period, window & cut) for label, window in t["states"]}
        out.append((k, cells, modulus, size, not mine & {(label % period, window & cut)
                                                        for label, window in other["states"]}))
    return out


def lean_extra(entries: list[tuple[str, int, int, int]] | None = None) -> str:
    """The traps of `Rule30Open.Columns.NaturalTraps`, one per entry of `EXTRA_TRAPS`, or of `NaturalTrapsLong` with
    `LONG_TRAPS`, each with its kernel check."""
    return "\n".join(lean_entry(extra_tables(word), f"nat{word}")
                     + f"\ntheorem nat{word}_check : nat{word}.check = true := by decide +kernel\n"
                     for word, *_ in (EXTRA_TRAPS if entries is None else entries))


def named_tables(module: str, name: str) -> dict:
    """The trap that `module_entries` names `name` in `module`, or a trap of a pair of `TrapPairs` (`pair<block>_<k>`)
    or `NaturalTrapsWalls` (`natw<block>_<k>`), as tables."""
    if module == "TrapPairs":
        block, index = name[4:].split("_")
        return pair_tables(block)[int(index)]
    if module == "NaturalTrapsWalls" and name.count("_") == 1:
        block, index = name[4:].split("_")
        return split_tables(block)[int(index)]
    return next(build() for m, n, build in module_entries() if (m, n) == (module, name))


def trap_chain(t: dict, depth: int) -> list[str]:
    """The blocks, each as its least rotation, of the columns at distances 0 to `depth` to the left of a trap's block in
    the chain that its lock carries (`chain`): the blocks a trap carried that far would be for."""
    full = t["word"] * (t["modulus"] // len(t["word"]))  # the block at the trap's labels
    values = "".join(str((t["first"] >> label) & 1) if full[label] == "0" else "0" for label in range(t["modulus"]))
    period = len(t["word"])
    return [min(c[:period][i:] + c[:period][:i] for i in range(period)) for c in chain(full, values, depth)]


def set_tables(block: str) -> list[tuple[str, str, dict]]:
    """The traps of the entry of `TRAP_SETS` for the block, as (module, name, tables): the traps of the trap modules by
    name (`named_tables`), then the natural traps, named `sets<block>_<k>` in `Rule30Open.Columns.TrapSets`."""
    _, named, natural = next(entry for entry in TRAP_SETS if entry[0] == block)
    out = [(module, name, named_tables(module, name)) for module, name in named]
    out += [("TrapSets", f"sets{block}_{k}", natural_tables(block, start, 12000, cells, modulus))
            for k, (start, cells, modulus) in enumerate(natural)]
    return out


def lean_trap_sets(part: int = 1024, piece: int = 1 << 16) -> str:
    """The natural traps of `Rule30Open.Columns.TrapSets`, those of each entry of `TRAP_SETS`: each with its kernel
    check, or, above 3,000 states, in parts (`lean_parts`)."""
    out = []
    for block, _, _ in TRAP_SETS:
        for module, name, t in set_tables(block):
            if module != "TrapSets":
                continue
            if len(t["states"]) > 3000:
                out.append(lean_parts(t, name, part, piece))
            else:
                out.append(lean_entry(t, name) + f"\ntheorem {name}_check : {name}.check = true := by decide +kernel\n")
    return "\n".join(out)


def lean_wall_natural(part: int = 1024, piece: int = 1 << 16) -> str:
    """The traps of `Rule30Open.Columns.NaturalTrapsWalls`, one per entry of `WALL_NATURAL` and two per entry of
    `WALL_SPLIT` (`natw<block>_0` and `_1`): each with its kernel check, or, above 3,000 states, in parts
    (`lean_parts`)."""
    traps = [(f"natw{word}", extra_tables(word)) for word, *_ in WALL_NATURAL]
    traps += [(f"natw{word}_{index}", t) for word, _ in WALL_SPLIT for index, t in enumerate(split_tables(word))]
    out = []
    for name, t in traps:
        if len(t["states"]) > 3000:
            out.append(lean_parts(t, name, part, piece))
        else:
            out.append(lean_entry(t, name) + f"\ntheorem {name}_check : {name}.check = true := by decide +kernel\n")
    return "\n".join(out)


def lean_large(part: int = 1024, piece: int = 1 << 16) -> str:
    """The trap of `Rule30Open.Columns.NaturalTrapsLarge`, the entry of `LARGE_TRAPS`: its packed numbers in pieces of
    `piece` bits (`lean_number`), and its check in parts of `part` states, one kernel check each (`allRangeT`), so that
    the kernel's tables of one part at a time are in memory, gathered by `allRange_cover` into `nat<block>_check`."""
    [(word, *_)] = LARGE_TRAPS
    return lean_parts(extra_tables(word), f"nat{word}", part, piece)


def lean_parts(t: dict, name: str, part: int = 1024, piece: int = 1 << 16) -> str:
    """A trap as `lean_entry` writes it, with its numbers in pieces of `piece` bits, and its check in parts of `part`
    states, one kernel check each (`allRangeT` of `Rule30Open.Columns.NaturalTrapsLarge`), gathered by
    `allRange_cover` into `<name>_check`."""
    full, rest = divmod(len(t["states"]), part)
    out = [lean_entry(t, name, piece)]
    for k, size in enumerate([part] * full + [rest]):
        out.append(f"set_option maxHeartbeats 0 in\ntheorem {name}_{k} : allRangeT {name}.nodeOK {part * k} {size} = true "
                   f":= by\n  decide +kernel\n")
    cases = "".join(f"  | {k}, _ => {name}_{k}\n" for k in range(full))
    out.append(f"/-- The first {full} parts, of {part} states each. -/\ntheorem {name}_parts : ∀ k, k < {full} → "
               f"allRangeT {name}.nodeOK ({part} * k) {part} = true\n{cases}  | _ + {full}, h => absurd h (by omega)\n")
    out.append(f"/-- **The trap passes the check**, gathered from its {full + 1} parts. -/\ntheorem {name}_check : "
               f"{name}.check = true := by\n  have hall := allRange_cover (by decide) {name}_parts {name}_{full}\n"
               f"  unfold WTrap.check\n  rw [allBelowT_of_forall (fun i hi => hall i (by\n    have : {name}.n = "
               f"{part} * {full} + {rest} := rfl\n    omega))]\n  decide\n")
    return "\n".join(out)


def extra_entry(cells: int, steps: int, entries: list[tuple[str, int, int, int]] | None = None) -> list[
        tuple[str, int, np.ndarray]]:
    """For each trap of `EXTRA_TRAPS` and `LARGE_TRAPS`, or of `entries`: its block, its width, and the entry step
    (`entry_steps`) of each right half with support in cells 1 .. `cells`, driven from each phase, or -1."""
    halves = list(range(1 << cells))
    found = []
    for word, *_ in tqdm(EXTRA_TRAPS + LARGE_TRAPS if entries is None else entries, desc="natural traps",
                         file=sys.stderr):
        t = extra_tables(word)
        times = np.concatenate([entry_steps(t, halves, phase, steps) for phase in range(len(word))])  # (P 2^cells,)
        found.append((word, t["cells"], times))
    return found


def wall_distances(period: int, depth: int) -> list[tuple[str, int, str]]:
    """The blocks of `period` that the walls of `WALLS` carry within `depth` columns, each once, at the first wall and
    the least distance that reaches it, leaving out the blocks the kit excludes: (wall, distance, block)."""
    seen, found = set(game.KIT_WORDS), []
    for name in WALLS[period]:
        for distance in range(depth + 1):
            word = carried(name, distance)["word"]
            if len(word) == period and word not in seen:
                seen.add(word)
                found.append((name, distance, word))
    return found


def walls_entry(period: int, cells: int, steps: int, depth: int = 40) -> list[tuple[str, int, str, int, np.ndarray]]:
    """For each trap of `wall_distances`: its wall, distance, block and width, and the entry step (`entry_steps`) of
    each right half with support in cells 1 .. `cells`, driven from each phase, or -1."""
    halves = list(range(1 << cells))
    found = []
    for name, distance, word in tqdm(wall_distances(period, depth), desc=f"traps of period {period}", file=sys.stderr):
        t = carried(name, distance)
        times = np.concatenate([entry_steps(t, halves, phase, steps) for phase in range(period)])  # (P 2^cells,)
        found.append((name, distance, word, t["cells"], times))
    return found


def census_entry(period: int, cells: int, steps: int) -> list[tuple[str, int, str, int, np.ndarray]]:
    """`walls_entry` for the traps of `CENSUS_TRAPS` of a period, with the block whose component each carries as its
    wall."""
    halves = list(range(1 << cells))
    found = []
    for entry in tqdm(CENSUS_TRAPS[period], desc=f"census traps of period {period}", file=sys.stderr):
        t = census_tables(entry)
        times = np.concatenate([entry_steps(t, halves, phase, steps) for phase in range(period)])  # (P 2^cells,)
        found.append((entry[1], entry[3], t["word"], t["cells"], times))
    return found


def far_entry(cells: int, steps: int) -> list[tuple[str, int, str, int, np.ndarray]]:
    """`walls_entry` for the traps of `FAR_WALLS`."""
    halves = list(range(1 << cells))
    found = []
    for period, entries in sorted(FAR_WALLS.items()):
        for name, distance in tqdm(entries, desc=f"far traps of period {period}", file=sys.stderr):
            t = carried(name, distance)
            times = np.concatenate([entry_steps(t, halves, phase, steps) for phase in range(period)])  # (P 2^cells,)
            found.append((name, distance, t["word"], t["cells"], times))
    return found


def lean_walls(period: int, depth: int, prefix: str, piece: int = 0, check: bool = False) -> str:
    """The trap definitions of `Rule30Open.Columns.ElevenTraps`, `TwelveTraps` or `ThirteenTraps`: each wall of the
    period carried to each distance of `wall_distances`, named by the prefix, the wall's index and the distance, with
    the packed numbers in pieces of `piece` bits (`lean_number`) and, with `check`, each with its own kernel check."""
    names = {name: k for k, name in enumerate(WALLS[period])}
    out = []
    for name, d, _ in wall_distances(period, depth):
        label = f"{prefix}{names[name]}_{d}"
        out.append(lean_entry(carried(name, d), label, piece)
                   + (f"\ntheorem {label}_check : {label}.check = true := by decide +kernel\n" if check else ""))
    return "\n".join(out)


def census_tables(entry: tuple[str, str, int, int]) -> dict:
    """The trap of an entry of `CENSUS_TRAPS`."""
    _, source, index, distance = entry
    return component_tables(source, 16, index, distance)


def lean_census(period: int, piece: int = 1 << 16) -> str:
    """The trap definitions of `Rule30Open.Columns.CensusTraps<period>`: each entry of `CENSUS_TRAPS` for the period,
    named by its block, with its own kernel check."""
    out = []
    for entry in CENSUS_TRAPS[period]:
        label = f"cen{entry[0]}"
        out.append(lean_entry(census_tables(entry), label, piece)
                   + f"\ntheorem {label}_check : {label}.check = true := by decide +kernel\n")
    return "\n".join(out)


def lean_long_large(part: int = 1024, piece: int = 1 << 16) -> str:
    """The traps of `Rule30Open.Columns.NaturalTrapsLongLarge`: each entry of `LONG_LARGE`, named by its block, checked
    in parts (`lean_parts`)."""
    return "\n".join(lean_parts(extra_tables(word), f"nat{word}", part, piece) for word, *_ in LONG_LARGE)


def lean_census_large(entries: list[tuple[str, str, int, int]] | None = None, part: int = 1024,
                      piece: int = 1 << 16) -> str:
    """The traps of `Rule30Open.Columns.CensusTrapsLarge`: each entry of `CENSUS_LARGE`, or of `entries` (those of
    `CensusTrapsLarge15` with `CENSUS_LARGE15`), named by its block, checked in parts (`lean_parts`)."""
    return "\n".join(lean_parts(census_tables(entry), f"cen{entry[0]}", part, piece)
                     for entry in (CENSUS_LARGE if entries is None else entries))


def lean_far(piece: int = 1 << 16) -> str:
    """The trap definitions of `Rule30Open.Columns.FarWalls`: each entry of `FAR_WALLS` carried, named by the period
    and the distance, with its own kernel check."""
    out = []
    for period, entries in sorted(FAR_WALLS.items()):
        for name, d in entries:
            label = f"far{period}_{d}"
            out.append(lean_entry(carried(name, d), label, piece)
                       + f"\ntheorem {label}_check : {label}.check = true := by decide +kernel\n")
    return "\n".join(out)


def lean_ten() -> str:
    """The trap definitions of `Rule30Open.Columns.TenTraps`: the wall of period 10 carried to each distance of
    `ten_distances`."""
    return "\n".join(lean_entry(carried("trap0000010001", d), f"ten{d}") for d in ten_distances())


def lean_nine() -> str:
    """The trap definitions of `Rule30Open.Columns.NineTraps`: the wall of period 9 carried to each distance of
    `nine_distances` but 0, whose trap is `trap001011111` of `WordTraps`. The module's second wall is
    `lean_trap("trap001010011")`."""
    return "\n".join(lean_entry(carried("trap001011111", d), f"nine{d}") for d in nine_distances() if d)


# The white half's runs that `Rule30Open.Columns.NineWhite` checks: a prefix for their names, the trap, the phase and
# the step at which the run is in the trap (`entry_steps` with --cells 0); and the length of a part of a run.
WHITE_RUNS = [("nwa", "trap001011111", 2, 119947), ("nwb", "trap001011111", 8, 201129),
              ("nwc", "trap001010011", 7, 91086), ("nwd", "trap001010011", 2, 169098)]
PART = 16384


def white_parts(word: str, phase: int, total: int, cells: int) -> tuple[list[int], list[int], list[int]]:
    """The run of the white right half driven by `word` from `phase`, cut into parts: the checkpoints 0, `PART`, 2
    `PART`, .., `total`, the number of cells of each that can still reach the first `cells` columns at step `total`
    (by the light cone, `total` - checkpoint + `cells`), and the rows at the checkpoints cut to those cells."""
    marks = list(range(0, total, PART)) + [total]
    need = [total - mark + cells for mark in marks]
    row, rows = 0, [0]
    for t in range(total):
        row = ((row << 1) | int(word[(t + phase) % len(word)])) ^ (row | (row >> 1))
        if t + 1 in marks:
            rows.append(row % (1 << need[len(rows)]))
    return marks, need, rows


def lean_white_run(prefix: str, name: str, phase: int, total: int) -> str:
    """The part of `Rule30Open.Columns.NineWhite` for one run: the rows at the checkpoints as literals, a kernel check
    of each part (`runDrive`), the chain of the parts (`part`) to a state of the trap, and the label of that state."""
    t = tables(name)
    word, cells = t["word"], t["cells"]
    marks, need, rows = white_parts(word, phase, total, cells)
    i = next(k for k, (label, window) in enumerate(t["states"])
             if window == rows[-1] and label % len(word) == (total + phase) % len(word))
    names = [f"{prefix}{j}" for j in range(1, len(marks) - 1)] + [f"{name}.st {i}"]
    digits = sys.get_int_max_str_digits()
    sys.set_int_max_str_digits(0)  # the rows have tens of thousands of digits
    try:
        out = [f"/-! ### `{word}` from phase {phase}: {total} steps in {len(marks) - 1} parts -/\n"]
        out += [f"def {names[j - 1]} : Nat := {rows[j]}\n" for j in range(1, len(marks) - 1)]
    finally:
        sys.set_int_max_str_digits(digits)
    previous = ["0"] + names[:-1]
    for j in range(1, len(marks)):
        out.append(f"theorem {prefix}_p{j} : runDrive {name}.b {marks[j] - marks[j - 1]} ({phase} + {marks[j - 1]}) "
                   f"{previous[j - 1]} % 2 ^ {need[j]} = {names[j - 1]} := by decide +kernel\n")
    proof = [f"theorem {prefix}_entry : rowN (phased {name}.b {phase}) 0 {total} % 2 ^ {cells} = {name}.st {i} := by",
             f"  have h0 := start {name}.b {phase} {need[0]}"]
    for j in range(1, len(marks)):
        before = previous[j - 1] if j == 1 else f"({previous[j - 1]})"
        proof.append(f"  have h{j} := part {name}.b {phase} {marks[j - 1]} {marks[j] - marks[j - 1]} {marks[j]} "
                     f"{need[j]} {need[j - 1]} {before} ({names[j - 1]}) rfl rfl h{j - 1} {prefix}_p{j}")
    proof.append(f"  exact h{len(marks) - 1}")
    out.append("\n".join(proof) + "\n")
    out.append(f"theorem {prefix}_label : ({total} + {phase}) % {name}.b.length = {name}.lab {i} % {name}.b.length := "
               f"by decide\n")
    return "\n".join(out)


def lean_white() -> str:
    """The runs of `Rule30Open.Columns.NineWhite`."""
    return "\n".join(lean_white_run(*run) for run in WHITE_RUNS)


def trap_states(name: str) -> tuple[str, int, set[tuple[int, int]]]:
    """For a trap of `TRAPS` or `NATURAL`: its block, its width, and its states as pairs of a phase of the block and a
    window."""
    t = tables(name)
    period = len(t["word"])
    return t["word"], t["cells"], {(label % period, window) for label, window in t["states"]}


def entry_steps(name: str | dict, halves: list[int], phase: int, steps: int) -> np.ndarray:
    """The first step before `steps` at which each finite right half (bit i is column i + 1), driven by the trap's
    block from `phase` (the column reads the block's letter `phase` at step 0), has its first columns in a state of the
    trap at the block's phase, or -1. The trap is a name of `TRAPS` or `NATURAL`, or tables; it is closed, so an
    entered half stays in it."""
    if isinstance(name, dict):
        word, cells = name["word"], name["cells"]
        states = {(label % len(word), window) for label, window in name["states"]}
        name = f"trap{word}"
    else:
        word, cells, states = trap_states(name)
    period, blocks = len(word), (cells + 63) // 64
    full, low = (1 << cells) - 1, np.uint64((1 << min(cells, 64)) - 1)
    firsts = [np.array(sorted({w & ((1 << 64) - 1) for ph, w in states if ph == q}), dtype=np.uint64)
              for q in range(period)]  # first words of the windows, by phase
    width = max([1] + [half.bit_length() for half in halves])
    rows = np.zeros((len(halves), (width + steps) // 64 + blocks + 2), dtype=np.uint64)  # (n, words)
    for i, half in enumerate(halves):
        for j in range(0, width, 64):
            rows[i, j // 64] = np.uint64((half >> j) & ((1 << 64) - 1))
    entry = np.full(len(halves), -1, dtype=np.int64)  # (n,)
    alive = np.arange(len(halves))  # (m,), row i of `rows` is half alive[i]
    for t in tqdm(range(steps), desc=f"{name} phase {phase}", file=sys.stderr, leave=False, mininterval=10):
        q = (t + phase) % period
        hit = np.zeros(len(alive), dtype=bool)  # (m,)
        for r in np.flatnonzero(np.isin(rows[:, 0] & low, firsts[q])).tolist():
            window = sum(int(rows[r, j]) << (64 * j) for j in range(blocks)) & full
            hit[r] = (q, window) in states
        if hit.any():
            entry[alive[hit]] = t
            rows, alive = rows[~hit], alive[~hit]
            if len(alive) == 0:
                break
        active = (width + t) // 64 + blocks + 2  # a half reaches column width + t + 1 at most
        rows[:, :active] = absorption.step_rows(rows[:, :active], int(word[q]))
    return entry  # (n,)


def coin_entry(name: str, support: int, start: int, steps: int, seed: int = 30) -> np.ndarray:
    """Entry into a trap of `TRAPS` or `NATURAL` with a fair coin beyond the window. Every right half with support in
    cells 1 .. `support`, driven by the trap's block from each phase, is run by the rule for `start` steps; from then on
    only its first cells, as many as the trap is wide, are kept, and the cell beyond them is a fair coin flipped at
    every step. Returns, in the order of `entry_steps` (phase by phase, then half), the first step after `start` at
    which the window is a state of the trap at its phase, or -1. The trap must be at most 63 cells wide."""
    word, cells, states = trap_states(name)
    period = len(word)
    assert cells < 64
    mask, top, one = np.uint64((1 << cells) - 1), np.uint64(cells - 1), np.uint64(1)
    members = [np.array(sorted(w for ph, w in states if ph == q), dtype=np.uint64) for q in range(period)]
    rng = np.random.default_rng(seed)
    times = []
    for phase in range(period):
        windows = []
        for half in range(1 << support):
            row = half
            for t in range(start):
                row = ((row << 1) | int(word[(t + phase) % period])) ^ (row | (row >> 1))
            windows.append(row & ((1 << cells) - 1))
        w = np.array(windows, dtype=np.uint64)  # (n,)
        entry = np.full(len(w), -1, dtype=np.int64)  # (n,)
        alive = np.arange(len(w))  # (m,), the halves not yet inside
        for t in range(steps):
            q = (start + phase + t) % period
            hit = np.isin(w[alive], members[q])  # (m,)
            entry[alive[hit]] = t
            alive = alive[~hit]
            if alive.size == 0:
                break
            x = w[alive]  # (m,)
            coins = rng.integers(0, 2, alive.size).astype(np.uint64)  # (m,)
            w[alive] = (((x << one) | np.uint64(int(word[q]))) ^ (x | (x >> one) | (coins << top))) & mask
        times.append(entry)
    return np.concatenate(times)  # (period * 2 ** support,)


def closure(word: str, modulus: int, cells: int, phase: int, window: int, cap: int,
            locked: bool = False) -> set[tuple[int, int]] | None:
    """The nodes (phase modulo `modulus`, window of `cells` cells) that the game of `word` reaches from one node under
    both values of the cell beyond, or None once they pass `cap`; with `locked`, also None once column 1 takes two
    values at one white phase (`fixes_left`)."""
    period, mask = len(word), (1 << cells) - 1
    start = (phase % modulus, window)
    seen, frontier, value = {start}, [start], {start[0]: window & 1}
    while frontier:
        reached = []
        for ph, w in frontier:
            left, core, after = (w << 1) | int(word[ph % period]), w | (w >> 1), (ph + 1) % modulus
            for free in (0, 1):
                node = (after, (left ^ (core | (free << (cells - 1)))) & mask)
                if node not in seen:
                    if locked and word[after % period] == "0" and value.setdefault(after, node[1] & 1) != node[1] & 1:
                        return None
                    seen.add(node)
                    reached.append(node)
                    if len(seen) > cap:
                        return None
        frontier = reached
    return seen


def escapes(word: str, modulus: int, cells: int, phase: int, window: int, walks: int = 64, seed: int = 30) -> bool:
    """Whether one of `walks` random runs of 4 * `cells` steps from the node, with random values of the cell beyond,
    shows column 1 with two values at one white phase. If so the node's closure is no trap; this rules out most widths
    at once, where `closure` would have to grow to its cap."""
    rng = np.random.default_rng(seed)
    period, mask = len(word), (1 << cells) - 1
    value: dict[int, int] = {}
    for _ in range(walks):
        ph, w = phase % modulus, window
        frees = rng.integers(0, 2, 4 * cells)  # (4 * cells,)
        for free in frees.tolist():
            if word[ph % period] == "0" and value.setdefault(ph, w & 1) != w & 1:
                return True
            left, core = (w << 1) | int(word[ph % period]), w | (w >> 1)
            ph, w = (ph + 1) % modulus, (left ^ (core | (free << (cells - 1)))) & mask
    return False


def fixes_left(word: str, nodes: set[tuple[int, int]]) -> bool:
    """Whether column 1 has one value at each white phase on the nodes, so that the column left of the word does."""
    period, value = len(word), {}
    return all(value.setdefault(ph, w & 1) == w & 1 for ph, w in nodes if word[ph % period] == "0")


def natural_trap(word: str, start: int, checkpoints: list[int], widths: list[int], moduli: list[int],
                 cap: int = 100000) -> tuple[int, int, int, int] | None:
    """The first checkpoint at which the true window of the right half `start` (bit i is column i + 1), driven by
    `word` from phase 0, has a closure of at most `cap` nodes on which column 1 is fixed at the white phases: a trap
    that this half has entered. Returns the time, the least such width, the modulus and the size, or None. A trap at
    one width gives one at every larger width, the windows that extend its states, but with more states."""
    row, period, last = start, len(word), max(checkpoints)
    wanted = set(checkpoints)
    for t in range(last + 1):
        if t in wanted:
            for cells in widths:
                for modulus in moduli:
                    window = row & ((1 << cells) - 1)
                    if escapes(word, modulus, cells, t, window):
                        continue
                    nodes = closure(word, modulus, cells, t, window, cap, locked=True)
                    if nodes is not None and fixes_left(word, nodes):
                        return t, cells, modulus, len(nodes)
        row = ((row << 1) | int(word[t % period])) ^ (row | (row >> 1))
    return None


def natural_summary(period: int, rows: list[tuple[str, int, list[tuple[int, int, int, int, int]]]],
                    starts: int) -> str:
    """One line on the natural traps of the primitive words of one period, from the rows (word, starts whose column 1
    locks, traps found) of `natural_scan` for the words that lock: how many words lock for some start, how many have
    a start inside a trap and how many every start, how many of the words with a trap need more than 16 cells or a
    phase modulo a multiple of the period, and how many have a locked window of 13 cells (`locks.has_lock`) or are
    excluded by the finite game at width 6, 10 or 14."""
    trapped = [(word, locked, traps) for word, locked, traps in rows if traps]
    every = [word for word, _, traps in trapped if len(traps) == starts]
    wide = [word for word, _, traps in trapped if min(t[2] for t in traps) > 16]
    multiple = [word for word, _, traps in trapped if all(t[3] > period for t in traps)]
    window = [word for word, _, _ in trapped if locks.has_lock(word, 13)]
    excluded = [word for word, _, _ in trapped if game.first_width(word, [6, 10, 14]) is not None]
    sizes: dict[int, int] = {}
    for _, _, traps in trapped:
        for trap in traps:
            sizes[trap[4]] = sizes.get(trap[4], 0) + 1
    common = sorted(sizes.items(), key=lambda item: -item[1])[:3]
    return (f"period {period}: {len(game.necklaces(period))} words, {len(rows)} lock for some start, {len(trapped)} have "
            f"a start inside a trap and {len(every)} every start; of those with a trap {len(wide)} need more than 16 "
            f"cells, {len(multiple)} a phase modulo a multiple of the period, {len(window)} have a locked window of 13 "
            f"cells and {len(excluded)} are excluded by the game; {sum(sizes.values())} pairs of a word and a start "
            f"inside a trap, the commonest sizes " + ", ".join(f"{size} states ({count})" for size, count in common))


def wall_chains(period: int, rows: list[tuple[str, int, list[tuple[int, int, int, int, int]]]], count: int = 3,
                starts: int = 30) -> list[tuple[int, str, int, int, int, set[str]]]:
    """For the `count` commonest trap sizes among the rows of `natural_scan` for one period: the size, the block whose
    trap of that size is narrowest, its width, and where the chain of that trap becomes periodic in the distance, with
    its spatial period and the blocks of the period among its columns up to one period past that point."""
    from computations import right_half
    halves = right_half.random_starts(starts, 64)
    sizes: dict[int, int] = {}
    for _, _, traps in rows:
        for trap in traps:
            sizes[trap[4]] = sizes.get(trap[4], 0) + 1
    found = []
    for size, _ in sorted(sizes.items(), key=lambda item: -item[1])[:count]:
        word, k, cells, modulus = min(((word, trap[0], trap[2], trap[3]) for word, _, traps in rows for trap in traps
                                       if trap[4] == size), key=lambda item: (item[2], item[0]))
        t = natural_tables(word, halves[k], 12000, cells, modulus)
        full = t["word"] * (t["modulus"] // len(t["word"]))
        values = "".join(str((t["first"] >> label) & 1) if full[label] == "0" else "0" for label in range(len(full)))
        start, cycle = chain_cycle(full, values)
        blocks = {necklace(c[:least_period(c)]) for c in chain(full, values, start + len(cycle))
                  if least_period(c) == period}
        found.append((size, word, cells, start, len(cycle), blocks))
    return found


def parse_natural(text: str) -> dict[int, list[tuple[str, int, list[tuple[int, int, int, int, int]]]]]:
    """The rows of a saved `--natural` output, by period."""
    import ast
    import re
    found: dict[int, list[tuple[str, int, list[tuple[int, int, int, int, int]]]]] = {}
    for line in re.finditer(r"^([01]+): column 1 locks for (\d+) of \d+ starts; natural traps (\[.*\])$", text, re.M):
        word = line.group(1)
        found.setdefault(len(word), []).append((word, int(line.group(2)), ast.literal_eval(line.group(3))))
    return found


def natural_scan(word: str, steps: int, starts: int = 30, max_width: int = 64) -> tuple[int, list[tuple[int, int, int, int, int]]]:
    """For the empty right half and `starts` random ones (`right_half.random_starts`), driven by `word`: how many lock
    column 1 over the second half of `steps` steps (`right_half.locked_period`), and for those the natural traps
    found at three late checkpoints, at the least width from 16 to `max_width` and with the phase modulo the lock's
    period or twice it, each as (start, time, width, modulus, size)."""
    from computations import right_half
    locks, found = 0, []
    for k, start in enumerate(right_half.random_starts(starts, 64)):
        period = right_half.locked_period(word, start, steps)
        if period is None:
            continue
        locks += 1
        # a half inside a trap keeps column 1 at the white times forever, so a later change rules out the checkpoints
        # before it
        last, _, _ = right_half.lock_breaks(word, start, 3 * steps, 2 * period, 0)
        late = [t for t in (steps * 3 // 5, steps * 4 // 5, steps - 1) if t > last]
        hit = natural_trap(word, start, late, list(range(16, max_width + 1)), [period, 2 * period]) if late else None
        if hit is not None:
            found.append((k, *hit))
    return locks, found


def white_lock(word: str, phase: int, steps: int) -> tuple[int, int | None, tuple[int, int, int, int] | None]:
    """The white right half driven by `word` from `phase` (the center reads `word[phase]` at step 0): the period with
    which column 1, read at the word's white times, repeats over the second half of `steps` steps (0 if it does not),
    and if it does, the step of its last change before that half and the natural trap it is in at three late steps,
    as `natural_trap` returns it."""
    from computations import right_half
    turned = word[phase:] + word[:phase]
    period = right_half.locked_period(turned, 0, steps)
    if period is None:
        return 0, None, None
    last, _, _ = right_half.lock_breaks(turned, 0, steps // 2, period, 0)
    later, _, _ = right_half.lock_breaks(turned, 0, 3 * steps // 2, 2 * period, 0)  # a trap keeps the lock forever
    late = [t for t in (steps * 3 // 5, steps * 4 // 5, steps - 1) if t > later]
    return period, last, natural_trap(turned, 0, late, list(range(16, 65)), [period, 2 * period]) if late else None


def white_runs(word: str, steps: int, cells: int) -> list[list[int]]:
    """The phases of `word` grouped by the white right half's run: the run from phase p, after `steps` - p steps, is at
    the phase `steps` of the word for every p, and two phases are in one group when their runs then agree on columns
    1 .. `cells`. A run whose center reads white first is still the white half one step later, so phase p joins
    phase p + 1 when `word[p]` is 0; runs can also merge later."""
    period, mask = len(word), (1 << cells) - 1
    windows = []
    for p in range(period):
        row = 0
        for s in range(steps - p):
            row = ((row << 1) | int(word[(p + s) % period])) ^ (row | (row >> 1))
        windows.append(row & mask)
    groups: dict[int, list[int]] = {}
    for p, window in enumerate(windows):
        groups.setdefault(window, []).append(p)
    return sorted(groups.values())


def white_scan(item: tuple[str, int], steps: int) -> tuple[str, int, int, int | None, tuple | None]:
    """`white_lock` for one (word, phase), as (word, phase, period, last change, trap)."""
    word, phase = item
    return (word, phase, *white_lock(word, phase, steps))


def edge_periods(columns: list[str], distance: int, phase: int, steps: int, span: int = 6) -> list[int | None]:
    """A background read off a chain, white to the right: the row at time 0 has, at cell x <= 0, the chain's column at
    distance `distance` - x read at `phase`, and is white at x > 0. For the columns x = -`span` .. `span`, the least
    period up to 64 with which each repeats over the second half of `steps` steps, or None. The chain must reach
    `distance` + `steps` + 64; the background is cut there, far enough left that its end does not reach the edge."""
    reach = steps + 64
    row = np.zeros(reach + span + steps + 8, dtype=np.uint8)  # (cells,), index i is cell i - reach
    for i in range(reach + 1):
        column = columns[distance + reach - i]
        row[i] = int(column[phase % len(column)])
    seen = np.zeros((steps, 2 * span + 1), dtype=np.uint8)  # (steps, 2 span + 1)
    for t in range(steps):
        seen[t] = row[reach - span:reach + span + 1]
        left, right = np.roll(row, 1), np.roll(row, -1)  # (cells,) each
        left[0], right[-1] = 0, 0
        row = left ^ (row | right)
    periods = []
    for k in range(2 * span + 1):
        tail = seen[steps // 2:, k]  # (steps / 2,)
        periods.append(next((p for p in range(1, 65) if np.array_equal(tail[p:], tail[:-p])), None))
    return periods


def ether_from(seed: str, values: str, distance: int, count: int) -> bool:
    """Whether columns distance, distance + 1, .., distance + count - 1 of the chain are the kit's ether read leftward
    from a B3 column: column distance + i is ether column 2 - i (modulo 7) at ether phase p - 2, p the phase of the
    seed (`absorption.ETHER`, the kit's table)."""
    columns = chain(seed, values, distance + count)
    return all(int(columns[distance + i][ph]) == absorption.ether(2 - i, ph - 2)
               for i in range(count) for ph in range(len(seed)))


def wall_as_chain() -> list[bool]:
    """For each bottom component of the locked nodes of 0111 with the phase counted modulo 8 (the block 01110111),
    at width 13, whether it is the kit's 109 wall states (`absorption.kit_wall`): the B3 column 1101 at ether phase p
    reads 0111 at phase p + 2."""
    width = 13
    wall = absorption.kit_wall()  # (4, 2^13)
    states = {(ph, int(s)) for ph in range(4) for s in np.flatnonzero(wall[ph])}
    return [{((int(x >> width) - 2) % 4, int(x & ((1 << width) - 1))) for x in members} == states
            for members in bottom_components("01110111", width)]


def t001_states() -> list[tuple[int, int]]:
    """The kit's trap `t001` for 001 (`Rule30EtherThreeTrap`), read from its source: each state's strip of 47 columns,
    column x at bit x - 1, and its label modulo 21."""
    import re
    from computations import period_three
    packed = dict(re.findall(r"def t001_(\w+) : Nat := (\d+)", period_three.TRAP.read_text(encoding="utf-8")))
    digits = sys.get_int_max_str_digits()
    sys.set_int_max_str_digits(0)  # the packed tables have thousands of digits
    try:
        strips, labels, count, label_bits = (int(packed[k]) for k in ("R", "L", "n", "lb"))
    finally:
        sys.set_int_max_str_digits(digits)
    width = period_three.TRAP_WIDTH
    return [((strips >> (width * i)) % (1 << width), (labels >> (label_bits * i)) % (1 << label_bits))
            for i in range(count)]


def t001_reach(width: int) -> float:
    """The share of the nodes of the game of 001 at `width`, the phase counted modulo 3 as the kit's `AbsorptionT`
    counts it, from which some values of the cell beyond reach the states of `t001` cut to their first `width` cells.
    Entry into `t001` for every finitely supported right half needs 1 at every width (`trap_reach`)."""
    low = (1 << width) - 1
    inside = np.zeros(3 << width, dtype=bool)  # (3 n,)
    for strip, label in t001_states():
        inside[(label % 3) << width | strip & low] = True
    return float(locks.back_search("001", width, inside).mean())


def t001_coin(widths: tuple[int, ...] = (12, 14, 16, 18, 20)) -> list[tuple[int, float]]:
    """For the kit's `t001`, the factor per step by which the chance of staying out of its states cut to `width` cells
    falls when column `width` + 1 is a fair coin, the phase modulo 3 as `AbsorptionT` counts it
    (`coin_lock.period_rate`, an upper bound wherever its iteration stops): (width, factor) for each width."""
    from computations import coin_lock
    states = t001_states()
    out = []
    for width in widths:
        member = np.zeros((3, 1 << width), dtype=bool)  # (3, 2^width)
        for strip, label in states:
            member[label % 3, strip & ((1 << width) - 1)] = True
        out.append((width, coin_lock.period_rate("001", member, limit=60000)))
    return out


def t001_as_chain() -> tuple[str, str, bool, bool, int]:
    """The kit's trap for 001 read as a chain: its last column that is a function of the label, the values of the next
    column at that column's white labels, whether `chain` from them gives the columns before it and then the center
    (black at the labels 2 modulo 3), whether those values are single, and the least width at which the last column's
    block, with the phase counted modulo 21, has a locked node."""
    states = t001_states()
    labels = np.array([label for _, label in states])  # (n,)
    members = np.array([strip for strip, _ in states], dtype=object)  # (n,)
    columns = []
    for j in range(64):
        bits = np.array([(strip >> j) & 1 for strip in members.tolist()])  # (n,)
        values = {}
        if any(values.setdefault(int(l), int(b)) != int(b) for l, b in zip(labels, bits)):
            break
        columns.append("".join(str(values[l]) for l in range(21)))
    seed, beyond = columns[-1], len(columns)
    seen: dict[int, set[int]] = {}
    for strip, label in states:
        seen.setdefault(label, set()).add((strip >> beyond) & 1)
    single = all(len(seen[l]) == 1 for l in range(21) if seed[l] == "0")
    values = "".join(str(min(seen[l])) if seed[l] == "0" else "0" for l in range(21))
    center = "".join("1" if l % 3 == 2 else "0" for l in range(21))
    rebuilt = chain(seed, values, beyond) == columns[::-1] + [center]
    least = next(w for w in range(1, 14) if locks.has_lock(seed, w))
    return seed, values, rebuilt, single, least


def set_step(windows: np.ndarray, column: int, width: int) -> np.ndarray:
    """The windows one step after any of `windows`, beside a column reading `column`, for both values of the next
    cell."""
    # windows: (2^W,) membership
    present = np.flatnonzero(windows)  # (m,)
    cells = (present[:, None] >> np.arange(width)[None, :]) & 1  # (m, W), cell x at index x - 1
    weights = 1 << np.arange(width)  # (W,)
    out = np.zeros(1 << width, dtype=bool)  # (2^W,)
    for free in (0, 1):
        left = np.concatenate([np.full((present.size, 1), column), cells[:, :-1]], axis=1)  # (m, W)
        right = np.concatenate([cells[:, 1:], np.full((present.size, 1), free)], axis=1)  # (m, W)
        out[((left ^ (cells | right)) * weights).sum(axis=1)] = True
    return out  # (2^W,)


def wall_returns(period: int, width: int, periods: int, run: int = 60) -> list[str]:
    """The values of the cell beside a column that repeats 0 1^(period - 1), at its white phase, period after period,
    over the windows that can follow the wall: all windows, then `run` steps beside a black column. Each entry is
    '0', '1' or '01'."""
    windows = np.ones(1 << width, dtype=bool)  # (2^W,)
    for _ in range(run):
        windows = set_step(windows, 1, width)
    found = []
    for _ in range(periods):
        windows = set_step(windows, 0, width)
        for _ in range(period - 1):
            windows = set_step(windows, 1, width)
        found.append("".join(sorted({str(w & 1) for w in np.flatnonzero(windows).tolist()})))
    return found


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--chain", type=str, default="", help="periods P whose chain of 0 1^(P-1) to print")
    parser.add_argument("--depth", type=int, default=12)
    parser.add_argument("--classify", type=str, default="", help="periods whose locks to place in seed chains")
    parser.add_argument("--lock-backgrounds", type=str, default="",
                        help="periods whose locked windows to sort by the background their chains end in")
    parser.add_argument("--ether", action="store_true", help="the chain of 0 1^7 and the kit's wall")
    parser.add_argument("--wall", type=str, default="", help="periods P for wall_returns of 0 1^(P-1)")
    parser.add_argument("--short", type=str, default="", help="periods whose seeds' chains to scan for shorter periods")
    parser.add_argument("--rest", type=int, default=None, help="with --short, only seeds of a long run and this many "
                        "other cells")
    parser.add_argument("--t001", action="store_true", help="the kit's trap for 001 as a chain")
    parser.add_argument("--t001-coin", action="store_true",
                        help="the fair coin's factor per step for t001 at widths 12 to 20")
    parser.add_argument("--t001-reach", type=int, default=0,
                        help="with a width, the share of nodes that can reach t001 cut to each width up to it")
    parser.add_argument("--verify", action="store_true", help="check the chain locks of short-period blocks directly")
    parser.add_argument("--lean", action="store_true", help="print the trap entries of WordTraps.lean")
    parser.add_argument("--lean-white", action="store_true", help="print the runs of NineWhite.lean")
    parser.add_argument("--lean-ten", action="store_true", help="print the trap entries of TenTraps.lean")
    parser.add_argument("--lean-ten-gap", action="store_true", help="print the entry data of TenGap.lean")
    parser.add_argument("--lean-wall-gaps", action="store_true", help="print the entry data of WallGaps.lean")
    parser.add_argument("--lean-far", action="store_true", help="print the traps of FarWalls.lean")
    parser.add_argument("--far-entry", action="store_true", help="entry into each trap of FarWalls")
    parser.add_argument("--lean-census", type=int, default=0, choices=[0, 13, 14, 15],
                        help="print the traps of CensusTraps13.lean, CensusTraps14.lean or CensusTraps15.lean")
    parser.add_argument("--census-entry", type=int, default=0, choices=[0, 13, 14, 15],
                        help="entry into each trap of CensusTraps13, CensusTraps14 or CensusTraps15")
    parser.add_argument("--lean-census-large", type=int, default=0, choices=[0, 14, 15],
                        help="print the traps of CensusTrapsLarge.lean (14) or CensusTrapsLarge15.lean (15)")
    parser.add_argument("--lean-long-large", action="store_true", help="print the traps of NaturalTrapsLongLarge.lean")
    parser.add_argument("--reach", type=int, default=0,
                        help="with a width, the share of the nodes of the game of that width that can reach each trap "
                             "of the trap modules, cut to that width when wider")
    parser.add_argument("--lean-missed", action="store_true",
                        help="the traps of MissedTraps, each with a closed set of windows apart from it")
    parser.add_argument("--lean-pairs", action="store_true",
                        help="the traps of TrapPairs, the two bottom components of each block of PAIRS")
    parser.add_argument("--lean-wall-natural", action="store_true",
                        help="the traps of NaturalTrapsWalls, natural traps for blocks whose wall traps fail")
    parser.add_argument("--wide-reach", type=int, metavar="WORKERS",
                        help="the test of reach at 22 cells for the natural traps, large census components, pairs and "
                             "sets, with this many processes (about three hours with two)")
    parser.add_argument("--wide-reach-carried", type=int, metavar="WORKERS",
                        help="the test of reach at 22 cells for the traps carried along a chain, with this many "
                             "processes (about five hours with three)")
    parser.add_argument("--natural-coin-widths", action="store_true",
                        help="the coin's factor per step for the natural traps of 16 cells in games of 16, 18 and 20 "
                             "cells")
    parser.add_argument("--lean-fifteen", action="store_true",
                        help="the traps of FifteenWalls, two walls of period 15 wider than 16 cells carried leftward")
    parser.add_argument("--lean-trap-sets", action="store_true",
                        help="the natural traps of TrapSets, for blocks whose every trap a sampled half stays apart from")
    parser.add_argument("--lean-traps001", action="store_true",
                        help="the two more traps for 001 of Rule30Open.Columns.Traps001, and the refutations")
    parser.add_argument("--scan001", action="store_true", help="the long-run seeds whose chains reach 001")
    parser.add_argument("--scan001-wider", action="store_true",
                        help="the same for longer periods and wider windows, about an hour")
    parser.add_argument("--lean-apart-traps", action="store_true",
                        help="the refutations and pair reductions of Rule30Open.Columns.ApartTraps")
    parser.add_argument("--chain-family", default="",
                        help="the traps of a block from the chains of long-run seeds, and a family pairwise apart")
    parser.add_argument("--chain-apart", action="store_true",
                        help="the chain locks of long-run seeds of periods 16 to 40 apart from a trap in Lean")
    parser.add_argument("--apart-pairs", action="store_true",
                        help="every two traps of one block in Lean, one holding a closed set apart from the other")
    parser.add_argument("--lean-wide-walls", action="store_true",
                        help="the walls of Rule30Open.Columns.WideWalls, of 22 cells, beside traps carried far")
    parser.add_argument("--lean-back", action="store_true",
                        help="the sets of Rule30Open.Columns.ReachRefuted, from the windows that can reach each trap")
    parser.add_argument("--lean-refuted", action="store_true",
                        help="the closed sets of RefutedTraps, which refute entry into traps of UNREACHED in Lean")
    parser.add_argument("--apart-census", type=int, metavar="WORKERS",
                        help="the traps and pairs that pass the test of reach but that a half of the natural scan stays "
                             "apart from, with this many processes (about an hour with three)")
    parser.add_argument("--halves-apart", action="store_true",
                        help="for each trap of NaturalTrapsWalls, the halves of its natural scan in traps apart from it")
    parser.add_argument("--lean-extra", action="store_true", help="print the trap entries of NaturalTraps.lean")
    parser.add_argument("--lean-long", action="store_true", help="print the trap entries of NaturalTrapsLong.lean")
    parser.add_argument("--long-entry", action="store_true",
                        help="entry of the halves with support in cells 1 .. --cells into each trap of "
                        "NaturalTrapsLong")
    parser.add_argument("--lean-large", action="store_true", help="print the trap and parts of NaturalTrapsLarge.lean")
    parser.add_argument("--lean-walls", type=int, default=0, choices=[0, 11, 12, 13, 14],
                        help="print the trap entries of ElevenTraps, TwelveTraps, ThirteenTraps or FourteenTraps")
    parser.add_argument("--walls-entry", type=int, default=0, choices=[0, 11, 12, 13, 14],
                        help="entry of the halves with support in cells 1 .. --cells into each trap of that module")
    parser.add_argument("--extra-entry", action="store_true",
                        help="entry of the halves with support in cells 1 .. --cells into each trap of NaturalTraps "
                        "and NaturalTrapsLarge")
    parser.add_argument("--natural-coin", action="store_true",
                        help="each trap of 16 cells of NaturalTraps against a fair coin in column 17")
    parser.add_argument("--ten-coin", action="store_true",
                        help="the period-10 wall against a fair coin beyond, and random halves of growing length")
    parser.add_argument("--ten-entry", action="store_true",
                        help="entry of the halves with support in cells 1 .. --cells into each trap of TenTraps")
    parser.add_argument("--entry", type=str, default="", help="traps whose entry by small right halves to measure")
    parser.add_argument("--cells", type=int, default=8, help="with --entry, every half with support in these cells")
    parser.add_argument("--steps", type=int, default=50000)
    parser.add_argument("--sample", type=int, default=0, help="with --entry, this many random pairs of a half and a "
                        "phase instead of all")
    parser.add_argument("--natural", type=str, default="", help="periods whose words to search for natural traps")
    parser.add_argument("--natural-from", type=str, default="", help="summarize a saved --natural output by period")
    parser.add_argument("--max-width", type=int, default=64, help="with --natural, the widest window closed")
    parser.add_argument("--starts", type=int, default=30, help="with --natural, random right halves besides the empty "
                        "one")
    parser.add_argument("--edges", action="store_true", help="backgrounds of the chains of 0 1^7 and of the first wall "
                        "of period 9, white to the right: do columns near the edge repeat?")
    parser.add_argument("--runs", type=str, default="", help="words whose white-half runs from the phases to group by "
                        "agreement on columns 1 .. --cells at step --steps")
    parser.add_argument("--coin", type=str, default="", help="traps whose entry to measure with a fair coin beyond "
                        "the window, from the small halves' windows at step 200")
    parser.add_argument("--white", type=str, default="", help="periods whose words drive the white right half, "
                        "from every phase, to look for a lock of column 1 and its trap")
    parser.add_argument("--nine", action="store_true", help="entry of the 31 starts into each trap of period 9")
    parser.add_argument("--width", type=int, default=13)
    parser.add_argument("--workers", type=int, default=1)
    args = parser.parse_args()
    kit = {necklace(word) for word in game.KIT_WORDS}
    for period in [int(p) for p in args.chain.split(",") if p]:
        seed = "0" + "1" * (period - 1)
        start, cycle = chain_cycle(seed, "0" * period)
        periods = sorted({least_period(c) for c in cycle})
        print(f"chain of {seed}, column m + 1 white at its white phase; periodic in the distance from distance "
              f"{start}, with period {len(cycle)} and columns of least periods {periods}")
        for distance, column in enumerate(chain(seed, "0" * period, args.depth)):
            word = necklace(column)
            primitive = least_period(column) == period
            lock = locks.has_lock(word, args.width) if primitive else None
            print(f"  distance {distance:2d}: {word}  primitive {primitive}  locked window at width {args.width}: "
                  f"{lock}  kit word: {word in kit}", flush=True)
    if args.lock_backgrounds:
        for period in [int(p) for p in args.lock_backgrounds.split(",")]:
            found = survey([period], args.width, args.workers)
            print(f"period {period}: {len(found)} blocks have a locked window of {args.width} cells", flush=True)
            rows = {}  # one row of each background, by spatial period
            for block, entries in found.items():
                for columns, values in entries:
                    row = background_row(columns[-1] if columns else block, values)
                    rows.setdefault(len(row), row)
            from computations.space_time_periodic import ring_period
            for size, (ends, reach) in sorted(lock_backgrounds(found).get(period, {}).items()):
                print(f"  background of {size} cells: the chains of the locks of {len(ends)} blocks end in it and "
                      f"hold {len(reach)} blocks of period {period}; one of its rows returns on its ring after "
                      f"{ring_period(rows[size], period)} steps", flush=True)
    if args.classify:
        found = survey([int(p) for p in args.classify.split(",")], args.width, args.workers)
        seeds, placed = classify(found, 2 * args.width)
        print(f"{len(found)} blocks have a locked node at width {args.width}; seeds and their lock values:")
        for seed, options in seeds.items():
            print(f"  {seed}: {', '.join(options)}")
        by_seed: dict[str, set[tuple[int, str]]] = {}
        for block, entries in placed.items():
            for seed, distance in entries:
                by_seed.setdefault(seed, set()).add((distance, block))
        for seed, entries in sorted(by_seed.items(), key=lambda item: (len(item[0]), item[0])):
            blocks = {block for _, block in entries}
            print(f"chain of {seed or '(none)'}: {len(blocks)} blocks: "
                  + " ".join(f"{block}@{distance}" for distance, block in sorted(entries)))
    if args.ether:
        start, cycle = chain_cycle("01111111", "00000000")
        print(f"chain of 01111111: periodic in the distance from distance {start}, with period {len(cycle)}: "
              + " ".join(necklace(column)[:least_period(column)] for column in cycle))
        for word in ("0111", "0011", "0001", "01"):
            first = next(d for d, column in enumerate(chain("01111111", "00000000", 40))
                         if necklace(column) == necklace(word * (8 // len(word))))
            least = next((w for w in range(1, 21) if locks.has_lock(word * (8 // len(word)), w)), None)
            print(f"  {word}: first at distance {first}; least width with a locked node, phase modulo 8: {least}",
                  flush=True)
        print("columns 8 .. 21 of the chain are the kit's ether, read leftward from B3:",
              ether_from("01111111", "00000000", 8, 14))
        print("bottom components of 01110111 at width 13 equal to the kit's 109 wall states:", wall_as_chain())
    if args.short:
        found = short_scan([int(p) for p in args.short.split(",")], args.width, args.depth, args.workers, args.rest)
        for block, result in found.items():
            for values, hits in result:
                for p, (distance, word) in sorted(hits.items()):
                    print(f"seed {block} (values {values}): period {p}, {word} at distance {distance}, a locked "
                          f"window of {distance + args.width} cells with the phase modulo {len(block)}", flush=True)
    if args.t001:
        seed, values, rebuilt, single, least = t001_as_chain()
        print(f"t001: columns 1 .. 38 are functions of the label modulo 21; column 38 repeats {seed} "
              f"({necklace(seed)}), column 39 reads {''.join(values[l] for l in range(21) if seed[l] == '0')} at its "
              f"white labels (one value each: {single}); the chain from it gives columns 37 .. 1 and the center 001: "
              f"{rebuilt}; that block has a locked node from width {least}")
    for name in [n for n in args.entry.split(",") if n]:
        word, cells, _ = trap_states(name)
        halves = list(range(1 << args.cells))
        if args.sample:  # a random sample of the pairs (half, phase), the same for every trap of the period
            picks = np.random.default_rng(30).choice(len(halves) * len(word), args.sample, replace=False)  # (s,)
            chosen = [[halves[k % len(halves)] for k in picks.tolist() if k // len(halves) == phase]
                      for phase in range(len(word))]
            what = "sampled halves and phases"
        else:
            chosen, what = [halves] * len(word), "halves and phases"
        times = np.concatenate([entry_steps(name, chosen[phase], phase, args.steps)
                                for phase in range(len(word)) if chosen[phase]])  # (n,)
        done = times[times >= 0]  # (k,)
        summary = (f", median {int(np.median(done))}, latest {int(done.max())}; by step: "
                   + ", ".join(f"{int((done < s).sum())} by {s}" for s in (50000, 100000, 200000, 500000)
                               if s <= args.steps)) if done.size else ""
        print(f"{name} ({word}, {cells} cells): {done.size} of {times.size} {what} with support in cells "
              f"1 .. {args.cells} enter by step {args.steps}{summary}", flush=True)
        if len(halves) == 1 and not args.sample:  # the white half alone: the step from each phase
            print("  by phase: " + ", ".join(f"{phase}: {int(t)}" for phase, t in enumerate(times)), flush=True)
    for period in [int(p) for p in args.natural.split(",") if p]:
        words = game.necklaces(period)
        scan = functools.partial(natural_scan, steps=args.steps, starts=args.starts, max_width=args.max_width)
        with multiprocessing.Pool(args.workers) as pool:
            results = tqdm(pool.imap(scan, words), total=len(words), desc=f"period {period}", file=sys.stderr,
                           mininterval=10)
            rows = []
            for word, (locks_found, traps) in zip(words, results):
                if locks_found:
                    rows.append((word, locks_found, traps))
                    print(f"{word}: column 1 locks for {locks_found} of {args.starts + 1} starts; natural traps "
                          f"{traps}", flush=True)
        print(natural_summary(period, rows, args.starts + 1), flush=True)
    if args.natural_from:
        with open(args.natural_from, encoding="utf-8") as saved:
            for period, rows in sorted(parse_natural(saved.read()).items()):
                print(natural_summary(period, rows, args.starts + 1), flush=True)
                walls = wall_chains(period, rows, starts=args.starts)
                for size, word, cells, start, spatial, blocks in walls:
                    print(f"  traps of {size} states: the wall of {word}, {cells} cells; its chain repeats from distance "
                          f"{start} with spatial period {spatial} and holds {len(blocks)} blocks of period {period}",
                          flush=True)
                reached = set().union(*(blocks for *_, blocks in walls))
                print(f"  together {len(reached)} blocks of period {period}, "
                      f"{len(reached - set(game.KIT_WORDS))} that the kit does not exclude", flush=True)
    if args.edges:
        backgrounds = [("the kit's ether, the chain of 0 1^7", chain("01111111", "0" * 8, args.steps + 300), 8, 7, 8)]
        t = tables("trap001011111")
        values = "".join(str((t["first"] >> ph) & 1) if t["word"][ph] == "0" else "0" for ph in range(9))
        # 15 distances suffice: there each column is the one 15 places right of it, 8 steps on
        backgrounds.append(("the background of period 9, the chain of the first wall", chain(t["word"], values,
                            args.steps + 500), 10, 15, 9))
        for label, columns, start, spatial, period in backgrounds:
            edges = [(d, ph) for d in range(start, start + spatial) for ph in range(period)]
            periodic = [(d, ph) for d, ph in tqdm(edges, desc="edges", file=sys.stderr, mininterval=10)
                        if any(p is not None for p in edge_periods(columns, d, ph, args.steps))]
            print(f"{label}: {len(periodic)} of {len(edges)} edges, white to the right, give a column among the 13 "
                  f"next to the edge that repeats with a period up to 64 over the second half of {args.steps} steps",
                  flush=True)
    for word in [w for w in args.runs.split(",") if w]:
        print(f"{word}: the white half's runs from the phases, by agreement on columns 1 .. {args.cells} at step "
              f"{args.steps}: {white_runs(word, args.steps, args.cells)}", flush=True)
    for name in [n for n in args.coin.split(",") if n]:
        times = coin_entry(name, args.cells, 200, args.steps)  # (n,)
        done = times[times >= 0]  # (k,)
        print(f"{name}: with a fair coin beyond the window from step 200, {done.size} of {times.size} halves and "
              f"phases with support in cells 1 .. {args.cells} enter by step {args.steps} after it"
              + (f", median {int(np.median(done))}" if done.size else "") + "; by step: "
              + ", ".join(f"{int((done < s).sum())} by {s}" for s in (1, 10000, 50000, 100000, 200000, 500000)
                          if s <= args.steps), flush=True)
    for period in [int(p) for p in args.white.split(",") if p]:
        items = [(word, phase) for word in game.necklaces(period) for phase in range(period)]
        scan = functools.partial(white_scan, steps=args.steps)
        with multiprocessing.Pool(args.workers) as pool:
            results = list(tqdm(pool.imap(scan, items), total=len(items), desc=f"white, period {period}",
                                file=sys.stderr, mininterval=10))
        locked = [r for r in results if r[2]]
        for word, phase, lock, last, trap in locked:
            print(f"{word} phase {phase}: column 1 of the white half locks with period {lock} from step {last + 1}; "
                  f"natural trap {trap}", flush=True)
        words = {word for word, *_ in locked}
        print(f"period {period}: the white half locks for {len(locked)} of {len(items)} words and phases, "
              f"{len(words)} of {len(game.necklaces(period))} words", flush=True)
    if args.nine:
        from computations import right_half
        starts = right_half.random_starts(30, 64)
        for distance in nine_distances():
            t = carried("trap001011111", distance)
            times = entry_steps(t, starts, 0, args.steps)  # (31,)
            done = sorted(int(x) for x in times if x >= 0)
            print(f"{t['word']} (distance {distance}, {t['cells']} cells): {len(done)} of 31 starts enter by step "
                  f"{args.steps}" + (f", at steps {done}" if done else ""), flush=True)
    if args.lean:
        print("\n".join(lean_trap(entry[0]) for entry in TRAPS + NATURAL[:1]))
        print(lean_nine())
        print(lean_trap(NATURAL[1][0]))
    if args.lean_white:
        print(lean_white())
    if args.lean_ten:
        print(lean_ten())
    if args.lean_ten_gap:
        print(lean_ten_gap())
    if args.lean_walls in (13, 14):
        prefix = "th" if args.lean_walls == 13 else "fo"
        print(lean_walls(args.lean_walls, WALL_DEPTHS[args.lean_walls], prefix, 1 << 16, True))
    elif args.lean_walls:
        print(lean_walls(args.lean_walls, 40, "el" if args.lean_walls == 11 else "tw"))
    if args.lean_extra:
        print(lean_extra())
    if args.lean_long:
        print(lean_extra(LONG_TRAPS))
    if args.lean_large:
        print(lean_large())
    if args.reach:
        rows = reach_census(args.reach)
        for module, word, cells, share in rows:
            if share < 1:
                print(f"{module}: {word} ({cells} cells): only {share:.4f} of the nodes can reach the trap", flush=True)
        full = sum(share == 1 for *_, share in rows)
        print(f"{len(rows)} traps and pairs, cut to {args.reach} cells when wider; every node of the game of "
              f"{args.reach} cells can reach {full} of them", flush=True)
    if args.lean_far:
        print(lean_far())
    if args.lean_census:
        print(lean_census(args.lean_census))
    if args.lean_census_large:
        print(lean_census_large(CENSUS_LARGE15 if args.lean_census_large == 15 else None))
    if args.lean_missed:
        print(lean_missed())
    if args.t001_coin:
        for width, factor in t001_coin():
            print(f"t001, a fair coin in column {width + 1}: the chance of staying out falls by {factor:.6f} per step, "
                  f"a mean of {1 / (1 - factor):.0f} steps")
    if args.t001_reach:
        shares = [t001_reach(width) for width in tqdm(range(1, args.t001_reach + 1), file=sys.stderr)]
        print(f"t001: at widths 1 to {args.t001_reach}, the share of the nodes of the game of 001 that can reach its "
              f"states cut to the width is at least {min(shares):.6f}", flush=True)
    if args.lean_pairs:
        print(lean_pairs())
    if args.lean_wall_natural:
        print(lean_wall_natural())
    for workers, census in ((args.wide_reach, wide_reach), (args.wide_reach_carried, wide_reach_carried)):
        if workers:
            rows = census(22, workers)
            print(f"{len(rows)} hypotheses, {sum(1 for row in rows if row[2] < 1)} fail at 22 cells")
            for module, name, share in rows:
                if share < 1:
                    print(f"{module} {name}: {share:.6f}")
    if args.natural_coin_widths:
        for word, factors in natural_coin_widths():
            print(f"{word}: " + ", ".join(f"{f:.6f}" for f in factors))
    if args.lean_fifteen:
        print(lean_fifteen())
    if args.lean_trap_sets:
        print(lean_trap_sets())
    if args.lean_back:
        print(lean_back_module())
        return
    if args.lean_traps001:
        print(lean_traps001())
        return
    if args.scan001 or args.scan001_wider:
        four = traps001_tables()
        for seed, values, width, distance in scan001(plans=SCAN001_WIDER if args.scan001_wider else SCAN001):
            t = trap_tables(seed, width, distance, values)
            apart = [name for name, other in four if apart_closed(other, t).any()]
            every = int(apart_closed([other for _, other in four], t).sum())
            print(f"{seed} (lock values {values}, width {width}): 001 at distance {distance}, a trap of {t['cells']} "
                  f"cells, labels modulo {t['modulus']}, {len(t['states'])} states; a closed set of its states apart "
                  f"from {', '.join(apart) if apart else 'none of the four'}, and from all four, of {every}")
        return
    if args.lean_apart_traps:
        print(lean_apart_traps())
        return
    if args.chain_family:
        traps, family = chain_family(args.chain_family)
        for name, t in traps:
            print(f"{name}: {t['cells']} cells, labels modulo {t['modulus']}, {len(t['states'])} states")
        print(f"{len(traps)} traps for {args.chain_family}; {len(family)} pairwise apart: "
              f"{', '.join(traps[i][0] for i in family)}")
        return
    if args.chain_apart:
        found = chain_apart()
        for block, seed, distance, module, name, cells in found:
            print(f"{block}: the lock of {seed} carried {distance} cells, a trap of {cells} cells, is apart from "
                  f"{module}.{name}")
        print(f"{len(found)} chain traps; traps refuted: {sorted({(m, n) for _, _, _, m, n, _ in found})}")
        return
    if args.apart_pairs:
        found = apart_pairs()
        for block, (ma, na), (mb, nb), size in found:
            print(f"{block}: {mb}.{nb} holds a closed set of {size} states apart from {ma}.{na}")
        print(f"{len(found)} ordered pairs, {len({refuted for _, refuted, _, _ in found})} traps refuted")
        print("APART_TRAPS:")
        for entry in apart_traps(found):
            print(f"    {entry},")
        return
    if args.lean_wide_walls:
        print(lean_wide_walls())
        return
    if args.lean_refuted:
        print(lean_refuted())
    if args.apart_census:
        rows = apart_census(args.apart_census)
        print(f"{len(rows)} traps or pairs, {sum(1 for row in rows if row[3])} with a half apart")
        for module, name, halves, away in rows:
            if away:
                print(f"{module} {name}: {len(away)} of {halves} halves apart {away}")
    if args.halves_apart:
        traps = [extra_tables(word) for word, *_ in WALL_NATURAL]
        traps += [t for word, _ in WALL_SPLIT for t in split_tables(word)]
        for t in tqdm(traps, desc="traps", file=sys.stderr, mininterval=10):
            apart = [(k, cells, size) for k, cells, _, size, away in halves_apart(t) if away]
            print(f"{t['word']} ({t['cells']} cells, {len(t['states'])} states): {len(apart)} halves apart {apart}")
    if args.lean_long_large:
        print(lean_long_large())
    if args.lean_wall_gaps:
        for name, trap, bound, prefix in WALL_GAPS:
            print(lean_gap(name, trap, bound, prefix))
    if args.walls_entry or args.far_entry or args.census_entry:
        counts = [0, 0, 0]  # traps that every pair, some pairs and no pair enter
        rows = (far_entry(args.cells, args.steps) if args.far_entry else
                census_entry(args.census_entry, args.cells, args.steps) if args.census_entry else
                walls_entry(args.walls_entry, args.cells, args.steps, WALL_DEPTHS[args.walls_entry]))
        for name, distance, word, cells, times in rows:
            done = times[times >= 0]  # (k,)
            counts[0 if done.size == times.size else 1 if done.size else 2] += 1
            print(f"{name} at distance {distance} ({word}, {cells} cells): {done.size} of {times.size} halves and phases "
                  f"enter by step {args.steps}" + (f", median {int(np.median(done))}, latest {int(done.max())}"
                                                   if done.size else ""), flush=True)
        scope = (f"period {args.walls_entry}" if args.walls_entry else
                 f"census traps of period {args.census_entry}" if args.census_entry else "far traps")
        print(f"{scope}: {counts[0]} traps entered by every pair, {counts[1]} by some, {counts[2]} by none", flush=True)
    if args.extra_entry or args.long_entry:
        counts = [0, 0, 0]  # traps that every pair, some pairs and no pair enter
        for word, cells, times in extra_entry(args.cells, args.steps, LONG_TRAPS if args.long_entry else None):
            done = times[times >= 0]  # (k,)
            counts[0 if done.size == times.size else 1 if done.size else 2] += 1
            print(f"{word} ({cells} cells): {done.size} of {times.size} halves and phases enter by step {args.steps}"
                  + (f", median {int(np.median(done))}, latest {int(done.max())}" if done.size else ""), flush=True)
        print(f"{counts[0]} traps entered by every pair, {counts[1]} by some, {counts[2]} by none", flush=True)
    if args.natural_coin:
        for word, coin in natural_coin():
            print(f"{word}: every window can enter: {coin['reachable']}, within {coin['longest_path']} steps; expected "
                  f"entry at most {coin['expected_max']}, mean at phase 0 {coin['expected_mean']}; decay per step "
                  f"{coin['decay']}; stay out after 12,000 steps at most {coin['stay_out']:.3g}; universal word "
                  f"{coin['word']}; a constant column 17 leaves {coin['constant']} out", flush=True)
    if args.ten_coin:
        coin = ten_coin()
        print(f"every window can enter: {coin['reachable']}, within {coin['longest_path']} steps; with a fair coin the "
              f"expected entry is at most {coin['expected_max']:.1f} steps, {coin['expected_mean']:.1f} on average at "
              f"phase 0; the chance of staying out falls by {coin['decay']:.6f} per step and after 12,000 steps is at "
              f"most {coin['stay_out']:.3g}; a word of {coin['word']} values of column 17 brings every window in; a "
              f"white or black column 17 leaves {coin['constant'][0]} and {coin['constant'][1]} windows out after "
              f"3,000 steps", flush=True)
        for length, times in ten_lengths([16, 64, 256, 1024]):
            done = times[times >= 0]  # (k,)
            print(f"random halves of {length} cells: {done.size} of {times.size} enter by step 100,000, median "
                  f"{int(np.median(done))}, latest {int(done.max())}", flush=True)
    if args.ten_entry:
        for distance, word, cells, times in ten_entry(args.cells, args.steps):
            done = times[times >= 0]  # (k,)
            print(f"distance {distance} ({word}, {cells} cells): {done.size} of {times.size} halves and phases enter by "
                  f"step {args.steps}" + (f", median {int(np.median(done))}, latest {int(done.max())}" if done.size
                                          else ""), flush=True)
    if args.verify:
        for seed, width, distance, want in VERIFIED:
            block, nodes = chain_lock(seed, width, distance, want)
            p = least_period(block)
            print(f"{necklace(block[:p])} (period {p}): the chain of {seed} at distance {distance}, {len(nodes)} nodes "
                  f"of {distance + width} cells with the phase modulo {len(seed)}; a lock by the rule on whole "
                  f"windows: {is_lock(block, nodes, distance + width)}", flush=True)
    for period in [int(p) for p in args.wall.split(",") if p]:
        print(f"0 1^{period - 1}: cell 1 at the white phase, period after period:",
              " ".join(wall_returns(period, args.width, 12)), flush=True)


if __name__ == "__main__":
    main()
