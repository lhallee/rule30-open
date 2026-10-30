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
writes it as a trap of `Rule30Open.Columns.WordTraps`.

    python -m computations.lock_chain --chain 8,9,10,11,12,13 --depth 12   # the chains of 0 1^(P-1), 15 s
    python -m computations.lock_chain --classify 4,8,10,11,12 --width 13 --workers 3   # every lock's seed, about 2 min
    python -m computations.lock_chain --ether   # the chain of 0 1^7, the kit's ether and its wall, about 1 min
    python -m computations.lock_chain --wall 4,5,6,7,8,9,10,11,12,13,14 --width 11   # returns to the wall, 1 s
    python -m computations.lock_chain --t001 --verify   # the kit's trap for 001 and the short-period locks, 1 min
    python -m computations.lock_chain --short 16,18,20,21 --width 9 --depth 3000 --workers 4   # about 40 min
    python -m computations.lock_chain --lean   # the trap entries of Rule30Open.Columns.WordTraps
"""

from __future__ import annotations

import argparse
import functools
import multiprocessing
import sys

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


def short_scan(periods: list[int], width: int, depth: int, workers: int = 1) -> dict[str, list[tuple[str, dict]]]:
    """`seed_short_columns` for every primitive block of these periods, keeping the seeds whose chain has a column of
    a shorter period within `depth`."""
    blocks = [block for period in periods for block in game.necklaces(period)]
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
    """A chain lock as a labelled trap: the block as its least rotation `word`, the window width, the labels' modulus
    (the seed's period), and the states, sorted, each a label and a window, with label l reading the block at phase
    l modulo its period; for each state the index of its successor under each value of the cell beyond, and the bits
    of column 1 at the white labels."""
    full, nodes = chain_lock(seed, width, distance, want)
    modulus, period = len(seed), least_period(full)
    word = necklace(full[:period])
    turn = next(r for r in range(period) if full[r:r + period] == word)  # full[r + l] = word[l]
    states = sorted({((ph - turn) % modulus, window) for ph, window in nodes})
    index = {state: i for i, state in enumerate(states)}
    cells, mask = distance + width, (1 << (distance + width)) - 1
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


def lean_trap(name: str, seed: str, width: int, distance: int, want: str | None = None) -> str:
    """The Lean entry `WTrap` for a chain lock, packed as the kit packs `t001`, with its kernel check."""
    t = trap_tables(seed, width, distance, want)
    n = len(t["states"])
    lb, ib = max(1, (t["modulus"] - 1).bit_length()), max(1, (n - 1).bit_length())
    windows = sum(window << (t["cells"] * i) for i, (_, window) in enumerate(t["states"]))
    labels = sum(label << (lb * i) for i, (label, _) in enumerate(t["states"]))
    nexts = sum(j << (ib * e) for e, j in enumerate(t["successors"]))
    block = ", ".join("true" if c == "1" else "false" for c in t["word"])
    digits = sys.get_int_max_str_digits()
    sys.set_int_max_str_digits(0)  # the packed tables have thousands of digits
    try:
        windows, labels, nexts = str(windows), str(labels), str(nexts)
    finally:
        sys.set_int_max_str_digits(digits)
    return (f"/-- The chain lock of `{seed}` at distance {distance}: the block `{t['word']}`, {t['cells']} cells, "
            f"labels modulo {t['modulus']}, {n} states. -/\n"
            f"def {name} : WTrap :=\n"
            f"  {{ b := [{block}], K := {t['cells']}, m := {t['modulus']}, n := {n}, lb := {lb}, ib := {ib},\n"
            f"    u := {t['first']},\n    R := {windows},\n    L := {labels},\n    S := {nexts} }}\n\n"
            f"theorem {name}_check : {name}.check = true := by decide +kernel\n")


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
    parser.add_argument("--ether", action="store_true", help="the chain of 0 1^7 and the kit's wall")
    parser.add_argument("--wall", type=str, default="", help="periods P for wall_returns of 0 1^(P-1)")
    parser.add_argument("--short", type=str, default="", help="periods whose seeds' chains to scan for shorter periods")
    parser.add_argument("--t001", action="store_true", help="the kit's trap for 001 as a chain")
    parser.add_argument("--verify", action="store_true", help="check the chain locks of short-period blocks directly")
    parser.add_argument("--lean", action="store_true", help="print the trap entries of WordTraps.lean")
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
        found = short_scan([int(p) for p in args.short.split(",")], args.width, args.depth, args.workers)
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
    if args.lean:
        print("\n".join(lean_trap(name, seed, width, distance, want) for name, seed, width, distance, want in TRAPS))
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
