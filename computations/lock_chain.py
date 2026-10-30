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
whether the white right half settles.

    python -m computations.lock_chain --chain 8,9,10,11,12,13 --depth 12   # the chains of 0 1^(P-1), 15 s
    python -m computations.lock_chain --classify 4,8,10,11,12 --width 13 --workers 3   # every lock's seed, about 2 min
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
    """The trap of `NATURAL` named `name` carried `distance` columns left by its chain: the block at that distance, read
    with the seed's labels, and as tables (`relabeled_tables`). The seed's lock values are its first cells at its white
    labels; the d columns of the chain go in front of each state's window."""
    seed, _, _, cells, modulus = next(entry for entry in NATURAL if entry[0] == name)[1:]
    t = tables(name)
    word, period = t["word"], len(t["word"])
    full = word * (modulus // period)  # the seed at its labels
    values = "".join(str((t["first"] >> label) & 1) if full[label] == "0" else "0" for label in range(modulus))
    columns = chain(full, values, distance)  # columns m, m - 1, .., m - distance at the labels
    nodes = set()
    for label, window in t["states"]:
        near = sum(int(columns[distance - 1 - j][label]) << j for j in range(distance))
        nodes.add((label, near | window << distance))
    return relabeled_tables(columns[distance], distance + cells, nodes)


# Natural traps: name, word, a right half that a run of the word drives into the trap (bit i is column i + 1;
# `right_half.random_starts(300, 64)[13]`, `[2]` and `[79]`), the time, the width and the modulus. The first is checked
# in `Rule30Open.Columns.WordTraps`, the second in `Rule30Open.Columns.NineTraps`; the third, a second trap for 01, is
# the chain of the lock of 0^4 1 0 1^8 (`test_period_two_fourteen`).
NATURAL = [("trap001011111", "001011111", 18202347099481127113, 12000, 43, 9),
           ("trap001010011", "001010011", 12828593127923856452, 12000, 41, 27),
           ("trap01fourteen", "01", 18368822234183756340, 12000, 31, 14)]


def tables(name: str) -> dict:
    """The tables of a trap of `TRAPS` or `NATURAL`."""
    for entry in TRAPS:
        if entry[0] == name:
            return trap_tables(*entry[1:])
    entry = next(entry for entry in NATURAL if entry[0] == name)
    return natural_tables(*entry[1:])


def lean_entry(t: dict, name: str) -> str:
    """The Lean definition of a trap `WTrap` from its tables, packed as the kit packs `t001`."""
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
    return (f"/-- The block `{t['word']}`: {t['cells']} cells, labels modulo {t['modulus']}, {n} states. -/\n"
            f"def {name} : WTrap :=\n"
            f"  {{ b := [{block}], K := {t['cells']}, m := {t['modulus']}, n := {n}, lb := {lb}, ib := {ib},\n"
            f"    u := {t['first']},\n    R := {windows},\n    L := {labels},\n    S := {nexts} }}\n")


def lean_trap(name: str) -> str:
    """The Lean entry `WTrap` for a trap of `TRAPS` or `NATURAL`, with its kernel check."""
    return lean_entry(tables(name), name) + f"\ntheorem {name}_check : {name}.check = true := by decide +kernel\n"


def nine_distances() -> list[int]:
    """The least distance at which the chain of the period-9 wall `001011111` holds each block of period 9."""
    seen, found = set(), []
    for distance in range(30):
        word = carried("trap001011111", distance)["word"]
        if len(word) == 9 and word not in seen:
            seen.add(word)
            found.append(distance)
    return found


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


def natural_scan(word: str, steps: int, starts: int = 30) -> tuple[int, list[tuple[int, int, int, int, int]]]:
    """For the empty right half and `starts` random ones (`right_half.random_starts`), driven by `word`: how many lock
    column 1 over the second half of `steps` steps (`right_half.locked_period`), and for those the natural traps
    found at three late checkpoints, at the least width from 16 to 64 and with the phase modulo the lock's period or
    twice it, each as (start, time, width, modulus, size)."""
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
        hit = natural_trap(word, start, late, list(range(16, 65)), [period, 2 * period]) if late else None
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
    parser.add_argument("--rest", type=int, default=None, help="with --short, only seeds of a long run and this many "
                        "other cells")
    parser.add_argument("--t001", action="store_true", help="the kit's trap for 001 as a chain")
    parser.add_argument("--verify", action="store_true", help="check the chain locks of short-period blocks directly")
    parser.add_argument("--lean", action="store_true", help="print the trap entries of WordTraps.lean")
    parser.add_argument("--lean-white", action="store_true", help="print the runs of NineWhite.lean")
    parser.add_argument("--entry", type=str, default="", help="traps whose entry by small right halves to measure")
    parser.add_argument("--cells", type=int, default=8, help="with --entry, every half with support in these cells")
    parser.add_argument("--steps", type=int, default=50000)
    parser.add_argument("--sample", type=int, default=0, help="with --entry, this many random pairs of a half and a "
                        "phase instead of all")
    parser.add_argument("--natural", type=str, default="", help="periods whose words to search for natural traps")
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
        scan = functools.partial(natural_scan, steps=args.steps, starts=args.starts)
        with multiprocessing.Pool(args.workers) as pool:
            results = tqdm(pool.imap(scan, words), total=len(words), desc=f"period {period}", file=sys.stderr,
                           mininterval=10)
            for word, (locks_found, traps) in zip(words, results):
                if locks_found:
                    print(f"{word}: column 1 locks for {locks_found} of {args.starts + 1} starts; natural traps "
                          f"{traps}", flush=True)
        print(f"period {period}: done", flush=True)
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
