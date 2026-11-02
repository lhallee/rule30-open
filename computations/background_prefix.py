"""Truncations of the backgrounds at the edges of the trap modules' walls, against the carried traps.

Each wall of the trap modules (`lock_chain.NATURAL`, carried in NineTraps, TenTraps and ElevenTraps to FourteenTraps)
is carried leftward by its chain, and the chain becomes periodic in the distance: from distance s on, column D + q is
column D. The columns from s on are a background, periodic in time and in space (`space_time_periodic`), and the trap
T_D carried to distance D is D chain columns, then the wall. Column D of the background repeats the block of T_D, so
the background right of it, cut after K cells and followed by a short word u and white, is a right half driven by that
block: the natural slow halves for T_D, as the truncated ether is for the kit's family (`ether_prefix`).

`background` builds the chain of a wall, its start s and period q; `bg_column` reads the background at any distance,
`ring_row` one row of it on its ring of q cells. `half_bits` is the background right of a column at a label, and
`block_phase` the phase of the block the column reads there. `inside_counts` asks, for every column of the background
that repeats the block of a trap, at how many labels the background right of it is a state of the trap. For the three
walls with s = 0 the background's window right of the wall's column is a state of the wall, so the halves beside the
aligned columns are in the trap at every label, and so is every truncation at least as wide as the trap. For the walls
with s > 0 no background half is in its trap, and T_D for D = x + i q, D - s at least the trap's width, is a trap of
the same block whose states, cut to the trap's width, are the background half beside x: apart from the trap, so entry
into it is false (`sibling`, checked independently with `lock_chain.apart_closed` in `sibling_apart`).
`sibling_identity` checks that T_(d + q) is T_d with q background columns in front. `truncation_entry` runs the
truncations: the entry step into the trap, whether column 1 kept the background's values before it, and entry into an
apart sibling (`family_depth`), which a half never leaves. `lean_siblings` and `lean_prefix` write the tables of
`Rule30Open.Columns.BackgroundSiblings` and `Rule30Open.Columns.BackgroundPrefix`.

    python -m computations.background_prefix --walls   # every trap: s, q, background halves inside, seconds
    python -m computations.background_prefix --siblings   # traps refuted by a background sibling, seconds
    python -m computations.background_prefix --truncate ten --kmax 465 --tail 4 --steps 50000   # ten0, ten1, ten23
    python -m computations.background_prefix --truncate NineTraps --names nine8 --kmax 135 --tail 2 --steps 5000
    python -m computations.background_prefix --lean-siblings   # the tables of BackgroundSiblings.lean
    python -m computations.background_prefix --lean-prefix   # the data of BackgroundPrefix.lean
"""

from __future__ import annotations

import argparse
import functools
import sys
from dataclasses import dataclass

import numpy as np
from tqdm.auto import tqdm

from computations import absorption
from computations import lock_chain as lc
from computations.period_three import in_sorted

MASK64 = (1 << 64) - 1
# The walls of the trap modules, by module, and the distances each module carries them to.
MODULE_WALLS = {"NineTraps": [("trap001011111", "nine")], "TenTraps": [("trap0000010001", "ten")],
                "ElevenTraps": [(name, f"el{k}_") for k, name in enumerate(lc.WALLS[11])],
                "TwelveTraps": [(name, f"tw{k}_") for k, name in enumerate(lc.WALLS[12])],
                "ThirteenTraps": [(name, f"th{k}_") for k, name in enumerate(lc.WALLS[13])],
                "FourteenTraps": [(name, f"fo{k}_") for k, name in enumerate(lc.WALLS[14])]}
# The three blocks of TenTraps whose truncations the module runs in full: the wall itself, the first block with
# columns of the background beside which the background half is outside its trap, and the block of the widest trap.
TEN_BLOCKS = [0, 1, 23]


@dataclass(frozen=True)
class Background:
    """A wall carried by its chain: the wall's name, its labels' modulus, its width, the chain columns at distances 0
    to start + period - 1 (each a word with letter l the column at label l), where the chain becomes periodic, and its
    period in the distance."""
    name: str
    modulus: int
    cells: int
    columns: tuple[str, ...]
    start: int
    period: int


@functools.lru_cache(maxsize=None)
def background(name: str) -> Background:
    """The chain of the wall `name` of `lock_chain.NATURAL` and where it becomes periodic (`lock_chain.chain_cycle`)."""
    t = lc.tables(name)
    word, modulus = t["word"], t["modulus"]
    full = word * (modulus // len(word))  # the wall's block at its labels; its least rotation, so labels are kept
    values = "".join(str((t["first"] >> label) & 1) if full[label] == "0" else "0" for label in range(modulus))
    start, cycle = lc.chain_cycle(full, values)
    columns = lc.chain(full, values, start + len(cycle) - 1)
    return Background(name, modulus, t["cells"], tuple(columns), start, len(cycle))


def bg_column(bg: Background, distance: int) -> str:
    """The background's column at a distance, any integer: the chain column for distance >= start, continued
    periodically to the right of the start."""
    return bg.columns[bg.start + (distance - bg.start) % bg.period]


def ring_row(bg: Background, label: int) -> list[int]:
    """The background's row at a label on its ring, cell i (left to right) the column at distance -i."""
    return [int(bg_column(bg, -i)[label]) for i in range(bg.period)]


def half_bits(bg: Background, x: int, label: int, cells: int) -> int:
    """The background right of its column x at a label, cells 1 .. `cells`, bit j - 1 for cell j (distance x - j)."""
    return sum(int(bg_column(bg, x - j)[label]) << (j - 1) for j in range(1, cells + 1))


def block_phase(bg: Background, x: int, label: int) -> tuple[str, int]:
    """The block (least rotation) that the background's column x repeats, and its phase at `label`: the column reads
    letter (phase + k) of the block at label + k."""
    column = bg_column(bg, x)
    period = lc.least_period(column)
    word = lc.necklace(column[:period])
    phase = next(p for p in range(period) if all(column[(label + k) % bg.modulus] == word[(p + k) % period]
                                                  for k in range(bg.modulus)))
    return word, phase


def occurrences(bg: Background, word: str) -> list[int]:
    """The distances x in start .. start + period - 1 whose background column repeats `word`."""
    found = []
    for x in range(bg.start, bg.start + bg.period):
        column = bg_column(bg, x)
        period = lc.least_period(column)
        if period == len(word) and lc.necklace(column[:period]) == word:
            found.append(x)
    return found


def state_set(t: dict) -> set[tuple[int, int]]:
    """The states of a labelled trap as pairs of a phase of its block and a window, as entry compares them."""
    period = len(t["word"])
    return {(label % period, window) for label, window in t["states"]}


def inside_counts(bg: Background, distance: int) -> list[tuple[int, int]]:
    """For each column x of the background repeating the block of the trap carried to `distance`, the number of
    labels at which the background half beside x is a state of that trap."""
    t = lc.carried(bg.name, distance)
    states = state_set(t)
    found = []
    for x in occurrences(bg, t["word"]):
        hits = 0
        for label in range(bg.modulus):
            word, phase = block_phase(bg, x, label)
            hits += (phase, half_bits(bg, x, label, t["cells"])) in states
        found.append((x, hits))
    return found


def sibling_identity(bg: Background, distance: int) -> bool:
    """Whether the trap carried to distance + q is the trap carried to `distance` with the q background columns right
    of column distance + q in front of every state, label by label (for distance >= start)."""
    near, far = lc.carried(bg.name, distance), lc.carried(bg.name, distance + bg.period)
    if near["word"] != far["word"] or near["modulus"] != far["modulus"]:
        return False
    column, period = bg_column(bg, distance), len(near["word"])
    turn = next(r for r in range(period) if (column + column)[r:r + period] == near["word"])  # label 0 reads word[0]
    front = {label: half_bits(bg, distance + bg.period, (label + turn) % bg.modulus, bg.period)
             for label in range(bg.modulus)}
    return set(far["states"]) == {(label, front[label] | window << bg.period) for label, window in near["states"]}


def sibling(bg: Background, distance: int, x: int) -> int:
    """The least D = x + i q with D - start at least the width of the trap carried to `distance`: the trap carried to
    D has the background half beside x on its first D - start cells, so, cut to that width, it is that half."""
    width = distance + bg.cells
    i = max(0, -(-(width + bg.start - x) // bg.period))
    return x + i * bg.period


def sibling_apart(bg: Background, distance: int, x: int) -> bool:
    """Whether the sibling of `sibling` is apart, as a whole, from the trap carried to `distance`, by
    `lock_chain.apart_closed`: the independent check of what `inside_counts` reports as 0."""
    near, far = lc.carried(bg.name, distance), lc.carried(bg.name, sibling(bg, distance, x))
    return bool(lc.apart_closed(near, far).all())


def tail_words(tail: int) -> list[tuple[int, int]]:
    """Every word u of at most `tail` cells, as (length, bits), bit i the cell i + 1 of u."""
    return [(n, u) for n in range(tail + 1) for u in range(1 << n)]


def truncations(bg: Background, x: int, label: int, kmax: int, tail: int) -> list[tuple[int, int, int, int]]:
    """The halves x_(K, u) beside column x at `label`: background on cells 1 .. K, then u, white beyond, for K = 1 ..
    kmax and every u of at most `tail` cells, as (K, length of u, u, half)."""
    base = half_bits(bg, x, label, kmax)
    return [(k, n, u, (base & ((1 << k) - 1)) | (u << k)) for k in range(1, kmax + 1) for n, u in tail_words(tail)]


def family_fields(bg: Background) -> list[np.ndarray]:
    """For each label, the sorted values of the start + width cells that follow the background prefix in a state of a
    trap carried to a distance D >= start: the chain's first start columns, then a state of the wall, as one word."""
    # out: M arrays of shape (k_L,)
    assert bg.start + bg.cells <= 64, "the field must fit one word"
    wall: dict[int, set[int]] = {}
    for label, w in lc.tables(bg.name)["states"]:
        wall.setdefault(label, set()).add(w)
    fields = []
    for label in range(bg.modulus):
        transient = sum(int(bg.columns[bg.start - 1 - j][label]) << j for j in range(bg.start))
        fields.append(np.array(sorted(transient | (w << bg.start) for w in wall.get(label, ())), dtype=np.uint64))
    return fields


def bits_at(rows: np.ndarray, offset: np.ndarray) -> np.ndarray:
    """The 64 bits of each row starting at its own bit offset."""
    # rows: (n, words); offset: (n,)
    index = np.arange(rows.shape[0])  # (n,)
    word, shift = offset // 64, (offset % 64).astype(np.uint64)  # (n,) each
    low = rows[index, word] >> shift  # (n,)
    high = rows[index, np.minimum(word + 1, rows.shape[1] - 1)]  # (n,)
    high = np.where(shift == 0, np.uint64(0), high << ((np.uint64(64) - shift) % np.uint64(64)))  # (n,)
    return low | high  # (n,)


def lowest_bit(v: np.ndarray) -> np.ndarray:
    """The index of the lowest set bit of each nonzero word."""
    # v: (n,)
    low = v & (~v + np.uint64(1))  # (n,), the lowest set bit alone
    out = np.zeros(v.shape, dtype=np.int64)  # (n,)
    for b in (32, 16, 8, 4, 2, 1):
        big = low >= (np.uint64(1) << np.uint64(b))  # (n,)
        out += np.where(big, b, 0)
        low = np.where(big, low >> np.uint64(b), low)
    return out  # (n,)


def family_depth(bg: Background, x: int, rows: np.ndarray, label: int, ref: np.ndarray,
                 fields: list[np.ndarray]) -> np.ndarray:
    """For each row, a distance D = x + i q >= start at which it is a state of the trap carried to D, or -1: its first
    D - start cells the background half beside x (`ref`, at `label`), then the field of `family_fields`. The first
    cell off the background lies in the field, so only the largest D whose field covers it, the one before, and D = x
    when start = 0 (the background's window is then a state of the wall) can hold."""
    # rows: (n, words); ref: (r,) with r <= words
    n, r = rows.shape[0], ref.size
    differ = rows[:, :r] ^ ref  # (n, r)
    nonzero = differ != 0  # (n, r)
    first = np.where(nonzero.any(axis=1), nonzero.argmax(axis=1), r)  # (n,)
    word = differ[np.arange(n), np.minimum(first, r - 1)]  # (n,)
    agree = np.where(first < r, first * 64 + lowest_bit(np.where(first < r, word, np.uint64(1))), r * 64)  # (n,)
    top = agree + bg.start
    largest = top - ((top - x) % bg.period)  # (n,), the largest D = x mod q with D - start <= agree
    found = np.full(n, -1, dtype=np.int64)  # (n,)
    keep = (1 << (bg.start + bg.cells)) - 1
    for cand in ([np.full(n, x)] if bg.start == 0 else []) + [largest, largest - bg.period]:
        ok = (cand >= bg.start) & (cand - bg.start + bg.start + bg.cells <= r * 64) & (found < 0)  # (n,)
        ok &= cand - bg.start <= agree
        if not ok.any():
            continue
        field = bits_at(rows, np.where(ok, cand - bg.start, 0)) & np.uint64(keep)  # (n,)
        ok &= in_sorted(field, fields[label])
        found = np.where(ok, cand, found)
    return found  # (n,)


@dataclass
class Entry:
    """The run of the truncations beside one column at one label: K, the tail's length and bits, the entry step into
    the trap or -1, whether column 1 kept the background's values at every step before entry (or before the end), the
    first step at which the half is a state of a trap carried to a distance D = x + i q (`family_depth`), or -1, and
    that D."""
    k: np.ndarray  # (n,)
    length: np.ndarray  # (n,)
    u: np.ndarray  # (n,)
    entry: np.ndarray  # (n,)
    clean: np.ndarray  # (n,)
    family: np.ndarray  # (n,)
    depth: np.ndarray  # (n,)


def truncation_entry(bg: Background, distance: int, x: int, label: int, kmax: int, tail: int,
                     steps: int) -> Entry:
    """Run every truncation of `truncations` beside column x from `label`, driven by the block of the trap carried to
    `distance`, for at most `steps` steps: entry into that trap, column 1 against the background's, and entry into the
    traps carried to the distances c + i q (`family_depth`), for every column c of the background repeating the block
    whose half is outside the trap. A half stops once it is in the trap, or in such a trap carried to a D with
    D - start at least the trap's width, which is apart from the trap (`sibling_apart`), so it never enters."""
    t = lc.carried(bg.name, distance)
    word, period, cells = t["word"], len(t["word"]), t["cells"]
    _, phase = block_phase(bg, x, label)
    states = state_set(t)
    items = truncations(bg, x, label, kmax, tail)
    blocks = (cells + 63) // 64
    firsts = [np.array(sorted({w & MASK64 for ph, w in states if ph == q}), dtype=np.uint64)
              for q in range(period)]  # first words of the windows, by phase
    width = kmax + tail
    words = (width + steps) // 64 + blocks + 2
    span = min(words, (kmax + tail + 2 * bg.period + bg.start + cells) // 64 + 2)  # words the family check reads
    assert bg.modulus == period, "the walls here count labels modulo the block's period"
    # the columns of the background repeating the block whose half is outside the trap, with the label at which each
    # reads each phase of the block: the traps carried to D = c + i q, D - start >= the trap's width, are apart from it
    others = [(c, {block_phase(bg, c, lab)[1]: lab for lab in range(bg.modulus)})
              for c, h in inside_counts(bg, distance) if h == 0]
    refs = {}
    for c, _ in others:
        for lab in range(bg.modulus):
            ref = half_bits(bg, c, lab, 64 * span)
            refs[c, lab] = np.array([(ref >> (64 * j)) & MASK64 for j in range(span)], dtype=np.uint64)  # (span,)
    fields = family_fields(bg)
    rows = np.zeros((len(items), words), dtype=np.uint64)  # (n, words)
    for i, (_, _, _, half) in enumerate(items):
        for j in range(0, width + 1, 64):
            rows[i, j // 64] = np.uint64((half >> j) & MASK64)
    n = len(items)
    entry = np.full(n, -1, dtype=np.int64)  # (n,)
    family = np.full(n, -1, dtype=np.int64)  # (n,)
    depth = np.full(n, -1, dtype=np.int64)  # (n,)
    clean = np.ones(n, dtype=bool)  # (n,)
    alive = np.arange(n)  # (m,), row i of `rows` is item alive[i]
    first_col = [int(bg_column(bg, x - 1)[lab]) for lab in range(bg.modulus)]  # (M,)
    full = (1 << cells) - 1
    low = np.uint64((1 << min(cells, 64)) - 1)
    need_family = bool(others)
    for s in tqdm(range(steps), desc=f"{bg.name} d={distance} x={x} label={label}", file=sys.stderr, leave=False,
                  mininterval=10):
        q, lab = (s + phase) % period, (label + s) % bg.modulus
        for r in np.flatnonzero(in_sorted(rows[:, 0] & low, firsts[q]) & (entry[alive] < 0)).tolist():
            window = sum(int(rows[r, j]) << (64 * j) for j in range(blocks)) & full
            if (q, window) in states:
                entry[alive[r]] = s
        open_ = family[alive] < 0  # (m,)
        if need_family and open_.any():
            found = np.full(int(open_.sum()), -1, dtype=np.int64)  # (o,)
            sub = rows[open_]  # (o, words)
            for c, label_of in others:
                at = label_of[q]  # the label at which column c reads the phase the drive reads now
                more = family_depth(bg, c, sub, at, refs[c, at], fields)  # (o,)
                found = np.where(found >= 0, found, more)
            got = alive[open_][found >= 0]
            family[got], depth[got] = s, found[found >= 0]
        clean[alive[(entry[alive] < 0) & ((rows[:, 0] & np.uint64(1)) != np.uint64(first_col[lab]))]] = False
        done = (entry[alive] >= 0) | ((family[alive] >= 0) & (depth[alive] - bg.start >= distance + cells))  # (m,)
        if done.any():
            rows, alive = rows[~done], alive[~done]
            if len(alive) == 0:
                break
        active = (width + s) // 64 + blocks + 2
        rows[:, :active] = absorption.step_rows(rows[:, :active], int(word[q]))
    k = np.array([it[0] for it in items], dtype=np.int64)  # (n,)
    length = np.array([it[1] for it in items], dtype=np.int64)  # (n,)
    u = np.array([it[2] for it in items], dtype=np.int64)  # (n,)
    return Entry(k, length, u, entry, clean, family, depth)


def base_length(e: Entry, period: int) -> int:
    """The base length B of the shift lemma: the largest, over the residues of K modulo `period`, of the least K in that
    residue whose truncations all enter with column 1 the background's before entry; -1 if some residue has no such K
    among those run. When every truncation of K >= W enters at step 0, B is below W + `period`."""
    kmax = int(e.k.max())
    good = {int(kk): bool(((e.entry[e.k == kk] >= 0) & e.clean[e.k == kk]).all()) for kk in range(1, kmax + 1)}
    best = -1
    for r in range(period):
        ks = [kk for kk in range(1, kmax + 1) if kk % period == r]
        firsts = [kk for kk in ks if good[kk]]
        if not firsts:
            return -1
        best = max(best, firsts[0])
    return best


def module_traps(module: str) -> list[tuple[str, str, int]]:
    """The traps of a wall module as (wall, Lean name, distance)."""
    found = []
    if module == "NineTraps":
        found = [("trap001011111", f"nine{d}" if d else "trap001011111", d) for d in lc.nine_distances()]
    elif module == "TenTraps":
        found = [("trap0000010001", f"ten{d}", d) for d in lc.ten_distances()]
    else:
        period = {"ElevenTraps": 11, "TwelveTraps": 12, "ThirteenTraps": 13, "FourteenTraps": 14}[module]
        prefix = dict(MODULE_WALLS[module])
        found = [(name, f"{prefix[name]}{d}", d) for name, d, _ in lc.wall_distances(period, lc.WALL_DEPTHS[period])]
    return found


def refuted_blocks(module: str) -> set[str]:
    """The blocks of the module whose trap's entry is already false by the lists of `lock_chain`: the test of reach at
    20 and 22 cells, halves apart, the walls of 22 cells, and the long-run chain trap that refutes `ten1`."""
    found = set(lc.UNREACHED.get(module, ())) | set(lc.UNREACHED_WIDE.get(module, ())) | set(lc.APART.get(module, ()))
    names = {name for mod, name, *_ in lc.REACH_REFUTED if mod == module} | \
        {name for mod, name in lc.WIDE_WALLS if mod == module}
    for name, lean, d in module_traps(module):
        if lean in names:
            found.add(lc.carried_word(name, d))
    if module == "TenTraps":
        found.add("0001001101")  # `ten1`, apart from a chain lock of 583 cells (`lock_chain.chain_apart`)
    return found


def walls_report() -> list[dict]:
    """For every trap of the wall modules: its module, name, distance, block, width, the wall's chain start and period,
    and `inside_counts`."""
    rows = []
    for module in MODULE_WALLS:
        traps = module_traps(module)
        for name, lean, d in tqdm(traps, desc=module, file=sys.stderr, leave=False):
            bg = background(name)
            t = lc.carried(name, d)
            rows.append({"module": module, "name": lean, "wall": name, "distance": d, "block": t["word"],
                         "cells": t["cells"], "start": bg.start, "period": bg.period, "modulus": bg.modulus,
                         "inside": inside_counts(bg, d)})
    return rows


def column_classes(bg: Background, distance: int, kmax: int) -> list[tuple[int, int, int]]:
    """The columns of the background repeating the trap's block, up to the symmetries of the background: two columns
    whose halves of `kmax` + 64 cells are the same set of (phase, half) over the labels give the same truncations.
    Each class as (a column x, the number of other columns in it, the labels at which its half is in the trap)."""
    classes: dict[frozenset, list[tuple[int, int]]] = {}
    for x, hits in inside_counts(bg, distance):
        key = frozenset((block_phase(bg, x, label)[1], half_bits(bg, x, label, kmax + 64))
                        for label in range(bg.modulus))
        classes.setdefault(key, []).append((x, hits))
    return [(members[0][0], len(members) - 1, members[0][1]) for members in classes.values()]


def truncation_summary(bg: Background, distance: int, kmax: int, tail: int, steps: int) -> list[dict]:
    """`truncation_entry` from every label beside one column of each class of `column_classes`, summed up: halves,
    entries into the trap (at step 0, and the least K from which every truncation is in it at step 0), the latest
    entry, entries after step 0 with column 1 off the background before, entries into an apart sibling and their
    latest step and distances, halves with neither, and the base length B (`base_length`), the largest over labels."""
    t = lc.carried(bg.name, distance)
    out = []
    for x, same, inside in column_classes(bg, distance, kmax):
        runs = [truncation_entry(bg, distance, x, label, kmax, tail, steps) for label in range(bg.modulus)]
        entry = np.concatenate([e.entry for e in runs])  # (h,)
        k = np.concatenate([e.k for e in runs])  # (h,)
        clean = np.concatenate([e.clean for e in runs])  # (h,)
        family = np.concatenate([e.family for e in runs])  # (h,)
        depth = np.concatenate([e.depth for e in runs])  # (h,)
        apart = (entry < 0) & (family >= 0) & (depth - bg.start >= distance + t["cells"])  # (h,)
        k0 = min([kk for kk in range(1, kmax + 1) if (entry[k >= kk] == 0).all()], default=-1)
        bases = [base_length(e, bg.period) for e in runs]
        out.append({"block": t["word"], "cells": t["cells"], "x": x, "same": same, "inside": inside,
                    "halves": int(entry.size), "entered": int((entry >= 0).sum()), "zero": int((entry == 0).sum()),
                    "k0": k0, "latest": int(entry.max()), "unclean": int(((entry > 0) & ~clean).sum()),
                    "apart": int(apart.sum()), "apart_latest": int(family[apart].max()) if apart.any() else -1,
                    "depths": sorted(set(depth[apart].tolist()))[:6], "open": int(((entry < 0) & ~apart).sum()),
                    "base": -1 if min(bases) < 0 else max(bases)})
    return out


def sibling_entries() -> list[tuple[str, str, str, int, int, int]]:
    """The traps of the wall modules refuted by a background sibling (`sibling_apart`) whose entry no list of
    `lock_chain` refutes already (`refuted_blocks`): (module, Lean name, wall, distance, column x, sibling distance D),
    D the least over the columns x outside the trap."""
    found = []
    for module in MODULE_WALLS:
        done = refuted_blocks(module)
        for name, lean, d in module_traps(module):
            bg = background(name)
            outside = [x for x, h in inside_counts(bg, d) if h == 0]
            if not outside or lc.carried_word(name, d) in done:
                continue
            x = min(outside, key=lambda c: sibling(bg, d, c))
            found.append((module, lean, name, d, x, sibling(bg, d, x)))
    return found


def lean_siblings(piece: int = 1 << 16) -> str:
    """The declarations of `Rule30Open.Columns.BackgroundSiblings`: for each entry of `sibling_entries`, the sibling as
    a trap with its kernel check that it is closed, the refuted trap's states as a set of windows (`WinSet` of
    `ReachRefuted`), that they hold its states and that the sibling avoids them, and the refutation of entry
    (`not_absorption_fwd`)."""
    out = []
    for module, lean, name, d, x, depth in tqdm(sibling_entries(), desc="siblings", file=sys.stderr, leave=False):
        bg = background(name)
        c, sib = lc.carried(name, d), lc.carried(name, depth)
        assert c["word"] == sib["word"] and lc.apart_closed(c, sib).all()
        cert, word = f"sib_{lean}", c["word"]
        doc = (f"/-- The sibling of `{lean}`: the wall carried {depth} columns, {depth - bg.start} of them columns of "
               "the background. The block")
        out.append(lc.lean_entry(sib, cert, piece).replace("/-- The block", doc, 1)
                   + f"\ntheorem {cert}_closed : {cert}.closedCheck = true := by decide +kernel\n\n"
                   f"/-- The states of `{lean}`, by label. -/\n"
                   + lc.lean_winset(f"{cert}_cut", word, c["cells"], lc.cut_rows((c,), c["cells"]), piece)
                   + f"\ntheorem {cert}_holds : {cert}_cut.holds {lean} = true := by decide +kernel\n\n"
                   f"theorem {cert}_avoids : {cert}_cut.avoids {cert} = true := by decide +kernel\n\n"
                   f"/-- **Entry into `{lean}` ({module}) is false**: the right half of state 0 of its sibling never "
                   f"enters it. -/\ntheorem {lean}_not_absorption_sibling : ¬ {lean}.Absorption :=\n"
                   f"  not_absorption_fwd _ {cert} {cert}_cut {cert}_closed rfl rfl (by decide) (by decide)\n"
                   f"    {cert}_holds {cert}_avoids (by decide)\n")
    return "\n".join(out)


def ring_rows(bg: Background) -> list[int]:
    """The background's rows on its ring, one per label, bit p the cell at position p (`ring_row`), as
    `BackgroundPrefix.lean` reads them."""
    return [sum(c << p for p, c in enumerate(ring_row(bg, label))) for label in range(bg.modulus)]


def prefix_entries(bg: Background, distance: int) -> list[tuple[int, int, int, int]]:
    """For the trap carried to `distance`, each column of the background whose half is inside it (`inside_counts`) and
    each label: (the column's position on the ring, label, phase of the block there, index of the trap's state equal
    to the background's window), as `BackgroundPrefix.lean` checks them."""
    t = lc.carried(bg.name, distance)
    index = {(label % len(t["word"]), window): i for i, (label, window) in enumerate(t["states"])}
    found = []
    for x, hits in inside_counts(bg, distance):
        if hits != bg.modulus:
            continue
        for label in range(bg.modulus):
            _, phase = block_phase(bg, x, label)
            found.append(((-x) % bg.period, label, phase, index[(phase, half_bits(bg, x, label, t["cells"]))]))
    return found


# The walls whose chains are periodic from distance 0, with their module, the Lean names of the ring and of the list,
# and the module's traps: the background's window beside the wall's column is a state of the wall.
PREFIX_WALLS = [("TenTraps", "trap0000010001", "tenRing", "tenBackground"),
                ("TwelveTraps", "trap000110110011", "twelveRing", "twelveBackground"),
                ("FourteenTraps", "trap00011100101011", "fourteenRing", "fourteenBackground")]


def lean_prefix() -> str:
    """The data of `Rule30Open.Columns.BackgroundPrefix`: for each wall of `PREFIX_WALLS`, the rows of its background
    (`ring_rows`) and, for each trap of the module carried from it, the positions of the aligned columns and the
    entries of `prefix_entries` packed 16 bits each, the phase in the low 4 and the state's index above."""
    out = []
    for module, wall, ring, listing in PREFIX_WALLS:
        bg = background(wall)
        assert bg.start == 0
        rows = ", ".join(str(v) for v in ring_rows(bg))
        out.append(f"/-- The background of period {bg.modulus} on its ring of {bg.period} cells, one row per label: "
                   f"position 0 is the column of `{wall[4:]}`, position `p` the column `p` cells right of it. -/\n"
                   f"def {ring} : List Nat :=\n  [{rows}]\n")
        items = []
        for name, lean, d in module_traps(module):
            if name != wall:
                continue
            entries = prefix_entries(bg, d)
            positions = list(dict.fromkeys(p for p, *_ in entries))
            code = 0
            for p, label, phase, i in entries:
                assert phase < 16 and i < 1 << 12
                code |= (i * 16 + phase) << (16 * (positions.index(p) * bg.modulus + label))
            items.append(f"({lean}, [{', '.join(map(str, positions))}], {code})")
        out.append(f"/-- The traps of {module} carried from `{wall[4:]}`, each with the positions of the columns of "
                   f"`{ring}` aligned with it and their entries. -/\n"
                   f"def {listing} : List (WTrap × List Nat × Nat) :=\n  [" + ",\n   ".join(items) + "]\n")
    return "\n".join(out)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--walls", action="store_true", help="every wall: start, period, background halves inside")
    parser.add_argument("--siblings", action="store_true", help="traps refuted by a background sibling")
    parser.add_argument("--lean-siblings", action="store_true", help="print BackgroundSiblings.lean's tables")
    parser.add_argument("--lean-prefix", action="store_true", help="print BackgroundPrefix.lean's data")
    parser.add_argument("--truncate", default="", help="'ten' for TEN_BLOCKS, or a module name, or 'all'")
    parser.add_argument("--blocks", default="", help="with --truncate ten, the distances to run instead of TEN_BLOCKS")
    parser.add_argument("--names", default="", help="with --truncate, only the traps of these Lean names")
    parser.add_argument("--kmax", type=int, default=465, help="longest truncation; 0 for three times the period")
    parser.add_argument("--tail", type=int, default=4)
    parser.add_argument("--steps", type=int, default=50000)
    args = parser.parse_args()
    if args.lean_siblings:
        print(lean_siblings())
    if args.lean_prefix:
        print(lean_prefix())
    if args.walls:
        for row in walls_report():
            counts = sorted({h for _, h in row["inside"]})
            print(f"{row['module']} {row['name']} d={row['distance']} {row['block']} cells={row['cells']} "
                  f"start={row['start']} q={row['period']} columns in background={len(row['inside'])} "
                  f"labels inside={counts}")
    if args.siblings:
        for module in MODULE_WALLS:
            done = refuted_blocks(module)
            new, old = [], []
            for name, lean, d in module_traps(module):
                bg = background(name)
                outside = [x for x, h in inside_counts(bg, d) if h == 0]
                if not outside:
                    continue
                x = min(outside, key=lambda c: sibling(bg, d, c))
                D = sibling(bg, d, x)
                assert sibling_apart(bg, d, x), (module, lean)
                block = lc.carried_word(name, d)
                (old if block in done else new).append(f"{lean} ({block}, sibling T_{D}, "
                                                      f"{D + bg.cells} cells)")
            print(f"{module}: {len(new) + len(old)} traps refuted by a background sibling, {len(new)} not refuted "
                  f"before: {new}; refuted before as well: {len(old)}")
    if args.truncate:
        if args.truncate == "ten":
            chosen = [int(d) for d in args.blocks.split(",")] if args.blocks else TEN_BLOCKS
            jobs = [("TenTraps", "trap0000010001", f"ten{d}", d) for d in chosen]
        else:
            modules = list(MODULE_WALLS) if args.truncate == "all" else args.truncate.split(",")
            jobs = [(m, name, lean, d) for m in modules for name, lean, d in module_traps(m)]
        if args.names:
            jobs = [job for job in jobs if job[2] in args.names.split(",")]
        for module, name, lean, d in jobs:
            bg = background(name)
            kmax = args.kmax or 3 * bg.period
            for row in truncation_summary(bg, d, kmax, args.tail, args.steps):
                print(f"{module} {lean} {row['block']} width {row['cells']}, column x={row['x']} (and "
                      f"{row['same']} more alike), labels inside {row['inside']}: K 1..{kmax}, tails <= {args.tail}, "
                      f"{args.steps} steps, {row['halves']} halves: in the trap {row['entered']} (at step 0 "
                      f"{row['zero']}, every K >= {row['k0']}), latest entry {row['latest']}, entered later with "
                      f"column 1 off the background {row['unclean']}; in an apart sibling {row['apart']} (latest "
                      f"{row['apart_latest']}, D {row['depths']}); neither {row['open']}; B {row['base']}",
                      flush=True)


if __name__ == "__main__":
    main()
