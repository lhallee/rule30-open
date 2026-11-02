"""The double-step game of the right half beside an alternating center, against the three closed sets together.

Beside an alternating center every right half of up to 20 cells enters one of three closed sets
(`computations.gate_census`): the gap trap (columns 1..16 with the count of white steps since the last black cell of
column 1), the kit's ether-and-wall family for 0101, and the lock of period seven (195 windows of 32 columns). This
module asks what a finite game says about all right halves at once.

A state of the game at width W is a window of columns 1..W at a white step of the center with the count d of white
steps since the last black cell of column 1 (d = 0 when column 1 is black, 1..4 when it is white, 4 meaning 4 or more,
and 5 for none yet). A move is a double step, white center then black, for one of the four values of column W + 1 at
the two steps (`gate_census.double_steps`). The game is the same in both phases of the center: the phase only fixes
which windows a finite half shows at its first white step (phase 1: its cells; phase 0: their image under a black
step). A consistent state has d = 0 exactly when column 1 is black, so the game has 3 * 2^W consistent states. A set
of states is held as one byte per window, bit d for the count d.

- `reach` (the test of reach): the states from which some play reaches the targets, which are over-approximated at
  widths below their own (`targets_over`): a gap-trap state if some extension to 16 columns is good for its count, a
  window that is the cut of a member of the family at any depth (`absorption.family_cut`), or a cut of a lock window.
  The states that cannot reach form a set that no move leaves; if nonempty, it avoids every target, and a finite half
  that enters it never enters the three sets.
- `forced_basin`: the states from which every play reaches the targets, under-approximated (`targets_under`): the
  gap trap's entry states (column 1 black, good with count 0), members of the family whose wall ends inside the
  window, and the lock only from W = 32 (so never here). The rank of a state is the sweep at which it enters.
- `residue`: the strongly connected components of the game outside the forced basin that hold a cycle, with the
  period of each (the gcd of its cycle lengths) and whether column 1 is a function of the cyclic class. The two
  states of the aligned ether (`ether_cycle`) lie in one of them at every width.
- `run_periodic`: spatially periodic right halves, run for a number of double steps, with their first exact entry
  into the three sets (`gate_census.gap_entry`, `absorption.family_depth`, the lock codes), and the states at
  width W of the halves that never enter.

    python -m computations.three_set_game reach --widths 10 12 14 16 18 19 20 22 24 26   # about 6 min, 2.1 GB at 26
    python -m computations.three_set_game basin --widths 16 17 18 19 20 21 22   # about 30 s
    python -m computations.three_set_game halves --period 12 --random 100 --max-period 32 --double-steps 10000 \
        --widths 16 18 20 22   # about 1 min
"""

from __future__ import annotations

import argparse
import functools
import sys
import time
from dataclasses import dataclass

import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components
from tqdm.auto import tqdm

from computations import absorption, gate_census

WORD = "0101"
COUNTS = 6  # d = 0 .. 4 and 5 for no black cell yet
ALL = np.uint8((1 << COUNTS) - 1)
GAP_WIDTH = gate_census.GAP_WIDTH
LOCK_WIDTH = gate_census.LOCK_WIDTH
CHUNK = 1 << 20  # windows per block when the successors are computed
ETHER_WORDS = ("0000010", "1001100")  # the aligned ether at the two white phases of the drive, cell 1 first


def after(d: int, black: int) -> int:
    """The count after a double step from count d, when column 1 is `black` at the new white step."""
    if black:
        return 0
    return 5 if d == 5 else min(d + 1, 4)


@functools.cache
def pull_table() -> np.ndarray:
    """For a byte of counts held at a window v and the color of column 1 of v, the byte of counts d from which a move
    into v lands on a held count: index 256 * (v & 1) + byte. Read-only."""
    table = np.zeros(512, dtype=np.uint8)  # (512,)
    for black in (0, 1):
        for byte in range(256):
            table[256 * black + byte] = sum(1 << d for d in range(COUNTS) if (byte >> after(d, black)) & 1)
    table.flags.writeable = False
    return table


@functools.cache
def popcount_table() -> np.ndarray:
    """The number of set bits of each byte. Read-only."""
    table = np.array([b.bit_count() for b in range(256)], dtype=np.int64)  # (256,)
    table.flags.writeable = False
    return table


def count(sets: np.ndarray) -> int:
    """The number of states in a set held as bytes."""
    # sets: (n,) uint8
    return int(popcount_table()[sets].sum())


def consistent(width: int) -> np.ndarray:
    """The consistent states: count 0 at windows black in column 1, counts 1 to 5 at the others."""
    return np.where(np.arange(1 << width) & 1, np.uint8(1), np.uint8(0x3E)).astype(np.uint8)  # (2^width,)


def start_states(width: int) -> np.ndarray:
    """The state of each window as the first white step of a half shows it: count 0 if black, else 5 (none yet)."""
    return np.where(np.arange(1 << width) & 1, np.uint8(1), np.uint8(1 << 5)).astype(np.uint8)  # (2^width,)


@dataclass
class Game:
    """The double-step game at one width: the four successors of every window, by the inputs 00, 01, 10, 11."""

    width: int
    succ: np.ndarray  # (4, 2^width) uint32
    cons: np.ndarray  # (2^width,) uint8, the consistent states


def successors(width: int) -> np.ndarray:
    """The four double steps of every window of `width` cells, in blocks of `CHUNK` windows."""
    n = 1 << width
    succ = np.empty((4, n), dtype=np.uint32)  # (4, 2^width)
    blocks = range(0, n, CHUNK)
    for lo in tqdm(blocks, desc=f"successors {width}", file=sys.stderr, leave=False, disable=len(blocks) < 8):
        hi = min(n, lo + CHUNK)
        succ[:, lo:hi] = gate_census.double_steps(np.arange(lo, hi, dtype=np.int64), width).T  # (4, block)
    return succ


def make_game(width: int) -> Game:
    """The game at `width` cells."""
    return Game(width, successors(width), consistent(width))


def pull(game: Game, sets: np.ndarray, every: bool) -> np.ndarray:
    """The states from which some move (or, if `every`, every move) lands in `sets`."""
    # sets: (n,) uint8
    white, black = pull_table()[:256], pull_table()[256:]  # (256,) each
    landing = white[sets]  # (n,) uint8, the counts that land in `sets` by a move into each window
    landing[1::2] = black[sets[1::2]]  # the windows black in column 1
    out = landing[game.succ[0]]  # (n,)
    for j in range(1, 4):
        if every:
            out &= landing[game.succ[j]]
        else:
            out |= landing[game.succ[j]]
    return out & game.cons  # (n,)


def reach(game: Game, target: np.ndarray, desc: str = "reach") -> tuple[np.ndarray, int]:
    """The consistent states from which some play reaches `target`, and the number of sweeps that added states."""
    # target: (n,) uint8
    seen = target & game.cons  # (n,)
    sweeps = 0
    with tqdm(desc=f"{desc} {game.width}", file=sys.stderr, leave=False) as bar:
        while True:
            new = seen | pull(game, seen, every=False)  # (n,)
            if np.array_equal(new, seen):
                return seen, sweeps
            seen, sweeps = new, sweeps + 1
            bar.update()


def forced_basin(game: Game, target: np.ndarray, desc: str = "basin") -> tuple[np.ndarray, list[int]]:
    """The consistent states from which every play reaches `target`, and the number of states of each rank: entry
    `r` counts the states that enter at sweep r, the target's states at rank 0. The largest rank is the length less
    one."""
    # target: (n,) uint8
    basin = target & game.cons  # (n,)
    total = count(basin)
    added = [total]
    with tqdm(desc=f"{desc} {game.width}", file=sys.stderr, leave=False) as bar:
        while True:
            new = basin | pull(game, basin, every=True)  # (n,)
            size = count(new)
            if size == total:
                return basin, added
            basin, added, total = new, added + [size - total], size
            bar.update()


def ranks(game: Game, target: np.ndarray) -> np.ndarray:
    """The rank of every state in the forced basin of `target`, -1 outside it and at inconsistent states; for small
    widths."""
    rank = np.full((1 << game.width, COUNTS), -1, dtype=np.int64)  # (n, 6)
    basin = target & game.cons  # (n,)
    sweep = 0
    while True:
        bits = ((basin[:, None] >> np.arange(COUNTS, dtype=np.uint8)) & 1).astype(bool)  # (n, 6)
        rank[bits & (rank < 0)] = sweep
        new = basin | pull(game, basin, every=True)  # (n,)
        if np.array_equal(new, basin):
            return rank
        basin, sweep = new, sweep + 1


# The targets.

def as_bytes(good: np.ndarray) -> np.ndarray:
    """A table of states (window, count) as one byte per window."""
    # good: (n, 6) bool
    return (good.astype(np.uint8) << np.arange(COUNTS, dtype=np.uint8)).sum(axis=1).astype(np.uint8)  # (n,)


def gap_over(width: int) -> np.ndarray:
    """The states whose window could be the cut of a window of 16 columns good for the gap trap with that count."""
    good = as_bytes(gate_census.gap_states(GAP_WIDTH))  # (2^16,)
    if width >= GAP_WIDTH:
        return good[np.arange(1 << width) & ((1 << GAP_WIDTH) - 1)]  # (2^width,)
    return np.bitwise_or.reduce(good.reshape(1 << (GAP_WIDTH - width), 1 << width), axis=0)  # (2^width,)


def gap_under(width: int) -> np.ndarray:
    """The entry states of the gap trap: column 1 black, count 0, and the first 16 columns good with count 0; none
    below 16 columns."""
    if width < GAP_WIDTH:
        return np.zeros(1 << width, dtype=np.uint8)  # (2^width,)
    entry = gate_census.gap_entry(GAP_WIDTH)  # (2^16,)
    return entry[np.arange(1 << width) & ((1 << GAP_WIDTH) - 1)].astype(np.uint8)  # (2^width,), bit 0


def family_over(width: int) -> np.ndarray:
    """The windows that are the first `width` cells of a member of the kit's family at a white step, at any depth:
    `absorption.family_cut` at the white phases 0 and 2 of the word, computed in blocks of windows."""
    wall = absorption.kit_wall()  # (4, 2^13)
    n = 1 << width
    inside = np.zeros(n, dtype=bool)  # (2^width,)
    for phase in (0, 2):
        for j0, shift in absorption.ALIGNMENTS[WORD]:
            psi = (phase + shift) % 4  # the ether phase of now
            pattern = sum(absorption.ether(j0 + p, psi) << (p - 1) for p in range(1, width + 1))
            for k in range(width + 7):
                if (j0 + k) % 7 != 2:
                    continue
                if k >= width:
                    inside[pattern] = True
                    continue
                cells = min(absorption.WALL_CELLS, width - k)
                starts = np.zeros(1 << cells, dtype=bool)  # (2^cells,), the wall states cut to `cells` cells
                starts[np.flatnonzero(wall[psi]) & ((1 << cells) - 1)] = True
                for lo in range(0, n, CHUNK):
                    w = np.arange(lo, min(n, lo + CHUNK), dtype=np.int64)  # (block,)
                    found = (((w ^ pattern) & ((1 << k) - 1)) == 0) & starts[(w >> k) & ((1 << cells) - 1)]
                    inside[lo:lo + w.size] |= found
    return np.where(inside, ALL, np.uint8(0)).astype(np.uint8)  # (2^width,)


def family_under(width: int) -> np.ndarray:
    """The windows that are members of the kit's family at a white step with the wall inside the window: the ether on
    columns 1..k and a wall state on columns k + 1 .. k + 13 <= width."""
    wall = absorption.kit_wall().reshape(-1)  # (4 2^13,)
    low = np.arange(1 << width, dtype=np.uint64)  # (2^width,)
    inside = np.zeros(1 << width, dtype=bool)  # (2^width,)
    for phase in (0, 2):  # the white steps of the drive
        depths, shifts, masks, patterns, offsets = absorption.family_terms(WORD, phase)  # (K,) each
        for k, shift, mask, pattern, offset in zip(depths, shifts, masks, patterns, offsets):
            if k + absorption.WALL_CELLS > width:
                continue
            strip = ((low >> shift) & np.uint64((1 << absorption.WALL_CELLS) - 1)).astype(np.int64)  # (2^width,)
            inside |= (((low ^ pattern) & mask) == 0) & wall[offset + strip]
    return np.where(inside, ALL, np.uint8(0)).astype(np.uint8)  # (2^width,)


@functools.cache
def lock_codes() -> np.ndarray:
    """The 195 windows of the lock of period seven, sorted. Read-only."""
    classes, _ = gate_census.seven_lock()
    codes = np.array(sorted(c for cls in classes for c in cls), dtype=np.int64)  # (195,)
    codes.flags.writeable = False
    return codes


def lock_over(width: int) -> np.ndarray:
    """The windows that are the first `width` cells of a window of the lock, of any class."""
    out = np.zeros(1 << width, dtype=np.uint8)  # (2^width,)
    if width <= LOCK_WIDTH:
        out[lock_codes() & ((1 << width) - 1)] = ALL
    return out


def lock_under(width: int) -> np.ndarray:
    """The windows of the lock, which needs its 32 columns: none at the widths of this module."""
    assert width < LOCK_WIDTH, "a byte per window is out of reach from 32 columns"
    return np.zeros(1 << width, dtype=np.uint8)  # (2^width,)


def targets_over(width: int) -> dict[str, np.ndarray]:
    """The three targets, over-approximated, for the test of reach."""
    return {"gap": gap_over(width), "family": family_over(width), "lock": lock_over(width)}  # (2^width,) each


def targets_under(width: int) -> dict[str, np.ndarray]:
    """The three targets, under-approximated, for the forced basin."""
    return {"gap": gap_under(width), "family": family_under(width), "lock": lock_under(width)}  # (2^width,) each


# The residue.

def bfs_levels(graph: csr_matrix, roots: np.ndarray) -> np.ndarray:
    """The distance of every node from the nearest root along the edges of `graph`, -1 if none."""
    # roots: (r,)
    level = np.full(graph.shape[0], -1, dtype=np.int64)  # (m,)
    frontier = roots.astype(np.int64)  # (f,)
    level[frontier] = 0
    depth = 0
    while frontier.size:
        lo, hi = graph.indptr[frontier], graph.indptr[frontier + 1]  # (f,) each
        lengths = hi - lo  # (f,)
        offsets = np.repeat(lo - np.cumsum(lengths) + lengths, lengths) + np.arange(int(lengths.sum()))  # (e,)
        nxt = np.unique(graph.indices[offsets])  # (e',)
        nxt = nxt[level[nxt] < 0]
        depth += 1
        level[nxt] = depth
        frontier = nxt
    return level  # (m,)


@dataclass
class Component:
    """A strongly connected component of the game outside the forced basin that holds a cycle."""

    size: int
    period: int  # the gcd of the lengths of its cycles
    locked: bool  # column 1 is a function of the class modulo the period
    windows: int  # distinct windows among its states


def outside_graph(game: Game, outside: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """The states of `outside` (window * 6 + count, in increasing order) and the moves between them, as positions in
    that list."""
    # outside: (n,) uint8
    bits = ((outside[:, None] >> np.arange(COUNTS, dtype=np.uint8)) & 1).astype(bool)  # (n, 6)
    nodes = np.flatnonzero(bits.reshape(-1))  # (m,)
    source, target = [], []
    for d in range(COUNTS):
        windows = np.flatnonzero(bits[:, d])  # (k,)
        for j in range(4):
            v = game.succ[j][windows].astype(np.int64)  # (k,)
            a = np.where(v & 1, 0, after(d, 0))  # (k,)
            keep = bits[v, a]  # (k,)
            source.append(windows[keep] * COUNTS + d)
            target.append(v[keep] * COUNTS + a[keep])
    src = np.searchsorted(nodes, np.concatenate(source))  # (e,)
    tgt = np.searchsorted(nodes, np.concatenate(target))  # (e,)
    return nodes, src, tgt  # (m,), (e,), (e,)


def residue(game: Game, basin: np.ndarray) -> tuple[list[Component], np.ndarray, np.ndarray]:
    """The components of the consistent states outside `basin` that hold a cycle, largest first; and, for every state
    outside the basin (window * 6 + count, increasing), the index of its component in that list or -1."""
    nodes, src, tgt = outside_graph(game, game.cons & ~basin)  # (m,), (e,), (e,)
    m = nodes.size
    graph = csr_matrix((np.ones(src.size, dtype=np.int8), (src, tgt)), shape=(m, m))
    _, label = connected_components(graph, directed=True, connection="strong")  # (m,)
    inner = label[src] == label[tgt]  # (e,)
    cyclic = np.unique(label[src[inner]])  # (c,), the components with a cycle
    sizes = np.bincount(label, minlength=label.max() + 1)[cyclic]  # (c,)
    order = cyclic[np.argsort(-sizes, kind="stable")]  # (c,)
    which = np.full(label.max() + 1, -1, dtype=np.int64)  # (labels,)
    which[order] = np.arange(order.size)
    # levels within each component, from its least state
    s, t = src[inner], tgt[inner]  # (e',) each
    sub = csr_matrix((np.ones(s.size, dtype=np.int8), (s, t)), shape=(m, m))
    member = which[label]  # (m,)
    roots = np.zeros(order.size, dtype=np.int64)  # (c,)
    first = np.flatnonzero(member >= 0)  # (m',)
    roots[member[first][::-1]] = first[::-1]  # the least state of each component
    level = bfs_levels(sub, roots)  # (m,)
    comp = member[s]  # (e',)
    sort = np.argsort(comp, kind="stable")  # (e',)
    delta = np.abs(level[s] + 1 - level[t])[sort]  # (e',)
    starts = np.searchsorted(comp[sort], np.arange(order.size))  # (c,)
    period = np.gcd.reduceat(delta, starts)  # (c,)
    out = []
    inside = np.flatnonzero(member >= 0)  # (m',)
    key = member[inside]  # (m',)
    sort = np.argsort(key, kind="stable")  # (m',)
    inside, key = inside[sort], key[sort]
    bounds = np.searchsorted(key, np.arange(order.size + 1))  # (c + 1,)
    for c in range(order.size):
        states = inside[bounds[c]:bounds[c + 1]]  # (size,)
        p = int(period[c])
        cls = level[states] % p  # (size,)
        col1 = (nodes[states] // COUNTS) & 1  # (size,)
        black = np.bincount(cls, weights=col1, minlength=p)  # (p,)
        total = np.bincount(cls, minlength=p)  # (p,)
        locked = bool(((black == 0) | (black == total)).all())
        out.append(Component(int(states.size), p, locked, int(np.unique(nodes[states] // COUNTS).size)))
    return out, nodes, member  # list, (m,), (m,)


# Periodic right halves.

def periodic_rows(words: list[tuple[int, int]], cells: int) -> np.ndarray:
    """Rows of `cells` cells, bit i across the 64-bit words being cell i + 1, repeating each word (bits, period)."""
    nwords = cells // 64 + 1
    rows = np.zeros((len(words), nwords), dtype=np.uint64)  # (h, nwords)
    for i, (bits, period) in enumerate(words):
        reps = (nwords * 64) // period + 1
        value = int("".join(format(bits, f"0{period}b")[::-1] for _ in range(reps))[::-1], 2)
        value &= (1 << (nwords * 64)) - 1
        for k in range(nwords):
            rows[i, k] = np.uint64((value >> (64 * k)) & 0xFFFFFFFFFFFFFFFF)
    return rows


@dataclass
class HalfRun:
    """The first exact entry of each half into the three sets, and the late states of the halves that never enter."""

    gap: np.ndarray  # (h,) first white step in the gap trap, -1 if none
    family: np.ndarray  # (h,)
    lock: np.ndarray  # (h,)
    late: dict[int, np.ndarray]  # half index -> (s, 2) late windows of 64 columns and counts at white steps


def run_periodic(words: list[tuple[int, int]], phase: int, double: int, late: int = 64) -> HalfRun:
    """Drive each spatially periodic half (bits, period), cell 1 first, with the center black at the steps of parity
    `phase`, for `double` double steps, and record its first entry into each set and, for the halves that enter none,
    the last `late` states (columns 1..64, count). The rows hold every cell that reaches column 64 in the run."""
    steps = 2 * double + 2
    return run_rows(periodic_rows(words, 64 + steps + 128), phase, double, late)


def ether_cycle(width: int) -> list[tuple[int, int]]:
    """The states of the aligned ether at the white steps, which alternate between its two white phases: column 1
    white with count 1, then black with count 0. A finite half that is a member of the kit's family at a depth of at
    least `width` shows them at every white step (the kit's `config_pure_ether`)."""
    windows = [int("".join(word[i % 7] for i in range(width))[::-1], 2) for word in ETHER_WORDS]
    return [(windows[0], 1), (windows[1], 0)]


def run_rows(rows: np.ndarray, phase: int, double: int, late: int) -> HalfRun:
    """`run_periodic` for any rows, bit i across the 64-bit words being cell i + 1, wide enough for the run."""
    # rows: (h, nwords)
    steps = 2 * double + 2
    rows = rows.copy()
    h = rows.shape[0]
    index = np.arange(h)  # (h,)
    entry = {name: np.full(h, -1, dtype=np.int64) for name in ("gap", "family", "lock")}  # (h,) each
    gap = gate_census.gap_entry(GAP_WIDTH)  # (2^16,)
    lock = lock_codes().astype(np.uint64)  # (195,)
    wall = absorption.kit_wall()  # (4, 2^13)
    counts = np.full(h, 5, dtype=np.int64)  # (h,)
    history: list[tuple[np.ndarray, np.ndarray, np.ndarray]] = []
    for t in tqdm(range(steps), desc=f"periodic halves phase {phase}", file=sys.stderr, leave=False):
        center = 1 if (t + phase) % 2 == 0 else 0
        if center == 0:
            low = rows[:, 0]  # (a,)
            black = (low & np.uint64(1)).astype(bool)  # (a,)
            counts = np.where(black, 0, np.where(counts == 5, 5, np.minimum(counts + 1, 4)))  # (a,)
            in_gap = gap[(low & np.uint64(0xFFFF)).astype(np.int64)]  # (a,)
            in_lock = np.isin(low & np.uint64(0xFFFFFFFF), lock)  # (a,)
            in_family = absorption.family_depth(WORD, low, 0, wall) >= 0  # (a,), word phase 0 is a white step
            for name, hit in (("gap", in_gap), ("lock", in_lock), ("family", in_family)):
                entry[name][index[hit]] = t
            keep = ~(in_gap | in_lock | in_family)  # (a,)
            rows, index, counts = rows[keep], index[keep], counts[keep]
            if index.size == 0:
                break
            if late and t >= steps - 2 * late - 2:
                history.append((index.copy(), rows[:, 0].copy(), counts.copy()))
        needed = 64 + (steps - t) + 1
        active = min(rows.shape[1], needed // 64 + 2)
        rows[:, :active] = absorption.step_rows(rows[:, :active], center)
    late_states: dict[int, np.ndarray] = {}
    for i in index.tolist():
        late_states[i] = np.array([[int(w[ix == i][0]), int(c[ix == i][0])] for ix, w, c in history if (ix == i).any()],
                                  dtype=np.uint64)  # (s, 2)
    return HalfRun(entry["gap"], entry["family"], entry["lock"], late_states)


def primitive_words(period: int) -> list[tuple[int, int]]:
    """Every word of exactly this primitive period, as (bits, period), bit i the cell i + 1 (every rotation)."""
    out = []
    for bits in range(1 << period):
        if all(bits != ((bits >> r) | (bits << (period - r))) & ((1 << period) - 1)
               for r in range(1, period) if period % r == 0):
            out.append((bits, period))
    return out


# Reports.

def share(states: np.ndarray, sets: np.ndarray) -> float:
    """The share of the states held in `states` (one per window, as bytes) that `sets` holds."""
    # states, sets: (n,) uint8
    return count(states & sets) / count(states)


def phase0_share(game: Game, sets: np.ndarray) -> float:
    """The share of (window, cell beyond) at a black step whose image, the first white step of a phase-0 half, is in
    `sets` with its starting count."""
    start = start_states(game.width)  # (n,)
    held = (start & sets) != 0  # (n,), each window's starting state is held
    total = 0
    n = 1 << game.width
    for beyond in (0, 1):
        for lo in range(0, n, CHUNK):
            w = np.arange(lo, min(n, lo + CHUNK), dtype=np.int64)  # (block,)
            mask = np.int64(n - 1)
            image = (((w << 1) | 1) & mask) ^ (w | ((w >> 1) | (beyond << (game.width - 1))))  # (block,)
            total += int(held[image].sum())
    return total / (2 * n)


def run_reach(widths: list[int]) -> None:
    """The test of reach at each width: the targets together and the gap trap alone."""
    for width in widths:
        started = time.perf_counter()
        game = make_game(width)
        targets = targets_over(width)
        union = targets["gap"] | targets["family"] | targets["lock"]  # (n,)
        seen, sweeps = reach(game, union, "reach")
        missed = count(game.cons & ~seen)
        alone, sweeps_gap = reach(game, targets["gap"], "reach gap")
        print(f"width {width}: targets cover {count(union & game.cons):,} of {count(game.cons):,} consistent states "
              f"(gap {count(targets['gap'] & game.cons):,}, family {count(targets['family'] & game.cons):,}, "
              f"lock {count(targets['lock'] & game.cons):,}); {missed:,} cannot reach them ({sweeps} sweeps); "
              f"{count(game.cons & ~alone):,} cannot reach the gap trap alone ({sweeps_gap} sweeps) "
              f"[{time.perf_counter() - started:.0f} s]", flush=True)
        del game, seen, alone


def run_basin(widths: list[int], components: bool) -> None:
    """The forced basin of the three sets and of the outright part at each width, and the residue."""
    for width in widths:
        started = time.perf_counter()
        game = make_game(width)
        targets = targets_under(width)
        start = start_states(width)  # (n,)
        for name, target in (("three sets", targets["gap"] | targets["family"] | targets["lock"]),
                             ("family and lock", targets["family"] | targets["lock"])):
            basin, added = forced_basin(game, target, name)
            print(f"width {width}, {name}: target {added[0]:,}, basin {count(basin):,} of {count(game.cons):,} "
                  f"consistent states ({count(basin) / count(game.cons):.4f}); starts phase 1 "
                  f"{share(start, basin):.4f}, phase 0 {phase0_share(game, basin):.4f}; largest rank "
                  f"{len(added) - 1} [{time.perf_counter() - started:.0f} s]", flush=True)
            if components and name == "three sets":
                comps, nodes, member = residue(game, basin)
                total = sum(c.size for c in comps)
                keys = np.array([w * COUNTS + d for w, d in ether_cycle(width)])  # (2,)
                pos = np.searchsorted(nodes, keys)  # (2,)
                found = (pos < nodes.size) & (nodes[np.minimum(pos, nodes.size - 1)] == keys)  # (2,)
                ether = sorted(set(member[pos[found]].tolist())) if found.all() else "in the basin"
                print(f"  residue: {len(comps)} components with a cycle, {total:,} states; largest "
                      f"{[(c.size, c.period, c.locked, c.windows) for c in comps[:6]]}; locked "
                      f"{sum(c.locked for c in comps)} ({sum(c.size for c in comps if c.locked):,} states); "
                      f"the aligned ether's states lie in component {ether}", flush=True)
        del game


def run_halves(period: int, random_count: int, max_period: int, double: int, widths: list[int], seed: int) -> None:
    """Every primitive periodic half up to `period`, and `random_count` random words of each period up to
    `max_period`, in both phases: which never enter, and where their late states lie in the residue."""
    rng = np.random.default_rng(seed)
    words = [w for p in range(1, period + 1) for w in primitive_words(p)]
    for p in range(period + 1, max_period + 1):
        words += [(int(rng.integers(0, 1 << p)), p) for _ in range(random_count)]
    games = {}
    for width in widths:
        game = make_game(width)
        targets = targets_under(width)
        basin, _ = forced_basin(game, targets["gap"] | targets["family"] | targets["lock"])
        comps, nodes, member = residue(game, basin)
        games[width] = (comps, nodes, member)
    for phase in (0, 1):
        run = run_periodic(words, phase, double)
        never = sorted(run.late)
        latest = int(max(run.gap.max(), run.family.max(), run.lock.max()))
        print(f"phase {phase}: {len(words)} periodic halves; gap {int((run.gap >= 0).sum())}, family "
              f"{int((run.family >= 0).sum())}, lock {int((run.lock >= 0).sum())}, none {len(never)} within "
              f"{double} double steps (latest entry at step {latest})", flush=True)
        for i in never[:40]:
            bits, p = words[i]
            cells = format(bits, f"0{p}b")[::-1]
            where = []
            for width, (comps, nodes, member) in games.items():
                states = run.late[i]  # (s, 2)
                key = ((states[:, 0] & np.uint64((1 << width) - 1)).astype(np.int64) * COUNTS
                       + states[:, 1].astype(np.int64))  # (s,)
                pos = np.searchsorted(nodes, key)  # (s,)
                found = (pos < nodes.size) & (nodes[np.minimum(pos, nodes.size - 1)] == key)  # (s,)
                comp = sorted(set(member[pos[found]].tolist()))
                where.append(f"W{width}: outside basin {int(found.sum())}/{key.size}, components {comp} "
                             + str([(comps[c].size, comps[c].period, comps[c].locked) for c in comp if c >= 0]))
            print(f"  never: period {p} word {cells}; " + "; ".join(where), flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("mode", choices=["reach", "basin", "halves"])
    parser.add_argument("--widths", type=int, nargs="+", default=[16])
    parser.add_argument("--no-residue", action="store_true")
    parser.add_argument("--period", type=int, default=12)
    parser.add_argument("--random", type=int, default=100)
    parser.add_argument("--max-period", type=int, default=32)
    parser.add_argument("--double-steps", type=int, default=10000)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    started = time.perf_counter()
    if args.mode == "reach":
        run_reach(args.widths)
    elif args.mode == "basin":
        run_basin(args.widths, not args.no_residue)
    else:
        run_halves(args.period, args.random, args.max_period, args.double_steps, args.widths, args.seed)
    print(f"({time.perf_counter() - started:.0f} s)")


if __name__ == "__main__":
    main()
