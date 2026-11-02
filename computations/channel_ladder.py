"""The channel from a free column into column 1 beside a repeating center, width by width, and its exact entropy.

The center repeats a block `b` of period P. The window holds columns 1 .. W (column x at bit x - 1 of an integer) and
column W + 1 is free at every step, so one step beside the center maps a window to two windows (`step`). A real right
half, finite or infinite, gives one play. The readings are column 1 at the chosen phases (`reads`; by default the white
phases of `b`, the readings of the finite game, where column -1 is the next center xor column 1). Every play ends in the
limit set, the windows with arbitrarily long histories (`limit_sets`).

1. **The prefix ladder** (`limit_sets`). Dropping column W + 1 maps a step at width W + 1 to a step at width W (the
   W-cell prefix of a successor is a successor of the prefix, with the old column W + 1 as the free cell), so the
   limit set at width W + 1 lies in {w : prefix_W(w) in L(W)}. The ladder starts from all 2^W windows at a small width
   and at each width trims those candidates: the limit set is the greatest set in which every node has a predecessor,
   which the trim reaches by removing nodes with no predecessor until none is left (`trim`).
2. **The cyclic-class test** (`classes`). On the step graph of the limit set, every strongly connected component with
   a move inside it has a cyclic period d (the gcd of its cycle lengths) and classes (the level modulo d). The reading
   is a function of the class in every such component exactly when every play reads an eventually periodic sequence;
   then masked Jen (`AdjacentColumns`, the kit's `Rule30MaskedJen`) excludes the block for every right half. The test
   is that of `game.component_periods` restricted to the limit set, where every component with a move lies.
3. **Exact entropy** (`component_growth`). Within each such component the readings form a sofic language; its subset
   automaton, period by period from the set of the component's phase-0 windows, is deterministic, so its growth per
   period is the Perron root of its graph, bracketed by Collatz-Wielandt bounds on each strongly connected component
   of the automaton. The entropy of the channel is the largest of these. Dropping the free column makes each step at
   width W + 1 a step at width W with the same readings, so the entropy never rises with W, and since the free column
   is free, every entropy here bounds from above the entropy of the real channel beside a real right half.
4. **Checks and helpers.** `simple_growth` repeats the entropy with a plain subset construction, sets compared whole,
   and dense eigenvalues, for small widths; `kit_wall_cells` asks whether a component's windows carry the kit's wall
   states (`absorption.kit_wall`); `fit_tail` fits g_inf + a r^W to the growth of the last widths, a heuristic.

    python -m computations.channel_ladder --block 0001 --widths 10-30           # the ladder for one word
    python -m computations.channel_ladder --block 0001 --widths 10-24 --reads all   # column 1 at every phase
    python -m computations.channel_ladder --block 000000001011 --widths 16 --base 16   # control: the class test passes
    python -m computations.channel_ladder --block 01 --widths 18-22             # control: period two, terminal trap
"""

from __future__ import annotations

import argparse
import itertools
import math
import resource
import time
from dataclasses import dataclass

import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import breadth_first_order, connected_components
from tqdm.auto import tqdm

from computations.rule30 import distinct


def step(windows: np.ndarray, width: int, center: int, free: int) -> np.ndarray:
    """One step of Rule 30 on columns 1 .. width beside a center reading `center`, with column width + 1 reading
    `free`. `windows` has shape (n,), int64; returns shape (n,)."""
    mask = np.int64((1 << width) - 1)
    left = ((windows << 1) | np.int64(center)) & mask  # (n,), column x - 1 at bit x - 1
    right = (windows >> 1) | (np.int64(free) << (width - 1))  # (n,), column x + 1 at bit x - 1
    return left ^ (windows | right)


def white_reads(block: str) -> tuple[int, ...]:
    """The white phases of `block`: there column -1 is the next center xor column 1."""
    return tuple(k for k, ch in enumerate(block) if ch == "0")


@dataclass(frozen=True)
class Ladder:
    """The limit sets at one width and the step graph on them. Node offset[k] + i is window sets[k][i] at phase k;
    succ[node] holds its two successors (free cell 0, 1), -1 where the successor is not in the limit set."""

    block: str
    width: int
    sets: tuple[np.ndarray, ...]  # P arrays (L_k,), sorted int64 windows at phase k
    offset: np.ndarray  # (P + 1,)
    succ: np.ndarray  # (N, 2), int64 node ids or -1


def graph(block: str, width: int, sets: list[np.ndarray]) -> np.ndarray:
    """The successors (free cell 0, 1) of each node of `sets` (P sorted arrays) among the nodes of `sets`, as global
    node ids in phase order, -1 where the successor is missing. Shape (N, 2)."""
    period = len(block)
    sizes = np.array([s.size for s in sets], dtype=np.int64)  # (P,)
    offset = np.concatenate([[0], np.cumsum(sizes)])  # (P + 1,)
    succ = np.full((int(offset[-1]), 2), -1, dtype=np.int64)  # (N, 2)
    for k in range(period):
        target = sets[(k + 1) % period]  # (L_{k+1},)
        for free in (0, 1):
            after = step(sets[k], width, int(block[k]), free)  # (L_k,)
            where = np.searchsorted(target, after)  # (L_k,)
            where = np.minimum(where, max(target.size - 1, 0))
            found = (target.size > 0) & (target[where] == after) if target.size else np.zeros(after.size, bool)
            succ[offset[k]:offset[k + 1], free] = np.where(found, where + offset[(k + 1) % period], -1)
    return succ


def trim(succ: np.ndarray) -> np.ndarray:
    """The greatest set of nodes in which every node has a predecessor, as a boolean mask (N,): remove the nodes with
    no predecessor among those left until none is left. `succ` has shape (N, 2), -1 for a missing move."""
    n = succ.shape[0]
    edges = succ.ravel()  # (2N,)
    sources = np.repeat(np.arange(n, dtype=np.int64), 2)  # (2N,)
    keep = edges >= 0
    edges, sources = edges[keep], sources[keep]  # (E,), (E,)
    indeg = np.bincount(edges, minlength=n)  # (N,)
    alive = np.ones(n, dtype=bool)  # (N,)
    dead = np.flatnonzero(indeg == 0)  # (d,)
    order = np.argsort(sources, kind="stable")  # (E,)
    edges = edges[order]
    start = np.searchsorted(sources[order], np.arange(n + 1))  # (N + 1,)
    while dead.size:
        alive[dead] = False
        lo, hi = start[dead], start[dead + 1]  # (d,), (d,)
        counts = hi - lo  # (d,)
        index = np.repeat(lo - np.concatenate([[0], np.cumsum(counts)[:-1]]), counts) + np.arange(counts.sum())
        hit = edges[index]  # (h,), targets of the removed nodes
        np.subtract.at(indeg, hit, 1)
        hit = distinct(hit)
        dead = hit[(indeg[hit] == 0) & alive[hit]]
    return alive


def restrict(block: str, width: int, candidates: list[np.ndarray]) -> Ladder:
    """The limit sets inside `candidates` (P sorted arrays of windows that contain the limit sets) and their graph."""
    succ = graph(block, width, candidates)  # (N, 2)
    alive = trim(succ)  # (N,)
    sizes = np.array([s.size for s in candidates], dtype=np.int64)  # (P,)
    offset = np.concatenate([[0], np.cumsum(sizes)])  # (P + 1,)
    sets = tuple(candidates[k][alive[offset[k]:offset[k + 1]]] for k in range(len(block)))
    return Ladder(block, width, sets, np.concatenate([[0], np.cumsum([s.size for s in sets])]),
                  graph(block, width, list(sets)))


def full_sets(block: str, width: int) -> Ladder:
    """The limit sets at `width` from all 2^width windows at every phase."""
    every = np.arange(1 << width, dtype=np.int64)  # (2^W,)
    return restrict(block, width, [every] * len(block))


def widen(ladder: Ladder) -> Ladder:
    """The limit sets at width W + 1 from those at W: the candidates are the windows whose W-cell prefix is in L(W)."""
    width = ladder.width + 1
    top = np.int64(1 << ladder.width)
    candidates = [np.concatenate([s, s + top]) for s in ladder.sets]  # P arrays (2 L_k,), sorted
    return restrict(ladder.block, width, candidates)


def limit_sets(block: str, widths: list[int], base: int = 10, progress: bool = True) -> dict[int, Ladder]:
    """The ladders at `widths`, built from the full sets at min(base, least width) and widened one cell at a time."""
    first = min(base, min(widths))
    ladder = full_sets(block, first)
    found = {first: ladder} if first in widths else {}
    for width in tqdm(range(first + 1, max(widths) + 1), desc=f"{block} widths", disable=not progress):
        ladder = widen(ladder)
        if width in widths:
            found[width] = ladder
    return found


@dataclass(frozen=True)
class Component:
    """One strongly connected component of the step graph with a move inside it."""

    nodes: np.ndarray  # (m,) global node ids, sorted
    cycle: int  # the gcd of its cycle lengths
    passes: bool  # whether every reading is a function of the cyclic class
    terminal: bool  # whether no move leaves it


def classes(ladder: Ladder, reads: tuple[int, ...]) -> list[Component]:
    """The components with a move inside them, their cyclic periods and the class test, largest first."""
    succ = ladder.succ
    n = succ.shape[0]
    sources = np.repeat(np.arange(n, dtype=np.int64), 2)  # (2N,)
    targets = succ.ravel()  # (2N,)
    keep = targets >= 0
    sources, targets = sources[keep], targets[keep]  # (E,), (E,)
    full = csr_matrix((np.ones(sources.size, dtype=np.int8), (sources, targets)), shape=(n, n))
    count, label = connected_components(full, directed=True, connection="strong")  # (N,)
    inside = label[sources] == label[targets]  # (E,)
    recurrent = np.zeros(count, dtype=bool)  # (count,)
    recurrent[label[sources[inside]]] = True
    leaves = np.zeros(count, dtype=bool)  # (count,)
    leaves[label[sources[~inside]]] = True
    phase = np.searchsorted(ladder.offset, np.arange(n), side="right") - 1  # (N,)
    windows = np.concatenate(ladder.sets)  # (N,)
    readable = np.isin(phase, np.array(reads, dtype=np.int64))  # (N,)
    src, tgt = sources[inside], targets[inside]  # (I,), (I,)
    # one search from a root joined to the first node of each component, along the moves inside components
    roots = np.full(count, -1, dtype=np.int64)  # (count,)
    order_nodes = np.arange(n, dtype=np.int64)
    roots[label[::-1]] = order_nodes[::-1]  # the first node of each component
    roots = roots[recurrent]  # (r,)
    root = n
    rows = np.concatenate([src, np.full(roots.size, root, dtype=np.int64)])
    cols = np.concatenate([tgt, roots])
    inner = csr_matrix((np.ones(rows.size, dtype=np.int8), (rows, cols)), shape=(n + 1, n + 1))
    _, parent = breadth_first_order(inner, root, directed=True, return_predecessors=True)  # (reached,)
    up = np.where(parent >= 0, parent, root).astype(np.int64)  # (N + 1,), unreached nodes and the root point at it
    up[root] = root
    level = (up != np.arange(n + 1)).astype(np.int64)  # (N + 1,), the depth by pointer jumping
    while (up != root).any():
        level += level[up]
        up = up[up]
    gap = np.abs(level[src] + 1 - level[tgt])  # (I,)
    cycle = np.zeros(count, dtype=np.int64)  # (count,)
    by = np.argsort(label[src], kind="stable")
    keys, first = np.unique(label[src][by], return_index=True)
    reduced = np.gcd.reduceat(gap[by], first) if gap.size else np.zeros(0, dtype=np.int64)
    cycle[keys] = reduced
    found = []
    members_all = np.argsort(label, kind="stable")  # (N,)
    bounds = np.searchsorted(label[members_all], np.arange(count + 1))  # (count + 1,)
    for comp in np.flatnonzero(recurrent).tolist():
        nodes = np.sort(members_all[bounds[comp]:bounds[comp + 1]])  # (m,)
        d = int(cycle[comp])
        pick = nodes[readable[nodes]]  # (r,)
        key = level[pick] % d  # (r,)
        seen = np.zeros((d, 2), dtype=bool)  # (d, 2)
        seen[key, (windows[pick] & 1).astype(np.int64)] = True
        found.append(Component(nodes, d, not bool(seen.all(axis=1).any()), not bool(leaves[comp])))
    found.sort(key=lambda c: -c.nodes.size)
    return found


def kit_wall_cells(ladder: Ladder, component: Component, first: int = 4) -> bool:
    """Whether every window of the component holds one of the kit's 109 wall states (`absorption.kit_wall`) on columns
    `first` .. `first` + 12, at the window's phase."""
    from computations.absorption import kit_wall

    wall = kit_wall()  # (4, 2^13)
    windows = np.concatenate(ladder.sets)[component.nodes]  # (m,)
    phase = np.searchsorted(ladder.offset, component.nodes, side="right") - 1  # (m,)
    strip = (windows >> (first - 1)) & ((1 << 13) - 1)  # (m,)
    return bool(wall[phase % 4, strip].all())


def period_moves(subset: np.ndarray, block: str, reads: tuple[int, ...], succ: np.ndarray,
                 bit: np.ndarray) -> list[tuple[int, np.ndarray]]:
    """The moves of the subset automaton over one period from `subset` (sorted local ids at phase 0): for each word of
    readings with a nonempty successor, the word as an integer and the sorted set of local ids it leads to. `succ` has
    shape (m, 2) in local ids (-1 outside the component), `bit` (m,) is column 1 at each node."""
    branches = [(0, subset)]
    for k in range(len(block)):
        split = []
        for word, part in branches:
            if k in reads:
                values = bit[part]  # (s,)
                for value in (0, 1):
                    piece = part[values == value]
                    if piece.size:
                        split.append((2 * word + value, piece))
            else:
                split.append((word, part))
        branches = []
        for word, part in split:
            after = succ[part].ravel()  # (2 s,)
            after = distinct(after[after >= 0])
            if after.size:
                branches.append((word, after))
    return branches


def perron(matrix: csr_matrix, tolerance: float = 1e-7, rounds: int = 20000) -> tuple[float, float]:
    """Collatz-Wielandt bounds (low, high) on the Perron root of an irreducible nonnegative matrix, from power
    iteration on matrix + identity (which removes the cyclic part)."""
    m = matrix.shape[0]
    shifted = matrix + csr_matrix((np.ones(m), (np.arange(m), np.arange(m))), shape=(m, m))
    vector = np.ones(m)  # (m,)
    low, high = 0.0, math.inf
    for _ in range(rounds):
        image = shifted @ vector  # (m,)
        ratio = image / vector  # (m,)
        low, high = float(ratio.min()) - 1, float(ratio.max()) - 1
        if high - low < tolerance:
            break
        vector = image / image.max()
    return low, high


def period_graph(ladder: Ladder, nodes: np.ndarray, reads: tuple[int, ...]) -> tuple[np.ndarray, np.ndarray,
                                                                                     np.ndarray]:
    """The plays inside the node set `nodes` (sorted global ids) period by period: its phase-0 nodes, the word of
    readings each reads over one period (a function of the phase-0 window, since the free column reaches column 1 only
    after `width` steps), and the phase-0 nodes it can reach after one period inside the set. Returns (start (s,),
    word (s,), successors (s, K)) with successors as indices into start, -1 for none, rows without repeats."""
    period = len(ladder.block)
    inside = np.zeros(ladder.succ.shape[0], dtype=bool)  # (N,)
    inside[nodes] = True
    succ = np.where(ladder.succ >= 0, ladder.succ, -1)  # (N, 2)
    succ = np.where((succ >= 0) & inside[np.maximum(succ, 0)], succ, -1)  # (N, 2), moves inside the set
    start = nodes[nodes < ladder.offset[1]]  # (s,)
    windows = np.concatenate(ladder.sets)  # (N,)
    word = np.zeros(start.size, dtype=np.int64)  # (s,)
    reach = start[:, None]  # (s, K_k), the nodes reachable after k steps
    for k in range(period):
        if k in reads:  # the reading at phase k is the same along every path, by the light cone
            present = reach >= 0  # (s, K_k)
            bits = np.where(present, windows[np.maximum(reach, 0)] & 1, -1)  # (s, K_k)
            value = bits.max(axis=1)  # (s,)
            assert ((bits == value[:, None]) | ~present).all(), "the reading depends on the free column"
            word = 2 * word + value
        reach = np.where(reach[:, :, None] >= 0, succ[np.maximum(reach, 0)], -1).reshape(start.size, -1)
        reach = np.sort(reach, axis=1)  # (s, 2 K_k)
        reach[:, 1:][reach[:, 1:] == reach[:, :-1]] = -1  # drop repeats
        keep = (reach >= 0).any(axis=0)  # (2 K_k,)
        reach = reach[:, keep]
    local = np.full(ladder.succ.shape[0], -1, dtype=np.int64)  # (N,)
    local[start] = np.arange(start.size)
    successors = np.where(reach >= 0, local[np.maximum(reach, 0)], -1)  # (s, K)
    return start, word, successors


def subset_automaton(word: np.ndarray, successors: np.ndarray, initial: list[np.ndarray], cap: int = 2_000_000,
                     chunk: int = 12_000_000,
                     progress: bool = True) -> tuple[int, np.ndarray, np.ndarray, np.ndarray, bool]:
    """The subset automaton of the node-labelled graph (`word` (s,), `successors` (s, K), -1 for none) from each set of
    `initial` (distinct sorted arrays of indices), which become states 0, 1, ...: from a set S, each word o read by
    some node of S leads to the set of successors of the nodes of S that read o. Built one breadth-first layer at a
    time, all sets of a layer at once; a set is named by its size and two sums of random 64-bit keys of its members
    (two different sets share a name with probability about 2^-128 per pair). Returns (states, sources, targets,
    words, complete), one move per (state, word)."""
    rng = np.random.default_rng(20261102)
    keys = rng.integers(0, 2**63, size=(2, word.size), dtype=np.uint64) * np.uint64(2) + np.uint64(1)  # (2, s)
    names: dict[tuple[int, int, int], int] = {}

    def name(members: np.ndarray) -> tuple[int, int, int]:
        return (int(members.size), int(keys[0, members].sum()), int(keys[1, members].sum()))

    owners, members = [], []
    for start in initial:
        assert name(start) not in names, "the initial sets must be distinct"
        names[name(start)] = len(names)
        owners.append(np.full(start.size, len(names) - 1, dtype=np.int64))
        members.append(start.astype(np.int64))
    owner = np.concatenate(owners)  # (f,), the state of each member of the frontier, increasing
    member = np.concatenate(members)  # (f,)
    labels: list[np.ndarray] = []
    sources: list[np.ndarray] = []
    targets: list[np.ndarray] = []
    width = successors.shape[1]
    span = int(word.max()) + 1 if word.size else 1
    bar = tqdm(desc="subsets", disable=not progress, mininterval=5, unit=" states")
    while member.size:
        new_owner: list[np.ndarray] = []
        new_member: list[np.ndarray] = []
        cut = np.searchsorted(owner, owner[np.arange(0, owner.size, max(1, chunk // width))])
        cut = np.unique(np.concatenate([cut, [owner.size]]))
        for lo, hi in itertools.pairwise(cut.tolist()):
            own, mem = owner[lo:hi], member[lo:hi]  # (c,), (c,)
            group = own * span + word[mem]  # (c,), state and word
            nxt = successors[mem]  # (c, K)
            group = np.repeat(group, width)[nxt.ravel() >= 0]  # (e,)
            nxt = nxt.ravel()[nxt.ravel() >= 0]  # (e,)
            combined = distinct(group * np.int64(word.size) + nxt)  # (u,), by group then member
            group, nxt = combined // word.size, combined % word.size  # (u,), (u,)
            first = np.flatnonzero(np.concatenate([[True], group[1:] != group[:-1]]))  # (g,)
            size = np.diff(np.concatenate([first, [group.size]]))  # (g,)
            sum0 = np.add.reduceat(keys[0, nxt], first) if first.size else np.zeros(0, np.uint64)  # (g,)
            sum1 = np.add.reduceat(keys[1, nxt], first) if first.size else np.zeros(0, np.uint64)  # (g,)
            target = np.empty(first.size, dtype=np.int64)  # (g,)
            for i, key in enumerate(zip(size.tolist(), sum0.tolist(), sum1.tolist())):
                found = names.get(key)
                if found is None:
                    if len(names) >= cap:
                        bar.close()
                        empty = np.zeros(0, np.int64)
                        return len(names), empty, empty, empty, False
                    found = len(names)
                    names[key] = found
                    new_owner.append(np.full(size[i], found, dtype=np.int64))
                    new_member.append(nxt[first[i]:first[i] + size[i]])
                target[i] = found
            sources.append(group[first] // span)
            labels.append(group[first] % span)
            targets.append(target)
        bar.update(len(names) - bar.n)
        owner = np.concatenate(new_owner) if new_owner else np.zeros(0, np.int64)
        member = np.concatenate(new_member) if new_member else np.zeros(0, np.int64)
    bar.close()
    return len(names), np.concatenate(sources), np.concatenate(targets), np.concatenate(labels), True


def growth_of(states: int, sources: np.ndarray, targets: np.ndarray) -> tuple[float, float]:
    """Bounds on the Perron root of the automaton's graph: the largest over its strongly connected components."""
    matrix = csr_matrix((np.ones(sources.size), (sources, targets)), shape=(states, states))
    matrix.sum_duplicates()
    low = high = 0.0
    count, label = connected_components(matrix, directed=True, connection="strong")  # (states,)
    coo = matrix.tocoo()
    inside = label[coo.row] == label[coo.col]  # (nnz,)
    weight = np.bincount(label[coo.row[inside]], weights=coo.data[inside], minlength=count)  # (count,)
    size = np.bincount(label, minlength=count)  # (count,)
    for comp in np.flatnonzero(weight > 0).tolist():
        if weight[comp] <= size[comp]:  # as many moves as states in a strong component: one cycle, root 1
            low, high = max(low, 1.0), max(high, 1.0)
            continue
        members = np.flatnonzero(label == comp)  # (c,)
        lo, hi = perron(matrix[members][:, members])
        if hi > high:
            low, high = max(low, lo), hi
        elif lo > low:
            low = lo
    return low, high


@dataclass(frozen=True)
class Growth:
    """The subset automaton of one component: its states, whether it closed within the cap, and the Perron root of its
    graph, bracketed, in words per period."""

    states: int
    complete: bool
    low: float
    high: float


def component_growth(ladder: Ladder, component: Component, reads: tuple[int, ...], cap: int = 2_000_000,
                     progress: bool = True) -> Growth:
    """The growth per period of the readings of the plays inside `component`, by the subset automaton from the set of
    its phase-0 windows."""
    start, word, successors = period_graph(ladder, component.nodes, reads)
    states, sources, targets, _, complete = subset_automaton(word, successors, [np.arange(start.size)], cap,
                                                             progress=progress)
    if not complete:
        return Growth(states, False, math.nan, math.nan)
    low, high = growth_of(states, sources, targets)
    return Growth(states, True, low, high)


def simple_growth(ladder: Ladder, component: Component, reads: tuple[int, ...]) -> float:
    """The same growth by a plain subset construction one set at a time, step by step, with sets compared whole and
    the Perron root from dense eigenvalues: the check for small widths."""
    nodes = component.nodes  # (m,)
    local = np.full(ladder.succ.shape[0], -1, dtype=np.int64)  # (N,)
    local[nodes] = np.arange(nodes.size)
    succ = ladder.succ[nodes]  # (m, 2)
    succ = np.where(succ >= 0, local[np.maximum(succ, 0)], -1)  # (m, 2) local, -1 outside
    bit = (np.concatenate(ladder.sets)[nodes] & 1).astype(np.int8)  # (m,)
    start = tuple(np.flatnonzero(nodes < ladder.offset[1]).tolist())
    ids = {start: 0}
    queue = [start]
    edges: list[tuple[int, int]] = []
    done = 0
    while done < len(queue):
        for _, after in period_moves(np.array(queue[done], dtype=np.int64), ladder.block, reads, succ, bit):
            key = tuple(after.tolist())
            if key not in ids:
                ids[key] = len(ids)
                queue.append(key)
            edges.append((done, ids[key]))
        done += 1
    matrix = np.zeros((len(ids), len(ids)))  # (states, states)
    for a, b in edges:
        matrix[a, b] += 1
    return float(max(abs(np.linalg.eigvals(matrix))))


def peak_gb() -> float:
    """The peak resident memory of this process, in GB."""
    return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2**20


def describe(ladder: Ladder, reads: tuple[int, ...], cap: int, entropy: bool, progress: bool) -> dict:
    """One rung of the ladder: the sizes, the components and, where the automaton fits, their growth per period."""
    comps = classes(ladder, reads)
    rows = []
    for comp in comps:
        growth = None
        if entropy and not comp.passes:
            growth = component_growth(ladder, comp, reads, cap, progress)
        rows.append((comp, growth))
    return {"width": ladder.width, "limit": [int(s.size) for s in ladder.sets], "components": rows}


def report(row: dict) -> str:
    """One line per rung and one per component."""
    lines = [f"W {row['width']}: limit set {row['limit']} (phase 0 .. P-1), peak {peak_gb():.2f} GB"]
    for comp, growth in row["components"]:
        text = f"  component {comp.nodes.size} nodes, cyclic period {comp.cycle}, class test " \
               f"{'passes' if comp.passes else 'fails'}, {'terminal' if comp.terminal else 'not terminal'}"
        if growth is not None:
            if growth.complete:
                text += (f"; automaton {growth.states} states, growth per period [{growth.low:.5f}, "
                         f"{growth.high:.5f}], {math.log2(max(growth.high, 1e-300)):.4f} bits")
            else:
                text += f"; automaton over {growth.states} states, not closed"
        lines.append(text)
    return "\n".join(lines)


def fit_tail(widths: list[int], growth: list[float]) -> tuple[float, float, float, float]:
    """The least-squares fit g(W) = g_inf + a r^W to the points, over a grid of r in (0, 1) with g_inf and a linear
    for each r. Returns (g_inf, a, r, root mean square residual). A heuristic extrapolation, not a bound."""
    x = np.array(widths, dtype=float)  # (n,)
    y = np.array(growth, dtype=float)  # (n,)
    best = (math.nan, math.nan, math.nan, math.inf)
    for r in np.linspace(0.30, 0.995, 1391):
        design = np.stack([np.ones_like(x), r ** (x - x[0])], axis=1)  # (n, 2)
        coef, *_ = np.linalg.lstsq(design, y, rcond=None)
        rms = float(np.sqrt(np.mean((design @ coef - y) ** 2)))
        if rms < best[3]:
            best = (float(coef[0]), float(coef[1]) / float(r) ** float(x[0]), float(r), rms)
    return best


def parse_widths(text: str) -> list[int]:
    """'10-14,18' to [10, 11, 12, 13, 14, 18]."""
    found: list[int] = []
    for part in text.split(","):
        if "-" in part:
            lo, hi = part.split("-")
            found.extend(range(int(lo), int(hi) + 1))
        else:
            found.append(int(part))
    return sorted(set(found))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--block", required=True)
    parser.add_argument("--widths", default="10-20")
    parser.add_argument("--reads", default="white", help="'white', 'all' or phases such as 0,1")
    parser.add_argument("--cap", type=int, default=2_000_000, help="most states of one subset automaton")
    parser.add_argument("--no-entropy", action="store_true", help="the class test alone")
    parser.add_argument("--base", type=int, default=10)
    args = parser.parse_args()
    block = args.block
    if args.reads == "white":
        reads = white_reads(block)
    elif args.reads == "all":
        reads = tuple(range(len(block)))
    else:
        reads = tuple(int(x) for x in args.reads.split(","))
    widths = parse_widths(args.widths)
    first = min(args.base, widths[0])
    ladder = full_sets(block, first)
    began = time.time()
    largest: dict[int, float] = {}  # the growth per period of the channel: the largest over the components
    for width in range(first, widths[-1] + 1):
        if width > first:
            ladder = widen(ladder)
        if width in widths:
            row = describe(ladder, reads, args.cap, not args.no_entropy, True)
            print(report(row), f"[{time.time() - began:.0f} s]", flush=True)
            found = [g.high for _, g in row["components"] if g is not None and g.complete]
            if found and all(g is None or g.complete for _, g in row["components"]):
                largest[width] = max(found)
    known = sorted(largest)
    for width in known:
        if width - 2 in largest:
            fall = largest[width - 2] - largest[width]
            print(f"W {width}: growth {largest[width]:.5f}, decrement over two cells {fall:.5f}")
    if len(known) >= 6:
        tail = known[-6:]
        g_inf, a, r, rms = fit_tail(tail, [largest[w] for w in tail])
        print(f"fit over W = {tail[0]} .. {tail[-1]}: g_inf {g_inf:.4f}, a {a:.4g}, r {r:.3f}, rms {rms:.2e}")


if __name__ == "__main__":
    main()
