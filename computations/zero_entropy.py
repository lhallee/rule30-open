"""Zero-entropy reading lists beside a center repeating a block, and the cyclic-class test that decides them.

Drive a right half with the center repeating a block `b` of period P and read column 1 at every white phase of `b` (the
"readings", k per period). Masked Jen excludes `b` as soon as the readings are eventually periodic for every right half.
A list of forbidden words whose entry is forced (`reading_certificates`) and whose shift has entropy 0 would do that:
in a shift of finite type of entropy 0 every strongly connected component of the de Bruijn graph is one cycle, so every
sequence of it is eventually periodic. This module looks for such lists, reduces their existence to the finite game
with cyclic classes in place of phases, and runs that test.

1. **Phase-aware word lists** (`sft_graph`, `sft_is_zero`, `sft_entropy`). A forbidden word may carry a read position
   j < k: the word is forbidden only when its first reading is at position j of the period (untagged words are
   forbidden at every position). Readings at chosen positions of a frame of r periods may also be fixed (`constants`),
   the variant where part of the readings is a forced periodic sequence. The graph has the nodes (position in the
   frame, last L - 1 readings) and one edge per allowed reading. Its entropy is 0 exactly when every strongly connected
   component with an edge has as many edges inside it as nodes (`sft_is_zero`), decided on integers; the value in bits
   per reading comes from a power iteration and is for the tables only.
2. **Forced lists** (`forced`, `learned`, `search`). The certificate of `reading_certificates` with phase-tagged words:
   the greatest set of states (phase, window of columns 1..W, last L - 1 readings) that both values of column W + 1
   keep without completing a forbidden word, then the ranks. The learned words are the minimal tagged words of at most
   `length` readings that no sampled half shows after a transient. `search` adds them greedily (several orders) while
   entry stays forced within a state budget, and tries every subset when few are left, keeping the list of lowest
   entropy.
3. **The obstruction** (`analyze`, `witness`). The width-W window graph (the finite game's graph, `game.moves`) has the
   nodes (phase, window) and two moves each. If a list is forced at width W, every closed walk inside a strongly
   connected component C of that graph reads only allowed words (a play can repeat the walk forever after entering the
   good set), so the list's shift contains the readings of every walk in C. Two closed walks through one node whose
   readings u, w do not commute (u w != w u) give a code {u, w}, and then every forced list at width W has entropy at
   least log2 x with x^-|u| + x^-|w| = 1 (more words of a prefix code raise the bound). Such walks exist in C exactly
   when the readings are not a function of C's cyclic class (the level modulo the gcd of its cycle lengths), the test
   of `game.component_periods`; when every C passes, the readings of every play are eventually periodic and masked Jen
   excludes the block outright. Dropping column W + 1 maps closed walks at width W + 1 to closed walks at width W with
   the same readings, so a pair at width W rules out every width up to W.
4. **Checks.** `naive_classes` rebuilds the window graph cell by cell in plain Python (Tarjan's algorithm, levels by
   a search) for an independent count of the components and their classes; `naive_walk` replays a walk of a code cell
   by cell; `driven_period` drives a right half of any length cell by cell and reads the period its readings settle
   into; `sampled_growth` is the heuristic growth of the distinct words of sampled readings.

    python -m computations.zero_entropy --block 001 --width 16              # the obstruction for one block
    python -m computations.zero_entropy --block 000000001011 --width 16 --naive   # closed by classes, checked twice
    python -m computations.zero_entropy --survey 3 12 --width 16 --workers 2  # every block of period 3 to 12
    python -m computations.zero_entropy --survey 3 12 --width 18 --walks 0 --workers 2   # the classes alone
    python -m computations.zero_entropy --search 001 --budget 4000000         # the forced list of least entropy
"""

from __future__ import annotations

import argparse
import functools
import itertools
import math
import multiprocessing
import sys
import time
from collections.abc import Iterator
from dataclasses import dataclass

import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components, shortest_path
from tqdm.auto import tqdm

from computations.game import moves, necklaces
from computations.reading_certificates import sample_readings, step

Word = tuple[str, int]  # a forbidden word and the read position of its first reading, -1 for every position


# ---------------------------------------------------------------------------------------------------------------------
# Phase-aware shifts of finite type


def completes(text: str, word: Word, position: int, k: int) -> bool:
    """Whether `text`, whose last reading is at read position `position` (mod k), ends with the tagged word."""
    u, j = word
    return text.endswith(u) and (j < 0 or (position - len(u) + 1) % k == j)


def sft_graph(words: tuple[Word, ...], k: int, constants: dict[int, int] | None = None,
              frame: int = 1) -> csr_matrix:
    """The de Bruijn graph of the readings that avoid the tagged words, k readings per period, with the reading at
    position j of a frame of `frame` periods fixed to `constants[j]`. Node j * 2^(L-1) + s: the next reading is at
    position j of the frame and s holds the last L - 1 readings, newest in bit 0."""
    constants = constants or {}
    m = k * frame
    keep = max([len(u) for u, _ in words] + [1]) - 1
    sufs = 1 << keep
    rows, cols = [], []
    for j in range(m):
        for s in range(sufs):
            for bit in (0, 1):
                if j in constants and constants[j] != bit:
                    continue
                text = (format(s, f"0{keep}b") if keep else "") + str(bit)
                if any(completes(text, w, j % k, k) for w in words):
                    continue
                rows.append(j * sufs + s)
                cols.append(((j + 1) % m) * sufs + (((s << 1) | bit) & (sufs - 1)))
    n = m * sufs
    return csr_matrix((np.ones(len(rows), dtype=np.int64), (rows, cols)), shape=(n, n))


def sft_is_zero(graph: csr_matrix) -> bool:
    """Whether every strongly connected component with an edge inside it is a single cycle: as many edges inside it as
    nodes, parallel edges counted by their weight. Exactly the graphs whose shift has entropy 0."""
    _, label = connected_components(graph, directed=True, connection="strong")  # (n,)
    coo = graph.tocoo()
    inside = label[coo.row] == label[coo.col]  # (e,)
    edges = np.bincount(label[coo.row[inside]], weights=coo.data[inside],
                        minlength=label.max() + 1).astype(np.int64)  # (components,), parallel edges counted
    nodes = np.bincount(label, minlength=label.max() + 1)  # (components,)
    return bool(np.all((edges == 0) | (edges == nodes)))


def sft_entropy(graph: csr_matrix, iterations: int = 4000) -> float:
    """The entropy in bits per reading: log2 of the spectral radius, by power iteration on A + I (whose radius is the
    radius of A plus 1 and which is aperiodic). Approximate, except that 0 is returned exactly when `sft_is_zero`."""
    n = graph.shape[0]
    if graph.nnz == 0 or sft_is_zero(graph):
        return 0.0
    a = graph.astype(np.float64)  # (n, n)
    v = np.ones(n) / n  # (n,)
    radius = 0.0
    for _ in range(iterations):
        u = a @ v + v  # (n,)
        new = float(u.sum())
        v = u / new
        if abs(new - radius) < 1e-13:
            break
        radius = new
    return max(0.0, math.log2(max(radius - 1.0, 1e-300)))


# ---------------------------------------------------------------------------------------------------------------------
# Forced lists of tagged words


def white_phases(block: str) -> tuple[int, ...]:
    """The phases at which the block reads 0."""
    return tuple(p for p, c in enumerate(block) if c == "0")


def forced(block: str, width: int, words: tuple[Word, ...]) -> tuple[bool, int, int]:
    """Whether entry into the good set of the tagged words read at every white phase is forced from every state at this
    width, the largest rank, and the number of states."""
    whites = white_phases(block)
    k, period = len(whites), len(block)
    keep = max(len(u) for u, _ in words) - 1
    n, sufs = 1 << width, 1 << keep
    win = np.arange(n, dtype=np.int64)  # (n,)
    suf = np.arange(sufs, dtype=np.int64)  # (S,)
    bit = win & 1  # (n,): column 1 before the step
    idx0, idx1 = [], []
    bad = np.zeros((period, n, sufs), dtype=bool)  # (P, n, S)
    for p in range(period):
        c = int(block[p])
        if p in whites:
            j = whites.index(p)
            table = np.zeros((sufs, 2), dtype=bool)  # (S, 2)
            for s in range(sufs):
                for b in (0, 1):
                    text = (format(s, f"0{keep}b") if keep else "") + str(b)
                    table[s, b] = any(completes(text, w, j, k) for w in words)
            s_new = ((suf[None, :] << 1) | bit[:, None]) & (sufs - 1)  # (n, S)
            bad[p] = table[suf[None, :], bit[:, None]]
        else:
            s_new = np.broadcast_to(suf[None, :], (n, sufs))  # (n, S)
        idx0.append(step(win, width, c, 0)[:, None] * sufs + s_new)  # (n, S)
        idx1.append(step(win, width, c, 1)[:, None] * sufs + s_new)  # (n, S)
    good = ~bad  # (P, n, S)
    while True:
        new = good.copy()
        for p in range(period):
            nxt = good[(p + 1) % period].ravel()  # (n * S,)
            new[p] &= nxt[idx0[p]] & nxt[idx1[p]]
        if np.array_equal(new, good):
            break
        good = new
    states = period * n * sufs
    if not good.any():
        return False, -1, states
    done, rank = good.copy(), 0  # (P, n, S)
    while not done.all():
        add = np.zeros_like(done)  # (P, n, S)
        for p in range(period):
            nxt = done[(p + 1) % period].ravel()  # (n * S,)
            add[p] = nxt[idx0[p]] & nxt[idx1[p]]
        add &= ~done
        if not add.any():
            return False, -1, states
        done |= add
        rank += 1
    return True, rank, states


def learned(block: str, runs: list[list[tuple[int, int]]], length: int) -> list[Word]:
    """The minimal tagged words of at most `length` readings that no sampled run shows: (u, j) unseen with (u[:-1], j)
    and (u[1:], j + 1) seen, the read position j taken mod k."""
    whites = white_phases(block)
    k = len(whites)
    seen: list[set[int]] = [set() for _ in range(length + 1)]  # seen[l]: codes j * 2^l + value of the seen words
    for run in runs:
        bits = np.array([b for _, b in run], dtype=np.int64)  # (m,)
        pos = np.array([whites.index(p) for p, _ in run], dtype=np.int64)  # (m,)
        code = np.zeros(bits.size, dtype=np.int64)  # (m,)
        for ln in range(1, length + 1):
            if bits.size < ln:
                break
            code = (code[:-1] << 1 | bits[ln - 1:]) if ln > 1 else bits.copy()  # (m - ln + 1,), words at each start
            seen[ln].update((pos[:code.size] * (1 << ln) + code).tolist())
    out: list[Word] = []
    for ln in range(1, length + 1):
        for j in range(k):
            for x in range(1 << ln):
                if j * (1 << ln) + x in seen[ln]:
                    continue
                if ln > 1 and (j * (1 << (ln - 1)) + (x >> 1) not in seen[ln - 1]
                               or ((j + 1) % k) * (1 << (ln - 1)) + (x & ((1 << (ln - 1)) - 1)) not in seen[ln - 1]):
                    continue
                out.append((format(x, f"0{ln}b"), j))
    return out


def list_entropy(block: str, words: tuple[Word, ...]) -> tuple[float, bool]:
    """The entropy of the readings at every white phase that avoid the tagged words, and whether it is exactly 0."""
    graph = sft_graph(words, len(white_phases(block)))
    return sft_entropy(graph), sft_is_zero(graph)


@dataclass
class Searched:
    """The forced list of least entropy found for a block."""

    block: str
    width: int
    words: tuple[Word, ...]
    entropy: float
    zero: bool
    rank: int
    states: int
    candidates: int


def search(block: str, budget: int, length: int = 10, max_width: int = 16, halves: int = 24, steps: int = 3000,
           orders: int = 4, exhaustive: int = 12, seed: int = 0, progress: bool = False) -> Searched | None:
    """The forced list of tagged learned words of least entropy within `budget` states: for each longest length L, the
    widest window the budget allows, the words of length at most L added greedily in `orders` orders (shortest first,
    then shuffled) while entry stays forced, and every subset when at most `exhaustive` candidates remain."""
    runs = sample_readings(block, halves, steps, seed)
    words = learned(block, runs, length)
    period = len(block)
    rng = np.random.default_rng(seed)
    best: Searched | None = None
    lengths = sorted({len(u) for u, _ in words})
    for ln in tqdm(lengths, desc=f"search {block}", file=sys.stderr, leave=False, disable=not progress):
        width = max_width
        while width > 2 and period * (1 << width) * (1 << (ln - 1)) > budget:
            width -= 1
        pool = [w for w in words if len(w[0]) <= ln and forced(block, width, (w,))[0]]
        if not pool or max(len(u) for u, _ in pool) < ln:
            continue
        tried: list[tuple[Word, ...]] = []
        if len(pool) <= exhaustive:
            for size in range(len(pool), 0, -1):
                for subset in itertools.combinations(pool, size):
                    if any(set(subset) <= set(t) for t in tried):
                        continue
                    if forced(block, width, subset)[0]:
                        tried.append(subset)
        else:
            for o in range(orders):
                order = sorted(pool, key=lambda w: (len(w[0]), w)) if o == 0 else \
                    [pool[i] for i in rng.permutation(len(pool))]
                chosen: list[Word] = []
                for w in order:
                    if forced(block, width, tuple(chosen + [w]))[0]:
                        chosen.append(w)
                tried.append(tuple(chosen))
        for chosen in tried:
            h, zero = list_entropy(block, chosen)
            ok, rank, states = forced(block, width, chosen)
            row = Searched(block, width, chosen, h, zero, rank, states, len(pool))
            if best is None or (not best.zero and (zero or h < best.entropy - 1e-9)):
                best = row
    return best


def factor_counts(runs: list[list[tuple[int, int]]], lengths: tuple[int, ...]) -> list[int]:
    """The number of distinct words of each length among the sampled readings (every white phase together)."""
    out = []
    for ln in lengths:
        seen: set[int] = set()
        for run in runs:
            bits = np.array([b for _, b in run], dtype=np.int64)  # (m,)
            if bits.size < ln:
                continue
            code = np.zeros(bits.size - ln + 1, dtype=np.int64)  # (m - ln + 1,)
            for i in range(ln):
                code = code << 1 | bits[i:bits.size - ln + 1 + i]
            seen.update(np.unique(code).tolist())
        out.append(len(seen))
    return out


def sampled_growth(block: str, halves: int = 24, steps: int = 3000, lengths: tuple[int, int] = (12, 20),
                   seed: int = 0) -> float:
    """A heuristic entropy of the sampled readings: log2 of the ratio of the numbers of distinct words of the two
    lengths, divided by the difference of the lengths. A sample, not a bound."""
    counts = factor_counts(sample_readings(block, halves, steps, seed), lengths)
    return math.log2(counts[1] / counts[0]) / (lengths[1] - lengths[0])


# ---------------------------------------------------------------------------------------------------------------------
# The obstruction in the window graph


@dataclass
class Analysis:
    """The recurrent components of the width-W window graph of a block and how the readings sit in them."""

    block: str
    width: int
    components: int  # recurrent components (with a move inside)
    phase_mixed: int  # recurrent components where the reading takes both values at one phase (the game fails)
    class_mixed: int  # recurrent components where it takes both values in one cyclic class (entropy above 0)
    largest: int  # nodes of the largest class-mixed component, 0 if none
    cycle: int  # its cyclic period in steps
    root: int  # a node of it in a class where both values meet, -1 if none


def readings_of(block: str, width: int) -> np.ndarray:
    """The reading at each node phase * 2^W + window: column 1 at a white phase, -1 at a black phase."""
    n = 1 << width
    out = np.full(len(block) * n, -1, dtype=np.int64)  # (P n,)
    for p in white_phases(block):
        out[p * n:(p + 1) * n] = np.arange(n) & 1
    return out


def analyze(block: str, width: int) -> Analysis:
    """The recurrent components of the window graph and whether the readings are a function of the phase (the game's
    test) and of the cyclic class (zero entropy) in each."""
    period, n = len(block), 1 << width
    nodes = period * n
    src, tgt = moves(block, width)  # (2 P n,), (2 P n,)
    graph = csr_matrix((np.ones(src.size, dtype=np.int8), (src, tgt)), shape=(nodes, nodes))
    _, label = connected_components(graph, directed=True, connection="strong")  # (P n,)
    inside = label[src] == label[tgt]  # (2 P n,)
    s_in, t_in = src[inside], tgt[inside]  # (e,), (e,)
    recurrent = np.unique(label[s_in])  # (c,)
    reading = readings_of(block, width)  # (P n,)
    if recurrent.size == 0:
        return Analysis(block, width, 0, 0, 0, 0, 0, -1)
    roots = np.full(label.max() + 1, -1, dtype=np.int64)  # (components,), the least node of each
    on = np.flatnonzero(np.isin(label, recurrent))  # (m,)
    first = np.unique(label[on], return_index=True)[1]  # (c,)
    roots[label[on[first]]] = on[first]
    # A super-root linked to each recurrent component's root; BFS levels along moves inside components
    sup = nodes
    rows = np.concatenate([s_in, np.full(recurrent.size, sup)])  # (e + c,)
    cols = np.concatenate([t_in, roots[recurrent]])  # (e + c,)
    inner = csr_matrix((np.ones(rows.size, dtype=np.int8), (rows, cols)), shape=(nodes + 1, nodes + 1))
    dist = shortest_path(inner, directed=True, unweighted=True, indices=sup)  # (P n + 1,)
    level = np.where(np.isfinite(dist), dist - 1, -1).astype(np.int64)[:nodes]  # (P n,)
    gap = np.abs(level[s_in] + 1 - level[t_in])  # (e,)
    cyc = np.zeros(label.max() + 1, dtype=np.int64)  # (components,)
    np.gcd.at(cyc, label[s_in], gap)
    white = on[reading[on] >= 0]  # (m',), nodes of recurrent components at white phases
    comp = label[white]  # (m',)

    def mixed(key: np.ndarray) -> np.ndarray:
        """The components in which some key shows both readings."""
        order = np.lexsort((key, comp))  # (m',)
        c, kk, r = comp[order], key[order], reading[white][order]  # (m',) each
        new = np.r_[True, (c[1:] != c[:-1]) | (kk[1:] != kk[:-1])]  # (m',), the first node of each group
        group = np.cumsum(new) - 1  # (m',)
        ones = np.bincount(group, weights=r)  # (groups,)
        count = np.bincount(group)  # (groups,)
        both = (ones > 0) & (ones < count)  # (groups,)
        return np.unique(c[new][both])

    phase_bad = mixed(white // n)
    class_bad = mixed(level[white] % cyc[comp])
    if class_bad.size == 0:
        return Analysis(block, width, int(recurrent.size), int(phase_bad.size), 0, 0, 0, -1)
    sizes = np.bincount(label)  # (components,)
    big = int(class_bad[np.argmax(sizes[class_bad])])
    # a node of the big component whose class shows both readings
    members = white[comp == big]  # (q,)
    cls = level[members] % cyc[big]  # (q,)
    root = -1
    for value in np.unique(cls).tolist():
        here = members[cls == value]
        if np.unique(reading[here]).size == 2:
            root = int(here[0])
            break
    return Analysis(block, width, int(recurrent.size), int(phase_bad.size), int(class_bad.size), int(sizes[big]),
                    int(cyc[big]), root)


@dataclass
class Witness:
    """Closed walks of the window graph through one node, each as its start window, phase and free inputs, with the
    readings, and the entropy bound of a code among them."""

    block: str
    width: int
    phase: int
    window: int
    inputs: list[list[int]]  # the free column W + 1 at each step of each walk
    labels: list[str]  # the readings of each walk
    code: list[int]  # indices of the walks whose readings form the code
    bound: float  # bits per reading


def code_bound(lengths: list[int]) -> float:
    """log2 x for the x > 1 with sum x^-l = 1, the growth of a code with these word lengths (0 for fewer than two)."""
    if len(lengths) < 2:
        return 0.0
    lo, hi = 1.0, 2.0
    for _ in range(200):
        mid = (lo + hi) / 2
        if sum(mid ** -ln for ln in lengths) > 1:
            lo = mid
        else:
            hi = mid
    return math.log2(lo)


def is_code(words: list[str]) -> bool:
    """Whether the distinct nonempty words are a code (every concatenation factors in one way): the Sardinas-Patterson
    test, which follows the sets of dangling suffixes until one contains a word or the empty word, or they repeat."""
    code = set(words)
    if len(code) != len(words) or "" in code:
        return False

    def quotients(left: set[str], right: set[str]) -> set[str]:
        """The words x with u x in `right` for some u in `left`."""
        return {v[len(u):] for u in left for v in right if v.startswith(u)}

    dangling = quotients(code, code) - {""}
    seen: set[frozenset[str]] = set()
    while dangling:
        if "" in dangling or dangling & code:
            return False
        key = frozenset(dangling)
        if key in seen:
            return True
        seen.add(key)
        dangling = quotients(code, dangling) | quotients(dangling, code)
    return True


def greedy_code(labels: list[str], limit: int = 40) -> list[int]:
    """Indices of a code among the labels, taken greedily from the shortest while the set stays a code, at most
    `limit` words; a single word or none gives no bound."""
    order = sorted(range(len(labels)), key=lambda i: (len(labels[i]), labels[i]))
    chosen: list[int] = []
    for i in order:
        if len(chosen) >= limit:
            break
        if is_code([labels[j] for j in chosen] + [labels[i]]):
            chosen.append(i)
    return chosen if len(chosen) >= 2 else []


MODULI = (2_147_483_647, 2_147_483_629)  # two primes below 2^31, so products fit in int64
BASE = 1_000_003


def tree_walks(fwd: csr_matrix, bwd: csr_matrix, v: int, reading: np.ndarray) -> tuple[np.ndarray, ...]:
    """The shortest walks v -> x (forward tree) and x -> v (backward tree) inside a component: distances,
    predecessors, and for each node the number of readings and the two hashes of the readings of the walk v -> x
    (the nodes v .. before x) and of the walk x -> v (the nodes x .. before v), letter 1 for white, 2 for black."""
    d_f, p_f = shortest_path(fwd, unweighted=True, indices=v, return_predecessors=True)  # (N,), (N,)
    d_b, p_b = shortest_path(bwd, unweighted=True, indices=v, return_predecessors=True)  # (N,), (N,)
    n = reading.size
    letter = np.where(reading >= 0, reading + 1, 0).astype(np.int64)  # (N,), 0 at black phases
    has = (letter > 0).astype(np.int64)  # (N,)
    f_len, b_len = np.zeros(n, dtype=np.int64), np.zeros(n, dtype=np.int64)  # (N,), (N,)
    f_hash, b_hash = np.zeros((2, n), dtype=np.int64), np.zeros((2, n), dtype=np.int64)  # (2, N), (2, N)
    depth = int(max(d_f[np.isfinite(d_f)].max(), d_b[np.isfinite(d_b)].max()))
    power = np.ones((2, depth + 2), dtype=np.int64)  # (2, depth + 2), BASE^l
    for i, m in enumerate(MODULI):
        for ln in range(1, depth + 2):
            power[i, ln] = power[i, ln - 1] * BASE % m
    for level in range(1, depth + 1):
        here = np.flatnonzero(d_f == level)  # (h,)
        par = p_f[here]  # (h,)
        f_len[here] = f_len[par] + has[par]
        for i, m in enumerate(MODULI):
            mult = np.where(has[par] > 0, BASE, 1)  # (h,)
            f_hash[i, here] = (f_hash[i, par] * mult + letter[par]) % m
        here = np.flatnonzero(d_b == level)  # (h,)
        nxt = p_b[here]  # (h,), the next node toward v
        b_len[here] = b_len[nxt] + has[here]
        for i, m in enumerate(MODULI):
            b_hash[i, here] = (letter[here] * power[i, b_len[nxt]] * has[here] + b_hash[i, nxt]) % m
    return d_f, p_f, d_b, p_b, f_len, f_hash, b_len, b_hash, letter, has


def walk_through(block: str, width: int, v: int, x: int, y: int, p_f: np.ndarray, p_b: np.ndarray,
                 reading: np.ndarray) -> tuple[list[int], str]:
    """The closed walk v .. x, y .. v along the trees, as its free inputs and its readings."""
    period, n = len(block), 1 << width
    path = [x]
    while path[-1] != v:
        path.append(int(p_f[path[-1]]))
    path.reverse()  # v .. x
    tail = [y]
    while tail[-1] != v:
        tail.append(int(p_b[tail[-1]]))  # y .. v
    walk = path + tail
    free = []
    for a, b in zip(walk[:-1], walk[1:]):
        ph, w = divmod(a, n)
        x0 = int(step(np.array([w]), width, int(block[ph]), 0)[0]) + ((ph + 1) % period) * n
        free.append(0 if x0 == b else 1)
    return free, "".join(str(int(reading[a])) for a in walk[:-1] if reading[a] >= 0)


def primitive_root(u: str) -> str:
    """The shortest z with u a power of z."""
    for d in range(1, len(u) + 1):
        if len(u) % d == 0 and u[:d] * (len(u) // d) == u:
            return u[:d]
    return u


def witness(block: str, width: int, root: int, walks: int = 200, roots: int = 4, seed: int = 0) -> Witness:
    """A code among closed walks through one node v of the component of `root`. Every closed walk at v is, in the
    free group, a product of the walks C_e = (tree walk v -> x) e (tree walk y -> v) over the moves e = (x, y) inside
    the component, so the readings of all closed walks at v are powers of one word z exactly when every C_e is. The
    readings of each C_e are compared with powers of z (the primitive root of the shortest C_e) by two polynomial
    hashes: a mismatch is exact, so the shortest C_e that mismatches does not commute with the shortest one, a two-word
    code (checked on the strings). The `walks` shortest C_e are then added greedily while the set stays a code. `root`
    and `roots - 1` random nodes of the component are tried; the code of the largest bound is kept."""
    period, n = len(block), 1 << width
    nodes = period * n
    src, tgt = moves(block, width)  # (2 P n,), (2 P n,)
    graph = csr_matrix((np.ones(src.size, dtype=np.int8), (src, tgt)), shape=(nodes, nodes))
    _, label = connected_components(graph, directed=True, connection="strong")  # (P n,)
    keep = (label[src] == label[root]) & (label[tgt] == label[root])  # (2 P n,)
    s_in, t_in = src[keep], tgt[keep]  # (e,), (e,)
    fwd = csr_matrix((np.ones(s_in.size, dtype=np.int8), (s_in, t_in)), shape=(nodes, nodes))
    bwd = csr_matrix((np.ones(s_in.size, dtype=np.int8), (t_in, s_in)), shape=(nodes, nodes))
    reading = readings_of(block, width)  # (P n,)
    members = np.flatnonzero(label == label[root])  # (m,)
    rng = np.random.default_rng(seed)
    starts = [root] + [int(v) for v in rng.choice(members, size=min(roots - 1, members.size), replace=False)]
    best: Witness | None = None
    for v in starts:
        d_f, p_f, d_b, p_b, f_len, f_hash, b_len, b_hash, letter, has = tree_walks(fwd, bwd, v, reading)
        total = d_f[s_in] + 1 + d_b[t_in]  # (e,), steps of each C_e
        c_len = f_len[s_in] + has[s_in] + b_len[t_in]  # (e,), readings of each C_e
        c_hash = np.zeros((2, s_in.size), dtype=np.int64)  # (2, e)
        top = int(c_len.max()) + 1
        for i, m in enumerate(MODULI):
            pw = np.ones(top + 1, dtype=np.int64)  # (top + 1,)
            for ln in range(1, top + 1):
                pw[ln] = pw[ln - 1] * BASE % m
            head = (f_hash[i, s_in] * np.where(has[s_in] > 0, BASE, 1) + letter[s_in]) % m  # (e,)
            c_hash[i] = (head * pw[b_len[t_in]] + b_hash[i, t_in]) % m
        first = int(np.argmin(total))
        free0, text0 = walk_through(block, width, v, int(s_in[first]), int(t_in[first]), p_f, p_b, reading)
        z = primitive_root(text0)
        zh = [0, 0]
        for i, m in enumerate(MODULI):
            for ch in z:
                zh[i] = (zh[i] * BASE + int(ch) + 1) % m
        power_ok = c_len % len(z) == 0  # (e,)
        for i, m in enumerate(MODULI):
            reps = np.zeros(top // len(z) + 2, dtype=np.int64)  # (reps,), hash of z^r
            zpow = pow(BASE, len(z), m)
            for r in range(1, reps.size):
                reps[r] = (reps[r - 1] * zpow + zh[i]) % m
            power_ok &= c_hash[i] == reps[np.minimum(c_len // len(z), reps.size - 1)]
        bad = np.flatnonzero(~power_ok)  # (b,), walks that are not powers of z
        labels, inputs = [text0], [free0]
        if bad.size:
            e = int(bad[np.argmin(total[bad])])
            free, text = walk_through(block, width, v, int(s_in[e]), int(t_in[e]), p_f, p_b, reading)
            labels.append(text)
            inputs.append(free)
        seen = set(labels)
        for e in np.argsort(total, kind="stable")[:walks].tolist():
            free, text = walk_through(block, width, v, int(s_in[e]), int(t_in[e]), p_f, p_b, reading)
            if text not in seen:
                seen.add(text)
                labels.append(text)
                inputs.append(free)
        pair = [0, 1] if bad.size and is_code(labels[:2]) else []
        code = greedy_code(labels)
        if code_bound([len(labels[i]) for i in code]) < code_bound([len(labels[i]) for i in pair]):
            code = pair
        ph, w = divmod(v, n)
        found = Witness(block, width, ph, w, inputs, labels, code, code_bound([len(labels[i]) for i in code]))
        if best is None or found.bound > best.bound:
            best = found
    assert best is not None
    return best


def naive_walk(block: str, width: int, phase: int, window: int, free: list[int]) -> tuple[int, int, str]:
    """Run the cells 1..W cell by cell (cell i + 1 from cells i, i + 1, i + 2 with the center as cell 0 and the free
    input as cell W + 1) and return the final phase, window and the readings at white phases."""
    cells = [(window >> i) & 1 for i in range(width)]
    out = []
    p = phase
    for x in free:
        center = int(block[p])
        if center == 0:
            out.append(str(cells[0]))
        row = [center] + cells + [x]
        cells = [row[i - 1] ^ (row[i] | row[i + 1]) for i in range(1, width + 1)]
        p = (p + 1) % len(block)
    return p, sum(b << i for i, b in enumerate(cells)), "".join(out)


def check_witness(wit: Witness) -> bool:
    """Every walk of the code returns to its start, cell by cell, with the stated readings, and the readings are a
    code of at least two words."""
    for i in wit.code:
        p, w, text = naive_walk(wit.block, wit.width, wit.phase, wit.window, wit.inputs[i])
        if (p, w, text) != (wit.phase, wit.window, wit.labels[i]):
            return False
    words = [wit.labels[i] for i in wit.code]
    return len(words) >= 2 and is_code(words)


def naive_classes(block: str, width: int) -> list[tuple[int, int, bool, bool]]:
    """The recurrent components of the window graph, built cell by cell in plain Python with Tarjan's algorithm and
    levels along a search inside each component: for each, its size, its cyclic period, whether the reading takes both
    values at one phase, and whether it takes both values in one cyclic class. Independent of `moves` and of scipy."""
    period, n = len(block), 1 << width
    nodes = period * n
    succ: list[tuple[int, int]] = []
    bar = tqdm(total=nodes, desc=f"naive graph {block}", file=sys.stderr, mininterval=10, disable=nodes < 200_000)
    for node in range(nodes):
        ph, w = divmod(node, n)
        out = []
        for x in (0, 1):
            cells = [int(block[ph])] + [(w >> i) & 1 for i in range(width)] + [x]
            v = 0
            for i in range(1, width + 1):
                v |= (cells[i - 1] ^ (cells[i] | cells[i + 1])) << (i - 1)
            out.append(((ph + 1) % period) * n + v)
        succ.append((out[0], out[1]))
        bar.update()
    bar.close()
    # Tarjan, iteratively
    index = [-1] * nodes
    low = [0] * nodes
    comp = [-1] * nodes
    on_stack = [False] * nodes
    stack: list[int] = []
    counter, ncomp = 0, 0
    for start in range(nodes):
        if index[start] >= 0:
            continue
        work = [(start, 0)]
        index[start] = low[start] = counter
        counter += 1
        stack.append(start)
        on_stack[start] = True
        while work:
            u, i = work[-1]
            if i < 2:
                work[-1] = (u, i + 1)
                v = succ[u][i]
                if index[v] < 0:
                    index[v] = low[v] = counter
                    counter += 1
                    stack.append(v)
                    on_stack[v] = True
                    work.append((v, 0))
                elif on_stack[v]:
                    low[u] = min(low[u], index[v])
                continue
            work.pop()
            if work:
                parent = work[-1][0]
                low[parent] = min(low[parent], low[u])
            if low[u] == index[u]:
                while True:
                    v = stack.pop()
                    on_stack[v] = False
                    comp[v] = ncomp
                    if v == u:
                        break
                ncomp += 1
    members: dict[int, list[int]] = {}
    for v in range(nodes):
        members.setdefault(comp[v], []).append(v)
    found = []
    for c, vs in members.items():
        inner = [(u, v) for u in vs for v in succ[u] if comp[v] == c]
        if not inner:
            continue
        level = {vs[0]: 0}
        queue = [vs[0]]
        for u in queue:
            for v in succ[u]:
                if comp[v] == c and v not in level:
                    level[v] = level[u] + 1
                    queue.append(v)
        cycle = 0
        for u, v in inner:
            cycle = math.gcd(cycle, abs(level[u] + 1 - level[v]))
        by_phase: dict[int, set[int]] = {}
        by_class: dict[int, set[int]] = {}
        for v in vs:
            ph, w = divmod(v, n)
            if block[ph] == "0":
                by_phase.setdefault(ph, set()).add(w & 1)
                by_class.setdefault(level[v] % cycle, set()).add(w & 1)
        found.append((len(vs), cycle, any(len(x) == 2 for x in by_phase.values()),
                      any(len(x) == 2 for x in by_class.values())))
    return sorted(found, reverse=True)


def driven_period(block: str, half: int, steps: int, tail: int) -> int:
    """The least p (a multiple of the block's period, at most `tail` / 2) such that the readings of column 1 of the
    right half `half` (bit i the cell i + 1), driven by the center repeating the block, repeat with p steps over the last
    `tail` steps of `steps`; 0 if none. Cell by cell on Python integers, so the half grows without bound."""
    row, col1 = half, []
    for t in range(steps):
        center = int(block[t % len(block)])
        col1.append(row & 1)
        row = ((row << 1) | center) ^ (row | (row >> 1))
    last = col1[steps - tail:]
    whites = [block[(steps - tail + i) % len(block)] == "0" for i in range(tail)]
    for p in range(len(block), tail // 2 + 1, len(block)):
        if all(last[i] == last[i + p] for i in range(tail - p) if whites[i]):
            return p
    return 0


# ---------------------------------------------------------------------------------------------------------------------
# The survey


def survey_one(block: str, width: int, walks: int) -> dict[str, object]:
    """The analysis of one block at one width, with a checked witness when some component's readings mix."""
    a = analyze(block, width)
    row: dict[str, object] = {"block": block, "components": a.components, "phase_mixed": a.phase_mixed,
                              "class_mixed": a.class_mixed, "largest": a.largest, "cycle": a.cycle}
    if a.root >= 0 and walks > 0:
        wit = witness(block, width, a.root, walks)
        row.update(bound=wit.bound, code=[len(wit.labels[i]) for i in wit.code], checked=check_witness(wit),
                   shortest=[wit.labels[i] for i in wit.code[:2]])
    return row


def survey(periods: range, width: int, walks: int, workers: int) -> Iterator[dict[str, object]]:
    """`survey_one` for every primitive necklace with both colors of the given periods, yielded as they finish."""
    blocks = [b for p in periods for b in necklaces(p) if "0" in b and "1" in b]
    task = functools.partial(survey_one, width=width, walks=walks)
    bar = functools.partial(tqdm, total=len(blocks), desc=f"blocks at width {width}", file=sys.stderr, mininterval=10)
    if workers > 1:
        with multiprocessing.get_context("spawn").Pool(workers) as pool:
            yield from bar(pool.imap(task, blocks, chunksize=2))
    else:
        yield from (task(b) for b in bar(blocks))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--block", help="analyze one block")
    parser.add_argument("--width", type=int, default=14)
    parser.add_argument("--walks", type=int, default=400, help="closed walks tried for the code")
    parser.add_argument("--survey", type=int, nargs=2, metavar=("MIN", "MAX"), help="periods of the survey")
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--search", nargs="*", help="blocks for the search of forced lists")
    parser.add_argument("--budget", type=int, default=4_000_000)
    parser.add_argument("--length", type=int, default=10, help="longest learned word")
    parser.add_argument("--naive", action="store_true", help="with --block: the components built cell by cell too")
    parser.add_argument("--orders", type=int, default=4, help="greedy orders tried by the search")
    parser.add_argument("--exhaustive", type=int, default=12, help="largest pool whose subsets are all tried")
    args = parser.parse_args()
    started = time.perf_counter()
    if args.block:
        print(survey_one(args.block, args.width, args.walks))
        if args.naive:
            print("cell by cell (size, cyclic period, mixed at a phase, mixed in a class):",
                  naive_classes(args.block, args.width))
    if args.survey:
        for row in survey(range(args.survey[0], args.survey[1] + 1), args.width, args.walks, args.workers):
            print(row, flush=True)
    if args.search:
        for block in args.search:
            row = search(block, args.budget, args.length, max_width=args.width, orders=args.orders,
                         exhaustive=args.exhaustive, progress=True)
            if row is None:
                print(f"{block}: no forced list within {args.budget} states", flush=True)
            else:
                print(f"{block}: width {row.width}, {len(row.words)} words of {row.candidates} forced alone, entropy "
                      f"{row.entropy:.3f}{' (exactly 0)' if row.zero else ''}, rank {row.rank}, {row.states} states, "
                      f"words {[u if j < 0 else f'{u}@{j}' for u, j in row.words]}", flush=True)
    print(f"({time.perf_counter() - started:.0f} s)", file=sys.stderr)


if __name__ == "__main__":
    main()
