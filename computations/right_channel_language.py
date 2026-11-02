"""The exact right channel beside an alternating center: the limit set of windows and the language of column 1.

Drive a right half with the center alternating and read its window of columns 1..W at the white steps of the center,
with column W + 1 free at both steps of each double step (`gate_census.double_steps`). Let S_0 be every window and
S_{i+1} the set of double steps, with every input, of the windows of S_i. The chain decreases (S_1 is inside S_0, and
the image keeps inclusion) and stops at its fixpoint E_W, the limit set, after `chain` iterations. A finite or
infinite right half has its window in S_s at its white step s, so in E_W from the white step `chain` on, whatever its
cells beyond the window. So column 1 at the white steps, the kit's `u R`, is from then on the column 1 of a path of
double steps inside E_W: the right channel at width W.

- `image_chain`: the rank of every window (the largest i with the window in S_i, at most `chain`) and the chain length.
- `window_components`: the strongly connected components of the double-step graph on E_W that hold a cycle, with the
  gcd of their cycle lengths, whether a double step leaves them, whether column 1 is a function of the cyclic class,
  whether they lie inside the gap trap (every window black in column 1 is, cut to 16 columns, an entry window of
  `gate_census.gap_entry`, so that every play from it has its black cells of column 1 come 3 or 5 white steps apart;
  from W = 16) and whether they hold the two windows of the aligned ether (`three_set_game.ether_cycle`).
- `determinize`: the subset construction of the language of column 1 of the paths in E_W (start state E_W; the
  letter b sends a subset to the double steps of its windows whose column 1 is b). Subsets are held as sorted index
  arrays into E_W only while they wait in the queue; the table of subsets keeps a 16-byte BLAKE2 digest of each (two
  subsets with the same digest would be merged; among the 127,589 subsets at W = 28 the chance of that is below 2^-94).
- `component_growths`: the growth per white step of each strongly connected component of the subset automaton
  (its spectral radius); the largest is the growth of the language, and log2 of it the entropy per white step.
- `kill_test`: every right half of up to `cells` cells, in both phases, run directly; its windows from the white step
  `start` on lie in E_W, and its column 1 from there on is read by the subset automaton without reaching the empty
  subset.

    python -m computations.right_channel_language ladder --widths 8 10 12 14 16 18 20 22 24   # about 70 s
    python -m computations.right_channel_language ladder --widths 26   # 3 to 6 min, under 1 GB
    python -m computations.right_channel_language ladder --widths 28   # about 30 min, 1.4 GB
    python -m computations.right_channel_language kill --width 14 --cells 14 --steps 1000 --start 20   # about 35 s
    python -m computations.right_channel_language lean --width 14   # the ranks as bitmaps for the Lean module
"""

from __future__ import annotations

import argparse
import hashlib
import math
import sys
import time
from dataclasses import dataclass

import numpy as np
import scipy.sparse as sp
from scipy.sparse.csgraph import connected_components
from tqdm.auto import tqdm

from computations.gate_census import double_steps

CHUNK = 1 << 22  # windows per block when the double steps are computed in blocks


def successors_of(codes: np.ndarray, width: int) -> np.ndarray:
    """The four double steps of each window of `codes`, as int64, computed in blocks."""
    # codes: (n,)
    out = np.empty((len(codes), 4), dtype=np.int64)  # (n, 4)
    for lo in range(0, len(codes), CHUNK):
        out[lo:lo + CHUNK] = double_steps(codes[lo:lo + CHUNK], width)
    return out


def image_chain(width: int, progress: bool = False) -> tuple[np.ndarray, int]:
    """rank[w] = the largest i <= chain with w in S_i, where S_0 is every window, S_{i+1} the image of S_i under the
    double step with every input, and chain the first i with S_{i+1} = S_i. The limit set E_W is rank == chain."""
    n = 1 << width
    cur = np.ones(n, dtype=bool)  # (2^W,) S_i
    rank = np.zeros(n, dtype=np.int16)  # (2^W,)
    bar = tqdm(desc=f"image chain W={width}", file=sys.stderr, disable=not progress, leave=False)
    chain = 0
    while True:
        nxt = np.zeros(n, dtype=bool)  # (2^W,) S_{i+1}
        for lo in range(0, n, CHUNK):
            members = lo + np.flatnonzero(cur[lo:lo + CHUNK])  # (block of S_i,)
            nxt[double_steps(members, width).ravel()] = True
        if np.array_equal(nxt, cur):
            break
        assert not (nxt & ~cur).any()  # the chain decreases
        cur = nxt
        chain += 1
        rank += cur
        bar.update(1)
    bar.close()
    return rank, chain


def limit_set(width: int, progress: bool = False) -> tuple[np.ndarray, int]:
    """The windows of E_W, sorted, and the chain length."""
    rank, chain = image_chain(width, progress)
    return np.flatnonzero(rank == chain), chain  # (|E_W|,)


def successor_index(codes: np.ndarray, width: int) -> np.ndarray:
    """The four double steps of each window of E_W as indices into `codes` (E_W is closed, so each lands in it)."""
    succ = successors_of(codes, width)  # (|E|, 4)
    idx = np.searchsorted(codes, succ)  # (|E|, 4)
    assert (codes[np.minimum(idx, len(codes) - 1)] == succ).all()  # image(E_W) is inside E_W
    return idx.astype(np.int32)


def is_closed_fixpoint(codes: np.ndarray, width: int) -> bool:
    """Whether the image of the set `codes` under the double step with every input is exactly the set."""
    img = np.unique(successors_of(codes, width))  # (|image|,)
    return bool(np.array_equal(img, np.unique(codes)))


@dataclass(frozen=True)
class Component:
    size: int
    period: int  # the gcd of the lengths of its cycles
    terminal: bool  # no double step leaves it
    locked: bool  # column 1 is a function of the cyclic class modulo the period
    gap: bool  # every window black in column 1, cut to 16 columns, is an entry window of the gap trap (`gap_entry`)
    ether: bool  # it holds the two windows of the aligned ether (`three_set_game.ether_cycle`)


def scc_labels(src: np.ndarray, dst: np.ndarray, m: int) -> tuple[int, np.ndarray]:
    """The strongly connected components of a directed graph on m nodes."""
    graph = sp.coo_matrix((np.ones(len(src), dtype=np.int8), (src, dst)), shape=(m, m)).tocsr()
    return connected_components(graph, directed=True, connection="strong")


def cycle_gcd(nodes: np.ndarray, src: np.ndarray, dst: np.ndarray) -> tuple[int, dict[int, int]]:
    """The gcd of the cycle lengths of a strongly connected set of nodes, from breadth-first levels: the gcd over its
    inner edges u -> v of level(u) + 1 - level(v); with the levels, whose residues modulo the gcd are the classes."""
    # nodes: (k,), src, dst: (e,) the inner edges
    level = {int(nodes[0]): 0}
    adj: dict[int, list[int]] = {}
    for a, b in zip(src.tolist(), dst.tolist()):
        adj.setdefault(a, []).append(b)
    frontier = [int(nodes[0])]
    while frontier:
        nxt = []
        for a in frontier:
            for b in adj.get(a, []):
                if b not in level:
                    level[b] = level[a] + 1
                    nxt.append(b)
        frontier = nxt
    g = 0
    for a, b in zip(src.tolist(), dst.tolist()):
        g = math.gcd(g, abs(level[a] + 1 - level[b]))
    return g, level


def window_components(codes: np.ndarray, succ_idx: np.ndarray, width: int) -> list[Component]:
    """The strongly connected components of the double-step graph on E_W that hold a cycle, largest first."""
    from computations.three_set_game import ether_cycle
    ether = [w for w, _ in ether_cycle(width)]
    entry = None
    if width >= 16:
        from computations.gate_census import gap_entry
        entry = gap_entry(16)  # (2^16,) black in column 1 and good with count 0
    m = len(codes)
    src = np.repeat(np.arange(m), 4)  # (4m,)
    dst = succ_idx.ravel()  # (4m,)
    _, lab = scc_labels(src, dst, m)
    inner = lab[src] == lab[dst]  # (4m,)
    sizes = np.bincount(lab)
    has_cycle = np.zeros(len(sizes), dtype=bool)
    has_cycle[lab[src[inner]]] = True
    leaves = np.zeros(len(sizes), dtype=bool)
    leaves[lab[src[~inner]]] = True
    out = []
    for c in np.flatnonzero(has_cycle):
        e = inner & (lab[src] == c)
        nodes = np.flatnonzero(lab == c)  # (k,)
        g, level = cycle_gcd(nodes, src[e], dst[e])
        cls = np.array([level[int(v)] % g for v in nodes])  # (k,)
        col1 = codes[nodes] & 1  # (k,)
        locked = all(len(np.unique(col1[cls == k])) == 1 for k in np.unique(cls))
        black = codes[nodes][col1 == 1]  # (black windows,)
        gap = entry is not None and len(black) > 0 and bool(entry[black & 0xFFFF].all())
        holds = bool(np.isin(ether, codes[nodes]).all())
        out.append(Component(int(sizes[c]), g, not leaves[c], locked, gap, holds))
    return sorted(out, key=lambda k: -k.size)


@dataclass(frozen=True)
class Automaton:
    states: int
    src: np.ndarray  # (e,) int32
    dst: np.ndarray  # (e,) int32
    bit: np.ndarray  # (e,) int8, the letter: column 1 after the double step
    complete: bool  # False when the construction stopped at the cap
    largest: int  # the largest subset
    table: np.ndarray  # (states, 2) the next state for the letters 0 and 1, -1 for the empty subset


def determinize(codes: np.ndarray, succ_idx: np.ndarray, cap: int = 2_000_000, progress: bool = False
                ) -> Automaton:
    """The subset construction from E_W. A subset waits in the queue as a sorted int32 index array; once expanded only
    its 16-byte digest stays, as the key of its state number."""
    bits = (codes & 1).astype(np.int8)  # (|E|,) column 1 of each window
    start = np.arange(len(codes), dtype=np.int32)  # (|E|,)
    ids = {hashlib.blake2b(start.tobytes(), digest_size=16).digest(): 0}
    queue = [start]
    head = 0
    src, dst, lab = [], [], []
    largest = len(start)
    bar = tqdm(desc="subsets", file=sys.stderr, disable=not progress, leave=False, mininterval=5)
    while head < len(queue) and len(ids) < cap:
        sub = queue[head]
        queue[head] = None  # type: ignore[call-overload]  # drop the expanded subset
        state = head
        head += 1
        nxt = succ_idx[sub].ravel()  # (4 |sub|,)
        nb = bits[nxt]  # (4 |sub|,)
        for b in (0, 1):
            t = np.unique(nxt[nb == b])  # (|T|,)
            if len(t) == 0:
                continue
            key = hashlib.blake2b(t.tobytes(), digest_size=16).digest()
            k = ids.get(key)
            if k is None:
                k = len(ids)
                ids[key] = k
                queue.append(t)
                largest = max(largest, len(t))
            src.append(state)
            dst.append(k)
            lab.append(b)
        bar.update(1)
    bar.close()
    m = len(ids)
    table = -np.ones((m, 2), dtype=np.int32)  # (m, 2)
    s, d, l = np.array(src, dtype=np.int32), np.array(dst, dtype=np.int32), np.array(lab, dtype=np.int8)
    table[s, l] = d
    return Automaton(m, s, d, l, head == len(queue), largest, table)


def spectral_radius(a: sp.csr_matrix) -> float:
    """The spectral radius of a nonnegative irreducible matrix: dense eigenvalues when small, else power iteration on
    a + I (aperiodic, with spectral radius one more), stopped when the ratio settles."""
    k = a.shape[0]
    if k <= 1500:
        return float(np.max(np.abs(np.linalg.eigvals(a.toarray())))) if a.nnz else 0.0
    b = (a + sp.identity(k, format="csr")).tocsr()
    v = np.ones(k) / k  # (k,)
    prev = 0.0
    for i in range(20000):
        w = b @ v  # (k,)
        r = float(w.sum())
        v = w / r
        if i > 50 and abs(r - prev) < 1e-12:
            break
        prev = r
    return r - 1.0


@dataclass(frozen=True)
class Growth:
    size: int
    growth: float  # per white step
    terminal: bool


def component_growths(aut: Automaton) -> list[Growth]:
    """The growth of each strongly connected component of the subset automaton that holds a cycle, largest first."""
    m = aut.states
    _, lab = scc_labels(aut.src, aut.dst, m)
    inner = lab[aut.src] == lab[aut.dst]  # (e,)
    leaves = np.zeros(lab.max() + 1, dtype=bool)
    leaves[lab[aut.src[~inner]]] = True
    out = []
    for c in np.unique(lab[aut.src[inner]]):
        nodes = np.flatnonzero(lab == c)  # (k,)
        local = np.full(m, -1)
        local[nodes] = np.arange(len(nodes))
        e = inner & (lab[aut.src] == c)
        a = sp.coo_matrix((np.ones(int(e.sum())), (local[aut.src[e]], local[aut.dst[e]])),
                          shape=(len(nodes), len(nodes))).tocsr()
        out.append(Growth(len(nodes), spectral_radius(a), not leaves[c]))
    return sorted(out, key=lambda g: -g.growth)


def word_counts(aut: Automaton, n: int) -> list[int]:
    """The number of words of each length 0..n that the automaton reads from its start, by paths."""
    count = np.zeros(aut.states, dtype=object)  # (states,)
    count[0] = 1
    out = [1]
    for _ in range(n):
        nxt = np.zeros(aut.states, dtype=object)  # (states,)
        for b in (0, 1):
            ok = aut.table[:, b] >= 0
            np.add.at(nxt, aut.table[ok, b], count[ok])
        count = nxt
        out.append(int(count.sum()))
    return out


def run_gate(aut: Automaton, gate: np.ndarray) -> np.ndarray:
    """For a batch of words (one per row), whether the automaton reads each from its start without the empty
    subset."""
    # gate: (h, n)
    state = np.zeros(gate.shape[0], dtype=np.int64)  # (h,)
    for j in range(gate.shape[1]):
        state = np.where(state >= 0, aut.table[np.maximum(state, 0), gate[:, j]], -1)
    return state >= 0  # (h,)


def driven_windows(halves: np.ndarray, phase: int, cells: int, steps: int, width: int) -> np.ndarray:
    """The windows of columns 1..width at the white steps 0, 1, ... of right halves of at most `cells` cells, driven by
    an alternating center (phase 0: black at the even steps, the kit's `altCol`; phase 1: black at the odd steps), on
    a strip wide enough that nothing beyond it reaches the window within `steps` steps."""
    # halves: (h,)
    span = width + steps + 1
    row = np.zeros((len(halves), span + 1), dtype=bool)  # (h, span + 1), column 0 at index 0
    for i in range(cells):
        row[:, i + 1] = (halves >> i) & 1
    weights = (1 << np.arange(width)).astype(np.int64)  # (width,)
    out = []
    for t in range(steps):
        center = (t + phase) % 2 == 0
        if not center:
            out.append(row[:, 1:width + 1].astype(np.int64) @ weights)  # (h,)
        row[:, 0] = center
        new = np.zeros_like(row)  # (h, span + 1)
        new[:, 1:-1] = row[:, :-2] ^ (row[:, 1:-1] | row[:, 2:])
        row = new
    return np.stack(out, axis=1)  # (h, white steps)


def kill_test(width: int, cells: int, steps: int, start: int, extra: list[int] | None = None,
              progress: bool = True) -> dict[str, int]:
    """Every right half below 2^cells (and the halves of `extra`), in both phases, for `steps` steps: the windows at
    the white steps from `start` on lie in E_W, and column 1 from `start` on is read by the subset automaton."""
    codes, chain = limit_set(width, progress)
    succ_idx = successor_index(codes, width)
    aut = determinize(codes, succ_idx, progress=progress)
    inside = np.zeros(1 << width, dtype=bool)  # (2^W,)
    inside[codes] = True
    halves = np.arange(1 << cells, dtype=np.int64)  # (2^cells,)
    out = {"chain": chain, "halves": 0, "window failures": 0, "word failures": 0}
    batch = 1 << 12
    jobs = [(phase, halves[lo:lo + batch], cells) for phase in (0, 1) for lo in range(0, len(halves), batch)]
    if extra:
        jobs += [(phase, np.array(extra, dtype=np.int64), max(extra).bit_length()) for phase in (0, 1)]
    for phase, part, c in tqdm(jobs, desc=f"kill test W={width}", file=sys.stderr, disable=not progress):
        wins = driven_windows(part, phase, c, steps, width)  # (h, white steps)
        late = wins[:, start:]  # (h, n)
        out["halves"] += len(part)
        out["window failures"] += int((~inside[late]).any(axis=1).sum())
        out["word failures"] += int((~run_gate(aut, (late & 1).astype(np.int64))).sum())
    return out


def ladder_row(width: int, cap: int, progress: bool = True) -> dict[str, object]:
    """One width of the ladder: the chain, the limit set, its window components, the subset automaton and the growths
    of its components."""
    started = time.perf_counter()
    codes, chain = limit_set(width, progress)
    succ_idx = successor_index(codes, width)
    comps = window_components(codes, succ_idx, width)
    aut = determinize(codes, succ_idx, cap, progress)
    growths = component_growths(aut) if aut.complete else []
    top = growths[0].growth if growths else float("nan")
    return {"W": width, "chain": chain, "E": len(codes), "window components": comps, "subsets": aut.states,
            "complete": aut.complete, "largest subset": aut.largest,
            "entropy": math.log2(top) if top > 0 else float("nan"),
            "positive": [g for g in growths if g.growth > 1 + 1e-9], "seconds": time.perf_counter() - started}


def lean_bitmaps(width: int) -> str:
    """The ranks of the windows in the image chain as bitmaps, as the Lean module
    `Rule30Open.PeriodTwo.ChannelLanguage` lists them: bit j of the rank of the window c is bit c of `rank<W>Bit<j>`."""
    rank, chain = image_chain(width)
    size = int((rank == chain).sum())
    lines = [f"/-! The ranks at `W = {width}`: the chain stops after {chain} images, with {size} windows in the limit "
             "set. -/"]
    for j in range(max(1, chain.bit_length())):
        m = int.from_bytes(np.packbits(((rank >> j) & 1).astype(np.uint8), bitorder="little").tobytes(), "little")
        lines += ["", f"/-- Bit {j} of the ranks at `W = {width}`. -/", f"def rank{width}Bit{j} : Nat :=", f"  0x{m:x}"]
    return "\n".join(lines)


def lean_rank(width: int, chain: int) -> str:
    """The Lean expression of the rank of the window `c` from the bitmaps."""
    terms = [f"(rank{width}Bit{j}.testBit c).toNat" for j in range(max(1, chain.bit_length()))]
    return " +\n  ".join(f"{1 << j} * {t}" if j else t for j, t in enumerate(terms))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("mode", choices=["ladder", "kill", "lean"])
    parser.add_argument("--widths", type=int, nargs="+", default=[8, 10, 12, 14])
    parser.add_argument("--width", type=int, default=14)
    parser.add_argument("--cells", type=int, default=14)
    parser.add_argument("--steps", type=int, default=1000)
    parser.add_argument("--start", type=int, default=20)
    parser.add_argument("--cap", type=int, default=2_000_000)
    args = parser.parse_args()
    started = time.perf_counter()
    if args.mode == "ladder":
        for w in args.widths:
            r = ladder_row(w, args.cap)
            comps = r["window components"]
            print(f"W={w}: chain {r['chain']}, |E| = {r['E']:,}, subset states {r['subsets']:,}"
                  f"{'' if r['complete'] else ' (stopped at the cap)'}, largest subset {r['largest subset']:,}, "
                  f"entropy {r['entropy']:.4f} per white step ({r['seconds']:.0f} s)", flush=True)
            print("  window components (size, gcd, terminal, column 1 locked, inside the gap trap, holds the ether):",
                  [(c.size, c.period, c.terminal, c.locked, c.gap, c.ether) for c in comps])
            print("  positive components of the subset automaton (size, growth, terminal):",
                  [(g.size, round(g.growth, 4), g.terminal) for g in r["positive"]], flush=True)
    elif args.mode == "kill":
        rng = np.random.default_rng(3)
        extra = [0] + [int(x) for x in rng.integers(1, 1 << 20, size=199)]  # the halves of gap_inverse_runs check
        print(kill_test(args.width, args.cells, args.steps, args.start, extra))
    else:
        print(lean_bitmaps(args.width))
    print(f"({time.perf_counter() - started:.0f} s)")


if __name__ == "__main__":
    main()
