"""The top of a defect on the ether: a certified census, the closed strips, and the window potential.

Write H(U) = (U >> 1) xor (U or (U << 1)) for the held map and B_t for the ether, the cycle of four states on seven
cells of the ring map, laid on the cells j >= 0 with an alignment (phase, offset): B_t(j) is bit (j + offset) mod 7 of
ether state (phase + t) mod 4. A rational 2-adic U whose tail is the ether from cell p on has the defect
D_t = H^t(U) xor B_t, zero above its top (item 5 of the shift model). D evolves on its own:

    D_{t+1}(j) = D_t(j + 1) xor ((x_t(j) or x_t(j - 1)) xor (B_t(j) or B_t(j - 1))),   x_t = D_t xor B_t, x_t(-1) = 0,

so the pair (D_t, t mod 4) is the state of a deterministic system, and a repeat of it certifies that the orbit of U, and
so its itinerary, is eventually periodic. Since D_0 is any word below 2^p as the head ranges over the words of p cells,
`census` follows every head of `head_bits` cells, 2^head_bits words in parallel as pairs of 64-bit words (128 cells),
for one alignment, until each one is settled: its defect lies in a closed strip (below), which bounds its top forever,
or its state repeats. It reports the highest top, the settling step and the way.

`closed_strips(width)` is the greatest set of strips D(c - width + 1 .. c), at a fixed cell c with the defect zero
above c, that one step maps into itself for both values of the cell D(c - width) below, and that never raise the top
above c. A defect that enters it keeps its top at or below c forever, whatever lies below. Computed directly on H, it
is empty for widths 1 to 12 and has 1,915 strips at width 13, all at one residue of c; this is the mirror of
`background_halves.wall_set` beside the ether.

`front_graph(window)` is the automaton of `held_shift.front_rate` as an explicit graph, and `max_mean_gain` its
largest mean gain per step over its cycles, by Karp's algorithm, together with one cycle that attains it. A potential
phi on the window states with gain + phi(after) - phi(before) <= 0 on every edge exists exactly when that number is at
most zero, so `max_mean_gain` decides exactly whether a potential on the window states bounds the top.
`realized_edges` collects the edges that actual defects take, and the same question is asked of that subgraph.

`local_entry` and `local_tree` ask whether the top cells of a head alone force entry into a closed strip: the cells at
or above t at step t read only the cells at or above 0 at step 0, so a word of n cells with anything below it is
followed exactly in a region that shrinks by one cell per step, and a word whose defect enters a closed strip inside
that region settles every head that ends in it. Words not settled are extended by one cell below.

    python -m computations.defect_potential census --bits 12          # every head of 12 cells, all 28 alignments
    python -m computations.defect_potential closed --width 14         # the closed strips of widths 1 to 14
    python -m computations.defect_potential karp --window 8           # the best potential on the window automaton
    python -m computations.defect_potential realized --window 8 --length 40 --steps 1500 --count 300   # edges used
    python -m computations.defect_potential tree --bits 4 --length 18    # top words that settle whatever lies below
    python -m computations.defect_potential random --length 400 --count 200 --steps 3000   # long random heads
"""

from __future__ import annotations

import argparse
import functools
import sys

import numpy as np
from tqdm.auto import tqdm

from computations.held_shift import held, ring_cycle

ETHER: list[int] = ring_cycle(0b1000000, 7)[1]  # the four ring states of the ether, bit j the ring cell j
STRIP = 13  # the narrowest width with a closed strip
MASK64 = (1 << 64) - 1
U64 = np.uint64


def ether_cell(phase: int, j: int) -> int:
    """Cell j of ether state `phase` (both taken modulo the cycle)."""
    return (ETHER[phase % 4] >> (j % 7)) & 1


def background(phase: int, offset: int, low: int, cells: int) -> int:
    """The background cells low .. low + cells - 1 at ether phase `phase` and alignment `offset`, as an integer whose
    bit i is cell low + i."""
    return _background(phase % 4, (low + offset) % 7, cells)


@functools.lru_cache(maxsize=None)
def _background(phase: int, shift: int, cells: int) -> int:
    """`background` for a phase below 4 and low + offset below 7, which is all it depends on, computed once."""
    return sum(ether_cell(phase, shift + i) << i for i in range(cells))


def defect_step(D: int, phase: int, offset: int, width: int) -> int:
    """One step of the defect D (bit j the cell j, zero from cell `width` - 1 on) at ether phase `phase`, by one step of
    the held map on the actual cells. Exact when the top of D is at most width - 2."""
    x = D ^ background(phase, offset, 0, width + 1)
    return (held(x) & ((1 << width) - 1)) ^ background(phase + 1, offset, 0, width)


def top(D: int) -> int:
    """The highest cell of the defect, -1 when there is none."""
    return D.bit_length() - 1


def bit_length64(x: np.ndarray) -> np.ndarray:
    """The bit length of each 64-bit word, exactly, through two 32-bit halves converted to floats."""
    high = (x >> U64(32)).astype(np.float64)  # (n,)
    low = (x & U64(0xFFFFFFFF)).astype(np.float64)  # (n,)
    _, eh = np.frexp(high)  # (n,), the bit length of the high half
    _, el = np.frexp(low)  # (n,)
    return np.where(high > 0, 32 + eh, el).astype(np.int64)  # (n,)


def tops128(lo: np.ndarray, hi: np.ndarray) -> np.ndarray:
    """The top of each defect held as two words, cells 0..63 in `lo` and 64..127 in `hi`; -1 when it is zero."""
    return np.where(hi != 0, 64 + bit_length64(hi), bit_length64(lo)) - 1  # (n,)


def words128(value: int) -> tuple[np.uint64, np.uint64]:
    """An integer of at most 128 bits as two 64-bit words."""
    return U64(value & MASK64), U64((value >> 64) & MASK64)


def step128(lo: np.ndarray, hi: np.ndarray, phase: int, offset: int) -> tuple[np.ndarray, np.ndarray]:
    """One step of every defect held as two words, at ether phase `phase`: exact for a defect whose top is at most 126."""
    b_lo, b_hi = words128(background(phase, offset, 0, 128))
    n_lo, n_hi = words128(background(phase + 1, offset, 0, 128))
    beyond = U64(ether_cell(phase, 128 + offset))
    x_lo, x_hi = lo ^ b_lo, hi ^ b_hi  # (n,), (n,) the actual cells
    up_lo = (x_lo >> U64(1)) | (x_hi << U64(63))  # (n,) cell j + 1 at bit j
    up_hi = (x_hi >> U64(1)) | (beyond << U64(63))  # (n,)
    down_lo = x_lo << U64(1)  # (n,) cell j - 1 at bit j; cell -1 is the held 0
    down_hi = (x_hi << U64(1)) | (x_lo >> U64(63))  # (n,)
    return (up_lo ^ (x_lo | down_lo)) ^ n_lo, (up_hi ^ (x_hi | down_hi)) ^ n_hi


@functools.lru_cache(maxsize=None)
def closed_strips(width: int) -> np.ndarray:
    """The greatest set of strips D(c - width + 1 .. c), bit i the cell c - width + 1 + i, with D zero above c, that one
    step maps into the set at the next phase for both values of D(c - width) and that never makes cell c + 1 a defect.
    Indexed by (ether phase, (c + offset) mod 7, strip): (4, 7, 2^width). Kept for the widths asked again, so the
    array is read-only."""
    alive = greatest_strips(width)  # (4, 7, 2^w)
    alive.flags.writeable = False
    return alive


def greatest_strips(width: int) -> np.ndarray:
    """`closed_strips`, computed."""
    n = 1 << width
    m = np.arange(n, dtype=np.int64)  # (2^w,) the strips
    alive = np.ones((4, 7, n), dtype=bool)  # (4, 7, 2^w)
    after = np.zeros((4, 7, 2, n), dtype=np.int64)  # (4, 7, 2, 2^w)
    for a in range(4):
        for r in range(7):
            low = r + 7 * (width // 7 + 2) - width + 1  # a cell c = low + width - 1 with c = r mod 7, c - width >= 0
            cell = lambda k: ether_cell(a, k)
            if cell(low + width) == 0:  # the top rises above c exactly when D(c) = 1 under a background 0
                alive[a, r] &= ((m >> (width - 1)) & 1) == 0
            for below in (0, 1):
                d = lambda k: (m >> (k - low)) & 1 if low <= k < low + width else (below if k == low - 1 else 0)
                new = np.zeros(n, dtype=np.int64)  # (2^w,)
                for k in range(low, low + width):
                    xk, xb = cell(k) ^ d(k), cell(k - 1) ^ d(k - 1)
                    new |= (d(k + 1) ^ ((xk | xb) ^ (cell(k) | cell(k - 1)))) << (k - low)
                after[a, r, below] = new
    while True:
        kept = alive.copy()  # (4, 7, 2^w)
        for a in range(4):
            for r in range(7):
                for below in (0, 1):
                    kept[a, r] &= alive[(a + 1) % 4, r][after[a, r, below]]
        if np.array_equal(kept, alive):
            return alive
        alive = kept


def strip_at(lo: np.ndarray, hi: np.ndarray, low: np.ndarray, width: int) -> np.ndarray:
    """The `width` cells low .. low + width - 1 of each defect held as two words, for low in 0 .. 127 - width. The
    shifts are clamped with `np.minimum` and `np.maximum`, which on these short arrays take a fraction of the time of
    `np.clip`."""
    s_lo = np.minimum(np.maximum(low, 0), 63).astype(np.uint64)  # (n,) every shift below 64, where numpy is defined
    s_spill = (64 - np.minimum(np.maximum(low, 1), 63)).astype(np.uint64)  # (n,)
    s_hi = np.minimum(np.maximum(low - 64, 0), 63).astype(np.uint64)  # (n,)
    in_lo = (lo >> s_lo) | np.where(low > 0, hi << s_spill, U64(0))  # (n,) for low < 64
    word = np.where(low < 64, in_lo, hi >> s_hi)  # (n,)
    return (word & U64((1 << width) - 1)).astype(np.int64)  # (n,)


def closed_cell(lo: np.ndarray, hi: np.ndarray, phase: int, offset: int, closed: np.ndarray) -> np.ndarray:
    """For each defect, the least cell c >= max(top, STRIP - 1) with the strip D(c - STRIP + 1 .. c) closed, or -1.
    A defect with such a c keeps its top at or below c from then on."""
    t = tops128(lo, hi)  # (n,)
    found = np.full(len(lo), -1, dtype=np.int64)  # (n,)
    for r in range(7):
        if not closed[phase % 4, r].any():
            continue
        base = np.maximum(t, STRIP - 1)  # (n,)
        c = base + ((r - base - offset) % 7)  # (n,) the least such c with (c + offset) mod 7 = r
        for extra in range(0, STRIP + 7, 7):
            cc = c + extra  # (n,)
            ok = (cc <= 126) & closed[phase % 4, r][strip_at(lo, hi, np.minimum(cc, 126) - STRIP + 1, STRIP)]
            found = np.where(ok & ((found < 0) | (cc < found)), cc, found)
    return found


def census(head_bits: int, phase: int, offset: int, max_steps: int, closed: np.ndarray,
           heads: np.ndarray | None = None) -> dict[str, np.ndarray]:
    """Follow every defect D_0 < 2^head_bits (or the given `heads`, as 64-bit words) on the ether at the alignment
    (phase, offset) until it is settled, in one of two ways, each a proof that its top is bounded and its orbit
    eventually periodic:

    - it enters a closed strip at a cell c (`closed_cell`): its top stays at or below c forever;
    - its state repeats: snapshots at the steps 4 2^k are compared with every later step that is a multiple of 4.

    Returns per head: `top`, the highest top up to the settling step; `bound`, a bound on the top of the whole orbit
    (the larger of `top` and c, or `top` for a repeat); `settled`, that step or -1; `period`, the period of a repeat or
    0; `cell`, the cell c of a closed strip or -1; and `overflow`, a head whose top passed 120, for which nothing is
    claimed."""
    if heads is None:
        heads = np.arange(1 << head_bits, dtype=np.uint64)  # (n,)
    n = len(heads)
    lo, hi = heads.astype(np.uint64), np.zeros(n, dtype=np.uint64)  # (n,), (n,) the defects still followed
    index = np.arange(n)  # (k,) which head each followed defect is
    best = tops128(lo, hi)  # (k,)
    out = {"top": np.zeros(n, dtype=np.int64), "bound": np.zeros(n, dtype=np.int64),
           "settled": np.full(n, -1, dtype=np.int64), "period": np.zeros(n, dtype=np.int64),
           "cell": np.full(n, -1, dtype=np.int64), "overflow": np.zeros(n, dtype=bool)}
    snap_lo, snap_hi, snap_t, next_snap = lo.copy(), hi.copy(), 0, 4
    for t in range(0, max_steps + 1):
        if t > 0:
            lo, hi = step128(lo, hi, phase + t - 1, offset)
            best = np.maximum(best, tops128(lo, hi))
        cell = closed_cell(lo, hi, phase + t, offset, closed)  # (k,)
        repeat = (t % 4 == 0) & (t > snap_t) & (lo == snap_lo) & (hi == snap_hi)  # (k,)
        over = best > 120  # (k,)
        done = (cell >= 0) | repeat | over  # (k,)
        if done.any():
            ids = index[done]
            out["top"][ids] = best[done]
            out["bound"][ids] = np.maximum(best[done], cell[done])
            out["settled"][ids] = np.where(over[done], -1, t)
            out["period"][ids] = np.where(repeat[done] & (cell[done] < 0), t - snap_t, 0)
            out["cell"][ids] = cell[done]
            out["overflow"][ids] = over[done]
            keep = ~done
            lo, hi, index, best = lo[keep], hi[keep], index[keep], best[keep]
            snap_lo, snap_hi = snap_lo[keep], snap_hi[keep]
        if len(index) == 0:
            break
        if t == next_snap:
            snap_lo, snap_hi, snap_t = lo.copy(), hi.copy(), t
            next_snap *= 2
    out["top"][index] = best
    out["bound"][index] = -1
    return out


def local_entry(words: np.ndarray, phase: int, offset: int, closed: np.ndarray) -> np.ndarray:
    """For defects whose cells 0 .. n - 1 are given by `words` and whose cells below 0 are unknown (any head, of any
    length, with the wall anywhere below), whether the defect provably enters a closed strip: cell j at step t reads
    only the cells at or above j - t at step 0, so the cells at or above t are exact at step t, and a closed strip at a
    cell c with c - STRIP + 1 >= t keeps the top at or below c whatever lies below. The run stops for a word once its
    top plus 7 falls below t, when no closed strip can lie in the exact cells any more. Returns the step of entry, or -1
    for a word that this does not settle. Words are 64-bit (n <= 64)."""
    lo, hi = words.astype(np.uint64), np.zeros(len(words), dtype=np.uint64)  # (k,), (k,)
    index = np.arange(len(words))  # (k,)
    out = np.full(len(words), -1, dtype=np.int64)  # (n,)
    t = 0
    while len(index):
        if t:
            lo, hi = step128(lo, hi, phase + t - 1, offset)
        cell = closed_cell(lo, hi, phase + t, offset, closed)  # (k,)
        hit = (cell >= 0) & (cell - STRIP + 1 >= t)  # (k,)
        out[index[hit]] = t
        tops = tops128(lo, hi)  # (k,)
        assert (tops <= 120).all(), "a word overflowed the 128 cells"
        keep = ~hit & (tops + 7 >= t)  # (k,)
        lo, hi, index = lo[keep], hi[keep], index[keep]
        t += 1
    return out


def local_tree(first: int, depth: int, closed: np.ndarray) -> list[tuple[int, int, int]]:
    """The tree of `local_entry`: start from every word of `first` cells whose top cell is a defect (a head whose top
    cells agree with the ether is a shorter head), at all 28 alignments, and extend each word that is not settled by
    one unknown cell below, up to `depth` cells. Returns per word length (length, words tried, words not settled).
    A level with no word left would settle every head of at least that many cells, whatever lies below."""
    rows = []
    level: list[tuple[int, int, np.ndarray]] = []
    for phase in range(4):
        for offset in range(7):
            level.append((phase, offset, np.arange(1 << (first - 1), 1 << first, dtype=np.uint64)))  # (2^(first-1),)
    for n in range(first, depth + 1):
        tried = sum(len(w) for _, _, w in level)
        nxt = []
        for phase, offset, words in level:
            if len(words) == 0:
                continue
            left = words[local_entry(words, phase, offset, closed) < 0]  # (k,)
            if n < depth and len(left):
                grown = np.concatenate([left << U64(1), (left << U64(1)) | U64(1)])  # (2k,) one more cell below
                nxt.append((phase, (offset - 1) % 7, grown))
            else:
                nxt.append((phase, (offset - 1) % 7, left))
        rows.append((n, tried, sum(len(w) for _, _, w in nxt) // (2 if n < depth else 1)))
        print(f"length {n}: {rows[-1][1]} words, {rows[-1][2]} not settled", file=sys.stderr, flush=True)
        level = nxt
    return rows


def front_graph(window: int) -> tuple[np.ndarray, np.ndarray, np.ndarray, int]:
    """The automaton of `held_shift.front_rate` on the ether: nodes (phase, top mod 7, the `window` - 1 cells below the
    top), and one node per phase for a top lost below the window, from which any node follows. Returns the sources,
    targets and gains of the edges and the number of nodes."""
    cycle, length = ETHER, 7
    period, cells = 4, 1 << (window - 1)
    lost = period * length * cells
    bg = lambda a, j: (cycle[a % period] >> (j % length)) & 1
    node = lambda a, b, m: (a * length + b) * cells + m
    src: list[int] = []
    dst: list[int] = []
    gain: list[int] = []
    for a in range(period):
        for b in range(length):
            for m in range(cells):
                x = {k: bg(a, b - k) for k in (-2, -1)}
                x[0] = 1 - bg(a, b)
                x.update({k: bg(a, b - k) ^ ((m >> (k - 1)) & 1) for k in range(1, window)})
                d = {k: x[k - 1] ^ (x[k] | x[k + 1]) ^ bg(a + 1, b - k) for k in range(-1, window - 1)}
                here = node(a, b, m)
                if d[-1]:
                    below = sum(d[i] << i for i in range(window - 1))
                    src.append(here); dst.append(node((a + 1) % period, (b + 1) % length, below)); gain.append(1)
                    continue
                for k in range(window - 1):
                    if d[k]:
                        known = window - 2 - k
                        base = sum(d[k + 1 + i] << i for i in range(known))
                        for free in range(1 << (window - 1 - known)):
                            src.append(here); dst.append(node((a + 1) % period, (b - k) % length, base | free << known))
                            gain.append(-k)
                        break
                else:
                    src.append(here); dst.append(lost + (a + 1) % period); gain.append(-(window - 1))
    for a in range(period):
        for b in range(length):
            for m in range(cells):
                src.append(lost + a); dst.append(node(a, b, m)); gain.append(0)
    return np.array(src), np.array(dst), np.array(gain), lost + period


def max_mean_gain(src: np.ndarray, dst: np.ndarray, gain: np.ndarray, nodes: int) -> tuple[float, list[int]]:
    """Karp's maximum mean cycle of the graph, exactly as a float of a ratio of integers, and the nodes of one cycle
    attaining it, found by following the predecessors of the best final node. -inf and [] for a graph without cycles."""
    n = nodes
    neg = np.iinfo(np.int64).min // 4
    value = np.full((n + 1, n), neg, dtype=np.int64)  # (n + 1, n) best gain of a walk of k edges ending at v
    parent = np.full((n + 1, n), -1, dtype=np.int64)  # (n + 1, n)
    value[0] = 0
    order = np.argsort(src, kind="stable")
    for k in tqdm(range(1, n + 1), desc="Karp", file=sys.stderr, leave=False, disable=n < 5000):
        cand = value[k - 1][src] + gain  # (edges,)
        cand[value[k - 1][src] == neg] = neg
        best = np.full(n, neg, dtype=np.int64)  # (n,)
        np.maximum.at(best, dst, cand)
        value[k] = best
        hit = (cand == best[dst]) & (cand > neg)  # (edges,)
        parent[k][dst[hit]] = src[hit]
    del order
    final = value[n]  # (n,)
    ok = final > neg
    if not ok.any():
        return float("-inf"), []
    ratios = np.full(n, np.inf)  # (n,)
    for v in np.flatnonzero(ok):
        ks = np.flatnonzero(value[:n, v] > neg)
        ratios[v] = np.min((final[v] - value[ks, v]) / (n - ks))
    v = int(np.argmax(np.where(ok, ratios, -np.inf)))
    walk = [v]
    for k in range(n, 0, -1):
        walk.append(int(parent[k][walk[-1]]))
    walk.reverse()
    seen: dict[int, int] = {}
    cycle: list[int] = []
    for i, u in enumerate(walk):
        if u in seen:
            cycle = walk[seen[u]:i]
            break
        seen[u] = i
    return float(ratios[v]), cycle


def realized_edges(window: int, head_bits: int, steps: int, rng: np.random.Generator, count: int) -> set[tuple[int, int]]:
    """The (source, target) pairs of `front_graph(window)` that defects actually take: `count` random heads of
    `head_bits` cells at random alignments, stepped `steps` times with Python integers. A top within window - 1 of cell 0
    reads the held 0 below it, which the window automaton treats as free, so those steps are skipped. A fall of
    `window` - 1 cells or more is recorded as the two edges through the node for a lost top."""
    cells = 1 << (window - 1)
    used: set[tuple[int, int]] = set()

    def node(D: int, phase: int, offset: int) -> int:
        T = top(D)
        m = (D >> (T - window + 1)) & (cells - 1) if T >= window - 1 else -1
        rev = sum(((m >> (window - 2 - i)) & 1) << i for i in range(window - 1))  # bit k - 1 the cell k below the top
        return ((phase % 4) * 7 + (T + offset) % 7) * cells + rev

    for _ in range(count):
        phase, offset = int(rng.integers(4)), int(rng.integers(7))
        D = int(rng.integers(1 << 62)) & ((1 << head_bits) - 1) | (1 << (head_bits - 1))
        width = head_bits + 140
        for t in range(steps):
            E = defect_step(D, phase + t, offset, width)
            if top(D) >= 2 * window and top(E) >= 2 * window:
                here, there = node(D, phase + t, offset), node(E, phase + t + 1, offset)
                if top(E) >= top(D) - (window - 2):
                    used.add((here, there))
                else:  # a top lost below the window passes through the node of its phase
                    lost = 4 * 7 * cells + (phase + t + 1) % 4
                    used |= {(here, lost), (lost, there)}
            D = E
            assert top(D) < width - 2
    return used


def closed_cell_int(D: int, phase: int, offset: int, closed: np.ndarray) -> int:
    """`closed_cell` for one defect held as a Python integer of any width: the least cell c >= max(top, STRIP - 1)
    with the strip D(c - STRIP + 1 .. c) closed, or -1."""
    base = max(top(D), STRIP - 1)
    for c in range(base, base + STRIP + 7):
        r = (c + offset) % 7
        if closed[phase % 4, r, (D >> (c - STRIP + 1)) & ((1 << STRIP) - 1)]:
            return c
    return -1


def random_heads(length: int, count: int, steps: int, seed: int,
                 closed: np.ndarray) -> list[tuple[int, int, int, int]]:
    """For `count` random heads of `length` cells at random alignments, followed by Python integers until the defect
    enters a closed strip or for `steps` steps: (highest top minus `length`, the step of entry or -1, the cell of the
    strip minus `length` or 0, the top at the end minus `length`)."""
    rng = np.random.default_rng(seed)
    out = []
    for _ in tqdm(range(count), desc=f"heads of {length}", file=sys.stderr, leave=False):
        phase, offset = int(rng.integers(4)), int(rng.integers(7))
        D = int.from_bytes(rng.bytes(length // 8 + 1), "little") & ((1 << length) - 1)
        width = length + steps + 4
        best, entry, cell = top(D), -1, 0
        for t in range(steps + 1):
            if t:
                D = defect_step(D, phase + t - 1, offset, width)
                best = max(best, top(D))
            c = closed_cell_int(D, phase + t, offset, closed)
            if c >= 0:
                entry, cell = t, c - length
                break
        out.append((best - length, entry, cell, top(D) - length))
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("mode", choices=["census", "closed", "karp", "random", "realized", "tree"])
    parser.add_argument("--bits", type=int, default=10)
    parser.add_argument("--steps", type=int, default=4096)
    parser.add_argument("--width", type=int, default=14)
    parser.add_argument("--window", type=int, default=8)
    parser.add_argument("--length", type=int, default=200)
    parser.add_argument("--count", type=int, default=100)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    if args.mode == "closed":
        for w in range(1, args.width + 1):
            c = closed_strips(w)
            print(f"width {w}: {int(c.sum())} closed strips, by phase {[int(c[a].sum()) for a in range(4)]}, "
                  f"by residue {[int(c[:, r].sum()) for r in range(7)]}")
    elif args.mode == "census":
        closed = closed_strips(STRIP)
        tot = {"heads": 0, "settled": 0, "strip": 0, "repeat": 0, "overflow": 0, "top": -1, "bound": -1,
               "last": -1, "repeat_top": -1}
        periods: set[int] = set()
        rises: list[np.ndarray] = []
        steps: list[np.ndarray] = []
        for phase in range(4):
            for offset in tqdm(range(7), desc=f"phase {phase}", file=sys.stderr, leave=False):
                r = census(args.bits, phase, offset, args.steps, closed)
                ok = r["settled"] >= 0
                strip, repeat = ok & (r["cell"] >= 0), ok & (r["cell"] < 0)
                tot["heads"] += len(ok); tot["settled"] += int(ok.sum()); tot["strip"] += int(strip.sum())
                tot["repeat"] += int(repeat.sum()); tot["overflow"] += int(r["overflow"].sum())
                tot["top"] = max(tot["top"], int(r["top"].max()))
                tot["bound"] = max(tot["bound"], int(r["bound"][ok].max()) if ok.any() else -1)
                tot["last"] = max(tot["last"], int(r["settled"].max()))
                if repeat.any():
                    tot["repeat_top"] = max(tot["repeat_top"], int(r["top"][repeat].max()))
                periods |= set(r["period"][repeat].tolist())
                rises.append(r["top"] - args.bits)
                steps.append(r["settled"])
                print(f"phase {phase} offset {offset}: settled {int(ok.sum())} of {len(ok)} (closed strip "
                      f"{int(strip.sum())}, repeat {int(repeat.sum())}), highest top {int(r['top'].max())}, bound "
                      f"{int(r['bound'][ok].max()) if ok.any() else -1}, last settled at step {int(r['settled'].max())}",
                      flush=True)
        print(f"heads of {args.bits} cells, all 28 alignments: settled {tot['settled']} of {tot['heads']} "
              f"({tot['strip']} by a closed strip, {tot['repeat']} by a repeat, overflow {tot['overflow']}); highest "
              f"top {tot['top']} = head + {tot['top'] - args.bits}; bound on every settled orbit {tot['bound']}; last "
              f"settled at step {tot['last']}; highest top of a head settled by a repeat {tot['repeat_top']}; "
              f"periods of the repeats {sorted(periods)}")
        rise, when = np.concatenate(rises), np.concatenate(steps)  # (28 2^bits,), (28 2^bits,)
        print("share of heads not settled after step: " + ", ".join(
            f"{s} {float((when > s).mean()):.2g}" for s in (50, 100, 150, 200, 250, 300, 400)))
        print("share of heads whose top rises more than x above the head: " + ", ".join(
            f"{x} {float((rise > x).mean()):.2g}" for x in (0, 10, 20, 30, 40, 50, 60)))
        k = int(np.argmax(rise))
        print(f"a head with the highest rise, {int(rise[k])}, settles at step {int(when[k])}")
    elif args.mode == "tree":
        for n, tried, left in local_tree(args.bits, args.length, closed_strips(STRIP)):
            print(f"word length {n}: {tried} words at the 28 alignments, {left} not settled whatever lies below")
    elif args.mode == "karp":
        src, dst, gain, nodes = front_graph(args.window)
        rate, cycle = max_mean_gain(src, dst, gain, nodes)
        edge = {(int(a), int(b)): int(g) for a, b, g in zip(src, dst, gain)}
        total = sum(edge[(cycle[i], cycle[(i + 1) % len(cycle)])] for i in range(len(cycle)))
        assert abs(total / len(cycle) - rate) < 1e-12, "the cycle does not attain the mean"
        print(f"window {args.window}: {nodes} nodes, {len(src)} edges, largest mean gain per step {rate:.6f}, "
              f"= {total}/{len(cycle)}, attained on a cycle of {len(cycle)} steps, checked edge by edge")
    elif args.mode == "realized":
        src, dst, gain, nodes = front_graph(args.window)
        used = realized_edges(args.window, args.length, args.steps, np.random.default_rng(args.seed), args.count)
        keep = np.array([(int(s), int(d)) in used for s, d in zip(src, dst)])  # (edges,)
        rate, cycle = max_mean_gain(src[keep], dst[keep], gain[keep], nodes)
        print(f"window {args.window}: {int(keep.sum())} of {len(src)} edges realized; largest mean gain per step "
              f"on them {rate:.6f} over a cycle of {len(cycle)} steps")
    else:
        out = random_heads(args.length, args.count, args.steps, args.seed, closed_strips(STRIP))
        best = np.array([o[0] for o in out])  # (count,)
        entry = np.array([o[1] for o in out])  # (count,)
        entered = entry >= 0
        print(f"heads of {args.length} cells, {args.count} heads, up to {args.steps} steps: entered a closed strip "
              f"{int(entered.sum())}, at step median {int(np.median(entry[entered])) if entered.any() else -1}, max "
              f"{int(entry.max())}; highest top minus length max {int(best.max())}, median {int(np.median(best))}; "
              f"strip cell minus length max {max(o[2] for o in out)}")


if __name__ == "__main__":
    main()
