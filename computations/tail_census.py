"""Every periodic tail of small spatial period under the held map, and the defect census on each background it reaches.

Write H(U) = (U >> 1) xor (U or (U << 1)) for the held map and K for the 2-adic U with H^t(U) odd at every odd t.
Conjecture (R) says that every rational point of K has an eventually periodic itinerary. A rational U has a head of p
cells and then a tail repeating a word of q cells; far from cell 0 the tail evolves as the ring map of q cells, which
falls onto a cycle (`ring_backgrounds`). A cycle of P states on a ring whose least spatial period is L is a background
B_t(j) = bit (j + o) mod L of state (a + t) mod P, at one of the P L alignments (a, o). The defect
D_t = H^t(U) xor B_t follows

    D_{t+1}(j) = D_t(j + 1) xor ((x_t(j) or x_t(j - 1)) xor (B_t(j) or B_t(j - 1))),   x_t = D_t xor B_t, x_t(-1) = 0,

so (D_t, t mod P) is the state of a deterministic system, and as in `defect_potential` (written for the ether) a
bounded top is the same as an eventually periodic orbit (item 5 of the shift model).

- `ring_backgrounds(max_q)`: every cycle of the ring map reached by a tail word of q <= max_q cells, up to rotation,
  with its spatial period L, its temporal period P, its least period up to a rotation (a traveling pattern has one
  below P) and the number of tail words and the longest transient that reach it.
- `alignments(bg)`: the P L alignments, one per distinct space-time pattern.
- `closed_strips(bg, width)`: the greatest set of strips D(c - width + 1 .. c), with D zero above c, that one step maps
  into the set for both values of D(c - width) and that never make cell c + 1 a defect, indexed by
  (phase, (c + o) mod L, strip). A defect inside one keeps its top at or below c forever, whatever lies below. For the
  ether this is `defect_potential.closed_strips`.
- `rising_sets(bg, width)`: the opposite, the windows of `width` cells below the highest top so far that keep the top
  inside the window and raise the highest top at least once in every few steps, for both values of the cell below. A
  defect whose window enters one has a top that grows without bound, so its orbit is not eventually periodic.
- `census(bg, a, o, heads, ...)`: every head followed as words of 64 cells in numpy, until it is settled (it enters a
  closed strip, or its state repeats), its window enters a growing set, its top passes the cells followed (a growing
  top) or the horizon ends. With
  `in_k`, the condition of K is checked at every odd step and a head is dropped when it breaks K; a head that enters
  a closed strip is then followed on until it breaks K or repeats, so the run also finds the periodic points of K on
  the background (a repeat with K held at every step, with a period that is a multiple of lcm(P, 2)).
- `front_speed(bg, a, o, head, steps)`: the top of one head stepped with Python integers, for the slope of a front,
  and `front_pattern` the gain per period of the top once it is periodic.
- `k_survival(bg, bits, steps)`: how many heads are still in K after each step.

    python -m computations.tail_census rings --max-q 14                 # the backgrounds of tails of up to 14 cells
    python -m computations.tail_census sets --max-q 12                 # closed strips and growing windows on each
    python -m computations.tail_census census --max-q 12 --bits 12     # the census on each, without and with K
    python -m computations.tail_census fronts --max-q 12 --steps 6000  # the speed of the growing tops
    python -m computations.tail_census survival --max-q 12 --bits 16 --steps 64   # heads still in K, step by step
"""

from __future__ import annotations

import argparse
import math
import sys
from dataclasses import dataclass

import numpy as np
from tqdm.auto import tqdm

from computations.held_shift import held, ring_cycle

U64 = np.uint64
MASK64 = (1 << 64) - 1


@dataclass(frozen=True)
class Background:
    """A cycle of the ring map: `states[a]` the ring word of state a (bit j the cell j) on `length` cells, the least
    spatial period, so that B_t(j) at alignment (a, o) is bit (j + o) mod length of states[(a + t) mod P]."""

    states: tuple[int, ...]
    length: int

    @property
    def period(self) -> int:
        return len(self.states)

    def cell(self, phase: int, j: int) -> int:
        """Cell j of state `phase`, both read cyclically."""
        return (self.states[phase % self.period] >> (j % self.length)) & 1

    def word(self, phase: int, offset: int, low: int, cells: int) -> int:
        """The cells low .. low + cells - 1 at state `phase` and alignment `offset`, bit i the cell low + i."""
        out, filled = rotate(self.states[phase % self.period], self.length, low + offset), self.length
        while filled < cells:  # doubling: the periodic extension of the rotated state
            out |= out << filled
            filled *= 2
        return out & ((1 << cells) - 1)

    def name(self) -> str:
        """The least rotation over the cycle of a state, as a word of L letters, cell 0 first."""
        best = min(rotate(s, self.length, k) for s in self.states for k in range(self.length))
        return "".join(str((best >> i) & 1) for i in range(self.length))


def rotate(word: int, length: int, k: int) -> int:
    """The ring word read from cell k on: bit j of the result is cell (j + k) mod length."""
    k %= length
    full = (1 << length) - 1
    return ((word >> k) | (word << (length - k))) & full


def least_spatial_period(word: int, length: int) -> int:
    """The least d dividing `length` with the ring word invariant under a rotation by d."""
    return next(d for d in range(1, length + 1) if length % d == 0 and rotate(word, length, d) == word)


def shift_period(bg: Background) -> tuple[int, int]:
    """The least k >= 1 with state k a rotation of state 0, and the rotation s (state k read from cell s on is state 0,
    so the pattern travels s cells toward cell 0, modulo L, every k steps)."""
    for k in range(1, bg.period + 1):
        for s in range(bg.length):
            if rotate(bg.states[k % bg.period], bg.length, s) == bg.states[0]:
                return k, s
    raise AssertionError("state P is state 0")


@dataclass(frozen=True)
class Ring:
    """A background reached by the tails of up to max_q cells: its name (`Background.name`), the background, the
    shift period of `shift_period`, and per q the number of words of q cells that reach it and their longest
    transient."""

    name: str
    bg: Background
    shift: tuple[int, int]
    words: dict[int, int]
    transient: dict[int, int]


def ring_backgrounds(max_q: int) -> list[Ring]:
    """Every cycle of the ring map reached by a word of q <= max_q cells, up to rotation, sorted by spatial period L,
    temporal period P and name."""
    found: dict[str, Ring] = {}
    for q in tqdm(range(1, max_q + 1), desc="ring sizes", file=sys.stderr, leave=False):
        name_of: dict[int, str] = {}  # a state on a cycle -> the name of its background
        for w in range(1 << q):
            transient, cycle = ring_cycle(w, q)
            if cycle[0] not in name_of:
                length = least_spatial_period(cycle[0], q)
                name = Background(tuple(c & ((1 << length) - 1) for c in cycle), length).name()
                for c in cycle:
                    name_of[c] = name
                if name not in found:
                    _, states = ring_cycle(int(name[::-1], 2), length)
                    bg = Background(tuple(states), length)
                    found[name] = Ring(name, bg, shift_period(bg), {}, {})
            ring = found[name_of[cycle[0]]]
            ring.words[q] = ring.words.get(q, 0) + 1
            ring.transient[q] = max(ring.transient.get(q, 0), transient)
    return sorted(found.values(), key=lambda r: (r.bg.length, r.bg.period, r.name))


def alignments(bg: Background) -> list[tuple[int, int]]:
    """One alignment (a, o) per distinct space-time pattern: (a, o) and (a', o') give the same background on the cells
    j >= 0 when state a + t read from o is state a' + t read from o' for every t."""
    seen: set[tuple[int, ...]] = set()
    out = []
    for a in range(bg.period):
        for o in range(bg.length):
            key = tuple(rotate(bg.states[(a + t) % bg.period], bg.length, o) for t in range(bg.period))
            if key not in seen:
                seen.add(key)
                out.append((a, o))
    return out


def window_cell(bits: list[np.ndarray], low: int, below: int, k: int) -> np.ndarray | int:
    """Cell k of every strip whose cells low .. low + len(bits) - 1 are `bits` (each (2^w,)), with `below` the cell
    low - 1 and the defect zero above the strip."""
    if low <= k < low + len(bits):
        return bits[k - low]
    return below if k == low - 1 else 0


def closed_strips(bg: Background, width: int) -> np.ndarray:
    """The greatest set of strips D(c - width + 1 .. c), bit i the cell c - width + 1 + i, with D zero above c, that one
    step maps into the set at the next phase for both values of D(c - width) and that never makes cell c + 1 a defect.
    Indexed by (phase, (c + offset) mod L, strip): (P, L, 2^width)."""
    P, L, n = bg.period, bg.length, 1 << width
    m = np.arange(n, dtype=np.int32)  # (2^w,) the strips
    alive = np.ones((P, L, n), dtype=bool)  # (P, L, 2^w)
    after = np.zeros((P, L, 2, n), dtype=np.int32)  # (P, L, 2, 2^w)
    low0 = L * (width // L + 2) - width + 1  # c = low + width - 1 is r mod L for low = low0 + r, and low >= 1
    for a in range(P):
        for r in range(L):
            low = low0 + r
            if bg.cell(a, low + width) == 0:  # the top rises above c exactly when D(c) = 1 under a background 0
                alive[a, r] &= ((m >> (width - 1)) & 1) == 0
            bits = [(m >> i) & 1 for i in range(width)]  # (2^w,) each, cell low + i
            for below in (0, 1):
                new = np.zeros(n, dtype=np.int32)  # (2^w,)
                for k in range(low, low + width):
                    b0, b1 = bg.cell(a, k), bg.cell(a, k - 1)
                    up, here, down = (window_cell(bits, low, below, j) for j in (k + 1, k, k - 1))
                    new |= (up ^ (((b0 ^ here) | (b1 ^ down)) ^ (b0 | b1))) << (k - low)
                after[a, r, below] = new
    while True:
        kept = alive.copy()  # (P, L, 2^w)
        for a in range(P):
            nxt = alive[(a + 1) % P]  # (L, 2^w)
            for below in (0, 1):
                kept[a] &= np.take_along_axis(nxt, after[a, :, below], axis=1)
        if np.array_equal(kept, alive):
            return alive
        alive = kept


def least_closed(bg: Background, max_width: int, budget: int = 1 << 27) -> tuple[int, np.ndarray | None]:
    """The least width with a nonempty set of closed strips, up to `max_width` and while P L 2^width stays within
    `budget`, with the set; (the last width tried, None) if there is none."""
    width = 0
    for width in range(1, max_width + 1):
        if bg.period * bg.length * (1 << width) > budget:
            return width - 1, None
        closed = closed_strips(bg, width)
        if closed.any():
            return width, closed
    return width, None


def rising_sets(bg: Background, width: int) -> tuple[np.ndarray, np.ndarray]:
    """The windows near the top of a defect that force its top to grow without bound, whatever lies below. Let h be
    the highest top reached so far; a window is the cells h - width + 1 .. h, with D zero above h, at a phase a and
    residue (h + o) mod L. One step, for either value of the cell D(h - width) below, gives the cells h - width + 1 ..
    h + 1, all known: if cell h + 1 is a defect, h rises by one (gain 1) and the new window is the cells
    h - width + 2 .. h + 1; otherwise h stays (gain 0). A window of zeros has lost the top (it may have fallen below).
    `alive` is the greatest set of nonzero windows that one step maps into the set for both inputs, so a defect inside
    keeps its top within width - 1 cells of h; `growing` removes from it every window from which some inputs reach a
    cycle of gain 0, so h rises at least once in every `growing.sum()` steps, and a defect whose window enters it has a
    top that grows without bound. Both indexed by (phase, (h + offset) mod L, window): (P, L, 2^width), bit
    width - 1 the cell h."""
    P, L, n = bg.period, bg.length, 1 << width
    m = np.arange(n, dtype=np.int64)  # (2^w,) the windows
    succ = np.zeros((P, L, 2, n), dtype=np.int64)  # (P, L, 2, 2^w) flat index of the next window
    gain = np.zeros((P, L, 2, n), dtype=np.int8)  # (P, L, 2, 2^w)
    low0 = L * (width // L + 2) - width + 1
    bits = [(m >> i) & 1 for i in range(width)]  # (2^w,) each, cell low + i
    for a in range(P):
        a1 = (a + 1) % P
        for r in range(L):
            low = low0 + r
            for below in (0, 1):
                new = np.zeros(n, dtype=np.int64)  # (2^w,) cells low .. low + width, bit i the cell low + i
                for k in range(low, low + width + 1):
                    b0, b1 = bg.cell(a, k), bg.cell(a, k - 1)
                    up, here, down = (window_cell(bits, low, below, j) for j in (k + 1, k, k - 1))
                    new |= (up ^ (((b0 ^ here) | (b1 ^ down)) ^ (b0 | b1))) << (k - low)
                rise = ((new >> width) & 1) == 1  # (2^w,)
                succ[a, r, below] = np.where(rise, ((a1 * L + (r + 1) % L) * n) + (new >> 1),
                                             ((a1 * L + r) * n) + (new & (n - 1)))
                gain[a, r, below] = rise.astype(np.int8)
    succ_flat = succ.transpose(0, 1, 3, 2).reshape(-1, 2)  # (P L 2^w, 2)
    gain_flat = gain.transpose(0, 1, 3, 2).reshape(-1, 2)  # (P L 2^w, 2)
    del succ, gain
    alive = np.broadcast_to(m > 0, (P * L, n)).reshape(-1).copy()  # (P L 2^w,) the top within the window
    while True:  # the greatest set closed under both inputs
        ok = alive & alive[succ_flat].all(axis=1)
        if np.array_equal(ok, alive):
            break
        alive = ok
    loop = alive.copy()  # (P L 2^w,) windows with an infinite walk of gain 0 inside `alive`
    while True:
        nxt = loop & ((gain_flat == 0) & loop[succ_flat]).any(axis=1)
        if np.array_equal(nxt, loop):
            break
        loop = nxt
    bad = loop.copy()  # (P L 2^w,) windows of `alive` from which some inputs reach `loop`
    while True:
        nxt = bad | (alive & bad[succ_flat].any(axis=1))
        if np.array_equal(nxt, bad):
            break
        bad = nxt
    growing = alive & ~bad
    return alive.reshape(P, L, n), growing.reshape(P, L, n)


def least_rising(bg: Background, max_width: int, budget: int = 1 << 26) -> tuple[int, np.ndarray | None]:
    """The least width with a nonempty `growing` set of `rising_sets`, up to `max_width` and while P L 2^width stays
    within `budget`, with the set; (the last width tried, None) if there is none."""
    width = 0
    for width in range(2, max_width + 1):
        if bg.period * bg.length * (1 << width) > budget:
            return width - 1, None
        _, growing = rising_sets(bg, width)
        if growing.any():
            return width, growing
    return width, None


# ---- the census, defects held as rows of 64-cell words --------------------------------------------------------------


def bit_length64(x: np.ndarray) -> np.ndarray:
    """The bit length of each 64-bit word, exactly, through two 32-bit halves converted to floats."""
    high = (x >> U64(32)).astype(np.float64)  # (...,)
    low = (x & U64(0xFFFFFFFF)).astype(np.float64)  # (...,)
    _, eh = np.frexp(high)  # (...,)
    _, el = np.frexp(low)  # (...,)
    return np.where(high > 0, 32 + eh, el).astype(np.int64)  # (...,)


def tops(D: np.ndarray) -> np.ndarray:
    """The top of each defect, rows of `words` words with cell 64 i + b at bit b of word i; -1 for none."""
    n, words = D.shape  # D: (n, words)
    nz = D != 0  # (n, words)
    last = words - 1 - np.argmax(nz[:, ::-1], axis=1)  # (n,) the highest nonzero word
    word = D[np.arange(n), last]  # (n,)
    return np.where(nz.any(axis=1), 64 * last + bit_length64(word) - 1, -1)  # (n,)


def as_words(value: int, words: int) -> np.ndarray:
    """An integer as `words` 64-bit words, low word first: (words,)."""
    return np.array([(value >> (64 * i)) & MASK64 for i in range(words)], dtype=np.uint64)  # (words,)


def background_words(bg: Background, offset: int, words: int) -> np.ndarray:
    """The background cells 0 .. 64 (words + 1) - 1 at every phase: (P, words + 1)."""
    return np.stack([as_words(bg.word(a, offset, 0, 64 * (words + 1)), words + 1) for a in range(bg.period)])


def step_words(D: np.ndarray, now: np.ndarray, nxt: np.ndarray) -> np.ndarray:
    """One step of every defect: `now` and `nxt` the background words at this step and the next, (words + 1,) each.
    Exact for a defect whose top is at most 64 words - 2."""
    words = D.shape[1]  # D: (n, words)
    x = D ^ now[:words]  # (n, words) the actual cells
    carry_up = np.concatenate([x[:, 1:], np.broadcast_to(now[words:], (len(x), 1))], axis=1)  # (n, words)
    up = (x >> U64(1)) | (carry_up << U64(63))  # (n, words) cell j + 1 at bit j
    carry_down = np.concatenate([np.zeros((len(x), 1), dtype=np.uint64), x[:, :-1]], axis=1)  # (n, words)
    down = (x << U64(1)) | (carry_down >> U64(63))  # (n, words) cell j - 1 at bit j; cell -1 is the held 0
    return (up ^ (x | down)) ^ nxt[:words]


def strip_at(D: np.ndarray, low: np.ndarray, width: int) -> np.ndarray:
    """The `width` <= 32 cells low .. low + width - 1 of each defect, for 0 <= low <= 64 words - width."""
    n = D.shape[0]  # D: (n, words)
    padded = np.concatenate([D, np.zeros((n, 1), dtype=np.uint64)], axis=1)  # (n, words + 1)
    i, b = low // 64, (low % 64).astype(np.uint64)  # (n,), (n,)
    w0 = padded[np.arange(n), i] >> b  # (n,)
    w1 = np.where(b > 0, padded[np.arange(n), i + 1] << ((U64(64) - b) % U64(64)), U64(0))  # (n,)
    return ((w0 | w1) & U64((1 << width) - 1)).astype(np.int64)  # (n,)


def closed_cell(D: np.ndarray, top: np.ndarray, phase: int, offset: int, closed: np.ndarray, width: int,
                limit: int) -> np.ndarray:
    """For each defect, the least cell c with max(top, width - 1) <= c <= limit whose strip D(c - width + 1 .. c) is
    closed, or -1. A defect with such a c keeps its top at or below c from then on. Candidates above top + width are
    the zero strip, so c runs up to max(top, width - 1) + width + L."""
    P, L = closed.shape[0], closed.shape[1]
    base = np.maximum(top, width - 1)  # (n,)
    found = np.full(len(D), -1, dtype=np.int64)  # (n,)
    open_rows = closed[phase % P]  # (L, 2^w)
    if not open_rows.any():
        return found
    for extra in range(width + L):
        c = base + extra  # (n,)
        ok = c <= limit  # (n,)
        strip = strip_at(D, np.minimum(c, limit) - width + 1, width)  # (n,)
        ok &= open_rows[(c + offset) % L, strip]
        found = np.where(ok & (found < 0), c, found)
    return found


def census(bg: Background, phase: int, offset: int, heads: np.ndarray, max_steps: int, closed: np.ndarray | None,
           width: int, in_k: bool = False, words: int = 4, growing: np.ndarray | None = None,
           rise_width: int = 0) -> dict[str, np.ndarray]:
    """Follow every defect D_0 in `heads` (integers below 2^62) at the alignment (phase, offset). A head stops when

    - it enters a closed strip (`closed_cell`), its top then bounded forever; with `in_k` the step is recorded in
      `strip` and the head is followed on;
    - its state repeats: snapshots at the steps m 2^k, m = P (or lcm(P, 2) with `in_k`), compared with every later
      multiple of m;
    - with `in_k`, it breaks K: bit 0 of D_t xor B_t is 0 at an odd step t;
    - its top window (the `rise_width` cells up to the top) lies in `growing` of `rising_sets`, so its top grows
      without bound and its orbit is not eventually periodic; the step is recorded in `rise`, and with `in_k` the head
      is followed on;
    - its top passes 64 words - 8 (`grow`), or the horizon `max_steps` ends.

    Returns per head: `top` (the highest top seen), `strip` (the step of entry into a closed strip, or -1), `cell` (its
    cell), `repeat` (the step of a repeat, or -1), `period`, `broke` (the step that broke K, or -1), `grow` (the step
    the top passed the cells followed, or -1), `rise` (the step its top window entered `growing`, or -1) and `end`
    (the last step followed)."""
    n = len(heads)
    P = bg.period
    m = math.lcm(P, 2) if in_k else P
    limit = 64 * words - 8
    bgw = background_words(bg, offset, words)  # (P, words + 1)
    D = np.zeros((n, words), dtype=np.uint64)  # (n, words)
    D[:, 0] = heads.astype(np.uint64)
    index = np.arange(n)  # (k,) which head each followed defect is
    best = tops(D)  # (k,)
    out = {key: np.full(n, -1, dtype=np.int64) for key in ("strip", "cell", "repeat", "broke", "grow", "rise", "end")}
    out["top"] = best.copy()
    out["period"] = np.zeros(n, dtype=np.int64)
    snap, snap_t, next_snap = D.copy(), 0, m
    for t in range(max_steps + 1):
        if t > 0:
            D = step_words(D, bgw[(phase + t - 1) % P], bgw[(phase + t) % P])
        now = tops(D)  # (k,)
        best = np.maximum(best, now)
        done = np.zeros(len(index), dtype=bool)  # (k,)
        if in_k and t % 2 == 1:
            broke = ((D[:, 0] ^ bgw[(phase + t) % P, 0]) & U64(1)) == 0  # (k,)
            out["broke"][index[broke]] = t
            done |= broke
        grow = (now > limit) & ~done  # (k,)
        out["grow"][index[grow]] = t
        done |= grow
        if closed is not None:
            fresh = (out["strip"][index] < 0) & ~done  # (k,)
            if fresh.any():
                cell = closed_cell(D[fresh], now[fresh], phase + t, offset, closed, width, limit)  # (f,)
                hit = cell >= 0  # (f,)
                ids = index[fresh][hit]
                out["strip"][ids], out["cell"][ids] = t, cell[hit]
                if not in_k:
                    done[np.flatnonzero(fresh)[hit]] = True
        if growing is not None:
            fresh = (out["rise"][index] < 0) & ~done & (now >= rise_width - 1)  # (k,)
            if fresh.any():
                window = strip_at(D[fresh], now[fresh] - rise_width + 1, rise_width)  # (f,)
                hit = growing[(phase + t) % P, (now[fresh] + offset) % bg.length, window]  # (f,)
                out["rise"][index[fresh][hit]] = t
                if not in_k:
                    done[np.flatnonzero(fresh)[hit]] = True
        if t % m == 0 and t > snap_t:
            rep = (D == snap).all(axis=1) & ~done  # (k,)
            out["repeat"][index[rep]] = t
            out["period"][index[rep]] = t - snap_t
            done |= rep
        if done.any() or t == max_steps:
            stop = done if t < max_steps else np.ones(len(index), dtype=bool)  # (k,)
            out["top"][index[stop]] = best[stop]
            out["end"][index[stop]] = t
            keep = ~stop
            D, index, best, snap = D[keep], index[keep], best[keep], snap[keep]
        if len(index) == 0:
            break
        if t == next_snap:
            snap, snap_t, next_snap = D.copy(), t, 2 * t
    return out


def summarize(out: dict[str, np.ndarray], in_k: bool) -> dict[str, int]:
    """Counts of a census: without K, settled by a closed strip, by a repeat, growing top, open at the horizon;
    with K, broke K (before or after entering a closed strip), reached a periodic point of K, growing top in K, open in
    K at the horizon (with how many of those are inside a closed strip)."""
    strip, rep, grow, broke = out["strip"] >= 0, out["repeat"] >= 0, out["grow"] >= 0, out["broke"] >= 0
    rise = out["rise"] >= 0
    if not in_k:
        return {"heads": len(strip), "strip": int(strip.sum()), "repeat": int((rep & ~strip).sum()),
                "rise": int(rise.sum()), "grow": int(grow.sum()), "open": int((~strip & ~rep & ~grow & ~rise).sum()),
                "last_rise": int(out["rise"].max(initial=-1)),
                "top": int(out["top"][~grow].max(initial=-1)),
                "last": int(out["end"][strip | rep].max(initial=-1))}
    return {"heads": len(strip), "broke": int(broke.sum()), "broke_in_strip": int((broke & strip).sum()),
            "broke_in_rise": int((broke & rise).sum()), "periodic_in_k": int(rep.sum()), "grow_in_k": int(grow.sum()),
            "open_in_k": int((~broke & ~rep & ~grow).sum()),
            "open_in_strip": int((~broke & ~rep & ~grow & strip).sum()),
            "last_break": int(out["broke"].max(initial=-1)), "top": int(out["top"][~grow].max(initial=-1))}


# ---- direct runs on Python integers ---------------------------------------------------------------------------------


def defect_run(bg: Background, phase: int, offset: int, head: int, steps: int) -> list[int]:
    """The defects D_0 .. D_steps of one head as Python integers, by the held map on the whole cells 0 .. width - 1
    with the background above the head (an independent check of `step_words`)."""
    width = head.bit_length() + 2 * steps + 4
    x = head ^ bg.word(phase, offset, 0, width)
    out = [head]
    for t in range(1, steps + 1):
        cells = width - t  # cells j < width - t read only cells below width
        x = held(x) & ((1 << cells) - 1)
        out.append(x ^ bg.word(phase + t, offset, 0, cells))
    return out


def in_k_steps(bg: Background, phase: int, offset: int, head: int, steps: int) -> int:
    """The first odd step t <= steps at which bit 0 of H^t(U) is 0, for U the head with the background above it; -1
    if there is none."""
    for t, D in enumerate(defect_run(bg, phase, offset, head, steps)):
        if t % 2 == 1 and ((D ^ bg.cell(phase + t, offset)) & 1) == 0:
            return t
    return -1


def front_speed(bg: Background, phase: int, offset: int, head: int, steps: int) -> list[int]:
    """The top of the defect of one head at each step 0 .. steps, from `defect_run`."""
    return [D.bit_length() - 1 for D in defect_run(bg, phase, offset, head, steps)]


# ---- the command line -----------------------------------------------------------------------------------------------


def run_background(bg: Background, bits: int, max_steps: int, in_k: bool,
                   sets: tuple[int, np.ndarray | None, int, np.ndarray | None]) -> dict[str, int]:
    """The census of every head below 2^bits at every alignment of `bg`, summed, with `sets` the closed strips of
    `least_closed` and the growing windows of `least_rising`: (width, closed or None, width, growing or None)."""
    width, closed, rise_width, growing = sets
    total: dict[str, int] = {}
    heads = np.arange(1 << bits, dtype=np.int64)  # (2^bits,)
    for a, o in tqdm(alignments(bg), desc=f"{bg.name()} K {'on' if in_k else 'off'}", file=sys.stderr, leave=False):
        out = census(bg, a, o, heads, max_steps, closed, width, in_k, growing=growing, rise_width=rise_width)
        for key, value in summarize(out, in_k).items():
            total[key] = max(total.get(key, -1), value) if key in ("top", "last", "last_break", "last_rise") \
                else total.get(key, 0) + value
    total["width"] = width if closed is not None else -width
    total["closed"] = int(closed.sum()) if closed is not None else 0
    total["rise_width"] = rise_width if growing is not None else -rise_width
    total["growing"] = int(growing.sum()) if growing is not None else 0
    total["alignments"] = len(alignments(bg))
    return total


def k_survival(bg: Background, bits: int, steps: int) -> np.ndarray:
    """For every head below 2^bits at every alignment, the number still in K after each step 0 .. steps (no odd step up
    to it has broken K), summed over the alignments: (steps + 1,)."""
    alive = np.zeros(steps + 1, dtype=np.int64)  # (steps + 1,)
    heads = np.arange(1 << bits, dtype=np.int64)  # (2^bits,)
    for a, o in tqdm(alignments(bg), desc=f"{bg.name()} survival", file=sys.stderr, leave=False):
        broke = census(bg, a, o, heads, steps, None, 0, in_k=True)["broke"]  # (2^bits,)
        broke = np.where(broke < 0, steps + 1, broke)  # (2^bits,)
        counts = np.bincount(broke, minlength=steps + 2)  # (steps + 2,) heads broken at each step
        alive += len(broke) - np.cumsum(counts)[:steps + 1]
    return alive


def front_pattern(tops: list[int], period: int, longest: int) -> tuple[int, int] | None:
    """The least k <= `longest`, a multiple of `period`, with top(t + k) - top(t) the same for every t in the second
    half of the run, and that gain; None if there is none (a front whose speed is not periodic in this run)."""
    steps = len(tops) - 1
    for k in range(period, longest + 1, period):
        if steps - k <= steps // 2:
            break
        gains = {tops[t + k] - tops[t] for t in range(steps // 2, steps - k + 1)}
        if len(gains) == 1:
            return k, gains.pop()
    return None


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("what", choices=["rings", "sets", "census", "fronts", "survival"])
    parser.add_argument("--max-q", type=int, default=10)
    parser.add_argument("--bits", type=int, default=12)
    parser.add_argument("--steps", type=int, default=3000)
    parser.add_argument("--closed-width", type=int, default=14, help="the widest closed strips tried")
    parser.add_argument("--rise-width", type=int, default=12, help="the widest growing windows tried")
    parser.add_argument("--count", type=int, default=20)
    parser.add_argument("--k-only", action="store_true", help="census: only with the condition of K")
    parser.add_argument("--only", type=str, default="", help="comma-separated background names to run")
    args = parser.parse_args()
    rows = ring_backgrounds(args.max_q)
    if args.only:
        rows = [r for r in rows if r.name in args.only.split(",")]
    for r in rows:
        bg = r.bg
        head = f"L {bg.length} P {bg.period} {r.name}"
        if args.what == "rings":
            print(f"{head}  shift {r.shift}  words {r.words}  transient {r.transient}  "
                  f"alignments {len(alignments(bg))}", flush=True)
        elif args.what == "sets":
            width, closed = least_closed(bg, args.closed_width)
            rise_width, growing = least_rising(bg, args.rise_width)
            strips = f"none up to width {width}" if closed is None else f"width {width}, {int(closed.sum())}"
            windows = (f"none up to width {rise_width}" if growing is None
                       else f"width {rise_width}, {int(growing.sum())}")
            print(f"{head}  closed strips: {strips}  growing windows: {windows}", flush=True)
        elif args.what == "census":
            sets = (*least_closed(bg, args.closed_width), *least_rising(bg, args.rise_width))
            for in_k in ((True,) if args.k_only else (False, True)):
                s = run_background(bg, args.bits, args.steps, in_k, sets)
                print(f"{head} K {'on ' if in_k else 'off'} {s}", flush=True)
        elif args.what == "survival":
            alive = k_survival(bg, args.bits, args.steps)  # (steps + 1,)
            marks = ", ".join(f"{t}: {alive[t] / alive[0]:.2e}" for t in range(0, args.steps + 1, 8))
            last = int(np.flatnonzero(alive)[-1]) + 1 if alive[-1] == 0 else -1
            print(f"{head}: share of heads still in K after step t, {marks}; the last break at step {last}"
                  if last >= 0 else f"{head}: share still in K, {marks}; {alive[-1]} heads in K at step {args.steps}",
                  flush=True)
        else:
            rng = np.random.default_rng(1)
            found: dict[str, int] = {}
            slopes = []
            for _ in tqdm(range(args.count), desc=head, file=sys.stderr, leave=False):
                a, o = int(rng.integers(bg.period)), int(rng.integers(bg.length))
                tops = front_speed(bg, a, o, int(rng.integers(1, 1 << 12)), args.steps)
                pattern = front_pattern(tops, bg.period, 6 * bg.period * bg.length)
                key = "chaotic" if pattern is None else f"{pattern[1]}/{pattern[0]}"
                found[key] = found.get(key, 0) + 1
                slopes.append((tops[-1] - tops[args.steps // 2]) / (args.steps - args.steps // 2))
            print(f"{head}: gain per period over the second half {found}; slopes {min(slopes):.3f} to "
                  f"{max(slopes):.3f}", flush=True)


if __name__ == "__main__":
    main()
