"""The structure of K: the count of its heads, its rational points by the period of their tail, the backward closure of
the periodic points in each family of tails, and a descent of the defect's top at a lag that grows with the top.

Write H(U) = (U >> 1) xor (U or (U << 1)) for the held map on 2-adic integers (cells 0, 1, 2, ...) and K for the U with
H^t(U) odd at every odd t. (R) says that every rational point of K has an eventually periodic itinerary.

A rational 2-adic integer is held exactly as `Rat` = (p, q, cells): its cells 0 .. p + q - 1 as the bits of an integer,
periodic with period q from cell p on, with q and then p least (`canon`). H maps such a number to one with preperiod at
most p + 1 and period dividing q (`rat_step`), and each of the two preimages under H with a given cell 0 is rational,
with a period dividing 4 q (`rat_preimage`). So the rational points whose tail period divides Q form a family F_Q that
H^2 maps into itself, and a point of K has exactly two preimages under H^2 in K (`k_preimages`).

- `head_count(h)`: the heads of h cells consistent with K at every odd step below h, 2^ceil(h/2) (item 1 of the shift
  model), and `stripe_heads(h, depth)`: the heads of the points of K with a stripe tail that reach a stripe within
  `depth` applications of H^2.
- `run_rat(x)`: the exact orbit of a rational until an odd step breaks K or a state repeats at two even steps.
- `zoo_points(max_n, max_q)`: the periodic points of H^2 in K with itinerary period at most `max_n` and a spatial tail
  period at most `max_q`, from the columns of the periodic itineraries.
- `purely_periodic(q)`: the purely periodic numbers of least period q (denominator 2^q - 1) that are points of K.
- `closure(seeds, Q)`, `closure_levels(seeds, Q, levels)`: the points of K with a tail period dividing Q whose orbit
  under H^2 reaches a seed, as a whole or level by level.
- `ring_transients(q)`: the longest transient into each background on the ring of q cells.
- `tree_rationals(depth, max_q)`: the rational points of K with p + q <= depth, from the tree of K (for the tests).
- `search_points(path, depth)`: the hits of `held_shift_search.c`, settled exactly.
- `descent(h, ...)`: for the heads of h cells on the ether, the first step at which K breaks or the top of the defect
  falls below its start, run on rows of numpy words; `closure_descent`: the same descent for the points of a closure.

    python -m computations.k_structure heads --max-h 24              # item (a), seconds
    python -m computations.k_structure families --max-q 16 --max-n 16 --search hits64.txt   # item (b), 10 minutes
    python -m computations.k_structure descent --min-h 21 --max-h 40  # item (c), about 15 minutes
"""

from __future__ import annotations

import argparse
import math
import sys
from collections import Counter, deque

import numpy as np
from tqdm.auto import tqdm

from computations.ether_certificate import background
from computations.held_shift import cycle_class, forced_halves
from computations.k_survivors import extend, held_rows

Rat = tuple[int, int, int]  # (preperiod p, period q, cells 0 .. p + q - 1 as bits), p and q least
U64 = np.uint64
ONE = U64(1)
MAX_PRE = 4096  # a rational whose preperiod passes this many cells is left undecided by `run_rat`
MAX_STEPS = 20_000  # steps of `run_rat` before a rational is left undecided


def mask(n: int) -> int:
    """The integer with the cells 0 .. n - 1 set."""
    return (1 << n) - 1


# ---- (a) the heads of K ---------------------------------------------------------------------------------------------


def head_count(h: int) -> int:
    """The heads of h cells that keep bit 0 of H^t odd at every odd t < h (bit 0 at step t reads the cells 0 .. t only),
    from the tree of `held_shift.forced_halves`."""
    return len(forced_halves(h))


# ---- rationals held exactly ----------------------------------------------------------------------------------------


def least_cyclic_period(word: int, q: int) -> int:
    """The least d dividing q with the cyclic word of q cells periodic with period d."""
    full = mask(q)
    return next(d for d in range(1, q + 1) if q % d == 0 and ((word >> d) | (word << (q - d))) & full == word)


def canon(cells: int, p: int, q: int) -> Rat:
    """The rational whose cells 0 .. p + q - 1 are `cells` (higher bits ignored), periodic with period q from p on, with
    the least period and then the least preperiod."""
    d = least_cyclic_period((cells >> p) & mask(q), q)
    cells &= mask(p + d)
    while p > 0 and (cells >> (p - 1)) & 1 == (cells >> (p - 1 + d)) & 1:
        p -= 1
        cells &= mask(p + d)
    return p, d, cells


def rat_cells(x: Rat, n: int) -> int:
    """The cells 0 .. n - 1 of the rational x."""
    p, q, cells = x
    word, filled = cells >> p, q  # the copies of the periodic part at 0, q, .., filled - q, doubled in number
    while filled < n - p:
        word |= word << filled
        filled *= 2
    return ((cells & mask(p)) | (word << p)) & mask(n)


def rat_step(x: Rat) -> Rat:
    """H(x): cell j reads the cells j - 1, j, j + 1, so the image is periodic with period q from cell p + 1 on and its
    cells 0 .. p + q are read off the cells 0 .. p + q + 1 of x."""
    p, q, _ = x
    u = rat_cells(x, p + q + 2)
    return canon((u >> 1) ^ (u | (u << 1)), p + 1, q)


DIGITS = bytes.maketrans(b"\x00\x01", b"01")  # the cells 0 and 1 as the characters of a binary number


def rat_preimage(x: Rat, c: int) -> Rat:
    """The rational U with H(U) = x and cell 0 of U equal to c: U(j + 1) = x(j) xor (U(j) or U(j - 1)), U(-1) = 0. From
    cell p of x on, the state (U(j), U(j - 1), j mod q) runs through at most 4 q values, so U is periodic from cell
    p + 4 q on with a period L <= 4 q that is a multiple of q; its least period is the least period of the window of
    8 q cells read there (by Fine and Wilf, a window of L + d cells with periods L and d has period gcd(L, d))."""
    p, q, _ = x
    n = p + 12 * q + 1
    v = rat_cells(x, n)
    u = [c]
    for j in range(n):
        u.append(((v >> j) & 1) ^ (u[j] | (u[j - 1] if j > 0 else 0)))
    lo, hi = p + 4 * q, p + 12 * q
    cells = bytes(u)  # cells[j] = U(j), compared as strings
    d = next(d for d in range(1, 4 * q + 1) if cells[lo:hi - d] == cells[lo + d:hi])
    return canon(int(cells[lo + d - 1::-1].translate(DIGITS), 2), lo, d)


def k_preimages(x: Rat) -> tuple[Rat, Rat]:
    """The two points U of K with H^2(U) = x, for x in K: H(U) is the preimage of x with cell 0 equal to 1 (bit 0 at
    step 1), and U is either preimage of it."""
    w = rat_preimage(x, 1)
    return rat_preimage(w, 0), rat_preimage(w, 1)


def run_rat(x: Rat, max_steps: int = MAX_STEPS, max_pre: int = MAX_PRE) -> dict[str, int]:
    """The exact orbit of x under H until an odd step with bit 0 equal to 0 (`how` 0, x is not in K) or a state seen
    again at two even steps (`how` 1: the orbit is periodic from `start` with the even period `period`, every odd step
    of the cycle has been tested, so x is in K and its itinerary is eventually periodic), else `how` -1. Also the
    largest preperiod over the run (`pre`) and the step of the decision."""
    seen: dict[Rat, int] = {}
    t, top = 0, x[0]
    while t <= max_steps and x[0] <= max_pre:
        if t % 2 == 1 and x[2] & 1 == 0:
            return {"how": 0, "step": t, "start": -1, "period": 0, "pre": top}
        if t % 2 == 0:
            if x in seen:
                return {"how": 1, "step": t, "start": seen[x], "period": t - seen[x], "pre": top}
            seen[x] = t
        x = rat_step(x)
        top = max(top, x[0])
        t += 1
    return {"how": -1, "step": t, "start": -1, "period": 0, "pre": top}


def h2(x: Rat) -> Rat:
    """H^2(x)."""
    return rat_step(rat_step(x))


def itinerary_period(x: Rat) -> int:
    """The least period of the itinerary (bit 0 at the even steps) of a periodic point x of H^2."""
    bits, y = [], x
    while True:
        bits.append(y[2] & 1)
        y = h2(y)
        if y == x:
            break
    n = len(bits)
    return next(d for d in range(1, n + 1) if n % d == 0 and all(bits[i] == bits[(i + d) % n] for i in range(n)))


def ring_class(x: Rat) -> tuple[int, int]:
    """The background that the tail of x falls onto on the ring of q cells: (least spatial period L, cycle length P),
    as in the tail census. The stripes are (2, 1), the ether (7, 4), the vacuum (1, 1)."""
    p, q, cells = x
    _, period_p, _, period_l = cycle_class(cells >> p, q)
    return period_l, period_p


def is_stripe(x: Rat) -> bool:
    """Whether the tail of x falls onto a stripe on the ring."""
    return ring_class(x) == (2, 1)


def stripe_heads(h: int, depth: int) -> int:
    """The distinct heads of h cells among the points of K with a stripe tail that reach one of the two stripes within
    `depth` applications of H^2 (the stripes A = 1010... and B = 0101... from cell 0, both in K)."""
    level = {canon(0b01, 0, 2), canon(0b10, 0, 2)}
    found = set(level)
    for _ in range(depth):
        level = {u for x in level for u in k_preimages(x)} - found
        found |= level
    return len({rat_cells(x, h) for x in found})


# ---- (b) periodic points, purely periodic points and the closures ---------------------------------------------------


def zoo_points(max_n: int, max_q: int, columns: int = 1024) -> set[Rat]:
    """The periodic points of H^2 in K with itinerary period at most `max_n`, a spatial tail period at most `max_q` and
    a preperiod of at most `columns` - 1 - max_q - 2 max_n (a word is resolved once the preperiods of its orbit at all 2 n
    steps, each at most the preperiod at step 0 plus the step, are at most `columns` - 2 - max_q). For an itinerary word of n readings, column 0 of the space-time pattern is the
    cyclic word of 2 n steps with 1 at the odd steps and the word at the even ones, and column k + 1 at step t is column
    k at step t + 1 xor (column k or column k - 1) at step t, column -1 zero. All words of a given n are run together
    as numpy words of 2 n bits; a word is resolved at the first column k at which the pair (column k - 1, column k)
    equals the pair d columns back, d <= max_q."""
    out: set[Rat] = set()
    for n in tqdm(range(1, max_n + 1), desc="itinerary periods", file=sys.stderr, leave=False):
        length = 2 * n
        full = U64((1 << length) - 1)
        words = np.arange(1 << n, dtype=U64)  # (w,)
        col = np.zeros(1 << n, dtype=U64)  # (w,): column 0, cell 0 at every step
        for s in range(n):
            col |= ((words >> U64(s)) & ONE) << U64(2 * s)
            col |= ONE << U64(2 * s + 1)
        hist = deque([np.zeros(1 << n, dtype=U64), col], maxlen=max_q + 2)  # the last columns: (w,) each
        cells = [(col & ONE).astype(np.uint8)]  # cell k of the point at step 0: (w,) each
        alive = np.ones(1 << n, dtype=bool)  # (w,)
        for k in range(1, columns):
            prev, cur = hist[-2], hist[-1]
            rot = ((cur >> ONE) | (cur << U64(length - 1))) & full  # cell t + 1 of column k at bit t: (w,)
            nxt = rot ^ (cur | prev)  # (w,)
            hist.append(nxt)
            cells.append((nxt & ONE).astype(np.uint8))
            # the pair (column k - 1, column k) against the pair d columns back
            for d in range(1, min(max_q, k) + 1):
                hit = alive & (hist[-1] == hist[-1 - d]) & (hist[-2] == hist[-2 - d])  # (w,)
                for i in np.flatnonzero(hit):
                    bits = sum(int(cells[j][i]) << j for j in range(k + 1))
                    out.add(canon(bits, k - d, d))
                alive &= ~hit
            if not alive.any():
                break
    return out


def periodic_orbit(x: Rat) -> list[Rat]:
    """The orbit of the periodic point x of H^2."""
    out, y = [x], h2(x)
    while y != x:
        out.append(y)
        y = h2(y)
    return out


def landing(x: Rat, periodic: set[Rat]) -> tuple[Rat, int]:
    """The periodic point that the orbit of x under H^2 first meets, and the applications of H^2 it takes."""
    n = 0
    while x not in periodic:
        x, n = h2(x), n + 1
    return x, n


def purely_periodic(q: int) -> list[tuple[Rat, dict[str, int]]]:
    """The purely periodic numbers of least period q (cells 0 .. q - 1 a primitive word, repeated) that are points of K,
    each with its run (`run_rat`); a word whose run is undecided is returned too."""
    out = []
    for word in range(1 << q):
        x = canon(word, 0, q)
        if x != (0, q, word):
            continue  # not of least period q
        r = run_rat(x)
        if r["how"] != 0:
            out.append((x, r))
    return out


def children(x: Rat, big_q: int, seeds: set[Rat]) -> list[Rat]:
    """The points of K that H^2 maps to x, with a tail period dividing `big_q`, other than the seeds."""
    return [u for u in k_preimages(x) if big_q % u[1] == 0 and u not in seeds]


def closure(seeds: set[Rat], big_q: int, max_pre: int = 1 << 30, max_points: int = 300_000) -> dict[Rat, int]:
    """The points of K with a tail period dividing `big_q` whose orbit under H^2 reaches one of the `seeds` (periodic
    points of K) through points with a preperiod of at most `max_pre`, each with the applications of H^2 it takes to
    reach a seed, by breadth-first search over `k_preimages`. Raises if the search passes `max_points` points. Since
    H raises the preperiod by at most 1, a point of the whole closure with preperiod p and depth s is found whenever
    p + 2 s <= `max_pre`."""
    seeds = {x for x in seeds if big_q % x[1] == 0}
    out = dict.fromkeys(seeds, 0)
    todo = deque(out)
    with tqdm(desc=f"closure of period {big_q}", unit=" points", file=sys.stderr, leave=False) as bar:
        while todo:
            x = todo.popleft()
            bar.update(1)
            for u in children(x, big_q, seeds):
                if u[0] <= max_pre and u not in out:
                    out[u] = out[x] + 1
                    todo.append(u)
                    if len(out) > max_points:
                        raise OverflowError(f"closure of period {big_q} passes {max_points} points")
    return out


def closure_levels(seeds: set[Rat], big_q: int, levels: int,
                   keep: int = -1) -> tuple[list[dict[str, int]], set[Rat], set[Rat]]:
    """The closure of `closure`, level by level (level s: the points that reach a seed in exactly s applications of
    H^2), through `levels` levels: per level the points, the points whose least tail period is below `big_q`, and the
    least and largest preperiod; the last level; and the points with p + q <= `keep`."""
    seeds = {x for x in seeds if big_q % x[1] == 0}
    level = set(seeds)
    kept = {x for x in level if x[0] + x[1] <= keep}
    rows = [{"points": len(level), "shorter": sum(x[1] < big_q for x in level), "min_pre": min(x[0] for x in level),
             "max_pre": max(x[0] for x in level)}]
    for _ in tqdm(range(levels), desc=f"levels of period {big_q}", file=sys.stderr, leave=False):
        level = {u for x in level for u in children(x, big_q, seeds)}
        if not level:
            break
        kept |= {x for x in level if x[0] + x[1] <= keep}
        rows.append({"points": len(level), "shorter": sum(x[1] < big_q for x in level),
                     "min_pre": min(x[0] for x in level), "max_pre": max(x[0] for x in level)})
    return rows, level, kept


def odd_steps_ok(x: np.ndarray) -> np.ndarray:
    """Whether each number of 64 cells (n,) keeps bit 0 of H^t odd at every odd t < 64 (bit 0 at step t reads the cells
    0 .. t only, so the numbers decide these steps): (n,) of bool."""
    ok = np.ones(len(x), dtype=bool)  # (n,)
    for t in range(1, 64):
        x = (x >> ONE) ^ (x | (x << ONE))  # (n,)
        if t % 2 == 1:
            ok &= (x & ONE) == ONE
    return ok


def ring_transients(q: int) -> dict[tuple[int, int], int]:
    """For each background (L, P) that words of q cells reach under the held map on a ring of q cells, the longest
    transient before a word is on its cycle. The map is held as an array f over all 2^q words; its powers f^(2^j) come
    by squaring, the cycle states are the image of f^(2^q), and the transient of each word is found by binary lifting
    over the powers."""
    full = mask(q)
    w = np.arange(1 << q, dtype=np.int64)  # (2^q,)
    up = ((w >> 1) | (w << (q - 1))) & full  # (2^q,): cell j + 1 at bit j
    down = ((w << 1) | (w >> (q - 1))) & full  # (2^q,): cell j - 1 at bit j
    f = (up ^ (w | down)) & full  # (2^q,): the image of each word
    powers = [f]  # f^(2^j) for j = 0 .. q: (2^q,) each
    for _ in range(q):
        powers.append(powers[-1][powers[-1]])
    on_cycle = np.zeros(1 << q, dtype=bool)  # (2^q,)
    on_cycle[powers[-1]] = True  # a transient is shorter than 2^q
    image = np.flatnonzero(on_cycle)  # (m,)
    cur, depth = w.copy(), np.zeros(1 << q, dtype=np.int64)  # (2^q,) each
    for j in range(q, -1, -1):  # the largest number of steps that stays off the cycles
        nxt = powers[j][cur]  # (2^q,)
        move = ~on_cycle[cur] & ~on_cycle[nxt]  # (2^q,)
        cur[move] = nxt[move]
        depth[move] += 1 << j
    off = ~on_cycle[cur]  # (2^q,): one more step reaches the cycle
    cur[off] = f[cur[off]]
    depth[off] += 1
    out: dict[tuple[int, int], int] = {}
    cls: dict[int, tuple[int, int]] = {}
    fl = f.tolist()
    for c in image.tolist():  # one class per cycle: the least spatial period of its states (the ring map commutes with
        if c not in cls:  # rotation, so they share it) and its length
            cycle, y = [c], fl[c]
            while y != c:
                cycle.append(y)
                y = fl[y]
            name = (least_cyclic_period(c, q), len(cycle))
            for y in cycle:
                cls[y] = name
    for c, d in zip(cur.tolist(), depth.tolist()):
        out[cls[c]] = max(out.get(cls[c], 0), d)
    return out


def tree_rationals(depth: int, max_q: int) -> set[Rat]:
    """The rational points of K with least period q <= `max_q` and p + q <= `depth`, found from the tree of K: each
    residue modulo 2^depth that is periodic with period q from cell p to the cell depth - 1 is extended periodically,
    tested at the odd steps below 64 on numpy words, and run exactly (`run_rat`). Independent of `k_preimages`."""
    halves = forced_halves(depth)  # (2^ceil(depth / 2),)
    out: set[Rat] = set()
    for q in range(1, max_q + 1):
        for p in range(depth - q + 1):
            length = depth - p - q
            diff = ((halves >> U64(p)) ^ (halves >> U64(p + q))) & U64(mask(length))  # (n,)
            cand = halves[diff == 0] & U64(mask(p + q))  # (m,)
            ext = cand & U64(mask(p))  # (m,): the periodic extension to 64 cells
            for pos in range(p, 64, q):
                ext |= ((cand >> U64(p)) << U64(pos)) & U64(mask(64))
            for c in cand[odd_steps_ok(ext)].tolist():
                x = canon(int(c), p, q)
                if x[1] == q and x not in out and run_rat(x)["how"] == 1:
                    out.add(x)
    return out


def search_points(path: str, depth: int) -> tuple[set[Rat], Counter[int]]:
    """The hits of `held_shift_search.c` (lines `q high low`, the first `depth` cells as hexadecimal words, q the period
    tried), each extended periodically and run exactly: the points of K among them, and the hits by the outcome of their
    run (0 a break of K, 1 a point of K, -1 undecided)."""
    out: set[Rat] = set()
    how: Counter[int] = Counter()
    with open(path) as handle:
        lines = handle.read().split("\n")
    for line in tqdm([s for s in lines if s.strip()], desc="hits", file=sys.stderr, leave=False):
        q, high, low = line.split()
        cells = ((int(high, 16) << 64) | int(low, 16)) & mask(depth)
        x = canon(cells, depth - int(q), int(q))
        r = run_rat(x)
        how[r["how"]] += 1
        if r["how"] == 1:
            out.add(x)
    return out, how


def denominator(x: Rat) -> int:
    """The reduced denominator of the rational x: x = head - word 2^p / (2^q - 1)."""
    p, q, cells = x
    return ((1 << q) - 1) // math.gcd((1 << q) - 1, (cells & mask(p)) * ((1 << q) - 1) - ((cells >> p) << p))


# ---- (c) descent of the top at a lag ------------------------------------------------------------------------------


def bit_length64(x: np.ndarray) -> np.ndarray:
    """The bit length of each 64-bit word (...,), exactly, through two 32-bit halves converted to floats: (...,)."""
    high = (x >> U64(32)).astype(np.float64)  # (...,)
    low = (x & U64(0xFFFFFFFF)).astype(np.float64)  # (...,)
    _, eh = np.frexp(high)  # (...,)
    _, el = np.frexp(low)  # (...,)
    return np.where(high > 0, 32 + eh, el).astype(np.int64)  # (...,)


def row_tops(d: np.ndarray, cells: int) -> np.ndarray:
    """The highest set cell below `cells` of each row (n, W) of words, -1 for none: (n,)."""
    n, words = d.shape
    d = d.copy()  # (n, W)
    for k in range(words):
        lo = 64 * k
        if cells <= lo:
            d[:, k] = 0
        elif cells < lo + 64:
            d[:, k] &= U64(mask(cells - lo))
    nz = d != 0  # (n, W)
    last = words - 1 - np.argmax(nz[:, ::-1], axis=1)  # (n,)
    word = d[np.arange(n), last]  # (n,)
    return np.where(nz.any(axis=1), 64 * last + bit_length64(word) - 1, -1)  # (n,)


def ether_rows(a: int, o: int, words: int) -> np.ndarray:
    """The ether at (a, o) on 64 `words` cells as one row of words: (words,)."""
    e = background(a, o, 64 * words)
    return np.array([(e >> (64 * k)) & mask(64) for k in range(words)], dtype=U64)  # (words,)


def descent(h: int, a: int, o: int, max_steps: int = 0) -> dict[str, object]:
    """For the heads of exactly h cells (the defect against the ether at (a, o) has its top at cell h - 1) on the tree
    of K: run each half and stop it at the first odd step with bit 0 equal to 0 (a break of K) or the first even step
    t >= 2 at which the top of the defect is below h - 1 (a descent). Returns the leaves, the breaks and descents by
    step, and the heads still running at `max_steps` (default 3 h + 16). A row holds the least number of words W with
    h + 2 max_steps < 64 W: cell j of H^t is right while j + t < 64 W, and the defect at step t lies below h + t."""
    steps = max_steps or 3 * h + 16
    words = (h + 2 * steps) // 64 + 1
    x = np.array([background(a, o, 64) & ~mask(h)], dtype=U64)  # (1,)
    x = extend(x, h, 0, h)  # (2^ceil(h / 2),): the leaves of the tree at h cells, the ether above
    eth_head = background(a, o, h)
    x = x[((x & U64(mask(h))) ^ U64(eth_head)) >> U64(h - 1) == ONE]  # (n,): the defect has exactly h cells
    leaves = len(x)
    rows = np.tile(ether_rows(a, o, words), (leaves, 1))  # (n, W)
    rows[:, 0] = x
    broke: Counter[int] = Counter()
    fell: Counter[int] = Counter()
    for t in range(1, steps + 1):
        rows = held_rows(rows)  # (n, W)
        if t % 2 == 1:
            ok = (rows[:, 0] & ONE) == ONE  # (n,)
            broke[t] += int((~ok).sum())
            rows = rows[ok]
        else:
            top = row_tops(rows ^ ether_rows(a + t, o, words)[None, :], 64 * words - t)  # (n,)
            down = top < h - 1  # (n,)
            fell[t] += int(down.sum())
            rows = rows[~down]
        if len(rows) == 0:
            break
    return {"leaves": leaves, "broke": broke, "fell": fell, "open": len(rows), "steps": steps}


def descent_census(h: int, max_steps: int = 0) -> dict[str, object]:
    """`descent` at all 28 alignments, summed."""
    out: dict[str, object] = {"leaves": 0, "broke": Counter(), "fell": Counter(), "open": 0}
    for a in range(4):
        for o in range(7):
            r = descent(h, a, o, max_steps)
            out["leaves"] += r["leaves"]
            out["broke"].update(r["broke"])
            out["fell"].update(r["fell"])
            out["open"] += r["open"]
            out["steps"] = r["steps"]
    return out


def closure_descent(points: dict[Rat, int], min_top: int) -> Counter[int]:
    """For the points of a closure whose preperiod p is at least `min_top` + 1 (for an ether tail, the defect has its
    top at cell p - 1 >= `min_top`): the first even step at which the preperiod falls below p, counted."""
    out: Counter[int] = Counter()
    for x in points:
        p = x[0]
        if p - 1 < min_top:
            continue
        y, t = x, 0
        while True:
            y, t = h2(y), t + 2
            if y[0] - 1 < p - 1:
                out[t] += 1
                break
    return out


# ---- reports --------------------------------------------------------------------------------------------------------


def report_heads(max_h: int) -> None:
    """Item (a): the head counts, against 2^ceil(h / 2), and the heads of the stripe tree."""
    for h in range(1, max_h + 1):
        print(f"h = {h}: {head_count(h)} heads, 2^ceil(h/2) = {2 ** ((h + 1) // 2)}")
    for h in range(2, min(max_h, 20) + 1, 2):
        d = (h + 1) // 2 - 1
        print(f"heads of {h} cells among the points of K with a stripe tail within {d} applications of H^2: "
              f"{stripe_heads(h, d)} of {2 ** (d + 1)}")


def report_families(max_q: int, max_n: int, exact_q: list[int], pruned_q: list[int], max_pre: int, levels: int,
                    search: str | None, depth: int) -> None:
    """Item (b): periodic points, purely periodic points, the closure of each tail period and the search."""
    periodic = zoo_points(max_n, max([max_q] + exact_q + pruned_q))
    print(f"periodic points of H^2 in K with itinerary period <= {max_n} and tail period <= "
          f"{max([max_q] + exact_q + pruned_q)}: {len(periodic)}")
    for (q, bg, n), v in sorted(Counter((x[1], ring_class(x), itinerary_period(x)) for x in periodic).items()):
        print(f"  tail period {q}, background {bg}, itinerary period {n}: {v} points, preperiods up to "
              f"{max(x[0] for x in periodic if x[1] == q)}")
    for q in range(1, max_q + 1):
        pts = purely_periodic(q)
        landed = Counter((ring_class(x), landing(x, periodic)[1]) for x, r in pts if r["how"] == 1)
        print(f"q = {q}: {len(pts)} purely periodic points of K of least period q "
              f"({sum(r['how'] == -1 for _, r in pts)} undecided); (background, H^2 steps to a periodic point): "
              f"{dict(landed)}", flush=True)
    found: set[Rat] = set()
    if search:
        found, how = search_points(search, depth)
        print(f"search to depth {depth}: {len(found)} points of K (hits by outcome of the exact run {dict(how)}); by "
              f"least period {dict(sorted(Counter(x[1] for x in found).items()))}; denominators "
              f"{dict(sorted(Counter(denominator(x) for x in found).items()))}; stripe tails "
              f"{sum(is_stripe(x) for x in found)}", flush=True)
    for big_q in sorted(set(range(1, max_q + 1)) | set(exact_q) | set(pruned_q)):
        seeds = {x for x in periodic if big_q % x[1] == 0 and not is_stripe(x)}
        hits = {x for x in found if big_q % x[1] == 0 and not is_stripe(x)}
        line = f"Q = {big_q}: {len(seeds)} periodic points (not stripes)"
        if big_q in pruned_q:
            rows, _, _ = closure_levels(seeds, big_q, levels)
            cl = closure(seeds, big_q, max_pre=max_pre, max_points=5_000_000)
            line += (f"; points per level through level {levels} {[r['points'] for r in rows]}, largest preperiod "
                     f"{max(r['max_pre'] for r in rows)}; closure through "
                     f"points of preperiod <= {max_pre}: {len(cl)} points, deepest level "
                     f"{max(cl.values(), default=-1)}")
        else:
            rows, _, kept = closure_levels(seeds, big_q, 200, depth) if seeds else ([], set(), set())
            line += (f"; closure {sum(r['points'] for r in rows)} points, depth {len(rows) - 1}, largest preperiod "
                     f"{max((r['max_pre'] for r in rows), default=-1)}; points per level "
                     f"{[r['points'] for r in rows]}, of which with a least tail period below {big_q} "
                     f"{[r['shorter'] for r in rows]}")
            if seeds and big_q <= 21:  # the powers of the ring map take 2^Q (Q + 1) words of 8 bytes
                tau = ring_transients(big_q).get((7, 4), 0)
                line += f"; longest ring transient into the ether {tau}, depth bound 14 + {(tau + 1) // 2}"
            cl = dict.fromkeys(kept, 0)
        if search:
            inrange = {x for x in cl if x[0] + x[1] <= depth}
            line += (f"; search points with p + q <= {depth}: {len(hits)} (by least period "
                     f"{dict(sorted(Counter(x[1] for x in hits).items()))}), the closure's: {len(inrange)}, equal: "
                     f"{inrange == hits}")
        print(line, flush=True)


def report_descent(min_h: int, max_h: int) -> None:
    """Item (c): the descent census by head, and the descent of the points of the closure of period 7."""
    seeds = {x for x in zoo_points(4, 7) if not is_stripe(x)}
    falls = closure_descent(closure(seeds, 7), 26)
    print(f"closure of period 7: {sum(falls.values())} points with a preperiod of at least 27; the even step at which "
          f"the preperiod first falls: {dict(sorted(falls.items()))}")
    for h in range(min_h, max_h + 1):
        r = descent_census(h)
        broke, fell = r["broke"], r["fell"]
        last = max(list(broke) + list(fell))
        late = sum(v for t, v in broke.items() if t > 2 * h) + sum(v for t, v in fell.items() if t > 2 * h)
        print(f"h = {h}: {r['leaves']} heads, {sum(broke.values())} break K (latest at step {max(broke, default=0)}), "
              f"{sum(fell.values())} descend (latest at step {max(fell, default=0)}), {r['open']} open at step "
              f"{r['steps']}; resolved by step {last} = {last / h:.2f} h; still running at step 2h: {late + r['open']}",
              flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="cmd", required=True)
    p_heads = sub.add_parser("heads")
    p_heads.add_argument("--max-h", type=int, default=24)
    p_fam = sub.add_parser("families")
    p_fam.add_argument("--max-q", type=int, default=14)
    p_fam.add_argument("--max-n", type=int, default=16)
    p_fam.add_argument("--exact-q", type=int, nargs="*", default=[21])
    p_fam.add_argument("--pruned-q", type=int, nargs="*", default=[28])
    p_fam.add_argument("--max-pre", type=int, default=100)
    p_fam.add_argument("--levels", type=int, default=13, help="levels of the closures of --pruned-q counted exactly")
    p_fam.add_argument("--search", default=None, help="the output of held_shift_search.c")
    p_fam.add_argument("--depth", type=int, default=64)
    p_desc = sub.add_parser("descent")
    p_desc.add_argument("--min-h", type=int, default=28)
    p_desc.add_argument("--max-h", type=int, default=36)
    args = parser.parse_args()
    if args.cmd == "heads":
        report_heads(args.max_h)
    elif args.cmd == "families":
        report_families(args.max_q, args.max_n, args.exact_q, args.pruned_q, args.max_pre, args.levels, args.search,
                        args.depth)
    else:
        report_descent(args.min_h, args.max_h)


if __name__ == "__main__":
    main()
