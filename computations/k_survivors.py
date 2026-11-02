"""The points of K with an ether tail: every head of up to 56 cells on the tree of K is run until it breaks K or its
orbit repeats, and the true points are compared with the backward closure of the periodic points they fall onto.

Write H(U) = (U >> 1) xor (U or (U << 1)) for the held map and K for the 2-adic U with H^t(U) odd at every odd t. The
ether is the cycle of four states of the held map on a ring of seven cells; at the alignment (a, o) its cell j is
`ether_certificate.eth(a, j + o)`. A half U whose cells from p on are the ether at (a, o) is the ether xor its defect
D_0 < 2^p, and its orbit is the ether at phase a + t xor the defect D_t, which follows `ether_certificate.step`.

A head of h cells can start a point of K only on the tree of `ether_k_tree`: both values at an even cell, the one
value at an odd cell d that keeps bit 0 of H^d odd. Past the head the cells are the ether, so at each odd d >= h the
condition of K is a test, not a choice. A head is a *true point* when the whole half is in K. This module decides that
for every head by three filters, each exact:

1. `tree_survivors(head, a, o)`: the tree over the cells 0 .. head - 1 and the tests at the odd steps head .. 63, on
   numbers of 64 cells held as numpy words. Bit 0 at step d reads only the cells 0 .. d, so 64 cells decide every odd
   step below 64.
2. `wide_survivors(x, a, o, cells)`: the same tests at the odd steps below `cells`, on numbers of `cells` cells held as
   rows of numpy words.
3. `settle(d0, a, o, max_steps)`: the exact run of the defect, with no bound on its top, until an odd step with bit 0
   equal to 0 (a break of K) or a repeat of the defect at two steps that are multiples of 4 (the orbit is then periodic,
   with a period that is a multiple of 4 and so even, and every odd step of the cycle has been tested: the half is in
   K). Each true point is so a finite certificate.

`classify(head)` runs the three filters at all 28 alignments. Every true point whose tail from cell p <= head on is the
ether is a leaf of the tree at `head` (the tree keeps every head that passes the odd steps below `head`), so one run at
the largest head counts the true points for every p <= head, by the bit length of D_0.

- `cycle_states`, `orbit_key`, `itinerary_period`, `periodic_seeds`: the cycle a true point falls onto and the periodic
  points of K on it.
- `preimage(d, a, o, c)`, `k_preimages(d, a, o)`, `backward_closure(seeds)`: the preimages under H and, in K, under
  H^2 that keep an ether tail, and the closure of a set of points of K under them.
- `closure_shape`, `monotone_counts`: the depth, branching and repeats of the closure, and how its defects rise.
- `tail7_closure(seeds)`: the same closure over every tail of period 7, to compare with the search of `held_shift`.
- `lean_roots`, `lean_section32()`: the census section of `Rule30Open.PeriodTwo.EtherKTree32`, the tree of
  `ether_k_tree` on heads of 32 cells with the bound 39, cut at cell 6 into eight kernel checks per alignment.

    python -m computations.k_survivors --head 40                # heads of up to 40 cells, about 15 s
    python -m computations.k_survivors --head 48                # about 4 minutes
    python -m computations.k_survivors --head 52                # about 20 minutes, 0.5 GB
    python -m computations.k_survivors --head 56                # about 2 hours, 0.6 GB
"""

from __future__ import annotations

import argparse
import resource
import sys
from collections import Counter

import numpy as np
from tqdm.auto import tqdm

from computations.ether_certificate import background, eth
from computations.ether_k_tree import ether_tail
from computations.no_k_tails16 import column_after

U64 = np.uint64
ONE = U64(1)
CELLS = 256  # cells of the wide filter: it tests the odd steps below 256
MAX_STEPS = 200_000  # steps of the exact run before a head is left undecided
WIDE_CHUNK = 1 << 20  # numbers per call of the wide filter, which holds about 5 arrays of 4 words per number
WIDE = 4096  # cells of the background held for the exact run; a defect whose top passes WIDE - 16 is left undecided


def held_words(x: np.ndarray) -> np.ndarray:
    """One step of the held map on numbers of 64 cells, one per entry (n,); the top cell reads a 0 above it, so cell j
    of H^t is right while j + t < 64: (n,)."""
    return (x >> ONE) ^ (x | (x << ONE))


def held_rows(x: np.ndarray) -> np.ndarray:
    """One step of the held map on numbers of 64 W cells, word k the cells 64 k .. 64 k + 63 (n, W); the top cell reads
    a 0 above it: (n, W)."""
    up = x >> ONE  # (n, W)
    up[:, :-1] |= x[:, 1:] << U64(63)
    down = x << ONE  # (n, W)
    down[:, 1:] |= x[:, :-1] >> U64(63)
    return up ^ (x | down)


def bit0_after(x: np.ndarray, d: int) -> np.ndarray:
    """Bit 0 of H^d of each number of 64 cells (n,), for d < 64: (n,) of 0 and 1."""
    for _ in range(d):
        x = held_words(x)
    return x & ONE


def extend(x: np.ndarray, head: int, start: int, stop: int) -> np.ndarray:
    """The tree of K from the cell `start` to the cell `stop` - 1 on the nodes x (n,), numbers of 64 cells with the
    cells below `start` chosen, the cells start .. head - 1 at 0 and the ether from `head` on: both values at an even
    cell of the head, the value that keeps bit 0 of H^d odd at an odd cell d of the head, and the test of that bit at an
    odd cell d >= head: (m,)."""
    for d in range(start, stop):
        if d < head and d % 2 == 0:
            x = np.concatenate([x, x | (ONE << U64(d))])  # (2 n,)
        elif d < head:
            x = x | ((bit0_after(x, d) ^ ONE) << U64(d))  # (n,): the value of cell d that keeps bit 0 odd
        elif d % 2 == 1:
            x = x[bit0_after(x, d) == ONE]  # (m,)
    return x


def tree_survivors(head: int, a: int, o: int, steps: int = 63, chunk: int = 1 << 18) -> np.ndarray:
    """The leaves of the tree of K over the heads of `head` cells under the ether at (a, o) that pass the odd steps
    head .. `steps` (< 64), as the numbers of 64 cells that hold the head and the ether above it, sorted: (m,). The
    tree is grown to a cell with at most `chunk` nodes and finished on groups of `chunk` / 2^(the rest / 2) nodes, so
    that no array holds more than about `chunk` numbers."""
    assert head <= 64 and steps < 64
    x = np.array([background(a, o, 64) & ~((1 << head) - 1)], dtype=U64)  # (1,): no cell of the head chosen
    split = 0
    while split < head and 2 ** ((split + 1) // 2) < chunk:
        split += 1
    x = extend(x, head, 0, split)  # (2^ceil(split / 2),)
    group = max(1, chunk >> ((head - split + 1) // 2))
    parts = [extend(x[i:i + group], head, split, steps + 1) for i in range(0, len(x), group)]
    return np.sort(np.concatenate(parts))


def as_rows(values: list[int], words: int) -> np.ndarray:
    """Python integers as rows of 64-bit words, word k the cells 64 k .. 64 k + 63: (len(values), words)."""
    mask = (1 << 64) - 1
    return np.array([[(v >> (64 * k)) & mask for k in range(words)] for v in values], dtype=U64).reshape(-1, words)


def wide_survivors(x: np.ndarray, a: int, o: int, cells: int = CELLS) -> tuple[np.ndarray, Counter[int]]:
    """The numbers of 64 cells x (n,), each a head and the ether at (a, o) above it, whose half passes every odd step
    below `cells`: (m,); and for the others how many first have bit 0 equal to 0 at each odd step."""
    assert cells % 64 == 0
    words = cells // 64
    rows = np.empty((len(x), words), dtype=U64)  # (n, words)
    rows[:, 0] = x
    tail = background(a, o, cells)
    rows[:, 1:] = as_rows([tail >> 64], words - 1)  # the ether above cell 63
    keep = np.arange(len(x))  # (n,): the index in x of each row
    broke: Counter[int] = Counter()
    for t in range(1, cells):
        rows = held_rows(rows)
        if t % 2 == 1:
            ok = (rows[:, 0] & ONE) == ONE  # (n,)
            if not ok.all():
                broke[t] += int((~ok).sum())
            rows, keep = rows[ok], keep[ok]
    return x[keep], broke


BACK = [[background(a, o, WIDE) for o in range(7)] for a in range(4)]  # the ether of WIDE cells by phase and offset


def dstep(d: int, phase: int, o: int) -> int:
    """One step of the defect d at the given phase and offset, exact for every top below WIDE - 2: H of (d xor the
    ether at the phase) xor the ether at the next phase, on the cells up to the top of d plus 2."""
    width = d.bit_length() + 3
    mask = (1 << width) - 1
    x = d ^ (BACK[phase % 4][o] & mask)
    return (((x >> 1) ^ (x | (x << 1))) ^ BACK[(phase + 1) % 4][o]) & (mask >> 1)


def settle(d0: int, a: int, o: int, max_steps: int = MAX_STEPS) -> dict[str, int]:
    """The exact run of the half with defect d0 at the alignment (a, o). Returns `how` (0 a break of K, 1 a repeat, -1
    undecided), `step` (of the break, or of the second visit of the repeat), `start` and `period` of the cycle (multiples
    of 4), `top` (the highest defect cell over the run, -1 for the ether) and `cycle_top` (over the cycle)."""
    seen: dict[int, int] = {}
    d, t, top = d0, 0, d0.bit_length() - 1
    while t <= max_steps and top < WIDE - 16:
        if t % 2 == 1 and (d & 1) == int(eth(a + t, o)):
            return {"how": 0, "step": t, "start": -1, "period": 0, "top": top, "cycle_top": -1}
        if t % 4 == 0:
            if d in seen:
                start = seen[d]
                ctop, e = -1, d
                for k in range(t - start):
                    ctop = max(ctop, e.bit_length() - 1)
                    e = dstep(e, a + start + k, o)
                return {"how": 1, "step": t, "start": start, "period": t - start, "top": top, "cycle_top": ctop}
            seen[d] = t
        d = dstep(d, a + t, o)
        top = max(top, d.bit_length() - 1)
        t += 1
    return {"how": -1, "step": t, "start": -1, "period": 0, "top": top, "cycle_top": -1}


def cycle_states(d0: int, a: int, o: int, r: dict[str, int]) -> list[tuple[int, int]]:
    """The states (phase mod 4, defect) of the cycle that the true point d0 falls onto, from its first step on."""
    d = d0
    for t in range(r["start"]):
        d = dstep(d, a + t, o)
    out = []
    for k in range(r["period"]):
        out.append(((a + r["start"] + k) % 4, d))
        d = dstep(d, a + r["start"] + k, o)
    assert d == out[0][1]
    return out


def orbit_key(states: list[tuple[int, int]], o: int) -> tuple[int, int, int]:
    """The periodic orbit through the cycle `states` at offset o: (o, phase, defect) of its least state."""
    phase, d = min(states)
    return o, phase, d


def least_period(seq: list[int]) -> int:
    """The least q > 0 with seq[i + q] = seq[i] cyclically (q divides len(seq))."""
    n = len(seq)
    return next(q for q in range(1, n + 1) if n % q == 0 and all(seq[i] == seq[(i + q) % n] for i in range(n)))


def itinerary_period(states: list[tuple[int, int]], o: int) -> int:
    """The least period of the itinerary (bit 0 at the even steps) on the cycle `states`, which starts at a step that
    is a multiple of 4 (`cycle_states`)."""
    bits = [(d & 1) ^ int(eth(phase, o)) for phase, d in states]
    assert all(bits[1::2])  # the odd steps of a point of K
    return least_period(bits[0::2])


def preimage(d: int, a: int, o: int, c: int) -> int:
    """The half U with H(U) = V and cell 0 of U equal to c, where V is the ether at (a, o) xor the defect d: the defect
    of U against the ether at phase a - 1 and offset o when U has an ether tail, else -1. U is read off V cell by cell,
    U(j + 1) = V(j) xor (U(j) or U(j - 1)) with U(-1) = 0. The ether at phase a - 1 obeys the same recurrence at every
    cell j >= 1 where V is the ether, so U has an ether tail exactly when U agrees with it on two adjacent cells at some
    j >= max(p, 1), p the bit length of d; the pair (U(j), U(j - 1)) with j mod 7 has 28 values, so if that happens it
    happens by j = p + 30."""
    p = d.bit_length()
    top = p + 32
    v = [((d >> j) & 1) ^ int(eth(a, j + o)) for j in range(top + 1)]
    e = [int(eth(a - 1, j + o)) for j in range(top + 2)]
    u = [c]
    for j in range(top):
        u.append(v[j] ^ (u[j] | (u[j - 1] if j > 0 else 0)))
    for j0 in range(max(p, 1), top):
        if u[j0] == e[j0] and u[j0 - 1] == e[j0 - 1]:
            return sum((u[j] ^ e[j]) << j for j in range(j0))
    return -1


def k_preimages(d: int, a: int, o: int) -> list[int]:
    """The defects (against the ether at phase a - 2, offset o) of the points U of K with H^2(U) = V that have an ether
    tail, for V the ether at (a, o) xor d in K. U is in K exactly when V is and bit 0 of H(U) is 1, so H(U) is the
    preimage of V with cell 0 equal to 1 and U is either preimage of it: two points of K, of which those with an ether
    tail are returned."""
    w = preimage(d, a, o, 1)
    if w < 0:
        return []
    return [u for u in (preimage(w, a - 1, o, 0), preimage(w, a - 1, o, 1)) if u >= 0]


def backward_closure(seeds: set[tuple[int, int, int]], max_cells: int = 4096) -> set[tuple[int, int, int]]:
    """The points of K with an ether tail whose orbit under H^2 reaches one of the `seeds` (a mod 4, o, defect), by
    taking the preimages of `k_preimages` until none is new. Raises if a defect passes `max_cells` cells."""
    out = set(seeds)
    todo = list(seeds)
    while todo:
        a, o, d = todo.pop()
        for u in k_preimages(d, a, o):
            key = ((a - 2) % 4, o, u)
            if key not in out:
                assert u.bit_length() <= max_cells
                out.add(key)
                todo.append(key)
    return out


def periodic_seeds(points: list[tuple[int, int, int, dict[str, int]]]) -> set[tuple[int, int, int]]:
    """The periodic points of K that the true points fall onto: the states of each cycle at the steps of the same parity
    as the true point (those are in K), as (phase, offset, defect)."""
    out = set()
    for a, o, d0, r in points:
        for k, (phase, d) in enumerate(cycle_states(d0, a, o, r)):
            if k % 2 == 0:
                out.add((phase, o, d))
    return out


def classify(head: int, cells: int = CELLS, max_steps: int = MAX_STEPS,
             alignments: list[tuple[int, int]] | None = None) -> dict[str, object]:
    """The three filters at every alignment: the leaves of the tree, the survivors of step 63 and of the wide filter,
    the late breaks (how many at each odd step above 63), and the true points as (a, o, d0, settling record)."""
    if alignments is None:
        alignments = [(a, o) for a in range(4) for o in range(7)]
    out: dict[str, object] = {"leaves": 0, "survive63": 0, "survive_wide": 0, "late_breaks": Counter(), "points": [],
                              "undecided": []}
    for a, o in tqdm(alignments, desc=f"heads of {head} cells", file=sys.stderr, leave=False):
        out["leaves"] += 2 ** ((head + 1) // 2)
        low = (1 << head) - 1
        surv = tree_survivors(head, a, o)  # (m,)
        out["survive63"] += len(surv)
        parts = [wide_survivors(surv[i:i + WIDE_CHUNK], a, o, cells) for i in range(0, len(surv), WIDE_CHUNK)]
        wide = np.concatenate([w for w, _ in parts] + [np.zeros(0, dtype=U64)])  # (k,)
        out["survive_wide"] += len(wide)
        for _, broke in parts:
            out["late_breaks"].update(broke)
        eth_head = background(a, o, head)
        for n in wide:
            d0 = (int(n) & low) ^ eth_head
            r = settle(d0, a, o, max_steps)
            if r["how"] == 0:
                out["late_breaks"][r["step"]] += 1
            elif r["how"] == 1:
                out["points"].append((a, o, d0, r))
            else:
                out["undecided"].append((a, o, d0, r))
    return out


def monotone_counts(points: set[tuple[int, int, int]]) -> tuple[Counter[int], Counter[int]]:
    """For points of K (phase, offset, defect): how many raise the top of their defect by each amount over its top at
    step 0 during the exact run (`settle`), and how many change the bit length of the defect by each amount under H^2."""
    rise: Counter[int] = Counter()
    grow: Counter[int] = Counter()
    for a, o, d in points:
        rise[settle(d, a, o)["top"] - (d.bit_length() - 1)] += 1
        grow[dstep(dstep(d, a, o), a + 1, o).bit_length() - d.bit_length()] += 1
    return rise, grow


def closure_shape(closure: set[tuple[int, int, int]], seeds: set[tuple[int, int, int]]) -> dict[str, object]:
    """The shape of the backward closure: the latest repeat of an exact run, the most applications of H^2 a point needs
    to reach a periodic point, how many points have 0, 1 or 2 preimages in K with an ether tail, and the longest run of
    ether cells strictly inside a defect."""
    def forward(k: tuple[int, int, int]) -> tuple[int, int, int]:
        a, o, d = k
        return (a + 2) % 4, o, dstep(dstep(d, a, o), a + 1, o)

    depth = 0
    for k in closure:
        n = 0
        while k not in seeds:
            k, n = forward(k), n + 1
        depth = max(depth, n)
    gaps = [max((len(r) for r in bin(d)[2:].split("1")), default=0) for _, _, d in closure]
    return {"repeat": max(settle(d, a, o)["step"] for a, o, d in closure), "depth": depth,
            "preimages": Counter(len(k_preimages(d, a, o)) for a, o, d in closure), "gap": max(gaps)}


def tail_cell(point: tuple[tuple[int, ...], int], j: int) -> int:
    """Cell j of a half given as (its cells 0 .. q + 6, its preperiod q), periodic with period 7 from q on."""
    cells, q = point
    return cells[j] if j < len(cells) else cells[q + (j - q) % 7]


def periodic7(cells: list[int], start: int) -> tuple[tuple[int, ...], int]:
    """The half whose cells are `cells` (at least start + 7 of them), periodic with period 7 from `start` on, as (its
    cells 0 .. q + 6, its least preperiod q)."""
    q = start
    while q > 0 and cells[q - 1] == cells[q + 6]:
        q -= 1
    return tuple(cells[:q + 7]), q


def preimage7(point: tuple[tuple[int, ...], int], c: int) -> tuple[tuple[int, ...], int] | None:
    """The half U with H(U) = V and cell 0 equal to c, for V periodic with period 7 from its preperiod q, when U is
    periodic with period 7 from some cell on, else None. From cell q on the pair (U(j), U(j - 1)) with j mod 7 runs
    through 28 states, so U is periodic from cell q + 28 on with a period that is a multiple of 7, and it is 7 exactly
    when 7 cells repeat over the next 77."""
    _, q = point
    top = q + 112
    u = [c]
    for j in range(top):
        u.append(tail_cell(point, j) ^ (u[j] | (u[j - 1] if j > 0 else 0)))
    if any(u[j] != u[j + 7] for j in range(q + 28, top - 6)):
        return None
    return periodic7(u, q + 28)


def tail7_closure(seeds: set[tuple[int, int, int]]) -> set[tuple[tuple[int, ...], int]]:
    """The points of K with a tail of period 7 (the ether or any other word) whose orbit under H^2 reaches one of the
    `seeds` (a mod 4, o, defect against the ether), each as (its cells 0 .. q + 6, its least preperiod q)."""
    out = set()
    for a, o, d in seeds:
        n = d.bit_length() + 7
        u = d ^ background(a, o, n + 7)
        out.add(periodic7([(u >> j) & 1 for j in range(n + 7)], n))
    todo = list(out)
    while todo:
        w = preimage7(todo.pop(), 1)  # H(U) for the points U of K over this one
        if w is None:
            continue
        for u in (preimage7(w, 0), preimage7(w, 1)):
            if u is not None and u not in out:
                assert u[1] < 4096
                out.add(u)
                todo.append(u)
    return out


LEAN_HEAD = 32  # the cells of a head in `EtherKTree32`
LEAN_BOUND = 39  # its bound on the defect: the head plus 7
LEAN_SPLIT = 6  # the cell at which its tree is cut into kernel checks: 2^3 subtrees per alignment


def lean_roots(a: int, o: int, head: int = LEAN_HEAD, split: int = LEAN_SPLIT) -> list[tuple[int, int, str]]:
    """The walk of the Lean `treeWith` over the cells 0 .. split - 1 at the alignment (a, o): every node as (cell d,
    number n, the Lean term that proves `treeWith leaf (head - d) d n = true` from the subtree checks)."""
    def node(d: int, n: int) -> tuple[str, list[int]]:
        if d == split:
            return "{}", [n]
        m = head - d - 1
        if d % 2 == 0:
            n1 = n | (1 << d)
            t0, r0 = node(d + 1, n)
            t1, r1 = node(d + 1, n1)
            return f"(treeWith_even_ok _ {m} {d} {n} {n1} (by decide) (by decide) {t0} {t1})", r0 + r1
        n1 = n if column_after(d, n) else n | (1 << d)
        t, r = node(d + 1, n1)
        return f"(treeWith_odd_ok _ {m} {d} {n} {n1} (by decide) (by decide +kernel) {t})", r
    term, roots = node(0, ether_tail(head, a, o))
    return [(split, n, term) for n in roots]


def lean_section32(head: int = LEAN_HEAD, bound: int = LEAN_BOUND, split: int = LEAN_SPLIT, rounds: int = 32,
                   fuel: int = 16) -> str:
    """The census section of `EtherKTree32`: one kernel check per subtree at the cell `split`, and per alignment the
    walk over the cells below `split` that joins them."""
    out = []
    for a in range(4):
        for o in range(7):
            roots = lean_roots(a, o, head, split)
            leaf = f"(etherLeaf {rounds} {head} {bound} {fuel} {a} {o})"
            for k, (d, n, _) in enumerate(roots):
                out.append(f"theorem ktree32_{a}_{o}_{k} : treeWith {leaf} {head - d} {d} {n} = true := by\n"
                           f"  decide +kernel")
            term = roots[0][2]
            for k in range(len(roots)):
                term = term.replace("{}", f"ktree32_{a}_{o}_{k}", 1)
            out.append(f"theorem ktree32_{a}_{o} : etherTreeOK {rounds} {head} {bound} {fuel} {a} {o} = true := by\n"
                       f"  unfold etherTreeOK\n"
                       f"  rw [show etherTail {head} {a} {o} = {ether_tail(head, a, o)} by decide +kernel]\n"
                       f"  exact {term}")
    cases = "\n".join(f"  | {a}, {o}, _, _ => ktree32_{a}_{o}" for a in range(4) for o in range(7))
    out.append(f"theorem ktree32 (a o : Nat) (ha : a < 4) (ho : o < 7) : etherTreeOK {rounds} {head} {bound} {fuel} a o "
               f"= true :=\n  match a, o, ha, ho with\n{cases}\n  | a + 4, _, ha, _ => absurd ha (by omega)\n"
               f"  | _, o + 7, _, ho => absurd ho (by omega)")
    return "\n\n".join(out)


def report(head: int, cells: int, max_steps: int) -> None:
    """Print the census of the true points of K with an ether tail from cell p <= head on."""
    r = classify(head, cells, max_steps)
    points = r["points"]
    late: Counter[int] = r["late_breaks"]
    print(f"heads of {head} cells: {r['leaves']} leaves, {r['survive63']} pass step 63, {r['survive_wide']} pass "
          f"every odd step below {cells}; {sum(late.values())} break K after step 63 (latest at step {max(late, default=0)}), "
          f"{len(points)} true points, {len(r['undecided'])} undecided")
    by_p = Counter(d0.bit_length() for _, _, d0, _ in points)
    run = 0
    print("p: true points with D_0 of exactly p cells, and with at most p cells")
    for p in range(head + 1):
        run += by_p.get(p, 0)
        if by_p.get(p, 0):
            print(f"  {p}: {by_p[p]} ({run})")
    by_align = Counter((a, o) for a, o, _, _ in points)
    print("by alignment (a, o): " + ", ".join(f"{k}: {v}" for k, v in sorted(by_align.items())))
    orbits: Counter[tuple[int, int, int]] = Counter()
    info: dict[tuple[int, int, int], tuple[int, int, int]] = {}
    for a, o, d0, rr in points:
        states = cycle_states(d0, a, o, rr)
        key = orbit_key(states, o)
        orbits[key] += 1
        info[key] = (rr["period"], itinerary_period(states, o), rr["cycle_top"])
    print(f"{len(orbits)} periodic orbits reached (offset, phase, least defect: points; period, itinerary period, "
          f"top of the cycle):")
    for key, v in sorted(orbits.items()):
        print(f"  {key}: {v}; {info[key]}")
    print(f"latest repeat at step {max((rr['step'] for *_, rr in points), default=0)}, highest top "
          f"{max((rr['top'] for *_, rr in points), default=-1)}")
    seeds = periodic_seeds(points)
    closure = backward_closure(seeds)
    found = {(a, o, d0) for a, o, d0, _ in points}
    inside = {k for k in closure if k[2].bit_length() <= head}
    print(f"{len(seeds)} periodic points of K among them; their backward closure has {len(closure)} points, defects of "
          f"up to {max(k[2].bit_length() for k in closure)} cells; the true points are the closure up to {head} cells: "
          f"{found == inside}")
    print("closure by p: " + ", ".join(f"{p}: {v}" for p, v in
                                       sorted(Counter(k[2].bit_length() for k in closure).items())))
    shape = closure_shape(closure, seeds)
    print(f"closure: every point repeats by step {shape['repeat']} and reaches a periodic point within {shape['depth']} "
          f"applications of H^2; points by their number of preimages in K with an ether tail: "
          f"{dict(sorted(shape['preimages'].items()))}; longest run of ether cells inside a defect {shape['gap']}")
    print("closure by alignment: " + ", ".join(f"{k}: {v}" for k, v in sorted(Counter(k[:2] for k in closure).items())))
    rise, grow = monotone_counts(closure)
    print("closure: rise of the top over the run: " + ", ".join(f"{k}: {v}" for k, v in sorted(rise.items())))
    print("closure: change of p under H^2: " + ", ".join(f"{k}: {v}" for k, v in sorted(grow.items())))
    tails = tail7_closure(seeds)
    print(f"with any tail of period 7 the closure has {len(tails)} points, {sum(q <= 57 for _, q in tails)} of them "
          f"with a preperiod of at most 57 (the search of item 7 of the shift model finds 278 with denominator 127)")
    print(f"peak memory {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2 ** 20:.2f} GB")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--head", type=int, default=40)
    parser.add_argument("--cells", type=int, default=CELLS)
    parser.add_argument("--max-steps", type=int, default=MAX_STEPS)
    args = parser.parse_args()
    report(args.head, args.cells, args.max_steps)


if __name__ == "__main__":
    main()
