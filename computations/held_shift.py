"""The period-two condition as a full shift, its periodic points, and its rational points.

Write H(U) = (U >> 1) xor (U or (U << 1)), the held map of `held_map`. Let K be the set of 2-adic integers U with
H^t(U) odd at every odd step t. Bit 0 of H^t(U) is bit t of U XOR a function of the lower bits, so the condition at
an odd step fixes bit t, and K is the graph of a map from the free bits u_0, u_2, u_4, ... (`forced_halves`). The
itinerary of U in K is the sequence of bit 0 of H^(2s)(U), s = 0, 1, ...; it is triangular in the free bits, so it is a
bijection from K onto {0, 1}^N, and the itinerary of H^2(U) is the shift of the itinerary of U. So (K, H^2) is the
one-sided full 2-shift (`itinerary`), and a positive integer U is a point of K with a vacuum tail.

A point of K that is periodic under the shift is temporally periodic: its column 0 has period 2n. The columns left of
it follow by the sideways recursion Y_(k+1)(t) = Y_k(t + 1) xor (Y_k(t) or Y_(k-1)(t)) on a finite set of cyclic
words, so the half is eventually periodic in space, a 2-adic rational: a domain. `domain` computes its preperiod and
period, and `zoo` all 2^n of them for each n. A block other than 01 enters through the kicked map
`kicked_step`: Rule 30 left of a column replaced by its effective boundary c'(t) = b(t) and b(t + 1), with cell -1
fixed at the black phases of the block b and free at the white phases (the checks of `left_halves`).

`rational_points` lists the points of K whose binary expansion has preperiod p and period q with p + 2q below a
depth, found along the tree of K, and `preperiod` follows each one's itinerary: every point found is preperiodic.
A rational point has a finite head and a tail that is periodic in space; far from the low end the tail evolves as the
held map on a ring (`ring_next`, `ring_cycle`), so it is periodic in time after a transient. `defect_tops` follows the
top of the defect, the highest cell that differs from that ring evolution: it climbs one cell at a step exactly where
the background reads 0 just above it, and never faster. Where the background has a column that stays 1 (only the two
stripes) the top is confined, so the orbit is eventually periodic (`stripe_window`); `attractors` lists which ring
attractor the tail of each rational point of K reaches. `degree_profile` gives the algebraic degree and term count of the forced bit u_(2s+1) as a polynomial over GF(2)
in the free bits u_0, .., u_(2s).

    python -m computations.held_shift --zoo 11              # the periods of the domains, n up to 11, about 1 min
    python -m computations.held_shift --rational 36         # the rational points of K with p + 2q <= 36, 20 s
    python -m computations.held_shift --degree 25           # algebraic degree of the forced bits
    python -m computations.held_shift --hits hits.txt       # verify the hits of held_shift_search.c
    python -m computations.held_shift --stripe 12           # defects on a stripe stay within one cell of the head
    python -m computations.held_shift --ether 6             # how far a defect climbs on the ether, 1500 steps
    python -m computations.held_shift --front 8 --rounds 20000   # a positive cycle of the front automaton, seconds
    python -m computations.held_shift --attractors 40       # the ring attractor of the tail of each rational point
    python -m computations.held_shift --zoo 8 --block 011   # the same for the kicked map of the block 011
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction

import numpy as np
from tqdm.auto import tqdm

ONE = np.uint64(1)


def held(U: int) -> int:
    """One step of the held map on a Python integer: Rule 30 left of a column held at 0, bit j the cell j + 1 away."""
    return (U >> 1) ^ (U | (U << 1))


def kicked_step(U: int, boundary: int) -> int:
    """One step of the held map beside a column whose effective boundary is `boundary`, 0 or 1: the cell next to the
    column reads (u_1 xor (u_0 or boundary))."""
    return (U >> 1) ^ (U | (U << 1) | boundary)


def bit0_after(V: np.ndarray, steps: int) -> np.ndarray:
    """Bit 0 of H^steps(V) for each V, from the bits 0 .. steps of V, which are all that it reads."""
    assert steps < 63, "the words hold 64 bits"
    W = V & np.uint64((1 << (steps + 1)) - 1)  # (n,)
    for s in range(steps):
        W = ((W >> ONE) ^ (W | (W << ONE))) & np.uint64((1 << (steps - s)) - 1)  # (n,)
    return W & ONE  # (n,)


def forced_halves(depth: int) -> np.ndarray:
    """The 2^ceil(depth / 2) residues modulo 2^depth of the points of K: the even bits are free, and each odd bit t is
    the one that makes bit 0 of H^t odd. Entry i has bit 2s equal to bit s of i."""
    assert depth < 63
    U = np.zeros(1, dtype=np.uint64)  # (1,)
    for n in range(depth):
        if n % 2 == 0:
            U = np.concatenate([U, U | np.uint64(1 << n)])  # (2 n_old,)
        else:
            U = U | ((bit0_after(U, n) ^ ONE) << np.uint64(n))  # (n_old,)
    return U  # (2^ceil(depth / 2),)


def itinerary(U: int, readings: int, mask_bits: int = 0) -> list[int]:
    """The first `readings` terms of the itinerary of U: bit 0 of H^(2s)(U). U is read modulo 2^(2 readings + mask_bits),
    which is exact for the terms asked."""
    bits = 2 * readings + 2 + mask_bits
    mask = (1 << bits) - 1
    V, out = U & mask, []
    for _ in range(readings):
        out.append(V & 1)
        V = held(held(V)) & mask
    return out


def eventual_period(sequence: list[int], longest: int = 100, settle: int = 3) -> tuple[int, int] | None:
    """The least (preperiod, period) with the period at most `longest` and the sequence periodic from the preperiod to
    its end, at least `settle` periods of it, or None."""
    for period in range(1, longest + 1):
        for pre in range(len(sequence) - settle * period + 1):
            if all(sequence[i] == sequence[i + period] for i in range(pre, len(sequence) - period)):
                return pre, period
    return None


def rotate(y: int, length: int, k: int) -> int:
    """The cyclic word y of `length` bits read k steps later: bit t of the result is bit (t + k) mod length of y."""
    k %= length
    return ((y >> k) | (y << (length - k))) & ((1 << length) - 1)


def column_zero(block: str, word: int, n: int) -> tuple[int, int]:
    """Column -1 and the effective boundary over n periods of `block`, as cyclic words of n len(block) bits, bit t the
    value at step t. The black phases of the block fix column -1 to the negation of the next value of the block; the
    white phases read the bits of `word`, in order."""
    period = len(block)
    column = boundary = reading = 0
    for t in range(n * period):
        now, after = int(block[t % period]), int(block[(t + 1) % period])
        boundary |= (now & after) << t
        if now:
            column |= (1 - after) << t
        else:
            column |= ((word >> reading) & 1) << t
            reading += 1
    assert reading == n * block.count("0")
    return column, boundary


def domain(block: str, word: int, n: int) -> tuple[list[int], list[int]]:
    """The left half that is temporally periodic with period n len(block) and reads `word` at the white phases of n
    periods of `block`, as the bits of its preperiod and of its period in space. Sideways: column k + 1 is column k one
    step later XOR (column k OR column k - 1), with the effective boundary as column -1 of the half."""
    length = n * len(block)
    full = (1 << length) - 1
    column, boundary = column_zero(block, word, n)
    prev, cur = boundary, column
    seen: dict[tuple[int, int], int] = {}
    bits: list[int] = []
    while (prev, cur) not in seen:
        seen[(prev, cur)] = len(bits)
        bits.append(cur & 1)
        prev, cur = cur, (rotate(cur, length, 1) ^ (cur | prev)) & full
    start = seen[(prev, cur)]
    pre, per = bits[:start], bits[start:]
    while pre and pre[-1] == per[-1]:  # the state includes column -1, so the first cells may still be periodic
        per = [pre.pop()] + per[:-1]
    for divisor in range(1, len(per)):
        if len(per) % divisor == 0 and per == per[:divisor] * (len(per) // divisor):
            per = per[:divisor]
            break
    return pre, per


def domain_integer(pre: list[int], per: list[int], bits: int) -> int:
    """The 2-adic integer with the given preperiod and period, truncated to `bits` bits."""
    seq = pre + per * (bits // len(per) + 1)
    return sum(bit << j for j, bit in enumerate(seq[:bits]))


def zoo(block: str, max_n: int) -> dict[int, Counter]:
    """For each n up to `max_n`, the count of periodic points by (spatial period) over the 2^(n w) words of the block's
    n w white readings, w the white phases per period."""
    white = block.count("0")
    census: dict[int, Counter] = {}
    for n in tqdm(range(1, max_n + 1), desc="n", leave=False):
        counts: Counter = Counter()
        for word in range(1 << (n * white)):
            pre, per = domain(block, word, n)
            counts[len(per)] += 1
        census[n] = counts
    return census


def rational_points(depth: int, steps: int) -> dict[Fraction, tuple[int, int]]:
    """The 2-adic rationals in K of preperiod p and period q with p + 2 q at most `depth`, as value -> (p, q) with p and
    q least, each checked to keep the condition through step `steps` in 2-adic arithmetic."""
    halves = forced_halves(depth)  # (2^ceil(depth / 2),)
    found: dict[Fraction, tuple[int, int]] = {}
    bits = steps + 2
    mask = (1 << bits) - 1
    for q in tqdm(range(1, depth // 2 + 1), desc="period", leave=False):
        for p in range(0, depth - 2 * q + 1):
            length = depth - p - q
            diff = ((halves >> np.uint64(p)) ^ (halves >> np.uint64(p + q))) & np.uint64((1 << length) - 1)  # (n,)
            for i in np.flatnonzero(diff == 0):
                u = int(halves[i])
                extension = u & ((1 << p) - 1)
                for pos in range(p, bits, q):
                    extension |= ((u >> p) & ((1 << q) - 1)) << pos
                extension &= mask
                V, alive = extension, True
                for t in range(steps):
                    if t % 2 == 1 and V & 1 == 0:
                        alive = False
                        break
                    V = held(V) & mask
                if alive:
                    pre, per = minimal_representation(extension, bits)
                    value = Fraction(extension & ((1 << pre) - 1)) - Fraction(
                        ((extension >> pre) & ((1 << per) - 1)) << pre, (1 << per) - 1)
                    found[value] = (pre, per)
    return found


def minimal_representation(value: int, bits: int) -> tuple[int, int]:
    """The least preperiod and period of the first `bits` bits of `value`, by total length, with two periods seen."""
    for total in range(1, bits // 3):
        for p in range(total):
            q = total - p
            if all(((value >> j) & 1) == ((value >> (j + q)) & 1) for j in range(p, bits - q)):
                return p, q
    raise AssertionError("no eventual period in the bits given")


def ring_next(word: int, length: int) -> int:
    """One step of the held map on a ring of `length` cells (bit j the cell j): new cell j is cell j + 1 xor
    (cell j or cell j - 1), indices mod `length`."""
    full = (1 << length) - 1
    above = ((word >> 1) | (word << (length - 1))) & full  # cell j + 1 at bit j
    below = ((word << 1) | (word >> (length - 1))) & full  # cell j - 1 at bit j
    return (above ^ (word | below)) & full


def ring_cycle(word: int, length: int) -> tuple[int, list[int]]:
    """The length of the transient and the cycle of states of the orbit of `word` on a ring of `length` cells."""
    seen: dict[int, int] = {}
    order: list[int] = []
    while word not in seen:
        seen[word] = len(order)
        order.append(word)
        word = ring_next(word, length)
    return seen[word], order[seen[word]:]


def cycle_class(word: int, length: int) -> tuple[int, int, int, int]:
    """(transient, cycle length, least primitive word, its period): the ring attractor that `word` reaches, named by
    the least rotation of the least primitive cell pattern on its cycle."""
    transient, cycle = ring_cycle(word, length)
    best = None
    for state in cycle:
        period = next(d for d in range(1, length + 1) if length % d == 0 and all(
            ((state >> i) & 1) == ((state >> (i + d)) & 1) for i in range(length - d)))
        block = state & ((1 << period) - 1)
        rotations = [((block >> r) | (block << (period - r))) & ((1 << period) - 1) for r in range(period)]
        candidate = (min(rotations), period)
        best = candidate if best is None or candidate < best else best
    assert best is not None
    return transient, len(cycle), best[0], best[1]


def replicate(word: int, length: int, width: int) -> int:
    """The first `width` bits of the periodic extension of the `length`-bit `word`: the copies at every multiple of
    `length` below `width`, doubled in number at each step."""
    out, filled = word, length  # the copies at 0, length, .., filled - length
    while filled < width:
        out |= out << filled
        filled *= 2
    return out & ((1 << width) - 1)


def defect_tops(head: int, preperiod: int, tail: int, length: int, steps: int) -> list[int]:
    """For the 2-adic integer with the `preperiod` bits of `head` and then `tail` repeated with period `length`, the
    highest cell, at each of the first `steps` steps, that differs from the ring evolution of the tail (cell j is
    ring cell (j - preperiod) mod length), or -1 if none. The cells are read to width preperiod + 2 steps."""
    width = preperiod + 2 * steps + 2 * length + 8
    mask = (1 << width) - 1
    x = ((head & ((1 << preperiod) - 1)) | (replicate(tail, length, width) << preperiod)) & mask
    ring, tops = tail, []
    shift = preperiod % length
    for t in range(steps):
        anchored = ((ring << shift) | (ring >> (length - shift))) & ((1 << length) - 1)  # bit j: ring cell j - p
        background = replicate(anchored, length, width)  # (width,) cell j is ring cell (j - preperiod) mod length
        tops.append((((x ^ background) & ((1 << (width - t - 2)) - 1))).bit_length() - 1)
        x = held(x) & mask
        ring = ring_next(ring, length)
    return tops


def stripe_window(max_head: int, steps_per_bit: int = 4) -> int:
    """The largest (top - preperiod) of the defect over every head of up to `max_head` bits on either stripe tail. The
    top cannot pass the cell just above the head, because a stripe has a 1 in every other column and the top climbs
    only above a 0, so the answer is 0 and a stripe tail gives an eventually periodic orbit."""
    worst = -1
    for tail in (0b01, 0b10):
        for p in range(1, max_head + 1):
            for head in range(1 << p):
                tops = defect_tops(head, p, tail, 2, steps_per_bit * p + 30)
                worst = max(worst, max(tops) - p)
    return worst


def ether_window(head_bits: int, steps: int) -> list[int]:
    """For the ether, the cycle of four states on seven cells and every rotation of each, the largest (top - preperiod)
    of the defect in each of the windows of steps [0, steps/5), [steps/5, steps/2) and [steps/2, steps), over every
    head of exactly `head_bits` bits. Unlike a stripe the ether does not bound the top by a column of ones; this
    records how far it goes."""
    _, cycle = ring_cycle(0b1000000, 7)
    words = sorted({((state >> r) | (state << (7 - r))) & 127 for state in cycle for r in range(7)})
    cuts = [0, steps // 5, steps // 2, steps]
    worst = [-head_bits - 1] * 3
    for tail in words:
        for head in range(1 << head_bits):
            tops = defect_tops(head, head_bits, tail, 7, steps)
            for i in range(3):
                worst[i] = max(worst[i], max(tops[cuts[i]:cuts[i + 1]]) - head_bits)
    return worst


def greedy_rise(cycle: list[int], length: int, steps: int) -> int:
    """How far a top that rises at every step where the background above it reads 0, and otherwise stays, gets in
    `steps` steps on the ring `cycle` of `length` cells, from cell 0 at time 0. It bounds the top of any defect."""
    top = 0
    for t in range(steps):
        if (cycle[t % len(cycle)] >> ((top + 1) % length)) & 1 == 0:
            top += 1
    return top


def front_rate(cycle: list[int], length: int, window: int, rounds: int) -> float:
    """An upper bound on the speed of the top of a defect on the background `cycle` (ring states, one per step) of
    `length` cells. The top and the `window - 1` cells below it are followed exactly; the cells below are free, and a
    top that falls out of the window is replaced by any top at least `window - 1` cells lower. The result is the
    longest path in the graph of these abstract states over `rounds` steps, per step, so it is positive when the
    bound cannot rule out a front. A stripe gives 0 and the vacuum gives 1."""
    period, cells = len(cycle), 1 << (window - 1)
    lost = period * length * cells
    background = lambda a, j: (cycle[a % period] >> (j % length)) & 1
    src: list[int] = []
    dst: list[int] = []
    gain: list[int] = []
    node = lambda a, b, m: (a * length + b) * cells + m
    for a in range(period):
        for b in range(length):
            for m in range(cells):
                x = {k: background(a, b - k) for k in (-2, -1)}
                x[0] = 1 - background(a, b)
                x.update({k: background(a, b - k) ^ ((m >> (k - 1)) & 1) for k in range(1, window)})
                d = {k: x[k - 1] ^ (x[k] | x[k + 1]) ^ background(a + 1, b - k) for k in range(-1, window - 1)}
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
    source, target, weight = np.array(src), np.array(dst), np.array(gain)
    value = np.zeros(lost + period, dtype=np.int64)
    for _ in range(rounds):
        step = value.copy()
        np.maximum.at(step, target, value[source] + weight)
        value = step
    return float(value.max()) / rounds


def stripe_invariant(head_bits: int, stripe_a: bool) -> tuple[list[int], int]:
    """Every point of K whose tail is a stripe and whose head has `head_bits` cells, exactly and without a time horizon.
    A state is the difference E of the head from the stripe, `head_bits` cells, at an even step. Two steps never raise
    the top (asserted for every E), so the states form a finite system; the result is its greatest invariant set under
    two steps with the condition at the odd step, as the sorted list of E, and how many of those do not reach E = 0, the
    stripe, which is 0 if the points of K with this tail all fall onto the stripe."""
    assert head_bits <= 24
    width = head_bits + 6
    stripe = sum(1 << j for j in range(width) if (j % 2 == 0) == stripe_a)
    stripe_word, full, one = np.uint64(stripe), np.uint64((1 << width) - 1), np.uint64(1)
    low = np.uint64((1 << head_bits) - 1)
    E = np.arange(1 << head_bits, dtype=np.uint64)  # (2^head_bits,)
    x = ((E ^ stripe_word) & low) | (stripe_word & ~low)  # (2^head_bits,) cells 0 .. head_bits - 1 differ by E
    y1 = ((x >> one) ^ (x | (x << one))) & full  # (2^head_bits,)
    y2 = ((y1 >> one) ^ (y1 | (y1 << one))) & full  # (2^head_bits,)
    after = y2 ^ stripe_word  # (2^head_bits,)
    assert not np.any((after >> np.uint64(head_bits)) & np.uint64(15)), "two steps raised the top"
    image = (after & low).astype(np.int64)  # (2^head_bits,)
    alive = (y1 & one) == one  # (2^head_bits,)
    while True:
        kept = alive & alive[image]
        if np.array_equal(kept, alive):
            break
        alive = kept
    states = np.flatnonzero(alive).tolist()
    stuck = 0
    for state in states:
        seen: set[int] = set()
        while state != 0 and state not in seen:
            seen.add(state)
            state = int(image[state])
        stuck += state != 0
    return states, stuck


def attractors(found: dict[Fraction, tuple[int, int]]) -> Counter:
    """The ring attractors (`cycle_class`, without the transient) of the tails of the rational points `found`."""
    census: Counter = Counter()
    bits = 4 * 128
    for value, (p, q) in found.items():
        code = (value.numerator * pow(value.denominator, -1, 1 << bits)) & ((1 << bits) - 1)
        tail = (code >> p) & ((1 << q) - 1)
        _, cycle_length, block, period = cycle_class(tail, q)
        census[(block, period, cycle_length)] += 1
    return census


def verified_hits(lines: list[str], depth: int, steps: int = 1200) -> tuple[dict[Fraction, tuple[int, int]], int]:
    """The rational points of K among the hits of `held_shift_search.c` (lines `q high low`, the first `depth` bits of
    the point as hexadecimal words, `q` the period tried): each hit is extended periodically, reduced to its least
    preperiod and period, and kept only if it holds the condition through `steps` steps in Python integers. Returns
    the points as value -> (p, q) and the number of hits that fail (survivors of the search by chance)."""
    bits = steps + 400
    mask = (1 << (steps + 100)) - 1
    found: dict[Fraction, tuple[int, int]] = {}
    failed = 0
    for line in lines:
        period, high, low = line.split()
        extension = ((int(high, 16) << 64) | int(low, 16)) & ((1 << depth) - 1)
        for position in range(depth, bits):
            extension |= ((extension >> (position - int(period))) & 1) << position
        V, alive = extension & mask, True
        for t in range(steps):
            if t % 2 == 1 and V & 1 == 0:
                alive = False
                break
            V = held(V) & mask
        if not alive:
            failed += 1
            continue
        pre, per = minimal_representation(extension, 3 * 130)
        value = Fraction(extension & ((1 << pre) - 1)) - Fraction(
            ((extension >> pre) & ((1 << per) - 1)) << pre, (1 << per) - 1)
        found.setdefault(value, (pre, per))
    return found, failed


def degree_profile(depth: int) -> list[tuple[int, int, int]]:
    """For each odd bit position 2s + 1 below `depth`, (position, algebraic degree, number of monomials) of the forced
    bit as a polynomial over GF(2) in the free bits, by the Moebius transform of its truth table."""
    halves = forced_halves(depth)  # (2^f,)
    free = (depth + 1) // 2
    rows = []
    for j in range(1, depth, 2):
        table = ((halves >> np.uint64(j)) & ONE).astype(np.uint8)  # (2^f,)
        for k in range(free):
            view = table.reshape(-1, 2, 1 << k)  # (blocks, 2, 2^k)
            view[:, 1, :] ^= view[:, 0, :]
        monomials = np.flatnonzero(table)  # (m,)
        rows.append((j, max(int(m).bit_count() for m in monomials), len(monomials)))
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--zoo", type=int, help="the domains: periodic points of the shift for n up to this")
    parser.add_argument("--block", default="01", help="with --zoo, the block of the center column")
    parser.add_argument("--rational", type=int, help="the rational points of K with p + 2 q up to this")
    parser.add_argument("--steps", type=int, default=330)
    parser.add_argument("--hits", help="the output of held_shift_search.c, to verify and summarize")
    parser.add_argument("--depth", type=int, default=64, help="with --hits, the depth the search ran to")
    parser.add_argument("--stripe", type=int, help="the defects on a stripe tail, over every head up to this length")
    parser.add_argument("--invariant", type=int, help="every point of K with a stripe tail and a head of this many cells")
    parser.add_argument("--front", type=int, help="the speed bound of the front automaton on the ether, for this window")
    parser.add_argument("--rounds", type=int, default=3200, help="steps of the longest path for --front")
    parser.add_argument("--ether", type=int, help="the defects on the ether, over every head of this many bits")
    parser.add_argument("--attractors", type=int, help="the ring attractors of the tails of the rational points")
    parser.add_argument("--degree", type=int, help="the algebraic degree of the forced bits below this position")
    args = parser.parse_args()
    if args.zoo:
        for n, counts in zoo(args.block, args.zoo).items():
            print(f"n = {n}: spatial periods (count) {sorted(counts.items())}", flush=True)
    if args.rational:
        found = rational_points(args.rational, args.steps)
        periods: Counter = Counter()
        orbit: Counter = Counter()
        for value, (p, q) in tqdm(sorted(found.items()), desc="itineraries", leave=False):
            code = (value.numerator * pow(value.denominator, -1, 1 << (2 * args.steps + 40))) & (
                (1 << (2 * args.steps + 40)) - 1)
            result = eventual_period(itinerary(code, args.steps // 2), settle=5)
            periods[q] += 1
            orbit[result[1] if result else None] += 1
        print(f"{len(found)} rational points with p + 2q <= {args.rational}, each through step {args.steps}")
        print("spatial periods:", sorted(periods.items()))
        print("itinerary periods (None: not preperiodic):", sorted(orbit.items(), key=str))
    if args.hits:
        with open(args.hits) as handle:
            found, failed = verified_hits(handle.read().splitlines(), args.depth)
        census: Counter = Counter()
        itineraries: Counter = Counter()
        stripe_preperiods: Counter = Counter()
        for value, (p, q) in tqdm(sorted(found.items()), desc="itineraries", leave=False):
            code = (value.numerator * pow(value.denominator, -1, 1 << 1200)) & ((1 << 1200) - 1)
            result = eventual_period(itinerary(code, 400), settle=5)
            census[value.denominator] += 1
            itineraries[result[1] if result else None] += 1
            if value.denominator == 3:
                stripe_preperiods[result[0] if result else None] += 1
        print(f"{len(found)} rational points ({failed} hits failed the 1200-step check)")
        print("denominators:", sorted(census.items()))
        print("itinerary periods (None: not preperiodic):", sorted(itineraries.items(), key=str))
        print("denominator 3, readings before the itinerary is periodic:", sorted(stripe_preperiods.items(), key=str))
        for (block, period, cycle), count in sorted(attractors(found).items()):
            print(f"attractor of cells {block:0{period}b} (period {period}, cycle {cycle}): {count} points")
    if args.invariant:
        for stripe_a in (True, False):
            states, stuck = stripe_invariant(args.invariant, stripe_a)
            print(f"stripe {'A' if stripe_a else 'B'}, head {args.invariant} cells: {len(states)} even-step states, "
                  f"{stuck} not reaching the stripe")
    if args.front:
        _, cycle = ring_cycle(0b1000000, 7)
        print("greedy rise on the ether in 2000 steps:", greedy_rise(cycle, 7, 2000))
        rate = front_rate(cycle, 7, args.front, args.rounds)
        nodes = len(cycle) * 7 * (1 << (args.front - 1)) + len(cycle)
        gain = round(rate * args.rounds)  # a walk without a positive cycle gains at most nodes - 1
        print(f"front speed bound, window {args.front}: {rate} over {args.rounds} steps, gain {gain} on {nodes} nodes, "
              f"positive cycle {'certified' if gain > nodes - 1 else 'not certified'}")
    if args.ether:
        print("largest top - preperiod on the ether, by window of steps:", ether_window(args.ether, 1500))
    if args.stripe:
        print(f"largest top - preperiod over heads of up to {args.stripe} bits on a stripe:", stripe_window(args.stripe))
    if args.attractors:
        for (block, period, cycle), count in sorted(attractors(rational_points(args.attractors, args.steps)).items()):
            print(f"attractor of cells {block:0{period}b} (period {period}, cycle {cycle}): {count} points")
    if args.degree:
        for j, degree, terms in degree_profile(args.degree):
            print(f"u_{j}: degree {degree}, {terms} monomials of {1 << ((j + 1) // 2)}")


if __name__ == "__main__":
    main()
