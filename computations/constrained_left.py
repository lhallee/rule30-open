"""The left half beside a center repeating 001 or 011, with the free bits of column -1 constrained by the right half.

If the center repeats a block b from some time on, column -1 is fixed at the black phases (left permutivity), and at a
white phase it is the reading xor the next center cell, where the reading is column 1 at that step. The right half
constrains the readings ([reading constraints](../findings/columns/reading-constraints.md)): for 001 the kit's
`skeleton_001` makes the reading at the first white step white, and `ThreeRuns` keeps the readings at the second
white step free of 010, 101 and 1001; for 011 the readings avoid 00 unless they are eventually white. A `Condition`
holds the block, the pinned readings and the forbidden words, read over the readings at every white step in time
order, as `gap_traps` reads them. With nothing but the pins it is the kit's left-only statement: `C3s001` for 001,
`C3w w011` for 011.

The left half runs as Rule 30 on the cells left of the center with the center replaced by the kit's effective boundary
c'(t) = c(t) and c(t + 1): white for 001, 010 for 011. Bit j of a half is cell -1 - j, and one step is
U -> (U >> 1) xor (U or (U << 1) or c'(t)).

- `tree_failures` searches every left half of at most M cells along the tree of readings the condition allows, as
  `left_halves.tree_failures` does: cell -1 at step t is bit t of the half xor a function of its lower bits, so the
  halves of at most M cells that keep the condition through step M - 1 are exactly as many as the words of M values of
  column -1 the condition allows (`count_words`), about 2^(h M) for the `entropy` h, in bits per step.
- `forced_cells` and `column_anf` give columns -1, -2, ... as functions of the readings, by the sideways map: column
  j - 1 at step t is column j at step t + 1 xor (column j or column j + 1 at step t).
- `periodic_half` gives the left half whose column -1 repeats a word of readings: it repeats in time, so the sideways
  map runs on cyclic words and the half is eventually periodic in space, never finitely supported.

    python -m computations.constrained_left --columns 6 --forced 36 --periodic 6   # formulas, fixed cells, periodic
    python -m computations.constrained_left --tree 60 --conditions 001-kit,011-kit   # about 2 min
    python -m computations.constrained_left --tree 92 --conditions 001-runs          # about 1 min
    python -m computations.constrained_left --tree 85 --conditions 011-no00          # about 2 min
"""

from __future__ import annotations

import argparse
import functools
import itertools
import math
import sys
from dataclasses import dataclass

import numpy as np
from tqdm.auto import tqdm

from computations.held_map import next_diagonal


@dataclass(frozen=True)
class Condition:
    """A left-half condition: the center repeats `block`; the reading at the white phases in `pins` is fixed; the
    sequence of readings at all white steps, in time order, avoids `words`."""

    name: str
    block: str
    pins: tuple[tuple[int, int], ...]
    words: tuple[str, ...]
    source: str


CONDITIONS = {
    c.name: c
    for c in (
        Condition("001-kit", "001", ((0, 0),), (), "the kit's C3s001 (skeleton_001 pins the first white step)"),
        Condition("001-runs", "001", ((0, 0),), ("00100", "10001", "1000001"),
                  "C3s001 with ThreeRuns: the second white step avoids 010, 101, 1001"),
        Condition("011-kit", "011", (), (), "the kit's C3w w011"),
        Condition("011-no00", "011", (), ("00",), "C3w w011 with readings free of 00 (forced up to white readings)"),
        Condition("011-trap", "011", (), ("00", "010", "01110", "011110"),
                  "C3w w011 with the words of the 011 trap (entered by small halves, not forced)"),
    )
}


def effective(block: str) -> list[int]:
    """The kit's effective boundary: the center at phase t and at phase t + 1 both black."""
    period = len(block)
    return [int(block[t] == "1" and block[(t + 1) % period] == "1") for t in range(period)]


@functools.lru_cache(maxsize=None)
def _word_step(words: tuple[str, ...], history: int, reading: int) -> int | None:
    """The history after `reading`, or None if it completes a word. A history is the last readings, at most the
    longest word less one, as bits after a leading sentinel 1."""
    keep = max((len(w) for w in words), default=1) - 1
    text = format(history, "b")[1:] + str(reading)
    if any(text.endswith(w) for w in words):
        return None
    tail = text[-keep:] if keep else ""
    return int("1" + tail, 2)


@functools.lru_cache(maxsize=None)
def advance(cond: Condition, phase: int, history: int, value: int) -> int | None:
    """The state after column -1 reads `value` at a step of phase `phase`, or None if the condition fails there."""
    block = cond.block
    period = len(block)
    after = int(block[(phase + 1) % period])
    if block[phase] == "1":  # a black phase: column -1 is the negation of the next center cell
        return None if value == after else history
    reading = value ^ after  # a white phase: column 1 is column -1 xor the next center cell
    pinned = dict(cond.pins).get(phase)
    if pinned is not None and reading != pinned:
        return None
    return _word_step(cond.words, history, reading)


def states(cond: Condition) -> list[int]:
    """Every history reachable from the empty one."""
    seen, queue = {1}, [1]
    while queue:
        h = queue.pop()
        for phase in range(len(cond.block)):
            for value in (0, 1):
                nxt = advance(cond, phase, h, value)
                if nxt is not None and nxt not in seen:
                    seen.add(nxt)
                    queue.append(nxt)
    return sorted(seen)


def transfer(cond: Condition) -> np.ndarray:
    """Entry ((p, h), (p + 1, h')) counts the values of column -1 that take phase p and history h to h'."""
    hs = states(cond)
    index = {h: i for i, h in enumerate(hs)}
    period, n = len(cond.block), len(hs)
    matrix = np.zeros((period * n, period * n))  # (P n, P n)
    for phase in range(period):
        for h in hs:
            for value in (0, 1):
                nxt = advance(cond, phase, h, value)
                if nxt is not None:
                    matrix[phase * n + index[h], ((phase + 1) % period) * n + index[nxt]] += 1
    return matrix  # (P n, P n)


def entropy(cond: Condition) -> float:
    """Bits per step of the sequences of column -1 the condition allows: log2 of the spectral radius of `transfer`."""
    return math.log2(max(abs(np.linalg.eigvals(transfer(cond)))))


def count_words(cond: Condition, phase: int, length: int) -> list[int]:
    """For n = 1 .. length, the number of words of n values of column -1, from phase `phase`, the condition allows."""
    period = len(cond.block)
    counts: dict[int, int] = {1: 1}
    out = []
    for t in range(length):
        nxt: dict[int, int] = {}
        for h, c in counts.items():
            for value in (0, 1):
                a = advance(cond, (t + phase) % period, h, value)
                if a is not None:
                    nxt[a] = nxt.get(a, 0) + c
        counts = nxt
        out.append(sum(counts.values()))
    return out


def run_half(cond: Condition, half: int, phase: int, limit: int) -> int:
    """The first step at which the left half `half` (bit j is cell -1 - j) fails the condition, run from phase
    `phase`, or `limit` if it keeps it through step `limit` - 1."""
    period = len(cond.block)
    boundary = effective(cond.block)
    h, u = 1, half
    for t in range(limit):
        p = (t + phase) % period
        h = advance(cond, p, h, u & 1)
        if h is None:
            return t
        u = (u >> 1) ^ (u | (u << 1) | boundary[p])
    return limit


def tree_failures(cond: Condition, max_support: int, phase: int,
                  limit: int = 100000) -> tuple[list[int], list[int], list[dict[int, int]]]:
    """For each M up to `max_support`: the latest first failure over the left halves of exactly M cells run from phase
    `phase`, the number of halves of at most M cells that keep the condition through step M - 1, and the histogram of
    first failures of the halves of exactly M cells that keep it through step M - 1. The search is
    `left_halves.tree_failures` with the history of readings in place of the latch. Raises AssertionError if a half
    keeps the condition through step `limit`."""
    period = len(cond.block)
    boundary = effective(cond.block)
    latest, branches = [0] * (max_support + 1), [0] * (max_support + 1)
    histogram: list[dict[int, int]] = [{} for _ in range(max_support + 1)]
    early = [False] * (max_support + 1)  # whether some half of more than m + 1 cells first fails at step m
    stack = [(0, 0, 0, 0, 1)]  # (m, antidiagonal m - 1, antidiagonal m - 2, bit m - 1, history at step m)
    while stack:
        m, a1, a2, top, hist = stack.pop()
        if m:
            branches[m] += 1
        if top:  # follow the half, of exactly m cells, until it fails
            t, b1, b2, h = m, a1, a2, hist
            while True:
                d = b1 | b2 | (boundary[(t - 1 + phase) % period] << (t - 1))
                h = advance(cond, (t + phase) % period, h, d.bit_count() % 2)
                if h is None:
                    break
                assert t < limit, f"a half of {m} cells keeps the condition through step {limit}"
                b1, b2, t = next_diagonal(0, d, t), b1, t + 1
            latest[m] = max(latest[m], t)
            histogram[m][t] = histogram[m].get(t, 0) + 1
        if m == max_support:
            continue
        d = a1 | a2 | ((boundary[(m - 1 + phase) % period] << (m - 1)) if m else 0)
        parity = d.bit_count() % 2
        for value in (0, 1):
            u = value ^ parity
            after = advance(cond, (m + phase) % period, hist, value)
            if after is not None:
                stack.append((m + 1, next_diagonal(u, d, m), a1, u, after))
            else:  # every half with these cells and cell m + 1 equal to u fails at step m
                latest[m + 1] = max(latest[m + 1], m) if u else latest[m + 1]
                early[m] = True
    for support in range(2, max_support + 1):
        latest[support] = max([latest[support]] + [m for m in range(support - 1) if early[m]])
    return latest[1:], branches[1:], histogram[1:]


def survivors(histogram: list[dict[int, int]], support: int, step: int) -> int:
    """The number of left halves of at most `support` cells that keep the condition through step `step`, for
    `step` at least `support` - 1, from the histograms of `tree_failures`."""
    return sum(c for m in range(support) for t, c in histogram[m].items() if t > step)


def report(cond: Condition, max_support: int, extra: tuple[int, ...] = (0, 10, 20, 30)) -> dict[str, object]:
    """Every phase of `tree_failures`: the largest margin past M of a first failure, the margins at M = 10, 20, ...,
    the growth exponent of the branch count over the second half of the range, and the survivors through step
    M - 1 + j for each j in `extra`, summed over the phases, at M = `max_support`, beside what fair coins give:
    if the values of column -1 past step M - 1 were fair coins, a half would keep the condition through step
    M - 1 + j with probability N(M + j) / (N(M) 2^j), for N(n) the allowed words of length n (`count_words`)."""
    period = len(cond.block)
    runs = [tree_failures(cond, max_support, phase)
            for phase in tqdm(range(period), desc=cond.name, file=sys.stderr, leave=False)]
    margin = [max(run[0][m - 1] for run in runs) - m for m in range(1, max_support + 1)]
    total = [sum(run[1][m - 1] for run in runs) for m in range(1, max_support + 1)]
    lo = max_support // 2
    slope = (math.log2(total[-1]) - math.log2(total[lo - 1])) / (max_support - lo)
    h = entropy(cond)
    return {
        "entropy": h,
        "slope": slope,
        "branches": total,
        "margins": margin,
        "largest": max(margin),
        "at": 1 + max(range(max_support), key=lambda m: margin[m]),
        "coins": max_support * h / (1 - h),
        "survivors": [sum(survivors(run[2], max_support, max_support - 1 + j) for run in runs) for j in extra],
        "coin_survivors": [sum(count_words(cond, phase, max_support + j)[-1] for phase in range(period)) / 2 ** j
                           for j in extra],
    }


def allowed_readings(cond: Condition, periods: int, pad: int = 4) -> list[tuple[int, ...]]:
    """The sequences of `periods` periods of readings (one per white phase, in time order) that occur after `pad`
    periods inside an allowed sequence of `periods` + 2 `pad` periods, the pins applied."""
    period = len(cond.block)
    white = [p for p in range(period) if cond.block[p] == "0"]
    pins = dict(cond.pins)
    out: set[tuple[int, ...]] = set()
    total = (periods + 2 * pad) * len(white)

    def extend(seq: list[int], h: int) -> None:
        k = len(seq)
        if k == total:
            out.add(tuple(seq[pad * len(white):(pad + periods) * len(white)]))
            return
        p = white[k % len(white)]
        for r in ((pins[p],) if p in pins else (0, 1)):
            nxt = _word_step(cond.words, h, r)
            if nxt is not None:
                extend(seq + [r], nxt)

    extend([], 1)
    return sorted(out)


def columns_from(cond: Condition, readings: tuple[int, ...], depth: int) -> list[list[int]]:
    """Columns -1 .. -depth over the steps they are known, from the readings of whole periods: column -1 from the
    pattern and the readings, then the sideways map. Column -k is known at k - 1 fewer steps than column -1."""
    block, period = cond.block, len(cond.block)
    white = [p for p in range(period) if block[p] == "0"]
    boundary = effective(block)
    col, it = [], iter(readings)
    for i in range(len(readings) // len(white)):
        for p in range(period):
            after = int(block[(p + 1) % period])
            col.append(1 - after if block[p] == "1" else next(it) ^ after)
    cols = [[boundary[t % period] for t in range(len(col))], col]
    for _ in range(depth - 1):
        a, b = cols[-2], cols[-1]
        cols.append([b[t + 1] ^ (b[t] | a[t]) for t in range(len(b) - 1)])
    return cols[1:]


def forced_cells(cond: Condition, depth: int, periods: int) -> list[str]:
    """For k = 1 .. depth, column -k at the phases of one period, a 0 or 1 where every allowed sequence of readings
    gives that value and * otherwise, in the eventual regime (`allowed_readings` of `periods` periods)."""
    period = len(cond.block)
    seen = [[set() for _ in range(period)] for _ in range(depth)]
    for readings in allowed_readings(cond, periods):
        cols = columns_from(cond, readings, depth)
        for k in range(depth):
            for p in range(period):
                seen[k][p].add(cols[k][p])
    return ["".join(str(next(iter(s))) if len(s) == 1 else "*" for s in row) for row in seen]


def column_anf(cond: Condition, depth: int, periods: int) -> list[list[str]]:
    """Columns -1 .. -depth at the phases of one period as polynomials over GF(2) in the free readings b0, b1, ...
    (b_i the reading at the free white phase of period i, every word allowed): the algebraic normal form, by the
    Moebius transform of the truth table."""
    period = len(cond.block)
    white = [p for p in range(period) if cond.block[p] == "0"]
    pins = dict(cond.pins)
    free = [p for p in white if p not in pins]
    assert len(free) == 1, "one free white phase per period"
    n = periods
    table = np.zeros((depth, period, 1 << n), dtype=np.uint8)  # (depth, P, 2^n)
    for x in range(1 << n):
        readings = tuple(pins.get(p, (x >> i) & 1) for i in range(n) for p in white)
        cols = columns_from(cond, readings, depth)
        for k in range(depth):
            for p in range(period):
                table[k, p, x] = cols[k][p]
    for i in range(n):  # Moebius transform along variable i
        bit = 1 << i
        for x in range(1 << n):
            if x & bit:
                table[:, :, x] ^= table[:, :, x ^ bit]
    out = []
    for k in range(depth):
        row = []
        for p in range(period):
            terms = ["".join(f"b{i}" for i in range(n) if (x >> i) & 1) or "1"
                     for x in range(1 << n) if table[k, p, x]]
            row.append(" + ".join(sorted(terms, key=lambda s: (len(s), s))) or "0")
        out.append(row)
    return out


def periodic_half(cond: Condition, word: tuple[int, ...], cells: int = 0) -> tuple[int, int, list[int]]:
    """The left half whose readings repeat `word` (one reading per white phase, the pins applied, in time order):
    its column -1 and the boundary repeat with period P q, so the sideways map runs on pairs of cyclic words, which
    repeat. Returns the preperiod and the period, in cells, of the sequence of columns, and the first `cells` cells
    of the half at step 0."""
    cols = columns_from(cond, word, 1)
    q = len(cols[0])
    boundary = effective(cond.block)
    a, b = tuple(boundary[t % len(cond.block)] for t in range(q)), tuple(cols[0])
    seen: dict[tuple[tuple[int, ...], tuple[int, ...]], int] = {}
    row: list[int] = []
    k = 0
    while (a, b) not in seen:
        seen[(a, b)] = k
        row.append(b[0])
        a, b = b, tuple(b[(t + 1) % q] ^ (b[t] | a[t]) for t in range(q))
        k += 1
    start = seen[(a, b)]
    period = k - start
    while len(row) < cells:
        row.append(row[start + (len(row) - start) % period])
    return start, period, row[:cells]


def periodic_survey(cond: Condition, max_period: int) -> dict[int, dict[int, int]]:
    """For each q up to `max_period`, the spatial periods (with counts) of the halves whose readings repeat a word of
    period dividing q that the condition allows forever."""
    period = len(cond.block)
    white = [p for p in range(period) if cond.block[p] == "0"]
    pins = dict(cond.pins)
    out: dict[int, dict[int, int]] = {}
    for q in range(1, max_period + 1):
        counts: dict[int, int] = {}
        for bits in itertools.product((0, 1), repeat=q):
            word = tuple(pins.get(p, bits[i]) for i in range(q) for p in white)
            text = "".join(map(str, word * (3 + max((len(w) for w in cond.words), default=1) // len(word))))
            if any(w in text for w in cond.words):
                continue
            _, spatial, _ = periodic_half(cond, word)
            counts[spatial] = counts.get(spatial, 0) + 1
        out[q] = dict(sorted(counts.items()))
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--conditions", default=",".join(CONDITIONS))
    parser.add_argument("--columns", type=int, help="columns -1 .. -k as polynomials in the readings")
    parser.add_argument("--forced", type=int, help="the fixed cells of columns -1 .. -k")
    parser.add_argument("--tree", type=int, help="every left half of at most this many cells")
    parser.add_argument("--periodic", type=int, help="the halves whose readings repeat with period up to this")
    args = parser.parse_args()
    conds = [CONDITIONS[name] for name in args.conditions.split(",")]
    for cond in conds:
        print(f"{cond.name}: {cond.source}; {entropy(cond):.4f} bits per step", flush=True)
        if args.columns:
            for k, row in enumerate(column_anf(cond, args.columns, args.columns // len(cond.block) + 3), start=1):
                print(f"  column -{k}: " + " | ".join(row))
        if args.forced:
            rows = forced_cells(cond, args.forced, args.forced // len(cond.block) + 2)
            fixed = [k + 1 for k, row in enumerate(rows) if row.strip("*")]
            print(f"  fixed cells: " + " ".join(f"-{k}:{rows[k - 1]}" for k in fixed)
                  + f"; none in columns -{fixed[-1] + 1} to -{args.forced}")
        if args.periodic:
            for q, counts in periodic_survey(cond, args.periodic).items():
                print(f"  readings of period dividing {q}: spatial periods " +
                      ", ".join(f"{s} ({c})" for s, c in counts.items()))
        if args.tree:
            r = report(cond, args.tree)
            m = args.tree
            print(f"  every left half of at most {m} cells fails in every phase; largest margin {r['largest']} at "
                  f"M = {r['at']}, margins at M = 10, 20, ...: {r['margins'][9::10]}, fair coins at M: "
                  f"{r['coins']:.1f}; halves through step M - 1: {r['branches'][-1]} (log2 slope "
                  f"{r['slope']:.4f}); through M - 1 + 0, 10, 20, 30: {r['survivors']}, fair coins: "
                  + ", ".join(f"{c:.1f}" for c in r["coin_survivors"]), flush=True)


if __name__ == "__main__":
    main()
