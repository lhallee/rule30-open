"""The left half beside a center that repeats a block: cell -1 at the black phases, for every block.

If the center column c repeats a block b from time T, then at every black phase, c(t) = 1, the rule gives
c(t + 1) = not x_t(-1): cell -1 must read not b(t + 1). That is a condition on the left half alone, driven by the
center, with the white phases free. Run with the kit's effective boundary c'(t) = c(t) and c(t + 1), as in its
`Rule30PeriodFourSkeleton.C3`, it is the kit's condition for 0111, and for 01 it is the period-two condition of
`held_map`; the kit's C3 for 0001 and 0011 adds readings at white phases that the right half forces.

`latch` adds what cell 1 forces, in the orbit of every row (`KickedForm`'s `right_latch` and `right_shown`): at a
white phase c(t + 1) = x_t(-1) xor x_t(1), so the reading of cell -1 shows cell 1, and a black cell 1 makes the next
cell 1 equal to not c(t). Cell 1 is then known until it reads white, and while it is known it fixes the reading at a
white phase. For 01 this is `period_two_golden`. `window_entropy` follows the readings as a window of cells 1 to W
sees them, with cell W + 1 free; a window of one cell is the latch.

`tree_failures` searches the left halves of up to M cells along the tree of readings the condition allows, as
`held_map.tree_failures` does for period four: cell -1 at step t is bit t of the starting half XOR a function of the
lower bits, so each allowed reading fixes one more cell, and the search visits about 2^(h M) branches, where `entropy`
h is the growth rate in bits per step of the sequences of readings the condition allows: w / P for a block with w
white phases in P, less with the latch. `survey` runs it on every primitive block of the given periods, with M as large
as a budget of branches allows.

    python -m computations.left_halves --blocks 01111,011111,0111111 --support 100   # about 3 min
    python -m computations.left_halves --periods 3,5,6,7,9 --budget 16   # every block, about 4 min on 4 workers
    python -m computations.left_halves --periods 3,5,6,7,9 --budget 16 --latch   # with cell 1's latch, about 6 min
    python -m computations.left_halves --blocks 01,0001 --window 10   # the entropy as wider right windows see it
    python -m computations.left_halves --entropies 14   # the latch's entropy over every block, period by period
"""

from __future__ import annotations

import argparse
import math
import sys
from multiprocessing import Pool

import numpy as np
from tqdm.auto import tqdm

from computations.game import necklaces
from computations.held_map import next_diagonal

UNKNOWN = 2  # the latch state when cell 1 is not known


def effective(block: str) -> list[int]:
    """The kit's effective boundary: the center at phase t and at phase t + 1 both black."""
    period = len(block)
    return [int(block[t] == "1" and block[(t + 1) % period] == "1") for t in range(period)]


def pattern(block: str) -> str:
    """Cell -1 at each phase: at a black phase the negation of the center's next value, at a white phase free (*)."""
    period = len(block)
    return "".join("*" if block[t] == "0" else str(1 - int(block[(t + 1) % period])) for t in range(period))


def advance(block: str, t: int, state: int, reading: int, latch: bool) -> int | None:
    """The latch state after cell -1 reads `reading` at step t (phase t mod P), or None if the condition fails. The
    state is cell 1 at step t, 0 or 1, or UNKNOWN; without `latch` it stays UNKNOWN and only black phases check."""
    period = len(block)
    now, after = int(block[t % period]), int(block[(t + 1) % period])
    if now:  # a black phase: cell -1 is the negation of the next center value, and a black cell 1 turns white
        if reading == after:
            return None
        return 0 if latch and state == 1 else UNKNOWN
    if not latch:
        return UNKNOWN
    shown = after ^ reading  # at a white phase the next center value is cell -1 xor cell 1
    if state != UNKNOWN and shown != state:
        return None
    return 1 if shown else UNKNOWN  # a black cell 1 beside a white center stays black


def transfer(block: str, latch: bool = False) -> np.ndarray:
    """The condition as an automaton: entry (3 p + s, 3 p' + s') counts the readings that take phase p and latch state s
    to phase p' = p + 1 mod P and state s'."""
    period = len(block)
    matrix = np.zeros((3 * period, 3 * period))  # (3P, 3P)
    for phase in range(period):
        for state in range(3):
            for reading in (0, 1):
                after = advance(block, phase, state, reading, latch)
                if after is not None:
                    matrix[3 * phase + state, 3 * ((phase + 1) % period) + after] += 1
    return matrix  # (3P, 3P)


def entropy(block: str, latch: bool = False) -> float:
    """The growth rate, in bits per step, of the sequences of readings the condition allows: log2 of the spectral
    radius of `transfer`."""
    return math.log2(max(abs(np.linalg.eigvals(transfer(block, latch)))))


def window_entropy(block: str, width: int) -> float:
    """The entropy, in bits per step, of the readings of cell -1 that some right half allows, as far as a window of
    cells 1 to `width` sees it, cell `width` + 1 free: at a black phase the check, at a white phase the reading
    c(t + 1) xor cell 1. The automaton runs on sets of windows; width 1 is the latch."""
    period = len(block)
    size = 1 << width

    def successors(center: int, window: int) -> list[int]:
        cells = [center] + [(window >> j) & 1 for j in range(width)]  # cells 0 .. width
        moved = sum((cells[j - 1] ^ (cells[j] | cells[j + 1])) << (j - 1) for j in range(1, width))
        last = cells[width - 1]  # the new cell `width` reads cell `width` - 1, itself and the free cell beyond
        return [moved | ((last ^ (cells[width] | free)) << (width - 1)) for free in (0, 1)]

    start = (0, (1 << size) - 1)  # phase 0, every window possible
    index, queue, edges = {start: 0}, [start], []
    while queue:
        phase, windows = queue.pop()
        now, after = int(block[phase]), int(block[(phase + 1) % period])
        for reading in (0, 1):
            if now and reading == after:
                continue
            image = 0
            for window in range(size):
                if (windows >> window) & 1 and (now or ((window & 1) ^ after) == reading):
                    for nxt in successors(now, window):
                        image |= 1 << nxt
            key = ((phase + 1) % period, image)
            if image and key not in index:
                index[key] = len(index)
                queue.append(key)
            if image:
                edges.append((index[(phase, windows)], index[key]))
    matrix = np.zeros((len(index), len(index)))  # (states, states)
    for a, b in edges:
        matrix[a, b] += 1
    return math.log2(max(abs(np.linalg.eigvals(matrix))))


def entropy_range(period: int, latch: bool = True) -> tuple[float, str, float, str]:
    """The largest and the smallest `entropy` over the primitive blocks of the period with a black phase, and the
    blocks that attain them."""
    rates = sorted((entropy(block, latch), block) for block in necklaces(period) if "1" in block)
    return rates[-1][0], rates[-1][1], rates[0][0], rates[0][1]


def tree_failures(block: str, max_support: int, phase: int, latch: bool = False,
                  limit: int = 100000) -> tuple[list[int], list[int]]:
    """For each M up to `max_support`, the latest first failure of the condition over the left halves of exactly M
    cells, the center read from phase `phase`, and the number of halves of at most M cells that keep it through step
    M - 1. Raises AssertionError if a half keeps it through step `limit`."""
    period = len(block)
    boundary = effective(block)
    latest, branches = [0] * (max_support + 1), [0] * (max_support + 1)
    early = [False] * (max_support + 1)  # whether some half of more than m + 1 cells first fails at step m
    stack = [(0, 0, 0, 0, UNKNOWN)]  # (m, antidiagonal m - 1, antidiagonal m - 2, bit m - 1, latch state at step m)
    while stack:
        m, a1, a2, top, state = stack.pop()
        if m:
            branches[m] += 1
        if top:  # follow the half, of exactly m cells, until it fails
            t, b1, b2, s = m, a1, a2, state
            while True:
                d = b1 | b2 | (boundary[(t - 1 + phase) % period] << (t - 1))
                s = advance(block, t + phase, s, d.bit_count() % 2, latch)
                if s is None:
                    break
                assert t < limit, f"a half of {m} cells keeps the condition through step {limit}"
                b1, b2, t = next_diagonal(0, d, t), b1, t + 1
            latest[m] = max(latest[m], t)
        if m == max_support:
            continue
        d = a1 | a2 | ((boundary[(m - 1 + phase) % period] << (m - 1)) if m else 0)
        parity = d.bit_count() % 2
        for reading in (0, 1):
            u = reading ^ parity
            after = advance(block, m + phase, state, reading, latch)
            if after is not None:
                stack.append((m + 1, next_diagonal(u, d, m), a1, u, after))
            else:  # every half with these cells and cell m + 1 equal to u fails at step m
                latest[m + 1] = max(latest[m + 1], m) if u else latest[m + 1]
                early[m] = True
    for support in range(2, max_support + 1):
        latest[support] = max([latest[support]] + [m for m in range(support - 1) if early[m]])
    return latest[1:], branches[1:]


def margins(block: str, max_support: int, latch: bool = False) -> list[int]:
    """For each M from 1, the latest first failure over the left halves of exactly M cells and every phase, minus M."""
    runs = [tree_failures(block, max_support, phase, latch) for phase in range(len(block))]
    return [max(run[0][m - 1] for run in runs) - m for m in range(1, max_support + 1)]


def survey_row(job: tuple[str, int, bool]) -> tuple[str, int, int, int, int, float]:
    """One block of the survey: the block, its support M, the largest margin up to M, the M where it occurs, the margin
    at M, and the margin at M that fair coins would give, M h / (1 - h) for the entropy h."""
    block, support, latch = job
    margin = margins(block, support, latch)
    worst = max(range(support), key=lambda m: margin[m])
    h = entropy(block, latch)
    return block, support, margin[worst], worst + 1, margin[-1], support * h / (1 - h)


def survey(periods: list[int], budget: int, latch: bool = False,
           workers: int = 4) -> list[tuple[str, int, int, int, int, float]]:
    """For every primitive block of the periods that has a black phase, `survey_row` with the support
    M = budget / entropy, at most 100, so that about 2^budget halves keep the condition through step M - 1; printed as
    each block finishes."""
    jobs = [(block, min(100, int(budget / max(entropy(block, latch), budget / 100) + 1e-9)), latch)
            for period in periods for block in necklaces(period) if "1" in block]
    rows = []
    with Pool(workers) as pool:
        for row in tqdm(pool.imap_unordered(survey_row, jobs), total=len(jobs), file=sys.stderr):
            block, support, worst, at, last, coins = row
            print(f"{block}: every left half of at most {support} cells fails; the latest at M + {worst} for M = "
                  f"{at}, and at M + {last} for M = {support}, against {coins:.1f} for fair coins", flush=True)
            rows.append(row)
    return sorted(rows, key=lambda row: (len(row[0]), row[0]))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--blocks", help="comma-separated blocks")
    parser.add_argument("--support", type=int, default=40, help="with --blocks, the largest support M")
    parser.add_argument("--periods", default="3,5,6,7,9")
    parser.add_argument("--budget", type=int, default=16, help="about 2^budget branches a block")
    parser.add_argument("--latch", action="store_true", help="add the readings that cell 1's latch forces")
    parser.add_argument("--window", type=int, help="with --blocks, the entropy for right windows up to this width")
    parser.add_argument("--entropies", type=int, help="the range of the entropy over the blocks of each period up to "
                        "this one, with the latch")
    parser.add_argument("--workers", type=int, default=4)
    args = parser.parse_args()
    if args.entropies:
        for period in range(1, args.entropies + 1):
            high, top, low, bottom = entropy_range(period)
            print(f"period {period}: with the latch, entropy {high:.4f} at most ({top}), {low:.4f} at least "
                  f"({bottom})", flush=True)
        return
    if args.blocks and args.window:
        for block in args.blocks.split(","):
            rates = ", ".join(f"{window_entropy(block, width):.3f}" for width in range(1, args.window + 1))
            print(f"{block}: {entropy(block):.3f} bits per step from the checks; with a right window of 1, 2, ... "
                  f"cells: {rates}", flush=True)
        return
    if args.blocks:
        for block in args.blocks.split(","):
            margin = margins(block, args.support, args.latch)
            worst = max(range(args.support), key=lambda m: margin[m])
            print(f"{block}: cell -1 must read {pattern(block)}; every left half of at most {args.support} cells "
                  f"fails in every phase, the latest at M + {margin[worst]} for M = {worst + 1}; margins at M = 10, "
                  f"20, ...: {margin[9::10]}", flush=True)
        return
    rows = survey([int(p) for p in args.periods.split(",")], args.budget, args.latch, args.workers)
    for period in sorted({len(row[0]) for row in rows}):
        group = [row for row in rows if len(row[0]) == period]
        supports = [row[1] for row in group]
        worst = max(group, key=lambda row: row[4])
        ratios = [row[4] / row[5] for row in group]
        print(f"period {period}: {len(group)} blocks, M from {min(supports)} to {max(supports)}; the largest margin "
              f"at M is {worst[4]}, for {worst[0]}; margin over fair coins from {min(ratios):.2f} to "
              f"{max(ratios):.2f}, mean {sum(ratios) / len(ratios):.2f}")
    ratios = [row[4] / row[5] for row in rows]
    print(f"all {len(rows)} blocks: margin over fair coins from {min(ratios):.2f} to {max(ratios):.2f}, mean "
          f"{sum(ratios) / len(ratios):.2f}")


if __name__ == "__main__":
    main()
