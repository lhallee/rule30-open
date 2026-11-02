"""How long a column of a small finite row follows a target word from a late onset T0, periodic targets against random.

`periodic_columns` asks whether a column of a row of w cells repeats from time 0. A column that repeats only from a
time T0 > 0 is the same question for the row at time T0, so this module measures the longest run of agreement with a
target from every onset: for every row whose black cells lie in cells 0 .. w - 1, every column of the support (with
`margin` more on each side), every onset T0 below `max_onset` and every target, the largest L such that the column
equals the target at the times T0 .. T0 + L - 1. A target is a word repeated from a phase (the periodic ones) or a fair
coin's word (the controls). The rows are bit-sliced as in `periodic_columns`: bit i of lane l is row 64 l + i.

Rule 30 is permutive in its left input, so cell (t, x) changes with the cell x - t of the row at time 0 whatever the
cells right of it hold. Column x = w - 1 + T0 at the times T0, T0 + 1, ... therefore takes the cells w - 1, w - 2, ...
of the row one at a time, and every target word of length w is followed from every onset T0 by some row of w cells
(`free_bit_row`; the bijection of `Rule30Open.RandomRows.LeftWindow`, read at the right end). Every question "does
some row of w cells follow b on a fixed window of times" is thus answered yes once w is the window's length, so none
is refuted for every w.

The optional `sat_longest` asks the same of the middle column for wider rows with a SAT solver (python-sat, the `sat`
optional dependency group), the light cone encoded with one variable per OR and XOR gate.

    python -m computations.late_onset --cells 8 12 16 20 --steps 160 --max-onset 120  # about 1.5 min
    python -m computations.late_onset --cells 12 --margin 120 --controls 8            # columns beyond the support
    python -m computations.late_onset --sat 16 --onsets 0 32 --controls 8             # needs python-sat
"""

from __future__ import annotations

import argparse
import math
import sys
import time

import numpy as np
from tqdm.auto import tqdm

from computations.periodic_columns import initial_rows, step

U64 = np.uint64
ALL = U64(0xFFFFFFFFFFFFFFFF)
WORDS = ("01", "001", "011")
BUCKETS = ((0, 1), (1, 8), (8, 32), (32, 64), (64, 120))


def periodic_target(word: str, phase: int, steps: int) -> list[int]:
    """The word repeated from the phase, letter t at time t."""
    return [int(word[(t + phase) % len(word)]) for t in range(steps)]


def random_targets(count: int, steps: int, seed: int = 1) -> list[list[int]]:
    """`count` fair coin words of length `steps`."""
    rng = np.random.default_rng(seed)
    return [rng.integers(0, 2, steps).tolist() for _ in range(count)]


def column_history(cells: int, steps: int, margin: int, first_lane: int, lanes: int) -> np.ndarray:
    """The columns -margin .. cells - 1 + margin at times 0 .. steps - 1 of the rows 64 first_lane .. 64 (first_lane +
    lanes) - 1, bit-sliced."""
    origin = steps + margin + 2
    width = 2 * origin + cells
    rows = initial_rows(cells, first_lane, lanes, width, origin)  # (width, lanes)
    history = np.empty((steps, cells + 2 * margin, lanes), dtype=U64)  # (steps, columns, lanes)
    for t in range(steps):
        history[t] = rows[origin - margin:origin + cells + margin]
        rows = step(rows, 30)
    return history


def onset_runs(history: np.ndarray, target: list[int], max_onset: int, first_lane: int) -> np.ndarray:
    """For each onset T0 < max_onset and column, the longest run of agreement with the target from T0 over the rows of
    the slice, the white row left out. A run that reaches the last time of the history is censored there."""
    steps, columns, lanes = history.shape
    want = np.array([ALL if bit else U64(0) for bit in target[:steps]], dtype=U64)  # (steps,)
    match = ~(history ^ want[:, None, None])  # (steps, columns, lanes)
    start = np.full((columns, lanes), ALL, dtype=U64)  # (columns, lanes)
    if first_lane == 0:
        start[:, 0] &= ~U64(1)  # the white row
    out = np.zeros((max_onset, columns), dtype=np.int64)  # (max_onset, columns)
    for onset in range(max_onset):
        alive = start.copy()  # (columns, lanes)
        for t in range(onset, steps):
            alive &= match[t]
            live = alive.any(axis=1)  # (columns,)
            if not live.any():
                break
            out[onset, live] = t - onset + 1
    return out


def runs_for_targets(cells: int, steps: int, max_onset: int, targets: list[list[int]], margin: int = 0,
                     chunk: int = 4096) -> np.ndarray:
    """The longest runs (targets, max_onset, columns) over every nonzero row of at most `cells` cells, the rows taken
    `chunk` lanes at a time."""
    lanes_total = max(1, (1 << cells) // 64)
    best = np.zeros((len(targets), max_onset, cells + 2 * margin), dtype=np.int64)  # (targets, onsets, columns)
    for first in tqdm(range(0, lanes_total, chunk), desc=f"{cells} cells", file=sys.stderr, leave=False):
        lanes = min(chunk, lanes_total - first)
        history = column_history(cells, steps, margin, first, lanes)  # (steps, columns, lanes)
        if cells < 6:
            history &= U64((1 << (1 << cells)) - 1)  # keep each row once
        for k, target in enumerate(targets):
            best[k] = np.maximum(best[k], onset_runs(history, target, max_onset, first))
    return best


def simulate_column(row: int, cells: int, column: int, steps: int) -> list[int]:
    """Column `column` at times 0 .. steps - 1 of the row with black cells at the set bits of `row` (bit x is cell x),
    by stepping whole integers: the independent check of the bit slices."""
    offset = steps + abs(column) + 2
    state = row << offset  # bit x + offset is cell x
    out = []
    for _ in range(steps):
        out.append((state >> (offset + column)) & 1)
        state = (state << 1) ^ (state | (state >> 1))  # new cell x = cell x - 1 xor (cell x or cell x + 1)
    return out


def free_bit_row(target: list[int], onset: int) -> int:
    """A row of len(target) cells whose column len(target) - 1 + onset follows the target from the onset: the cells
    are fixed from the right, cell w - 1 - i chosen so that the column is right at time onset + i."""
    width = len(target)
    column, row = width - 1 + onset, 0
    for i in range(width):
        cell = width - 1 - i
        if simulate_column(row, width, column, onset + i + 1)[-1] != target[i]:
            row |= 1 << cell  # permutive: flipping cell x - t flips cell (t, x)
    return row


def sat_longest(cells: int, target: list[int], onset: int, cap: int) -> tuple[int, int]:
    """The largest L <= cap for which some row with black cells in 0 .. cells - 1 has its middle column cells // 2
    equal to the target at the times onset .. onset + L - 1, and the solver's conflicts in the call that refutes L + 1
    (0 when none does). Needs python-sat."""
    from pysat.solvers import Cadical153

    mid, horizon = cells // 2, onset + cap
    clauses: list[list[int]] = []
    count = [cells]

    def gate(kind: str, a: int | bool, b: int | bool) -> int | bool:
        """A literal for (a or b) or (a xor b), constants folded."""
        if isinstance(a, bool) and isinstance(b, bool):
            return (a or b) if kind == "or" else (a != b)
        if isinstance(a, bool) or isinstance(b, bool):
            const, lit = (a, b) if isinstance(a, bool) else (b, a)
            if kind == "or":
                return True if const else lit
            return -lit if const else lit  # type: ignore[operator]
        count[0] += 1
        z = count[0]
        if kind == "or":
            clauses.extend([[-a, z], [-b, z], [a, b, -z]])
        else:
            clauses.extend([[-a, -b, -z], [a, b, -z], [a, -b, z], [-a, b, z]])
        return z

    row: dict[int, int | bool] = {x: x + 1 for x in range(cells)}  # seed cell x is variable x + 1
    column: list[int | bool] = [row.get(mid, False)]
    for t in range(1, horizon):
        lo, hi = mid - (horizon - t), mid + (horizon - t)  # only the backward cone of the last cell is needed
        new: dict[int, int | bool] = {}
        for x in range(max(lo, -t), min(hi, cells - 1 + t) + 1):
            new[x] = gate("xor", row.get(x - 1, False), gate("or", row.get(x, False), row.get(x + 1, False)))
        row = new
        column.append(row.get(mid, False))
    with Cadical153(bootstrap_with=clauses) as solver:
        assumptions: list[int] = []
        for length in range(1, cap + 1):
            lit = column[onset + length - 1]
            want = bool(target[onset + length - 1])
            if isinstance(lit, bool):
                if lit != want:
                    return length - 1, 0
                continue
            assumptions.append(lit if want else -lit)
            before = solver.accum_stats().get("conflicts", 0)
            if not solver.solve(assumptions=assumptions):
                return length - 1, solver.accum_stats().get("conflicts", 0) - before
    return cap, 0


def chance(cells: int, columns: int, onsets: int) -> float:
    """log2 of the number of (row, column, onset) trials for one target: about the longest run a fair coin's column
    would give."""
    return math.log2(((1 << cells) - 1) * columns * onsets)


def report(cells: int, steps: int, max_onset: int, margin: int, controls: int) -> None:
    """The longest runs by onset bucket for each periodic target, and their spread over the random controls."""
    names = [f"{w} phase {p}" for w in WORDS for p in range(len(w))]
    targets = [periodic_target(w, p, steps) for w in WORDS for p in range(len(w))]
    targets += random_targets(controls, steps)
    runs = runs_for_targets(cells, steps, max_onset, targets, margin)  # (targets, onsets, columns)
    buckets = [(a, min(b, max_onset)) for a, b in BUCKETS if a < max_onset]
    columns = cells + 2 * margin
    best = np.array([[runs[k, a:b].max() for a, b in buckets] for k in range(len(targets))])  # (targets, buckets)
    censored = any(runs[k, onset].max() >= steps - onset for k in range(len(targets)) for onset in range(max_onset))
    print(f"w = {cells}, columns {-margin} .. {cells - 1 + margin}, {steps} steps; the longest run over every row, "
          f"column and onset of each bucket{' (some run reached the last step)' if censored else ''}")
    print("| target | " + " | ".join(f"$T_0 \\in [{a}, {b})$" for a, b in buckets) + " |")
    print("|---|" + "---|" * len(buckets))
    for name, line in zip(names, best):
        print(f"| {name} | " + " | ".join(str(int(v)) for v in line) + " |")
    print(f"| {len(names)} periodic targets, least to most | " + " | ".join(
        f"{int(best[:len(names), i].min())} to {int(best[:len(names), i].max())}" for i in range(len(buckets))) + " |")
    control = best[len(names):]  # (controls, buckets)
    if control.size:
        print(f"| {controls} random targets, least to most (median) | " + " | ".join(
            f"{int(control[:, i].min())} to {int(control[:, i].max())} ({np.median(control[:, i]):g})"
            for i in range(len(buckets))) + " |")
    single = runs.max(axis=2)  # (targets, onsets): the longest run at each single onset
    for label, part in (("periodic", single[:len(names)]), ("random", single[len(names):])):
        print(f"| {label} targets, mean over single onsets | " + " | ".join(
            f"{part[:, a:b].mean():.1f}" for a, b in buckets) + " |")
    print("| chance, $\\log_2$ of the trials | " + " | ".join(f"{chance(cells, columns, b - a):.1f}"
                                                            for a, b in buckets) + " |")
    periodic, random_single = single[:len(names)], single[len(names):]  # (8, onsets), (controls, onsets)
    print(f"single onsets 0 .. {max_onset - 1}: periodic targets {int(periodic.min())} to {int(periodic.max())} "
          f"(mean {periodic.mean():.2f}); random targets {int(random_single.min())} to {int(random_single.max())} "
          f"(mean {random_single.mean():.2f}); chance for one onset {chance(cells, columns, 1):.1f}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--cells", type=int, nargs="+", default=[8, 12, 16])
    parser.add_argument("--steps", type=int, default=160)
    parser.add_argument("--max-onset", type=int, default=120)
    parser.add_argument("--margin", type=int, default=0, help="columns beyond the support on each side")
    parser.add_argument("--controls", type=int, default=24, help="random target words")
    parser.add_argument("--sat", type=int, nargs="*", help="widths for the SAT search of the middle column")
    parser.add_argument("--onsets", type=int, nargs="+", default=[0, 32, 64], help="--sat: the onsets")
    parser.add_argument("--extra", type=int, default=30, help="--sat: the cap on L is the width plus this")
    args = parser.parse_args()

    started = time.perf_counter()
    if args.sat:
        controls = random_targets(args.controls, max(args.onsets) + max(args.sat) + args.extra + 1)
        for cells in args.sat:
            for onset in args.onsets:
                cap = cells + args.extra
                periodic = {w: [sat_longest(cells, periodic_target(w, p, onset + cap), onset, cap)
                                for p in range(len(w))] for w in WORDS}
                random_runs = [sat_longest(cells, c, onset, cap)[0] for c in controls]
                print(f"w = {cells}, T0 = {onset}: " + "; ".join(
                    f"{w} by phase {[r[0] for r in rs]} (conflicts refuting the next {[r[1] for r in rs]})"
                    for w, rs in periodic.items()) + f"; random targets {random_runs}", flush=True)
    else:
        for cells in args.cells:
            report(cells, args.steps, args.max_onset, args.margin, args.controls)
    print(f"({time.perf_counter() - started:.0f} s)")


if __name__ == "__main__":
    main()
