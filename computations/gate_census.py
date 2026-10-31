"""Where right halves beside an alternating center end up: a gap trap, a lock of period seven, or the ether family.

Drive a right half with the center alternating, black at the even steps when `phase` is 0 and at the odd steps when it
is 1 (phase 0 is the kit's `altCol`). A right half is an integer whose bit i is cell i + 1. At the white steps, column
1 is the kit's `u R`, the sequence whose complement the one candidate left half `Psi R` takes as its free bits. Three
closed sets of windows decide what column 1 does from some step on, whatever the cells beyond the window do:

- `gap_states(16)`: the greatest set of pairs (window of columns 1..16, white steps since the last black cell of
  column 1) that the double step keeps for every input from the right and on which the next black cell comes 3 or 5
  white steps later. A half whose window is black in column 1 and good with 0 steps since the last black cell has gaps
  of 3 and 5 from then on, the setting of the kit's `Rule30GateTrap` (its 829 windows are all good, `kit_trap_inside`)
  and of its open `Q01Gap`.
- `seven_lock()`: the closure of the late windows of columns 1..32 of the half 0101001 (the number 74, which locks
  with period 14) under every input from the right: 195 windows in seven classes, on which column 1 repeats 0101000
  at the white steps. `Rule30Open.PeriodTwo.SevenLock` checks the closure in the kernel and turns it into an
  exclusion of period two for every half that enters it.
- The kit's ether-and-wall family for the word 0101 (`computations.absorption`), on which column 1 is periodic.

`census` follows every right half of up to `cells` cells and reports which set it enters first.

    python -m computations.gate_census census --cells 16 --steps 8000   # about 2 min
    python -m computations.gate_census lock   # the lock of period seven and its classes
    python -m computations.gate_census lean   # the classes as the Lean file lists them
    python -m computations.gate_census zones   # the time-periodic zones of halves that lock
"""

from __future__ import annotations

import argparse
import functools
import sys
import time
from collections import deque

import numpy as np
from tqdm.auto import tqdm

from computations import absorption

GAP_WIDTH = 16
LOCK_WIDTH = 32
LOCK_SEED = 74  # cells 2, 4 and 7 black: locks with period 14 from about step 380
LOCK_WORD = "0101000"  # column 1 at successive white steps, class 0 first


def step_window(w: int, width: int, center: int, beyond: int) -> int:
    """One step of the window `w` of columns 1..width, with `center` in column 0 and `beyond` in column width + 1."""
    left = ((w << 1) | center) & ((1 << width) - 1)
    right = (w >> 1) | (beyond << (width - 1))
    return left ^ (w | right)


def double_step(w: int, width: int, x1: int, x2: int) -> int:
    """Two steps from a white step of the center: column 0 is white, then black; x1, x2 are column width + 1."""
    return step_window(step_window(w, width, 0, x1), width, 1, x2)


def double_steps(windows: np.ndarray, width: int) -> np.ndarray:
    """The four double steps of every window, for the inputs (x1, x2) = 00, 01, 10, 11."""
    # windows: (n,)
    mask = np.int64((1 << width) - 1)
    out = []
    for x1 in (0, 1):
        for x2 in (0, 1):
            w = windows.astype(np.int64)  # (n,)
            for center, beyond in ((0, x1), (1, x2)):
                w = (((w << 1) | center) & mask) ^ (w | ((w >> 1) | (beyond << (width - 1))))
            out.append(w)
    return np.stack(out, axis=1)  # (n, 4)


@functools.lru_cache(maxsize=None)
def gap_states(width: int = GAP_WIDTH) -> np.ndarray:
    """good[w, d]: from window w at a white step, d white steps after the last black cell of column 1 (d = 5: none
    yet), every later black cell of column 1 comes 3 or 5 white steps after the one before, whatever the input from
    the right. The greatest fixed point, by removing bad states until none is left."""
    succ = double_steps(np.arange(1 << width), width)  # (2^width, 4)
    black = (succ & 1).astype(bool)  # (2^width, 4)
    good = np.ones((1 << width, 6), dtype=bool)  # (2^width, 6)
    while True:
        new = good.copy()
        for d in range(6):
            for j in range(4):
                v, b = succ[:, j], black[:, j]  # (2^width,) each
                if d == 5:
                    ok = np.where(b, good[v, 0], good[v, 5])
                else:
                    gap = d + 1
                    ok = np.where(b, (gap in (3, 5)) & good[v, 0], (gap < 5) & good[v, min(gap, 4)])
                new[:, d] &= ok
        if np.array_equal(new, good):
            return good  # (2^width, 6)
        good = new


def gap_entry(width: int = GAP_WIDTH) -> np.ndarray:
    """The windows black in column 1 from which every later gap is 3 or 5."""
    good = gap_states(width)  # (2^width, 6)
    return good[:, 0] & (np.arange(1 << width) & 1).astype(bool)  # (2^width,)


def kit_trap_inside(codes: list[int], width: int = GAP_WIDTH) -> bool:
    """Whether every window of a list (such as the kit's `trapCodes`) is good for some count of white steps."""
    good = gap_states(width)  # (2^width, 6)
    return bool(good[np.array(codes)].any(axis=1).all())


def late_windows(half: int, phase: int, steps: int, start: int, width: int) -> list[int]:
    """The windows of columns 1..width at the white steps from `start` to `steps` of the driven half."""
    row, out = half, []
    for t in range(steps):
        center = 1 if (t + phase) % 2 == 0 else 0
        if center == 0 and t >= start:
            out.append(row & ((1 << width) - 1))
        row = ((row << 1) | center) ^ (row | (row >> 1))
    return out


def closure(seeds: list[int], width: int, cap: int = 1 << 22) -> set[int] | None:
    """The windows reachable from `seeds` by double steps with every input, or None past `cap` windows."""
    seen, queue = set(seeds), deque(seeds)
    while queue:
        w = queue.popleft()
        for x1 in (0, 1):
            for x2 in (0, 1):
                v = double_step(w, width, x1, x2)
                if v not in seen:
                    seen.add(v)
                    queue.append(v)
                    if len(seen) > cap:
                        return None
    return seen


def phase_classes(windows: set[int], width: int, period: int) -> tuple[list[list[int]], str] | None:
    """Split a closed set into classes 0..period-1 that the double step moves from k to k + 1, with column 1 constant
    on each class, starting from the least window; None if no such split exists. Assumes one connected component."""
    first = min(windows)
    label = {first: 0}
    queue = deque([first])
    while queue:
        w = queue.popleft()
        for x1 in (0, 1):
            for x2 in (0, 1):
                v, k = double_step(w, width, x1, x2), (label[w] + 1) % period
                if v in label:
                    if label[v] != k:
                        return None
                else:
                    label[v] = k
                    queue.append(v)
    if set(label) != windows:
        return None
    word = ["?"] * period
    for w, k in label.items():
        if word[k] not in ("?", str(w & 1)):
            return None
        word[k] = str(w & 1)
    classes = [sorted(w for w, k in label.items() if k == j) for j in range(period)]
    return classes, "".join(word)


@functools.lru_cache(maxsize=None)
def seven_lock(steps: int = 8000) -> tuple[list[list[int]], str]:
    """The lock of period seven: the closure of the late windows of `LOCK_SEED`, split into its seven classes,
    rotated so that its column-1 word is `LOCK_WORD`."""
    seeds = sorted(set(late_windows(LOCK_SEED, 0, steps, steps // 2, LOCK_WIDTH)))
    windows = closure(seeds, LOCK_WIDTH)
    assert windows is not None
    split = phase_classes(windows, LOCK_WIDTH, 7)
    assert split is not None
    classes, word = split
    for r in range(7):
        if word[r:] + word[:r] == LOCK_WORD:
            return classes[r:] + classes[:r], LOCK_WORD
    raise AssertionError(word)


def census(cells: int, phase: int, steps: int, gap: np.ndarray, lock: list[list[int]],
           wall: np.ndarray) -> dict[str, np.ndarray]:
    """For every right half below 2^cells: the first white step at which it enters the gap trap, the lock, or (checked
    only for the halves that enter neither) the kit's ether-and-wall family; -1 if not before `steps`."""
    lock_codes = np.array(sorted(c for cls in lock for c in cls), dtype=np.uint64)  # (195,)
    words = (cells + steps + 2) // 64 + 1
    rows = np.zeros((1 << cells, words), dtype=np.uint64)  # (2^cells, words)
    rows[:, 0] = np.arange(1 << cells, dtype=np.uint64)
    index = np.arange(1 << cells)  # (2^cells,)
    entry = {name: np.full(1 << cells, -1, dtype=np.int64) for name in ("gap", "lock", "family")}  # (2^cells,) each
    for t in tqdm(range(steps), desc=f"cells {cells} phase {phase}", file=sys.stderr, leave=False):
        center = 1 if (t + phase) % 2 == 0 else 0
        if center == 0:
            low = rows[:, 0]  # (n,)
            in_gap = gap[(low & np.uint64(0xFFFF)).astype(np.int64)]  # (n,)
            in_lock = np.isin(low & np.uint64(0xFFFFFFFF), lock_codes) & ~in_gap  # (n,)
            entry["gap"][index[in_gap]] = t
            entry["lock"][index[in_lock]] = t
            keep = ~(in_gap | in_lock)  # (n,)
            rows, index = rows[keep], index[keep]
            if index.size == 0:
                break
        active = min(words, (cells + t + 2) // 64 + 1)
        rows[:, :active] = absorption.step_rows(rows[:, :active], center)
    rest = np.flatnonzero((entry["gap"] < 0) & (entry["lock"] < 0))  # (m,)
    if rest.size:
        start = np.zeros((rest.size, words), dtype=np.uint64)  # (m, words)
        start[:, 0] = rest.astype(np.uint64)
        # absorption's phase p reads the word 0101 at (t + p) % 4, so its phase 1 is black at the even steps
        entry["family"][rest] = absorption.absorb("0101", start, 1 - phase, steps, wall, cells)
    return entry


def periodic_zone(half: int, phase: int, period: int, steps: int) -> int:
    """How many columns 1, 2, ... of the driven half repeat with `period` (in steps) over the second half of the run."""
    rows, row = [], half
    for t in range(steps):
        rows.append(row)
        center = 1 if (t + phase) % 2 == 0 else 0
        row = ((row << 1) | center) ^ (row | (row >> 1))
    zone = 0
    while all((rows[t] >> zone) & 1 == (rows[t + period] >> zone) & 1 for t in range(steps // 2, steps - period)):
        zone += 1
    return zone


def lean_classes(classes: list[list[int]]) -> str:
    """The match arms of `lockCls` in `Rule30Open.PeriodTwo.SevenLock`."""
    arms = []
    for k, codes in enumerate(classes):
        lines = ",\n    ".join(", ".join(str(c) for c in codes[i:i + 8]) for i in range(0, len(codes), 8))
        arms.append(f"  | {k} => [\n    {lines}]")
    return "\n".join(arms)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("mode", choices=["census", "lock", "lean", "zones"])
    parser.add_argument("--cells", type=int, default=12)
    parser.add_argument("--steps", type=int, default=8000)
    args = parser.parse_args()
    started = time.perf_counter()
    classes, word = seven_lock()
    if args.mode == "lean":
        print(lean_classes(classes))
        return
    print(f"lock of period seven: {sum(map(len, classes))} windows of {LOCK_WIDTH} cells, classes of "
          f"{[len(c) for c in classes]}, column 1 reads {word} at the white steps")
    if args.mode == "lock":
        return
    if args.mode == "zones":
        for half, phase in ((0x1F, 0), (0x3B0, 0), (0x1D870, 0), (LOCK_SEED, 0)):
            period = 14 if half == LOCK_SEED else 4
            cells = "".join(str((half >> i) & 1) for i in range(half.bit_length()))
            print(f"half {cells} (cell 1 first), phase {phase}: columns 1 to "
                  f"{periodic_zone(half, phase, period, 12000)} repeat with period {period}")
        return
    gap = gap_entry()  # (2^16,)
    print(f"gap trap: {int(gap.sum())} windows of {GAP_WIDTH} cells black in column 1 with every later gap 3 or 5")
    wall = absorption.kit_wall()  # (4, 2^13)
    for phase in (0, 1):
        entry = census(args.cells, phase, args.steps, gap, classes, wall)
        counts = {name: int((times >= 0).sum()) for name, times in entry.items()}
        latest = {name: int(times.max()) for name, times in entry.items()}
        none = np.flatnonzero((entry["gap"] < 0) & (entry["lock"] < 0) & (entry["family"] < 0))
        print(f"phase {phase}: of {1 << args.cells} right halves of up to {args.cells} cells, {counts['gap']} enter "
              f"the gap trap (latest at step {latest['gap']}), {counts['lock']} the lock (latest {latest['lock']}), "
              f"{counts['family']} the kit's family (latest {latest['family']}), {none.size} none within "
              f"{args.steps} steps" + (f": {[hex(h) for h in none[:10]]}" if none.size else ""))
    print(f"({time.perf_counter() - started:.0f} s)")


if __name__ == "__main__":
    main()
