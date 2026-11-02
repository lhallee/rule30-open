"""Returns of a real defect to its own top window, the memory of the walled ether defect, and its Nerode count.

The defect D_t of a 2-adic integer whose tail is the ether is defined in `defect_potential`: D_t = H^t(U) xor B_t,
with B_t the ether at an alignment (phase, offset), and (D_t, t mod 4) is the state of a deterministic system. This
module asks three questions of that system.

`returns` follows random heads until their defect enters a closed strip of 13 cells and looks, inside each orbit, for
a return to the same window state at a higher top. The window state at width k is (phase mod 4, (top + offset) mod 7,
the k - 1 cells below the top); it fixes the k actual cells at the top, since the ether cells there are fixed by the
phase and the residue. Only steps with the top at least 2k count, so that the window is far from the wall. A potential
V = top + phi(window state) that never increases along the orbit cannot exist when the orbit returns to one window
state with a higher top, and a return at width k is a return at every smaller width. `example` re-finds the first
such return at k = 24 and prints it.

`forget` asks whether the walled defect forgets its bottom: for every defect on the cells [0, m + T), grouped by its
top w cells, it counts the distinct words of the m lowest cells of D_T. A top that fixes the bottom would make the
bottom a function of the top.

`nerode` computes the highest top over a fixed number of steps of every defect below 2^bits at all 28 alignments and
counts the Nerode classes of prefixes of m cells: two prefixes are equivalent when every word of `suffix` cells on the
other side gives the same outcome at every alignment used. It reads prefixes from the bottom (cells 0 .. m - 1, the
suffix above them) and from the top (the m highest cells, the suffix below them).

    python -m computations.defect_returns returns --count 3000 --windows 8,10,12,13,14,16,18,20,24 --seed 7
    python -m computations.defect_returns returns --count 30000 --windows 13,16,20,24,28,32 --seed 11
    python -m computations.defect_returns example --window 24 --seed 7
    python -m computations.defect_returns forget --cells 3 --steps 12
    python -m computations.defect_returns nerode --bits 16 --suffix 8 --steps 600
"""

from __future__ import annotations

import argparse
import sys
from functools import cache

import numpy as np
from tqdm.auto import tqdm

from computations.defect_potential import (
    STRIP,
    background,
    closed_cell_int,
    closed_strips,
    defect_step,
    step128,
    top,
    tops128,
)
from computations.held_shift import held

U64 = np.uint64
WIDTH = 400  # cells followed for a random head; the top stays below WIDTH - 2 (checked)


@cache
def _ether(phase: int, offset: int, cells: int) -> int:
    """`defect_potential.background(phase, offset, 0, cells)`, kept for each of the 28 alignments."""
    return background(phase, offset, 0, cells)


def step(D: int, phase: int, offset: int, width: int = WIDTH) -> int:
    """`defect_potential.defect_step` with the ether kept between calls: exact for a top of at most width - 2."""
    x = D ^ _ether(phase % 4, offset, width + 1)
    return (held(x) & ((1 << width) - 1)) ^ _ether((phase + 1) % 4, offset, width)


def random_head(rng: np.random.Generator, length: int) -> tuple[int, int, int]:
    """A random alignment and a random head of `length` cells whose top cell is a defect: (phase, offset, D_0)."""
    phase, offset = int(rng.integers(4)), int(rng.integers(7))
    D = int.from_bytes(rng.bytes(length // 8 + 1), "little") & ((1 << length) - 1) | (1 << (length - 1))
    return phase, offset, D


def follow(D: int, phase: int, offset: int, steps: int, closed: np.ndarray) -> tuple[list[int], int, int]:
    """The defects D_0, D_1, ... before entry into a closed strip, the step of entry (-1 if none within `steps`), and
    the defect at that step."""
    trace: list[int] = []
    for t in range(steps):
        if closed_cell_int(D, phase + t, offset, closed) >= 0:
            return trace, t, D
        assert top(D) < WIDTH - 2
        trace.append(D)
        D = step(D, phase + t, offset)
    return trace, -1, D


def window_key(D: int, phase: int, offset: int, k: int) -> tuple[int, int, int]:
    """The window state at width k: (phase mod 4, (top + offset) mod 7, the k - 1 cells below the top)."""
    T = top(D)
    return phase % 4, (T + offset) % 7, (D >> (T - k + 1)) & ((1 << (k - 1)) - 1)


def window_keys(trace: list[int], phase: int, offset: int, k: int) -> list[tuple[int, int, int] | None]:
    """The window state at each step of the trace, None where the top is below 2k."""
    return [window_key(d, phase + i, offset, k) if top(d) >= 2 * k else None for i, d in enumerate(trace)]


def best_return(trace: list[int], keys: list[tuple[int, int, int] | None]) -> tuple[int, int, int]:
    """The largest gain top(D_i) - top(D_j) over pairs j < i with one window state, inside a stretch of steps whose top
    stays at least 2k, and the first pair (j, i) that attains it: (gain, j, i), gain 0 when there is none."""
    first: dict[tuple[int, int, int], int] = {}
    best = (0, -1, -1)
    for i, key in enumerate(keys):
        if key is None:
            first.clear()
            continue
        if key in first:
            j = first[key]
            gain = top(trace[i]) - top(trace[j])
            if gain > best[0]:
                best = (gain, j, i)
        first.setdefault(key, i)
    return best


def first_return(trace: list[int], keys: list[tuple[int, int, int] | None]) -> tuple[int, int] | None:
    """The first step i with a step j < i in the same stretch, the same window state and a lower top: (j, i)."""
    first: dict[tuple[int, int, int], int] = {}
    for i, key in enumerate(keys):
        if key is None:
            first.clear()
            continue
        if key in first and top(trace[i]) > top(trace[first[key]]):
            return first[key], i
        first.setdefault(key, i)
    return None


def back_to_back(trace: list[int], keys: list[tuple[int, int, int] | None], longest: int = 200) -> int:
    """The most passes in a row through one cycle of positive gain: for a period p up to `longest`, a stretch whose
    window states repeat with period p for r >= p steps, with the top higher after p steps, gives r // p + 1 passes."""
    best, n = 0, len(keys)
    for p in range(1, min(longest, n // 2) + 1):
        run = 0
        for i in range(p, n):
            if keys[i] is not None and keys[i] == keys[i - p]:
                run += 1
                if run >= p and top(trace[i]) > top(trace[i - p]):
                    best = max(best, run // p + 1)
            else:
                run = 0
    return best


def rises_after_entry(D: int, phase: int, offset: int, steps: int) -> bool:
    """Whether the top rises from one step to the next within `steps` steps after a defect D enters a closed strip."""
    for u in range(steps):
        E = step(D, phase + u, offset)
        if top(E) > top(D):
            return True
        D = E
    return False


def survey(count: int, length: int, steps: int, windows: list[int], seed: int) -> dict[str, object]:
    """Follow `count` random heads of `length` cells for up to `steps` steps. For each width k: the runs with a return
    of positive gain, the largest gain, and the most passes in a row through one positive cycle; also the runs that
    entered a closed strip and those whose top still rises within 56 steps after entry."""
    closed = closed_strips(STRIP)  # (4, 7, 2^13)
    rng = np.random.default_rng(seed)
    hits = {k: 0 for k in windows}
    gains = {k: 0 for k in windows}
    passes = {k: 0 for k in windows}
    entered = rising = 0
    for _ in tqdm(range(count), desc="random heads", file=sys.stderr):
        phase, offset, D = random_head(rng, length)
        trace, entry, last = follow(D, phase, offset, steps, closed)
        if entry >= 0:
            entered += 1
            rising += rises_after_entry(last, phase + entry, offset, 56)
        for k in windows:
            keys = window_keys(trace, phase, offset, k)
            gain, _, _ = best_return(trace, keys)
            if gain > 0:
                hits[k] += 1
                gains[k] = max(gains[k], gain)
                passes[k] = max(passes[k], back_to_back(trace, keys))
    return {"entered": entered, "rising": rising, "hits": hits, "gains": gains, "passes": passes}


def example(window: int, count: int, length: int, steps: int, seed: int) -> tuple[int, int, int, int, int, int] | None:
    """The first random head (in the order of `survey` with the same seed) whose orbit returns to one window state of
    `window` cells at a higher top before entry: (D_0, phase, offset, j, i, step of entry)."""
    closed = closed_strips(STRIP)  # (4, 7, 2^13)
    rng = np.random.default_rng(seed)
    for _ in range(count):
        phase, offset, D = random_head(rng, length)
        trace, entry, _ = follow(D, phase, offset, steps, closed)
        pair = first_return(trace, window_keys(trace, phase, offset, window))
        if pair is not None:
            return D, phase, offset, pair[0], pair[1], entry
    return None


def bottoms(m: int, t_max: int, phase: int, offset: int) -> np.ndarray:
    """The m lowest cells of D_t for every defect D_0 < 2^(m + t_max) at t = 0 .. t_max: (t_max + 1, 2^(m + t_max))."""
    n = 1 << (m + t_max)
    lo = np.arange(n, dtype=np.uint64)  # (n,)
    hi = np.zeros(n, dtype=np.uint64)  # (n,)
    out = np.zeros((t_max + 1, n), dtype=np.int64)  # (t_max + 1, n)
    out[0] = (lo & U64((1 << m) - 1)).astype(np.int64)
    for t in range(t_max):
        lo, hi = step128(lo, hi, phase + t, offset)
        out[t + 1] = (lo & U64((1 << m) - 1)).astype(np.int64)
    return out


def bottom_spread(bottom: np.ndarray, m: int, T: int, w: int) -> tuple[int, float]:
    """Over the defects on [0, m + T), grouped by their top w cells: the most distinct bottom words of D_T in one group
    and the share of groups with exactly one. bottom: (>= 2^(m + T),) the bottom word of D_T of each defect."""
    L = m + T
    d = np.arange(1 << L, dtype=np.int64)  # (2^L,)
    pairs = np.unique((d >> (L - w)) * (1 << m) + bottom[: 1 << L])  # (pairs,) top word and bottom word
    _, counts = np.unique(pairs >> m, return_counts=True)  # (groups,)
    return int(counts.max()), float(np.mean(counts == 1))


def forget_table(m: int, t_max: int) -> dict[tuple[int, int], tuple[int, float]]:
    """For T = 1 .. t_max and w = 6 and w = m + T - 2 (two free cells): the most distinct bottoms over the 28
    alignments and the mean share of top words that fix the bottom."""
    worst: dict[tuple[int, int], list[int]] = {}
    share: dict[tuple[int, int], list[float]] = {}
    for a in tqdm(range(28), desc="alignments", file=sys.stderr, leave=False):
        b = bottoms(m, t_max, *divmod(a, 7))  # (t_max + 1, 2^(m + t_max))
        for T in range(1, t_max + 1):
            for w in sorted({6, max(6, m + T - 2)}):
                if w <= m + T:
                    c, s = bottom_spread(b[T], m, T, w)
                    worst.setdefault((T, w), []).append(c)
                    share.setdefault((T, w), []).append(s)
    return {key: (max(worst[key]), float(np.mean(share[key]))) for key in worst}


def flip_share(m: int, T: int, phase: int, offset: int) -> float:
    """The share of defects on [0, m + T) whose m lowest cells at step T do not change when cell 0 alone is flipped."""
    b = bottoms(m, T, phase, offset)[T]  # (2^(m + T),)
    d = np.arange(1 << (m + T))  # (2^(m + T),)
    return float(np.mean(b == b[d ^ 1]))


def highest_tops(bits: int, steps: int) -> np.ndarray:
    """The highest top over `steps` steps of every defect below 2^bits at each alignment 7 phase + offset: (28, 2^bits).
    Exact while the top stays below 127 (checked)."""
    out = np.zeros((28, 1 << bits), dtype=np.int64)  # (28, 2^bits)
    for a in tqdm(range(28), desc="alignments", file=sys.stderr, leave=False):
        phase, offset = divmod(a, 7)
        lo = np.arange(1 << bits, dtype=np.uint64)  # (2^bits,)
        hi = np.zeros(1 << bits, dtype=np.uint64)  # (2^bits,)
        best = tops128(lo, hi)  # (2^bits,)
        for t in range(steps):
            lo, hi = step128(lo, hi, phase + t, offset)
            best = np.maximum(best, tops128(lo, hi))
        assert best.max() <= 125
        out[a] = best
    return out


def nerode_classes(table: np.ndarray, m: int, suffix: int, low_prefix: bool) -> int:
    """The number of classes of the 2^m prefixes under: equal outcome for every suffix word at every row. table:
    (alignments, 2^(m + suffix)), the outcome of each word of m + suffix cells (bit i the cell i)."""
    p = np.arange(1 << m)[:, None]  # (2^m, 1)
    s = np.arange(1 << suffix)[None, :]  # (1, 2^suffix)
    words = p | (s << m) if low_prefix else s | (p << suffix)  # (2^m, 2^suffix)
    vec = np.transpose(table[:, words], (1, 0, 2)).reshape(1 << m, -1)  # (2^m, alignments 2^suffix)
    return len(np.unique(vec, axis=0))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("mode", choices=["returns", "example", "forget", "nerode"])
    parser.add_argument("--count", type=int, default=3000)
    parser.add_argument("--length", type=int, default=40)
    parser.add_argument("--steps", type=int, default=2000)
    parser.add_argument("--windows", type=str, default="8,10,12,13,14,16,18,20,24")
    parser.add_argument("--window", type=int, default=24)
    parser.add_argument("--seed", type=int, default=7)
    parser.add_argument("--cells", type=int, default=3)
    parser.add_argument("--bits", type=int, default=16)
    parser.add_argument("--suffix", type=int, default=8)
    args = parser.parse_args()
    if args.mode == "returns":
        windows = [int(k) for k in args.windows.split(",")]
        r = survey(args.count, args.length, args.steps, windows, args.seed)
        print(f"{args.count} random heads of {args.length} cells, seed {args.seed}: entered a closed strip within "
              f"{args.steps} steps {r['entered']}; top still rises step to step within 56 steps after entry "
              f"{r['rising']}")
        print("k  runs-with-positive-return  largest-gain  most-passes-in-a-row")
        for k in windows:
            print(f"{k:2d} {r['hits'][k]:6d} {r['gains'][k]:6d} {r['passes'][k]:4d}")
    elif args.mode == "example":
        found = example(args.window, args.count, args.length, args.steps, args.seed)
        if found is None:
            print(f"no return at window {args.window} in {args.count} heads")
        else:
            D, phase, offset, j, i, entry = found
            E = D
            tops = {}
            for t in range(i + 1):
                tops[t] = top(E)
                E = defect_step(E, phase + t, offset, WIDTH)
            print(f"head {D:#x}, phase {phase}, offset {offset}: top {tops[j]} at step {j}, top {tops[i]} at step {i}, "
                  f"the same window state of {args.window} cells; entry into a closed strip at step {entry}")
    elif args.mode == "forget":
        m = args.cells
        print("T  w  free-cells  most-distinct-bottoms  mean-share-of-top-words-with-one-bottom")
        for (T, w), (c, s) in sorted(forget_table(m, args.steps).items()):
            print(f"{T:2d} {w:2d} {m + T - w:3d} {c:4d} {s:8.3f}")
        for T in (4, 8, 12):
            print(f"T = {T}: share of defects whose {m} lowest cells ignore a flip of cell 0, alignment (0, 0): "
                  f"{flip_share(m, T, 0, 0):.3f}")
    else:
        tops = highest_tops(args.bits, args.steps)  # (28, 2^bits)
        print(f"highest top over {args.steps} steps of every defect below 2^{args.bits}: {int(tops.max())}")
        S = args.suffix
        ms = range(1, args.bits - S + 1)
        outcomes = {"exact top": lambda t, n: t, "top // 4": lambda t, n: t // 4,
                    "rise >= 10": lambda t, n: (t - (n - 1) >= 10).astype(np.int64)}
        for name, f in outcomes.items():
            for low in (True, False):
                row = [nerode_classes(f(tops[:, : 1 << (m + S)], m + S), m, S, low) for m in ms]
                print(f"{name}, {'low' if low else 'high'} prefixes, 28 alignments: c(m) for m = 1 .. {ms[-1]}: {row}")
        for a in (0, 13):
            for low in (True, False):
                row = [nerode_classes(outcomes["rise >= 10"](tops[a:a + 1, : 1 << (m + S)], m + S), m, S, low)
                       for m in ms]
                print(f"rise >= 10, {'low' if low else 'high'} prefixes, alignment {a}: c(m): {row}")


if __name__ == "__main__":
    main()
