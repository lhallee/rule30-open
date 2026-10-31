"""Traps that constrain column 1 without making it periodic, for a center repeating any block.

Drive a right half with the center repeating a block `b` from phase `p` (the center at step t is b[(t + p) % P]), and
read column 1 at the white steps of the block, the steps t with b[(t + p) % P] = 0. Under an eventual period those
readings are, up to complement, the free bits of the left half (at a white step the next center cell is column -1 xor
column 1, or that with the OR term of the cell itself when the block reads 0 then 0), so they carry what the left half
has to absorb. Masked Jen needs them periodic, and for many blocks they never become periodic. They can still become
constrained: some words never occur in them again.

A trap here is a set of states (window of columns 1..W at a step of the block's phase, the last L - 1 readings) that
one step keeps for both values of column W + 1, such that no reading completes a forbidden word. `greatest_trap`
computes the largest one for a list of forbidden words; a right half enters when its state is in it, and from then on
its readings avoid the words forever, whatever the cells beyond column W do. `forbidden_words` lists the minimal words
that a sample of driven halves never shows after a transient, `forced_entry` the windows from which every input from
the right leads into the trap, and `census` the first entry of every right half of up to `cells` cells.

    python -m computations.gap_traps --block 011 --width 16   # the trap of 011: zeros never 1, 2, 4 or 5 apart
    python -m computations.gap_traps --block 011 --width 16 --cells 16   # every half of up to 16 cells enters
    python -m computations.gap_traps --survey 7 --width 14 --cells 10   # every block of period up to 7, about 10 min
    python -m computations.gap_traps --block 001 --width 13 --words 11 1001 00100 10001 --forced   # forced
"""

from __future__ import annotations

import argparse
import functools
import sys
import time

import numpy as np
from tqdm.auto import tqdm

from computations import absorption


def is_white(block: str, phase: int, t: int) -> bool:
    """Whether the center reads 0 at step t."""
    return block[(t + phase) % len(block)] == "0"


def readings(block: str, phase: int, half: int, steps: int) -> list[int]:
    """Column 1 at the white steps before `steps` of the right half `half` (bit i the cell i + 1)."""
    row, out = half, []
    for t in range(steps):
        center = int(block[(t + phase) % len(block)])
        if center == 0:
            out.append(row & 1)
        row = ((row << 1) | center) ^ (row | (row >> 1))
    return out


def forbidden_words(block: str, length: int, halves: int, steps: int, seed: int = 0) -> list[str]:
    """The minimal words of at most `length` readings that no sampled half shows after the first quarter of its run:
    every half of up to 6 cells and `halves` random halves of 40 cells, from every phase."""
    rng = np.random.default_rng(seed)
    starts = list(range(64)) + [int(x) for x in rng.integers(0, 1 << 40, halves)]
    seen: set[str] = set()
    for phase in range(len(block)):
        for half in starts:
            r = "".join(map(str, readings(block, phase, half, steps)[steps // (4 * len(block)):]))
            for k in range(1, length + 1):
                seen.update(r[i:i + k] for i in range(len(r) - k + 1))
    minimal = []
    for k in range(1, length + 1):
        for x in range(1 << k):
            w = format(x, f"0{k}b")
            if w not in seen and w[1:] in seen and w[:-1] in seen:
                minimal.append(w)
    return minimal


def step_windows(windows: np.ndarray, width: int, center: int, beyond: int) -> np.ndarray:
    """One step of every window of columns 1..width, with `center` in column 0 and `beyond` in column width + 1."""
    # windows: (n,)
    mask = np.int64((1 << width) - 1)
    return (((windows << 1) | center) & mask) ^ (windows | ((windows >> 1) | (beyond << (width - 1))))  # (n,)


@functools.lru_cache(maxsize=None)
def greatest_trap(block: str, width: int, words: tuple[str, ...]) -> np.ndarray:
    """good[phase, window, suffix]: the greatest set of states that one step keeps for both inputs without completing
    a forbidden word. The suffix holds the last L - 1 readings, newest in bit 0, where L is the longest word; states
    are taken at the step `phase` of the block (the center reads block[phase] next)."""
    period, n = len(block), 1 << width
    keep = max(len(w) for w in words) - 1
    sufs = 1 << keep
    windows = np.arange(n, dtype=np.int64)  # (n,)
    bad_word = np.zeros((sufs, 2), dtype=bool)  # (sufs, 2): appending this reading completes a forbidden word
    for s in range(sufs):
        for bit in (0, 1):
            text = "".join(str((s >> i) & 1) for i in range(keep - 1, -1, -1)) + str(bit)
            bad_word[s, bit] = any(text.endswith(w) for w in words)
    good = np.ones((period, n, sufs), dtype=bool)  # (period, n, sufs)
    nxt = [[step_windows(windows, width, int(block[p]), x) for x in (0, 1)] for p in range(period)]  # (n,) each
    while True:
        new = good.copy()
        for p in range(period):
            q = (p + 1) % period
            for x in (0, 1):
                v = nxt[p][x]  # (n,)
                if block[p] == "0":
                    bit = (windows & 1).astype(np.int64)  # the reading at this white step, before the step
                    s_new = ((np.arange(sufs)[None, :] << 1) | bit[:, None]) & (sufs - 1)  # (n, sufs)
                    ok = ~bad_word[np.arange(sufs)[None, :], bit[:, None]] & good[q][v[:, None], s_new]
                else:
                    ok = good[q][v[:, None], np.arange(sufs)[None, :]]  # (n, sufs)
                new[p] &= ok
        if np.array_equal(new, good):
            return good  # (period, n, sufs)
        good = new


def forced_entry(good: np.ndarray, block: str, width: int) -> np.ndarray:
    """forced[phase, window, suffix]: every input sequence from the right leads from the state into the trap."""
    return forced_layers(good, block, width)[0]


def forced_layers(good: np.ndarray, block: str, width: int) -> tuple[np.ndarray, int]:
    """The states from which every input sequence leads into the trap, and the number of steps the slowest takes."""
    period, n, sufs = good.shape
    windows = np.arange(n, dtype=np.int64)  # (n,)
    nxt = [[step_windows(windows, width, int(block[p]), x) for x in (0, 1)] for p in range(period)]
    forced = good.copy()  # (period, n, sufs)
    depth = 0
    while True:
        new = forced.copy()
        for p in range(period):
            q = (p + 1) % period
            if block[p] == "0":
                bit = (windows & 1).astype(np.int64)
                s_new = ((np.arange(sufs)[None, :] << 1) | bit[:, None]) & (sufs - 1)  # (n, sufs)
            else:
                s_new = np.broadcast_to(np.arange(sufs)[None, :], (n, sufs))
            both = forced[q][nxt[p][0][:, None], s_new] & forced[q][nxt[p][1][:, None], s_new]  # (n, sufs)
            new[p] |= both
        if np.array_equal(new, forced):
            return forced, depth
        forced = new
        depth += 1


def census(block: str, width: int, words: tuple[str, ...], cells: int, phase: int, steps: int) -> np.ndarray:
    """The first step at which each right half below 2^cells is in the trap, with its true last readings, or -1."""
    good = greatest_trap(block, width, words)  # (period, 2^width, sufs)
    period, _, sufs = good.shape
    keep = sufs.bit_length() - 1
    n_words = (cells + steps + 2) // 64 + 1
    rows = np.zeros((1 << cells, n_words), dtype=np.uint64)  # (2^cells, words)
    rows[:, 0] = np.arange(1 << cells, dtype=np.uint64)
    index = np.arange(1 << cells)  # (2^cells,)
    suffix = np.zeros(1 << cells, dtype=np.int64)  # (2^cells,)
    seen = 0
    times = np.full(1 << cells, -1, dtype=np.int64)  # (2^cells,)
    mask = np.uint64((1 << width) - 1)
    for t in range(steps):
        p = (t + phase) % period
        if seen >= keep:
            inside = good[p][(rows[:, 0] & mask).astype(np.int64), suffix]  # (n,)
            times[index[inside]] = t
            rows, index, suffix = rows[~inside], index[~inside], suffix[~inside]
            if index.size == 0:
                break
        center = int(block[p])
        if center == 0:
            suffix = ((suffix << 1) | (rows[:, 0] & np.uint64(1)).astype(np.int64)) & (sufs - 1)
            seen += 1
        active = min(n_words, (cells + t + 2) // 64 + 1)
        rows[:, :active] = absorption.step_rows(rows[:, :active], center)
    return times  # (2^cells,)


def word_entropy(words: tuple[str, ...]) -> float:
    """The topological entropy, in bits per reading, of the binary sequences that avoid every word in `words`: the
    log of the spectral radius of the graph on the last L - 1 readings."""
    keep = max(len(w) for w in words) - 1
    n = 1 << keep
    graph = np.zeros((n, n))  # (n, n)
    for s in range(n):
        for bit in (0, 1):
            text = "".join(str((s >> i) & 1) for i in range(keep - 1, -1, -1)) + str(bit)
            if not any(text.endswith(w) for w in words) and not any(w in text[:-1] for w in words):
                graph[s, ((s << 1) | bit) & (n - 1)] = 1
    radius = max(abs(np.linalg.eigvals(graph))) if n > 1 else float(graph.sum())
    return float(np.log2(radius)) if radius > 0 else float("-inf")


def necklace_blocks(period: int) -> list[str]:
    """The primitive blocks of a period, one per rotation class, with at least one 0 and one 1."""
    out = []
    for x in range(1 << period):
        w = format(x, f"0{period}b")
        rotations = {w[i:] + w[:i] for i in range(period)}
        if w == min(rotations) and len(rotations) == period and "0" in w and "1" in w:
            out.append(w)
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--block", default="011")
    parser.add_argument("--width", type=int, default=16)
    parser.add_argument("--length", type=int, default=8, help="longest forbidden word to learn")
    parser.add_argument("--words", nargs="*", help="forbidden words to use instead of learning them")
    parser.add_argument("--cells", type=int, default=0, help="census of every right half of up to this many cells")
    parser.add_argument("--steps", type=int, default=4000)
    parser.add_argument("--survey", type=int, default=0, help="every primitive block of period up to this")
    parser.add_argument("--forced", action="store_true", help="whether every input from the right leads into the trap")
    args = parser.parse_args()
    started = time.perf_counter()
    blocks = [args.block] if not args.survey else [b for p in range(2, args.survey + 1) for b in necklace_blocks(p)]
    for block in tqdm(blocks, desc="blocks", file=sys.stderr, leave=False, disable=len(blocks) == 1):
        words = tuple(args.words) if args.words else tuple(forbidden_words(block, args.length, 40, 6000))
        if not words:
            print(f"{block}: every word of up to {args.length} readings occurs")
            continue
        good = greatest_trap(block, args.width, words)
        size = int(good.any(axis=2).sum())
        line = (f"{block}: forbidden {list(words)} (entropy {word_entropy(words):.3f} bits per reading); trap of {size} "
                f"(phase, window) pairs at width {args.width}")
        if size and args.forced:
            forced, depth = forced_layers(good, block, args.width)
            line += (f"; entry forced from every state within {depth} steps" if forced.all() else
                     f"; entry not forced from {int((~forced).sum())} of {forced.size} states")
        if size and args.cells:
            results = []
            for phase in range(len(block)):
                times = census(block, args.width, words, args.cells, phase, args.steps)
                results.append((int((times >= 0).sum()), int(times.max())))
            line += "; census " + ", ".join(f"phase {p}: {k} of {1 << args.cells} (latest {m})"
                                            for p, (k, m) in enumerate(results))
        print(line, flush=True)
    print(f"({time.perf_counter() - started:.0f} s)")


if __name__ == "__main__":
    main()
