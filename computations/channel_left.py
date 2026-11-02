"""The kit's left-half statement C3 for a period-four word, with the free reading constrained by the right channel.

`C3 w` (the kit's `Rule30PeriodFourSkeleton.C3`) asks that no finitely supported left half, run with the effective
boundary c'(t) = w(t) and w(t + 1), keep column -1 on the pattern P_w from some time on: (0, *, 0, 1) for 0001,
(*, 0, 0, 1) for 0011 and 0111, with one free reading in four. At a white phase column -1 is column 1 xor the next
center cell, so the free reading is column 1 at one phase, a reading of the right channel of `channel_ladder`. Beside a
center that repeats w, the window of columns 1 .. W lies in the limit set after finitely many periods, and from then on
column 1 reads the labels of a path of the limit set's step graph. So a left half that meets `C3 w` and sits beside a
real right half has, from some time on, readings that the channel's automaton accepts.

- `channel_dfa` builds that automaton: the subset automaton of the whole limit set at width W, one state per set of
  windows at one phase, started from the whole limit set at each phase, reading column 1 at the white phases (the
  readings at the black phase are not needed: column -1 there is fixed). `minimize` merges states with the same
  future (Moore's refinement); `entropy` is the bits per step of the column -1 sequences that the pattern and the
  automaton allow together.
- `tree_failures` is the search of `constrained_left.tree_failures` with the automaton's state in place of the
  history of readings: every left half of at most M cells whose column -1 keeps the condition through step M - 1 is
  followed with white cells beyond -M until it fails. The count of such halves is the count of allowed words.
- `run_half` steps one half cell by cell, for the tests.

    python -m computations.channel_left --word 0001 --width 22 --projection 16-24   # entropy of the free reading
    python -m computations.channel_left --word 0001 --width 22 --tree 100          # the census, every phase
    python -m computations.channel_left --word 0001 --tree 60 --free               # the kit's C3, unconstrained
"""

from __future__ import annotations

import argparse
import math
import sys
import time
from dataclasses import dataclass

import numpy as np
from tqdm.auto import tqdm

from computations.channel_ladder import (
    Ladder,
    growth_of,
    limit_sets,
    parse_widths,
    subset_automaton,
    white_reads,
)
from computations.constrained_left import effective
from computations.held_map import next_diagonal

# The kit's pattern P_w on column -1 at phases 0 to 3 (`colPattern`), '*' for the free reading.
PATTERNS = {"0001": "0*01", "0011": "*001", "0111": "*001"}


@dataclass(frozen=True)
class Channel:
    """A deterministic automaton on column 1, one state per step: `phase` (S,) is the phase of each state, `delta`
    (S, 2) the state after column 1 reads 0 or 1 at that phase (-1 where no path reads it; both entries equal at a
    phase that is not read), `start` (P,) the state of the whole limit set at each phase."""

    block: str
    width: int
    reads: tuple[int, ...]
    phase: np.ndarray  # (S,)
    delta: np.ndarray  # (S, 2)
    start: np.ndarray  # (P,)


def channel_dfa(ladder: Ladder, reads: tuple[int, ...] | None = None, progress: bool = False) -> Channel:
    """The subset automaton of the readings of every path of the limit set's step graph, from each phase."""
    block = ladder.block
    reads = white_reads(block) if reads is None else reads
    period = len(block)
    windows = np.concatenate(ladder.sets)  # (N,)
    node_phase = np.repeat(np.arange(period), np.diff(ladder.offset))  # (N,)
    readable = np.isin(node_phase, np.array(reads, dtype=np.int64))  # (N,)
    word = np.where(readable, windows & 1, 0).astype(np.int64)  # (N,)
    initial = [np.arange(ladder.offset[k], ladder.offset[k + 1], dtype=np.int64) for k in range(period)]
    states, sources, targets, words, complete = subset_automaton(word, ladder.succ, initial, progress=progress)
    assert complete
    # the phase of each state: states are reached from the initial ones one step at a time
    phase = np.full(states, -1, dtype=np.int64)  # (S,)
    phase[:period] = np.arange(period)
    order = np.argsort(sources, kind="stable")
    sources, targets, words = sources[order], targets[order], words[order]
    changed = True
    while changed:
        known = phase[sources] >= 0
        fill = known & (phase[targets] < 0)
        phase[targets[fill]] = (phase[sources[fill]] + 1) % period
        changed = bool(fill.any())
    assert (phase >= 0).all()
    assert (phase[targets] == (phase[sources] + 1) % period).all()
    delta = np.full((states, 2), -1, dtype=np.int64)  # (S, 2)
    read = np.isin(phase[sources], np.array(reads, dtype=np.int64))  # (moves,)
    delta[sources[read], words[read]] = targets[read]
    delta[sources[~read], 0] = targets[~read]
    delta[sources[~read], 1] = targets[~read]
    return Channel(block, ladder.width, tuple(reads), phase, delta, np.arange(period, dtype=np.int64))


def minimize(channel: Channel) -> Channel:
    """The minimal automaton with the same language from each state: Moore's refinement of the partition by phase."""
    label = channel.phase.copy()  # (S,)
    count = int(label.max()) + 1
    while True:
        nxt = np.where(channel.delta >= 0, label[np.maximum(channel.delta, 0)], -1)  # (S, 2)
        base = np.int64(count + 1)
        key = (label * base + nxt[:, 0] + 1) * base + nxt[:, 1] + 1  # (S,), the class and the classes it moves to
        order = np.argsort(key, kind="stable")  # (S,)
        new = np.concatenate([[False], key[order][1:] != key[order][:-1]])  # (S,)
        fresh = np.empty(key.size, dtype=np.int64)  # (S,)
        fresh[order] = np.cumsum(new)
        if int(fresh.max()) + 1 == count:
            break
        label, count = fresh, int(fresh.max()) + 1
    first = np.zeros(count, dtype=np.int64)  # (C,), one state of each class
    first[label[::-1]] = np.arange(label.size)[::-1]
    delta = np.where(channel.delta[first] >= 0, label[np.maximum(channel.delta[first], 0)], -1)  # (C, 2)
    return Channel(channel.block, channel.width, channel.reads, channel.phase[first], delta, label[channel.start])


def with_no11(channel: Channel) -> Channel:
    """The product with the kit's `no11_0001` for 0001: column 1 at phase 1 is never black in two consecutive periods.
    State 2 s + b is state s with b the last reading at phase 1."""
    assert channel.block == "0001"
    size = channel.phase.size
    delta = np.full((2 * size, 2), -1, dtype=np.int64)  # (2 S, 2)
    for last in (0, 1):
        rows = 2 * np.arange(size) + last  # (S,)
        for value in (0, 1):
            target = channel.delta[:, value]  # (S,)
            keep = np.where(channel.phase == 1, value, last)  # (S,), the last phase-1 reading after the move
            after = np.where(target >= 0, 2 * target + keep, -1)  # (S,)
            after[(channel.phase == 1) & (last == 1) & (value == 1)] = -1
            delta[rows, value] = after
    product = Channel(channel.block, channel.width, channel.reads, np.repeat(channel.phase, 2), delta,
                      2 * channel.start)
    return minimize(product)


def build(word: str, width: int, base: int = 10, progress: bool = False, no11: bool = False) -> Channel:
    """The minimal channel automaton of `word` at `width`, with the kit's `no11_0001` if `no11`."""
    ladder = limit_sets(word, [width], base=base, progress=progress)[width]
    channel = minimize(channel_dfa(ladder, progress=progress))
    return with_no11(channel) if no11 else channel


def advance(channel: Channel | None, pattern: str, state: int, phase: int, value: int) -> int | None:
    """The state after column -1 reads `value` at a step of phase `phase`, or None if the pattern or the channel
    fails there. Without a channel the state stays 0 (the kit's C3)."""
    want = pattern[phase]
    if want != "*" and int(want) != value:
        return None
    if channel is None:
        return state
    block = channel.block
    reading = value ^ int(block[(phase + 1) % len(block)]) if block[phase] == "0" else 0
    after = int(channel.delta[state, reading])
    return None if after < 0 else after


def transfer(channel: Channel, pattern: str) -> tuple[np.ndarray, np.ndarray]:
    """The moves (source, target) of the automaton on column -1, one per allowed value. Shapes (k,), (k,)."""
    sources, targets = [], []
    for state in range(channel.phase.size):
        for value in (0, 1):
            after = advance(channel, pattern, state, int(channel.phase[state]), value)
            if after is not None:
                sources.append(state)
                targets.append(after)
    return np.array(sources, dtype=np.int64), np.array(targets, dtype=np.int64)


def entropy(channel: Channel | None, pattern: str) -> float:
    """Bits per step of the column -1 sequences that the pattern and the channel allow: log2 of the Perron root of
    the automaton's graph (the Collatz-Wielandt upper bound, within 1e-7 of the lower)."""
    if channel is None:
        return pattern.count("*") / len(pattern)
    sources, targets = transfer(channel, pattern)
    _, high = growth_of(channel.phase.size, sources, targets)
    return math.log2(high)


def count_words(channel: Channel | None, pattern: str, phase: int, length: int) -> list[int]:
    """For n = 1 .. length, the number of words of n values of column -1 from phase `phase` that are allowed."""
    period = len(pattern)
    counts = {0 if channel is None else int(channel.start[phase]): 1}
    out = []
    for t in range(length):
        nxt: dict[int, int] = {}
        for state, c in counts.items():
            for value in (0, 1):
                after = advance(channel, pattern, state, (t + phase) % period, value)
                if after is not None:
                    nxt[after] = nxt.get(after, 0) + c
        counts = nxt
        out.append(sum(counts.values()))
    return out


def run_half(channel: Channel | None, word: str, half: int, phase: int, limit: int) -> int:
    """The first step at which the left half `half` (bit j is cell -1 - j) fails, run from phase `phase`, or `limit`
    if it keeps the condition through step `limit` - 1."""
    pattern, boundary, period = PATTERNS[word], effective(word), len(word)
    state, u = (0 if channel is None else int(channel.start[phase])), half
    for t in range(limit):
        p = (t + phase) % period
        after = advance(channel, pattern, state, p, u & 1)
        if after is None:
            return t
        state = after
        u = (u >> 1) ^ (u | (u << 1) | boundary[p])
    return limit


def tree_failures(channel: Channel | None, word: str, max_support: int, phase: int,
                  limit: int = 100000) -> tuple[list[int], list[int]]:
    """For each M up to `max_support`: the latest first failure over the left halves of exactly M cells run from
    phase `phase`, and the number of halves of at most M cells that keep the condition through step M - 1. The search
    of `constrained_left.tree_failures` with the channel's state in place of the history. Raises AssertionError if a
    half keeps the condition through step `limit`."""
    pattern, boundary, period = PATTERNS[word], effective(word), len(word)
    latest, branches = [0] * (max_support + 1), [0] * (max_support + 1)
    early = [False] * (max_support + 1)
    start = 0 if channel is None else int(channel.start[phase])
    stack = [(0, 0, 0, 0, start)]  # (m, antidiagonal m - 1, antidiagonal m - 2, bit m - 1, state at step m)
    while stack:
        m, a1, a2, top, state = stack.pop()
        if m:
            branches[m] += 1
        if top:  # follow the half, of exactly m cells, until it fails
            t, b1, b2, s = m, a1, a2, state
            while True:
                d = b1 | b2 | (boundary[(t - 1 + phase) % period] << (t - 1))
                after = advance(channel, pattern, s, (t + phase) % period, d.bit_count() % 2)
                if after is None:
                    break
                s = after
                assert t < limit, f"a half of {m} cells keeps the condition through step {limit}"
                b1, b2, t = next_diagonal(0, d, t), b1, t + 1
            latest[m] = max(latest[m], t)
        if m == max_support:
            continue
        d = a1 | a2 | ((boundary[(m - 1 + phase) % period] << (m - 1)) if m else 0)
        parity = d.bit_count() % 2
        for value in (0, 1):
            u = value ^ parity
            after = advance(channel, pattern, state, (m + phase) % period, value)
            if after is not None:
                stack.append((m + 1, next_diagonal(u, d, m), a1, u, after))
            else:
                latest[m + 1] = max(latest[m + 1], m) if u else latest[m + 1]
                early[m] = True
    for support in range(2, max_support + 1):
        latest[support] = max([latest[support]] + [m for m in range(support - 1) if early[m]])
    return latest[1:], branches[1:]


def census(channel: Channel | None, word: str, max_support: int) -> dict[str, object]:
    """Every phase of `tree_failures`: margins past M, branch counts summed over the phases, and the fair-coin margin
    hM/(1 - h) at M = `max_support` for the entropy h of the condition."""
    period = len(word)
    runs = [tree_failures(channel, word, max_support, phase)
            for phase in tqdm(range(period), desc="phases", file=sys.stderr, leave=False)]
    latest = [max(run[0][m - 1] for run in runs) for m in range(1, max_support + 1)]
    margin = [latest[m - 1] - m for m in range(1, max_support + 1)]
    total = [sum(run[1][m - 1] for run in runs) for m in range(1, max_support + 1)]
    h = entropy(channel, PATTERNS[word])
    return {"entropy": h, "latest": latest, "margins": margin, "branches": total, "largest": max(margin),
            "at": 1 + max(range(max_support), key=lambda m: margin[m]), "coins": max_support * h / (1 - h)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--word", default="0001", choices=sorted(PATTERNS))
    parser.add_argument("--width", type=int, default=22)
    parser.add_argument("--projection", help="widths at which to report the automaton and its entropy, e.g. 16-24")
    parser.add_argument("--tree", type=int, help="the census of the halves of at most this many cells")
    parser.add_argument("--free", action="store_true", help="the kit's C3 without the channel")
    parser.add_argument("--no11", action="store_true", help="also the kit's no11_0001 (0001 only)")
    args = parser.parse_args()
    word = args.word
    if args.projection:
        widths = parse_widths(args.projection)
        ladders = limit_sets(word, widths, progress=True)
        for width in widths:
            began = time.time()
            full = channel_dfa(ladders[width], progress=True)
            small = minimize(full)
            h = entropy(small, PATTERNS[word])
            print(f"{word} W {width}: automaton {full.phase.size} states, minimal {small.phase.size}; "
                  f"{h:.5f} bits per step, {4 * h:.4f} bits per period ({h / 0.25:.3f} of the kit's free reading) "
                  f"[{time.time() - began:.0f} s]", flush=True)
    if args.tree:
        channel = None if args.free else build(word, args.width, progress=True, no11=args.no11)
        began = time.time()
        row = census(channel, word, args.tree)
        margins = row["margins"]
        name = "free" if args.free else f"channel W {args.width}" + (" with no11" if args.no11 else "")
        print(f"{word} {name}: entropy {row['entropy']:.5f} bits per "
              f"step; every half of at most {args.tree} cells fails, in every phase")
        print(f"  largest margin {row['largest']} at M = {row['at']}; fair coins at M: {row['coins']:.1f}")
        for m in range(10, args.tree + 1, 10):
            print(f"  M {m}: latest failure {row['latest'][m - 1]}, margin {margins[m - 1]}, "
                  f"halves through step M - 1 {row['branches'][m - 1]}")
        print(f"  [{time.time() - began:.0f} s]")


if __name__ == "__main__":
    main()
