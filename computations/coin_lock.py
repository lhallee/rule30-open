"""The period-four lock with a fair coin beyond the window, against Rule 30's own right half.

Drive a right half with the center repeating `word`, as in `lock_certificate.py`, and take the certificate there: the
union over the white-phase values of column 1 (the `jen` seed) of the greatest family of windows of columns 1 .. W that
the rule never leaves, whatever column W + 1 does. A window inside it keeps column 1 fixed at the white times forever.
Whether a run enters it depends only on what column W + 1 does. This module computes

- `entry_paths`: from each window and phase, the fewest steps after which some sequence of values of column W + 1
  brings the window into the certificate, and a first value on such a shortest sequence;
- `universal_word`: one sequence of values of column W + 1 that brings every window at phase 0 into the certificate,
  found greedily, so that a run whose column W + 1 reads it from a time divisible by the period enters;
- `stay_out`, `expected_entry`, `decay_rate`: with column W + 1 replaced by a fair coin flipped at every step, the
  probability of staying out of the certificate for a number of steps, the expected entry time, and the rate at which
  the probability of staying out decays per step;
- `sample`: Rule 30's own right halves, the empty one and random ones of 64 cells from `right_half.random_starts`, when
  each enters the certificate, and when those that never do enter the kit's ether-and-wall family (`absorption.py`).

    python -m computations.coin_lock 0001 0011 0111 --widths 14 16 18   # entry paths and universal words
    python -m computations.coin_lock 0001 0011 0111 --chain-width 16 --samples 1000   # the coin, then Rule 30
"""

from __future__ import annotations

import argparse
import sys
import time
import numpy as np

from tqdm.auto import tqdm

from computations import absorption
from computations.lock_certificate import entry_time, greatest_invariant_set, jen_seeds, successor_table
from computations.right_half import random_starts


UNREACHED = np.iinfo(np.int64).max // 4


def certificate(word: str, width: int) -> np.ndarray:
    """The certificate of the `jen` seed at this width: the union over the white-phase values of column 1 of the
    greatest invariant families, as membership masks."""
    members = [greatest_invariant_set(word, seed, width)[0] for seed in jen_seeds(word)]  # each (period, 2^W)
    return np.logical_or.reduce(members)  # (period, 2^W)


def entry_paths(word: str, member: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """dist[ph, s], the fewest steps after which some values of column W + 1 bring window s at phase ph into the
    certificate (UNREACHED if none do), and first[ph, s], the value of column W + 1 at the first of those steps."""
    # member: (period, 2^W)
    period, size = member.shape
    successors = successor_table(word, size.bit_length() - 1)  # (period, 2, 2^W)
    dist = np.where(member, 0, UNREACHED).astype(np.int64)  # (period, 2^W)
    first = np.zeros((period, size), dtype=np.int8)  # (period, 2^W)
    changed = True
    while changed:
        changed = False
        for ph in range(period):
            after = dist[(ph + 1) % period][successors[ph]] + 1  # (2, 2^W)
            best = np.minimum(after[0], after[1])  # (2^W,)
            better = (best < dist[ph]) & ~member[ph]  # (2^W,)
            if better.any():
                dist[ph][better] = best[better]
                first[ph][better] = (after[1] < after[0])[better]
                changed = True
    return dist, first  # (period, 2^W) each


def universal_word(word: str, member: np.ndarray) -> list[int]:
    """Values of column W + 1 that bring every window at phase 0 into the certificate: repeatedly follow a shortest
    path from the closest window not yet inside, moving every window along. The certificate holds every window it
    contains, so each round brings at least one more window in, and the loop ends when every window can enter."""
    # member: (period, 2^W)
    period, size = member.shape
    dist, first = entry_paths(word, member)  # (period, 2^W) each
    if (dist >= UNREACHED).any():
        raise ValueError("some window cannot enter the certificate")
    successors = successor_table(word, size.bit_length() - 1)  # (period, 2, 2^W)
    windows = np.arange(size, dtype=np.int64)  # (n,), the windows the word has led every start to
    ph, values = 0, []
    while True:
        outside = windows[~member[ph][windows]]  # (m,)
        if outside.size == 0:
            return values
        window = int(outside[np.argmin(dist[ph][outside])])
        while not member[ph][window]:
            value = int(first[ph][window])
            values.append(value)
            windows = np.unique(successors[ph, value][windows])  # (n,)
            window = int(successors[ph, value][window])
            ph = (ph + 1) % period


def run_word(word: str, member: np.ndarray, values: list[int], phase: int = 0) -> np.ndarray:
    """Every window after column W + 1 reads `values` from phase `phase`, and the phase at the end."""
    # member: (period, 2^W)
    period, size = member.shape
    successors = successor_table(word, size.bit_length() - 1)  # (period, 2, 2^W)
    windows = np.arange(size, dtype=np.int64)  # (2^W,)
    for t, value in enumerate(values):
        windows = successors[(phase + t) % period, value][windows]  # (2^W,)
    return windows  # (2^W,)


def coin_step(word: str, member: np.ndarray, values: np.ndarray, successors: np.ndarray) -> np.ndarray:
    """One step back of a quantity on windows with a fair coin beyond: the average over the coin of its value one step
    later, set to 0 on the certificate."""
    # member: (period, 2^W); values: (period, 2^W); successors: (period, 2, 2^W)
    period = member.shape[0]
    out = np.empty_like(values)  # (period, 2^W)
    for ph in range(period):
        later = values[(ph + 1) % period]  # (2^W,)
        out[ph] = 0.5 * (later[successors[ph, 0]] + later[successors[ph, 1]])
    out[member] = 0.0
    return out  # (period, 2^W)


def stay_out(word: str, member: np.ndarray, steps: int) -> np.ndarray:
    """out[ph, s], the probability that window s at phase ph stays out of the certificate for `steps` steps when column
    W + 1 is a fair coin."""
    # member: (period, 2^W)
    successors = successor_table(word, member.shape[1].bit_length() - 1)  # (period, 2, 2^W)
    out = np.where(member, 0.0, 1.0)  # (period, 2^W)
    for _ in tqdm(range(steps), desc=f"stay out, {word}", file=sys.stderr, leave=False):
        out = coin_step(word, member, out, successors)
    return out  # (period, 2^W)


def expected_entry(word: str, member: np.ndarray, tolerance: float = 1e-7) -> np.ndarray:
    """out[ph, s], the expected entry time of window s at phase ph when column W + 1 is a fair coin, by value
    iteration from 0; the iterates increase to the solution, and stop when no value moves by `tolerance`."""
    # member: (period, 2^W)
    successors = successor_table(word, member.shape[1].bit_length() - 1)  # (period, 2, 2^W)
    out = np.zeros(member.shape)  # (period, 2^W)
    with tqdm(desc=f"expected entry, {word}", file=sys.stderr, leave=False) as bar:
        while True:
            new = coin_step(word, member, out, successors) + np.where(member, 0.0, 1.0)  # (period, 2^W)
            if np.abs(new - out).max() < tolerance:
                return new  # (period, 2^W)
            out = new
            bar.update()


def decay_rate(word: str, member: np.ndarray, settle: int = 100, tolerance: float = 1e-11) -> float:
    """The factor per step by which the probability of staying out decays with a fair coin beyond: power iteration of
    one period of `coin_step` from phase 0, until the factor per period changes by less than `tolerance` over
    `settle` periods."""
    # member: (period, 2^W)
    period = member.shape[0]
    successors = successor_table(word, member.shape[1].bit_length() - 1)  # (period, 2, 2^W)
    values = np.where(member, 0.0, 1.0)  # (period, 2^W)
    factors: list[float] = []
    with tqdm(desc=f"decay, {word}", file=sys.stderr, leave=False) as bar:
        while len(factors) <= settle or abs(factors[-1] - factors[-1 - settle]) >= tolerance:
            before = values[0].sum()
            for _ in range(period):
                values = coin_step(word, member, values, successors)
            factors.append(float(values[0].sum() / before))
            values /= values[0].sum()
            bar.update()
    return factors[-1] ** (1 / period)


def sample(word: str, member: np.ndarray, count: int, steps: int) -> tuple[np.ndarray, np.ndarray]:
    """For the empty right half and count - 1 random halves of 64 cells (`right_half.random_starts`), driven from phase
    0 in Rule 30 itself: when each first lies in the certificate within `steps` steps (-1 if never), and, for those
    that never do, when they enter the kit's ether-and-wall family within 4,000 steps (-1 if never)."""
    # member: (period, 2^W)
    starts = random_starts(count - 1, 64)
    times = np.array([-1 if (t := entry_time(word, member, start, steps)) is None else t
                      for start in tqdm(starts, desc=f"starts, {word}", file=sys.stderr, leave=False)])  # (count,)
    missing = np.flatnonzero(times < 0)  # (m,)
    bits = np.zeros((missing.size, 4000 + 70), dtype=np.uint8)  # (m, cells)
    bits[:, :64] = [[(starts[i] >> j) & 1 for j in range(64)] for i in missing.tolist()]
    family = absorption.absorb(word, absorption.packed(bits), 0, 4000, absorption.kit_wall(), 64)  # (m,)
    return times, family  # (count,), (m,)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("words", nargs="+")
    parser.add_argument("--widths", type=int, nargs="*", default=[14, 16, 18], help="entry paths and universal words")
    parser.add_argument("--chain-width", type=int, help="the width for the fair coin and the sample")
    parser.add_argument("--stay-steps", type=int, default=12000, help="the coin: steps to stay out")
    parser.add_argument("--samples", type=int, default=0, help="Rule 30's own right halves, the first one empty")
    parser.add_argument("--steps", type=int, default=12000, help="the sample: steps searched for entry")
    args = parser.parse_args()

    started = time.perf_counter()
    for word in args.words:
        for width in args.widths:
            member = certificate(word, width)  # (period, 2^W)
            if not member.any():
                print(f"{word}, width {width}: no certificate")
                continue
            dist, _ = entry_paths(word, member)  # (period, 2^W)
            reached = (dist < UNREACHED).sum(axis=1).tolist()
            values = universal_word(word, member)
            ends = run_word(word, member, values)  # (2^W,)
            print(f"{word}, width {width}: certificate {member.sum(axis=1).tolist()}; can enter {reached} of "
                  f"{1 << width} windows per phase, within {int(dist[dist < UNREACHED].max())} steps; universal word "
                  f"of {len(values)} values, every window inside after it: "
                  f"{bool(member[len(values) % len(word)][ends].all())}")
        if args.chain_width is None:
            continue
        member = certificate(word, args.chain_width)  # (period, 2^W)
        expected = expected_entry(word, member)  # (period, 2^W)
        out = stay_out(word, member, args.stay_steps)  # (period, 2^W)
        print(f"{word}, width {args.chain_width}, fair coin: expected entry at most {expected.max():.1f} steps, "
              f"{expected[0].mean():.1f} on average over windows at phase 0; decay per step "
              f"{decay_rate(word, member):.5f}; stays out for {args.stay_steps} steps with probability at most "
              f"{out.max():.2e}")
        if args.samples:
            times, family = sample(word, member, args.samples, args.steps)  # (samples,), (m,)
            entered = times[times >= 0]  # (k,)
            print(f"{word}, width {args.chain_width}, Rule 30: {entered.size} of {times.size} starts enter within "
                  f"{args.steps} steps, by step {int(entered.max())} (median {int(np.median(entered))}); the "
                  f"{family.size} that do not, first {np.flatnonzero(times < 0)[:4].tolist()}, enter the family: "
                  f"{int((family >= 0).sum())}, by step {int(family.max()) if family.size else None}")
    print(f"({time.perf_counter() - started:.0f} s)")


if __name__ == "__main__":
    main()
