"""Rank certificates on the readings of column 1 beside a center repeating a block, for any block and any word list.

Drive a right half with the center repeating a block `b` of period P: the state at step t has the phase
p = (t + ph) % P, and the center reads b[p] during the step. At a white phase p (b[p] = 0) in a chosen set, column 1
before the step is a reading. A state is a phase p, a window w < 2^W of columns 1..W (bit i is column i + 1) and the
last L - 1 readings s < 2^(L - 1) (newest in bit 0), where L is the longest forbidden word. One step moves the window as
the kit's `stripStep W (b[p] = 1) z w` with column W + 1 equal to z, unknown, so every state has two successors.

1. **The good set** (`certificate`): the greatest set of states that both successors keep without a reading
   completing a forbidden word. Rank 0.
2. **The ranks**: rank k for a state outside the lower ranks whose two successors both have rank below k. Entry is
   forced when every state has a rank; then every right half, finite or not, has readings that avoid the words with
   the last reading at a step at least the largest rank.
3. **The kernel cost** (`kernel_seconds`): the module `Rule30Open.Columns.ThreeRuns` checks 196,608 states (block 001,
   width 13, three stored readings) in about 2 to 4 minutes on a loaded machine, so about 0.6 to 1.2 ms per state.
   The estimate scales that by the state count; it is a rough guide, not a measurement. `Runs00001` (163,840 states,
   width 12) built in 153 s on the same loaded machine.
4. **The search** (`search`): for a block and a set of read phases, the learned words (minimal words of at most 8
   readings that no sampled half shows after a transient, as `gap_traps.forbidden_words` but at the chosen phases),
   then the configurations (W, L) by increasing state count P * 2^W * 2^(L - 1), and at each the first single word
   of length L whose entry is forced. At the cheapest configuration the list is then extended greedily by learned
   words of length at most L while entry stays forced. A list is new when it lowers the entropy of the readings
   below what the sampled constant phases already give (`new_entropy`): forbidding 11 at both white phases of 001
   says nothing beyond the kit's white first white step.
5. **The strongest list** (`strongest`): at the phases of the cheapest single-phase certificate, for each longest
   length L, the learned words added greedily while entry stays forced at the widest window within a state budget
   (400,000 by default), then the narrowest window that still forces that list; the list of lowest entropy wins.

    python -m computations.reading_certificates --block 00001 --phases 0 --width 12 --words 11 1001   # 29 steps
    python -m computations.reading_certificates --block 00001 --phases 0 --width 12 --words 11 1001 \
        --check Rule30Open/Columns/Runs00001.lean   # the tables of Runs00001 are these ranks
    python -m computations.reading_certificates --survey   # the 22 blocks of reading-constraints.md, about 20 min

`computations.reading_modules` writes the Lean module of a certificate read at one phase.
"""

from __future__ import annotations

import argparse
import re
import sys
import time
from dataclasses import dataclass
from pathlib import Path

import numpy as np
from tqdm.auto import tqdm

from computations.gap_traps import word_entropy

SECONDS_PER_STATE = (120 / 196_608, 240 / 196_608)  # ThreeRuns: 196,608 states in 2 to 4 minutes under load

# The 15 blocks with forced entry at width 14 and the 7 with a forced sublist (findings/columns/reading-constraints.md)
FORCED_BLOCKS = ("001", "00001", "00011", "00101", "000011", "000101", "000111", "001101", "0000001", "0000011",
                 "0000101", "0001001", "0001011", "0001111", "0110111")
SUBLIST_BLOCKS = ("011", "00111", "01011", "000001", "001111", "010111", "0011011")


@dataclass(frozen=True)
class Spec:
    """A certificate to compute: the block, the white phases read, the width and the forbidden words."""

    block: str
    phases: tuple[int, ...]
    width: int
    words: tuple[str, ...]

    @property
    def keep(self) -> int:
        """The number of stored readings, L - 1."""
        return max(len(w) for w in self.words) - 1

    @property
    def states(self) -> int:
        """The number of states P * 2^W * 2^(L - 1)."""
        return len(self.block) * (1 << self.width) * (1 << self.keep)


def step(w: np.ndarray, width: int, c: int, x: int) -> np.ndarray:
    """One step of windows of columns 1..width with the center c and column width + 1 equal to x."""
    # w: (n,) int64 -> (n,) int64
    mask = (1 << width) - 1
    return (((w << 1) | c) ^ (w | (w >> 1) | (x << (width - 1)))) & mask


def bad_table(words: tuple[str, ...], keep: int) -> np.ndarray:
    """bad[s, b]: the reading b after the stored readings s (newest in bit 0) completes a forbidden word."""
    out = np.zeros((1 << keep, 2), dtype=bool)  # (2^keep, 2)
    for s in range(1 << keep):
        for b in (0, 1):
            text = (format(s, f"0{keep}b") if keep else "") + str(b)
            out[s, b] = any(text.endswith(word) for word in words)
    return out


def transitions(spec: Spec) -> tuple[list[np.ndarray], list[np.ndarray], np.ndarray]:
    """For each phase p, the flat indices into the states of phase p + 1 of the two successors, and the bad states.

    Returns idx0[p], idx1[p] of shape (n, S) with n = 2^W and S = 2^keep, and bad of shape (P, n, S)."""
    period, n, sufs = len(spec.block), 1 << spec.width, 1 << spec.keep
    win = np.arange(n, dtype=np.int64)  # (n,)
    suf = np.arange(sufs, dtype=np.int64)  # (S,)
    table = bad_table(spec.words, spec.keep)  # (S, 2)
    bit = win & 1  # (n,): column 1 before the step
    idx0, idx1 = [], []
    bad = np.zeros((period, n, sufs), dtype=bool)  # (P, n, S)
    for p in range(period):
        c = int(spec.block[p])
        if p in spec.phases:
            s_new = ((suf[None, :] << 1) | bit[:, None]) & (sufs - 1)  # (n, S)
            bad[p] = table[suf[None, :], bit[:, None]]
        else:
            s_new = np.broadcast_to(suf[None, :], (n, sufs))  # (n, S)
        idx0.append(step(win, spec.width, c, 0)[:, None] * sufs + s_new)  # (n, S)
        idx1.append(step(win, spec.width, c, 1)[:, None] * sufs + s_new)  # (n, S)
    return idx0, idx1, bad


def certificate(spec: Spec, progress: bool = False) -> tuple[np.ndarray, np.ndarray]:
    """The good set and the rank of every state, both of shape (P, 2^W, 2^keep); rank -1 where none exists."""
    for p in spec.phases:
        assert spec.block[p] == "0", "readings are taken at white phases"
    period = len(spec.block)
    idx0, idx1, bad = transitions(spec)
    good = ~bad.copy()  # (P, n, S)
    bar = tqdm(desc="good set", unit=" rounds", file=sys.stderr, leave=False, disable=not progress)
    while True:
        new = good & ~bad
        for p in range(period):
            nxt = good[(p + 1) % period].ravel()  # (n * S,)
            new[p] &= nxt[idx0[p]] & nxt[idx1[p]]
        bar.update()
        if np.array_equal(new, good):
            break
        good = new
    bar.close()
    rank = np.where(good, 0, -1).astype(np.int32)  # (P, n, S)
    k = 0
    bar = tqdm(desc="ranks", unit=" layers", file=sys.stderr, leave=False, disable=not progress)
    while True:
        done = rank >= 0  # (P, n, S)
        add = np.zeros_like(done)  # (P, n, S)
        for p in range(period):
            nxt = done[(p + 1) % period].ravel()  # (n * S,)
            add[p] = nxt[idx0[p]] & nxt[idx1[p]]
        add &= ~done
        if not add.any():
            bar.close()
            return good, rank
        k += 1
        rank[add] = k
        bar.update()


def is_forced(spec: Spec) -> tuple[bool, int]:
    """Whether every state has a rank, and the largest rank (-1 when the good set is empty or entry is not forced)."""
    good, rank = certificate(spec)
    if not good.any() or (rank < 0).any():
        return False, -1
    return True, int(rank.max())


def kernel_seconds(states: int) -> tuple[float, float]:
    """The rough kernel time of a certificate with this many states, scaled from ThreeRuns."""
    return states * SECONDS_PER_STATE[0], states * SECONDS_PER_STATE[1]


# ---------------------------------------------------------------------------------------------------------------------
# Learned words and entropy at chosen phases


def phase_readings(block: str, phase: int, half: int, steps: int) -> list[tuple[int, int]]:
    """(phase of the step, column 1) at the white steps before `steps` of the right half `half` (bit i the cell i + 1)."""
    row, out = half, []
    for t in range(steps):
        p = (t + phase) % len(block)
        center = int(block[p])
        if center == 0:
            out.append((p, row & 1))
        row = ((row << 1) | center) ^ (row | (row >> 1))
    return out


def sample_readings(block: str, halves: int, steps: int, seed: int = 0) -> list[list[tuple[int, int]]]:
    """The readings of every half of up to 6 cells and `halves` random halves of 40 cells, from every phase, after the
    first quarter of the run."""
    rng = np.random.default_rng(seed)
    starts = list(range(64)) + [int(x) for x in rng.integers(0, 1 << 40, halves)]
    runs = []
    jobs = [(ph, h) for ph in range(len(block)) for h in starts]
    for ph, half in tqdm(jobs, desc=f"sample {block}", file=sys.stderr, leave=False):
        r = phase_readings(block, ph, half, steps)
        runs.append(r[len(r) // 4:])
    return runs


def learned_words(runs: list[list[tuple[int, int]]], phases: tuple[int, ...], length: int = 8) -> list[str]:
    """The minimal words of at most `length` readings at the phases `phases` that no sampled run shows."""
    seen: set[str] = set()
    for run in runs:
        text = "".join(str(b) for p, b in run if p in phases)
        for k in range(1, length + 1):
            seen.update(text[i:i + k] for i in range(len(text) - k + 1))
    minimal = []
    for k in range(1, length + 1):
        for x in range(1 << k):
            w = format(x, f"0{k}b")
            if w not in seen and (k == 1 or (w[1:] in seen and w[:-1] in seen)):
                minimal.append(w)
    return minimal


def constant_phases(runs: list[list[tuple[int, int]]], phases: tuple[int, ...]) -> dict[int, int]:
    """The read phases at which every sampled run reads one constant value, with that value."""
    out = {}
    for p in phases:
        values = {b for run in runs for q, b in run if q == p}
        if len(values) == 1:
            out[p] = values.pop()
    return out


def phase_entropy(words: tuple[str, ...], k: int, constants: dict[int, int]) -> float:
    """The entropy, in bits per reading, of the sequences that avoid `words` and whose readings at positions j mod k
    in `constants` equal the given value: log2 of the spectral radius of the graph on (position, last L - 1 readings)."""
    keep = max([len(w) for w in words] + [1]) - 1
    sufs = 1 << keep
    graph = np.zeros((k * sufs, k * sufs))  # (k * S, k * S)
    for j in range(k):
        for s in range(sufs):
            for bit in (0, 1):
                if j in constants and constants[j] != bit:
                    continue
                text = (format(s, f"0{keep}b") if keep else "") + str(bit)
                if any(text.endswith(w) for w in words) or any(w in text[:-1] for w in words):
                    continue
                graph[j * sufs + s, ((j + 1) % k) * sufs + (((s << 1) | bit) & (sufs - 1))] += 1
    radius = max(abs(np.linalg.eigvals(graph)))
    return float(np.log2(radius)) if radius > 1e-12 else float("-inf")


def new_entropy(words: tuple[str, ...], phases: tuple[int, ...], constants: dict[int, int]) -> tuple[float, float]:
    """The entropy of the readings at `phases` under the sampled constants alone, and with the words too."""
    pos = {p: j for j, p in enumerate(phases)}
    const = {pos[p]: b for p, b in constants.items() if p in pos}
    return phase_entropy((), len(phases), const), phase_entropy(words, len(phases), const)


# ---------------------------------------------------------------------------------------------------------------------
# The search


@dataclass
class Found:
    """The cheapest certificate found for a block and a set of read phases."""

    block: str
    phases: tuple[int, ...]
    width: int
    words: tuple[str, ...]
    states: int
    max_rank: int
    entropy: float
    extended: tuple[str, ...]
    ext_rank: int
    ext_entropy: float


def white_phases(block: str) -> tuple[int, ...]:
    """The phases at which the block reads 0."""
    return tuple(p for p, c in enumerate(block) if c == "0")


def search(block: str, phases: tuple[int, ...], runs: list[list[tuple[int, int]]], budget: int,
           widths: range = range(4, 15)) -> Found | None:
    """The cheapest configuration with a single learned word whose entry is forced and which is new, extended
    greedily at the same configuration. None when no configuration within the budget works."""
    words = learned_words(runs, phases)
    constants = constant_phases(runs, phases)
    base = new_entropy((), phases, constants)[0]
    if base <= 1e-9:
        return None  # every read phase is constant in the samples: the kit's kind of statement
    candidates = [w for w in words if new_entropy((w,), phases, constants)[1] < base - 1e-9]
    lengths = sorted({len(w) for w in candidates})
    period = len(block)
    configs = sorted((period * (1 << wd) * (1 << (ln - 1)), wd, ln) for wd in widths for ln in lengths
                     if period * (1 << wd) * (1 << (ln - 1)) <= budget)
    for states, wd, ln in configs:
        for w in (u for u in candidates if len(u) == ln):
            forced, top = is_forced(Spec(block, phases, wd, (w,)))
            if not forced:
                continue
            chosen, rank = [w], top
            for u in candidates:
                if len(u) <= ln and u not in chosen:
                    ok, r = is_forced(Spec(block, phases, wd, tuple(chosen + [u])))
                    if ok:
                        chosen.append(u)
                        rank = r
            return Found(block, phases, wd, (w,), states, top, new_entropy((w,), phases, constants)[1],
                         tuple(chosen), rank, new_entropy(tuple(chosen), phases, constants)[1])
    return None


def strongest(block: str, phases: tuple[int, ...], runs: list[list[tuple[int, int]]], budget: int,
              max_width: int = 14) -> Found | None:
    """The forced list of learned words of lowest entropy within the budget: for each longest length L, the learned
    words of length at most L added greedily (shortest first) while entry stays forced at the widest window the
    budget allows, then the narrowest window at which that list is still forced."""
    words = learned_words(runs, phases)
    constants = constant_phases(runs, phases)
    base = new_entropy((), phases, constants)[0]
    candidates = [w for w in words if new_entropy((w,), phases, constants)[1] < base - 1e-9]
    period, best = len(block), None
    lengths = sorted({len(w) for w in candidates})
    for ln in tqdm(lengths, desc=f"strongest {block} {list(phases)}", file=sys.stderr, leave=False):
        wd = max_width
        while wd > 1 and period * (1 << wd) * (1 << (ln - 1)) > budget:
            wd -= 1
        chosen: list[str] = []
        for u in (u for u in candidates if len(u) <= ln):
            if is_forced(Spec(block, phases, wd, tuple(chosen + [u])))[0]:
                chosen.append(u)
        if not chosen or max(len(u) for u in chosen) < ln:
            continue
        while wd > 1 and is_forced(Spec(block, phases, wd - 1, tuple(chosen)))[0]:
            wd -= 1
        spec = Spec(block, phases, wd, tuple(chosen))
        top = is_forced(spec)[1]
        h = new_entropy(tuple(chosen), phases, constants)[1]
        row = Found(block, phases, wd, tuple(chosen), spec.states, top, h, tuple(chosen), top, h)
        if best is None or (h, row.states) < (best.entropy - 1e-9, best.states):
            best = row
    return best


def survey(blocks: tuple[str, ...], budget: int, lean_budget: int, halves: int,
           steps: int) -> list[tuple[str, Found | None]]:
    """For every block, the cheapest certificate for each single white phase and for all white phases (kind
    "cheapest"), and the strongest within `lean_budget` states at the phases of the cheapest single-phase one, or of
    all white phases when no single phase has one (kind "strongest")."""
    out: list[tuple[str, Found | None]] = []
    for block in tqdm(blocks, desc="blocks", file=sys.stderr):
        runs = sample_readings(block, halves, steps)
        whites = white_phases(block)
        choices = [(p,) for p in whites] + ([whites] if len(whites) > 1 else [])
        rows = [search(block, phases, runs, budget) for phases in choices]
        for phases, row in zip(choices, rows):
            constant = len(constant_phases(runs, phases)) == len(phases)
            out.append((f"cheapest {block} {list(phases)}" + (" (constant in the samples)" if constant else ""), row))
        singles = [r for r in rows[:len(whites)] if r is not None]
        pick = min(singles, key=lambda r: r.states) if singles else (rows[-1] if rows[-1] is not None else None)
        if pick is not None:
            out.append((f"strongest {block} {list(pick.phases)}", strongest(block, pick.phases, runs, lean_budget)))
    return out


def describe(row: Found) -> str:
    """One line for a certificate."""
    lo, hi = kernel_seconds(row.states)
    text = (f"width {row.width}, words {list(row.words)}, {row.states} states, max rank {row.max_rank}, entropy "
            f"{row.entropy:.3f}")
    if len(row.phases) > 1:
        text += f" ({word_entropy(row.words):.3f} without the sampled constants)"
    if row.extended != row.words:
        text += f"; extended {list(row.extended)} (max rank {row.ext_rank}, entropy {row.ext_entropy:.3f})"
    return text + f"; kernel about {lo / 60:.1f} to {hi / 60:.1f} min"


# ---------------------------------------------------------------------------------------------------------------------
# Lean tables


def tables(rank: np.ndarray, bits: int) -> list[int]:
    """The packed rank tables: entry S p + s holds the rank of window w in bits `bits` w .. `bits` w + bits - 1."""
    period, n, sufs = rank.shape
    out = []
    for p in range(period):
        for s in range(sufs):
            value = 0
            for w in range(n - 1, -1, -1):
                value = (value << bits) | int(rank[p, w, s])
            out.append(value)
    return out


def lean_tables(path: Path) -> list[int]:
    """The tables written in a Lean file as `def rankTabs : List Nat := [...]`."""
    body = path.read_text(encoding="utf-8").split("def rankTabs : List Nat := [", 1)[1].split("]", 1)[0]
    return [int(h, 16) for h in re.findall(r"0x[0-9a-f]+", body)]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--block", default="001")
    parser.add_argument("--phases", type=int, nargs="*", help="white phases read (default: all)")
    parser.add_argument("--width", type=int, default=13)
    parser.add_argument("--words", nargs="*", default=["010", "101", "1001"])
    parser.add_argument("--survey", action="store_true", help="search the 22 blocks of reading-constraints.md")
    parser.add_argument("--blocks", nargs="*", help="blocks for --survey (default: the 22)")
    parser.add_argument("--budget", type=int, default=3_000_000, help="largest state count searched")
    parser.add_argument("--lean-budget", type=int, default=400_000, help="largest state count of the strongest list")
    parser.add_argument("--halves", type=int, default=40)
    parser.add_argument("--steps", type=int, default=6000)
    parser.add_argument("--lean", action="store_true", help="print the tables as Lean")
    parser.add_argument("--check", type=Path, help="compare with the tables of this Lean file")
    args = parser.parse_args()
    started = time.perf_counter()
    if args.survey:
        blocks = tuple(args.blocks) if args.blocks else FORCED_BLOCKS + SUBLIST_BLOCKS
        for label, row in survey(blocks, args.budget, args.lean_budget, args.halves, args.steps):
            print(f"{label}: " + (describe(row) if row else f"nothing within the budget"), flush=True)
        print(f"({time.perf_counter() - started:.0f} s)", file=sys.stderr)
        return
    phases = tuple(args.phases) if args.phases is not None else white_phases(args.block)
    spec = Spec(args.block, phases, args.width, tuple(args.words))
    good, rank = certificate(spec, progress=True)
    forced = bool(good.any() and (rank >= 0).all())
    lo, hi = kernel_seconds(spec.states)
    print(f"{spec.block} phases {list(phases)} width {spec.width} words {list(spec.words)}: good set of "
          f"{int(good.sum())} of {spec.states} states; entry "
          + (f"forced within {int(rank.max())} steps" if forced else f"not forced from {int((rank < 0).sum())} states")
          + f"; entropy {word_entropy(spec.words):.3f}; kernel about {lo / 60:.1f} to {hi / 60:.1f} min",
          file=sys.stderr)
    if not forced:
        sys.exit(1)
    bits = max(1, int(rank.max()).bit_length())
    if args.check:
        same = tables(rank, bits) == lean_tables(args.check)
        print(f"the tables of {args.check.name} are these ranks" if same else "the tables differ", file=sys.stderr)
        sys.exit(0 if same else 1)
    if args.lean:
        print(f"-- {bits} bits per rank, max rank {int(rank.max())}")
        print("def rankTabs : List Nat := [")
        print(",\n".join(f"  {hex(v)}" for v in tables(rank, bits)))
        print("]")


if __name__ == "__main__":
    main()
