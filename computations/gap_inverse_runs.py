"""Constant runs of the inverse diagonal over the gap shift, the stream form of the kit's `Q01Gap`.

At a white step of an alternating center the kit's endpoint symbol e_j = encodePair(x_{-1}, x_{-2}) at time o + 2j + 2
(kit main, `Rule30SEPToPeriodTwo.actualEndpoint`) is 1 or 2, and since the center turns black at the next step, column 1
is black exactly when e_j = 1 (`pair_one_requires_right`). The kit's gate trap (`Rule30GateTrap.gaps_of_entry`) puts the
black cells of column 1 at the white steps 3 or 5 apart, so a right half in the trap gives a stream e that is
eventually 2 forever or eventually in the gap shift X_gap = {1 2 2, 1 2 2 2 2}^omega (`trap_streams` checks this on
right halves that enter the trap, `chart_check` checks the kit's chart from e to the left half on the same runs).

The kit's inverse diagonal I = inverse e (`Rule30WedgeBridge.inverse`) reads e only on [floor(s/2), s] at s. For a
window v = e_h e_{h+1} ... the rows E_i[0] = 3 - v_i, E_i[1] = phi(v_{i-1}, E_i[0]),
E_i[t] = phi(E_{i-1}[t-2], E_i[t-1]) (t <= 2i, `window_rows`) do not depend on h, and the antidiagonal of the kit's
cone at h + i agrees with E_i on t <= 2i, so I(h + i) = E_i[h + i] for every h <= i. A run of length r at s is
I(s) = ... = I(s + r - 1) = c with c in {2, 3}; it is a property of the window e_h .. e_{s + r - 1}, h = floor(s/2), of
length ceil(s/2) + r.

- N(s, r): the number of words of the class (its factor language, so every stream of the class in every phase) of
  length ceil(s/2) + r that, as the window at h = floor(s/2), have a run of length at least r at s (`run_counts`, and
  `gap_inverse_runs.c` for the large runs; `brute_counts` is the independent check by the kit's recursion on whole
  words). R(s) is the longest run at s. phi(a, .) is a bijection, so at most one next symbol keeps a run going.
- The coin model: every forced symbol is uniform on the four symbols, so the expected count is
  2 4^{-r} |L_{ceil(s/2) + r}|, with L_n the words of length n of the class (`coin_counts`); it grows like
  lambda^{s/2}, lambda = 1.1939 the growth rate of the gap shift (lambda^5 = lambda^2 + 1).
- `sample_runs`: random streams from the measure of maximal entropy of a class, the longest run at each position.

    python -m computations.gap_inverse_runs check              # the coding on right halves in the trap: a few seconds
    python -m computations.gap_inverse_runs exhaust --n 90     # gap shift, s <= 180: about 70 s on two threads
    python -m computations.gap_inverse_runs controls           # binary to n = 26 and hard-core to n = 36: about 85 s
    python -m computations.gap_inverse_runs sample             # 10^5 streams of length 400 in each class: about 25 s

The C searches use two OpenMP threads.
"""

from __future__ import annotations

import argparse
import functools
import os
import subprocess
import sys
from collections.abc import Callable
from dataclasses import dataclass

import numpy as np
from tqdm.auto import tqdm

from computations.seed_onsets import _binary
from computations.wedge_hypotheses import PHI, kit_inverse

GAP, BINARY, HARD_CORE = 0, 1, 2
CLASS_NAMES = {GAP: "gap shift", BINARY: "binary", HARD_CORE: "hard-core"}
START = 0  # the grammar state of the empty word in every class


def gap_lambda() -> float:
    """The growth rate of the gap shift: the root above 1 of x^5 = x^2 + 1."""
    roots = np.roots([1, 0, 0, -1, 0, -1])  # (5,)
    return float(max(r.real for r in roots if abs(r.imag) < 1e-12))


def next_state(cls: int, state: int, x: int) -> int:
    """The grammar state after the symbol x in {1, 2}, or -1 if x cannot follow. Gap shift: 8 * (a 1 seen) + the
    number of 2s since the last 1 (or since the start); hard-core: 1 after a 1."""
    if cls == BINARY:
        return 0
    if cls == HARD_CORE:
        return (-1 if state else 1) if x == 1 else 0
    seen, d = state >> 3, state & 7
    if x == 2:
        return (seen << 3) | (d + 1) if d < 4 else -1
    return 8 if (not seen or d in (2, 4)) else -1


def factor_words(cls: int, n: int) -> list[tuple[int, ...]]:
    """Every word of length n of the class, in the order 1 < 2."""
    out: list[tuple[int, ...]] = []

    def rec(w: list[int], st: int) -> None:
        if len(w) == n:
            out.append(tuple(w))
            return
        for x in (1, 2):
            ns = next_state(cls, st, x)
            if ns >= 0:
                w.append(x)
                rec(w, ns)
                w.pop()

    rec([], START)
    return out


def language_counts(cls: int, n: int) -> np.ndarray:
    """|L_m| for m = 0 .. n, the number of words of length m of the class, by the grammar."""
    counts = np.zeros(n + 1, dtype=object)  # (n + 1,), exact integers
    cur = {START: 1}
    counts[0] = 1
    for m in range(1, n + 1):
        new: dict[int, int] = {}
        for st, c in cur.items():
            for x in (1, 2):
                ns = next_state(cls, st, x)
                if ns >= 0:
                    new[ns] = new.get(ns, 0) + c
        cur = new
        counts[m] = sum(cur.values())
    return counts


def is_gap_stream(e: list[int] | tuple[int, ...]) -> bool:
    """Whether a finite word is a word of the gap shift."""
    st = START
    for x in e:
        st = next_state(GAP, st, x)
        if st < 0:
            return False
    return True


# ---------------------------------------------------------------------------------------------------------------------
# The cone of a window


def window_rows(v: list[int] | tuple[int, ...]) -> list[list[int]]:
    """The rows E_0 .. E_{len(v)-1} of a window; E_i has 2i + 1 entries."""
    rows: list[list[int]] = []
    for i, x in enumerate(v):
        E = [3 - x]  # (2i + 1,) when filled
        if i:
            P = rows[-1]
            E.append(PHI[v[i - 1]][E[0]])
            for t in range(2, 2 * i + 1):
                E.append(PHI[P[t - 2]][E[t - 1]])
        rows.append(E)
    return rows


def kit_cone(e: tuple[int, ...]) -> Callable[[int, int], int]:
    """The kit's recursion `cone e t j`, memoized, for a finite word (defined while j + t < len(e))."""

    @functools.lru_cache(maxsize=None)
    def cone(t: int, j: int) -> int:
        if t == 0:
            return 3 - e[j]
        if t == 1:
            return PHI[e[j]][3 - e[j + 1]]
        return PHI[cone(t - 2, j + 1)][cone(t - 1, j + 1)]

    return cone


# ---------------------------------------------------------------------------------------------------------------------
# Run counts


@dataclass(frozen=True)
class RunCounts:
    cls: int
    n: int  # windows of length up to n, so s <= 2n
    rmax: int
    counts: np.ndarray  # (2n + 1, rmax + 1): counts[s, r] = N(s, r), r >= 1
    witness: dict[int, tuple[int, ...]]  # s -> the least window with the longest run at s
    words: np.ndarray  # (n + 2,): words[i] = |L_i|, i >= 1

    def record(self) -> np.ndarray:
        """R(s), the longest run at s, for s <= 2n (0 when there is none)."""
        has = self.counts[:, 1:] > 0  # (2n + 1, rmax)
        return np.where(has.any(axis=1), has.shape[1] - np.argmax(has[:, ::-1], axis=1), 0)  # (2n + 1,)


def run_counts(cls: int, n: int, rmax: int) -> RunCounts:
    """N(s, r) for s <= 2n by the window search with forced runs, in Python (the reference for the C search)."""
    counts = np.zeros((2 * n + 1, rmax + 1), dtype=np.int64)  # (2n + 1, rmax + 1)
    words = np.zeros(n + 2, dtype=np.int64)  # (n + 2,)
    best: dict[int, tuple[int, tuple[int, ...]]] = {}
    v: list[int] = []
    rows: list[list[int]] = []

    def push(x: int) -> None:
        i = len(v)
        E = [3 - x]  # (2i + 1,)
        if i:
            E.append(PHI[v[-1]][E[0]])
            P = rows[-1]
            for t in range(2, 2 * i + 1):
                E.append(PHI[P[t - 2]][E[t - 1]])
        v.append(x)
        rows.append(E)

    def pop() -> None:
        v.pop()
        rows.pop()

    def note(s: int, length: int) -> None:
        counts[s, length] += 1
        key = (-length, tuple(v))
        if s not in best or key < (-best[s][0], best[s][1]):
            best[s] = (length, tuple(v))

    def follow(st: int, s: int, h: int, c: int, length: int) -> None:
        if length >= rmax:
            return
        for x in (1, 2):
            ns = next_state(cls, st, x)
            if ns < 0:
                continue
            push(x)
            i = len(v) - 1
            if rows[i][h + i] == c:
                note(s, length + 1)
                follow(ns, s, h, c, length + 1)
                pop()
                return
            pop()

    def dfs(st: int) -> None:
        i = len(v)
        for x in (1, 2):
            ns = next_state(cls, st, x)
            if ns < 0:
                continue
            push(x)
            words[i + 1] += 1
            for s in (2 * i, 2 * i - 1):
                if s < 0:
                    continue
                h = s // 2
                c = rows[i][h + i]
                if c in (2, 3):
                    note(s, 1)
                    follow(ns, s, h, c, 1)
            if i + 1 <= n:
                dfs(ns)
            pop()

    dfs(START)
    return RunCounts(cls, n, rmax, counts, {s: w for s, (_, w) in best.items()}, words)


def brute_counts(cls: int, L: int, rmax: int) -> np.ndarray:
    """N(s, r) for s + r <= L from every word of length L of the class: the kit's recursion row by row on whole words
    (`wedge_hypotheses.kit_inverse`), and the distinct windows e_{floor(s/2)} .. e_{s+r-1} that carry the run."""
    words = np.array(factor_words(cls, L), dtype=np.uint8)  # (W, L)
    inv = kit_inverse(words)  # (W, L)
    out = np.zeros((L + 1, rmax + 1), dtype=np.int64)  # (L + 1, rmax + 1)
    for s in range(L):
        c = inv[:, s]  # (W,)
        alive = (c == 2) | (c == 3)  # (W,)
        for r in range(1, min(rmax, L - s) + 1):
            alive = alive & (inv[:, s + r - 1] == c)  # (W,)
            if not alive.any():
                break
            out[s, r] = len({row.tobytes() for row in words[alive, s // 2:s + r]})
    return out


def c_counts(cls: int, n: int, rmax: int = 40, threads: int = 2, progress: bool = True) -> RunCounts:
    """`run_counts` by `gap_inverse_runs.c` with OpenMP, with a progress bar over the split subtrees."""
    split = min(n, {GAP: 30, BINARY: 14, HARD_CORE: 20}[cls])
    proc = subprocess.Popen([str(_binary("gap_inverse_runs")), "exhaust", str(cls), str(n), str(rmax), str(split)],
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                            env={**os.environ, "OMP_NUM_THREADS": str(threads)})
    bar = tqdm(total=1, desc=f"{CLASS_NAMES[cls]} n={n}", file=sys.stderr, disable=not progress, leave=False)
    assert proc.stderr is not None and proc.stdout is not None
    for line in proc.stderr:
        f = line.split()
        if f and f[0] == "P":
            bar.total = int(f[2])
            bar.n = int(f[1])
            bar.refresh()
    out = proc.stdout.read()
    bar.close()
    assert proc.wait() == 0, "gap_inverse_runs.c failed"
    counts = np.zeros((2 * n + 1, rmax + 1), dtype=np.int64)  # (2n + 1, rmax + 1)
    words = np.zeros(n + 2, dtype=np.int64)  # (n + 2,)
    witness: dict[int, tuple[int, ...]] = {}
    for line in out.splitlines():
        tag, *f = line.split()
        if tag == "N":
            counts[int(f[0]), int(f[1])] = int(f[2])
        elif tag == "W":
            witness[int(f[0])] = tuple(int(ch) for ch in f[2])
        elif tag == "L":
            words[int(f[0])] = int(f[1])
    return RunCounts(cls, n, rmax, counts, witness, words)


def coin_counts(cls: int, n: int, rmax: int) -> np.ndarray:
    """The coin model's expected N(s, r) for s <= 2n: 2 4^{-r} |L_{ceil(s/2) + r}|."""
    lang = language_counts(cls, n + 1 + rmax)  # (n + rmax + 2,)
    out = np.zeros((2 * n + 1, rmax + 1))  # (2n + 1, rmax + 1)
    for s in range(2 * n + 1):
        for r in range(1, rmax + 1):
            out[s, r] = 2 * float(lang[(s + 1) // 2 + r]) / 4.0 ** r
    return out


def growth(counts: np.ndarray, r: int, lo: int, hi: int) -> float:
    """The growth factor per two steps of s of N(s, r) over lo <= s <= hi (least squares on the log, both parities
    fitted with their own constant)."""
    xs, ys, par = [], [], []
    for s in range(lo, hi + 1):
        if counts[s, r] > 0:
            xs.append(s / 2)
            ys.append(np.log(float(counts[s, r])))
            par.append(s % 2)
    X = np.column_stack([np.array(xs), 1 - np.array(par), np.array(par)])  # (m, 3)
    coef, *_ = np.linalg.lstsq(X, np.array(ys), rcond=None)  # (3,)
    return float(np.exp(coef[0]))


# ---------------------------------------------------------------------------------------------------------------------
# Random streams


@dataclass(frozen=True)
class Samples:
    cls: int
    L: int
    count: int
    maxrun: np.ndarray  # (L,): the longest run at s over the sample (runs cut at L)
    at_least: np.ndarray  # (L, rmax + 1): the streams with a run of length >= r at s, s + r <= L
    longest: dict[int, int]  # r -> the streams whose longest run is r


def sample_runs(cls: int, L: int = 400, count: int = 100_000, seed: int = 1, rmax: int = 40, threads: int = 2,
                progress: bool = True) -> Samples:
    """Random streams of length L from the measure of maximal entropy of the class (`gap_inverse_runs.c sample`)."""
    proc = subprocess.Popen([str(_binary("gap_inverse_runs")), "sample", str(cls), str(L), str(count), str(seed),
                             str(rmax)], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                            env={**os.environ, "OMP_NUM_THREADS": str(threads)})
    bar = tqdm(total=count, desc=f"sample {CLASS_NAMES[cls]}", file=sys.stderr, disable=not progress, leave=False)
    assert proc.stderr is not None and proc.stdout is not None
    for line in proc.stderr:
        f = line.split()
        if f and f[0] == "P":
            bar.n = int(f[1])
            bar.refresh()
    out = proc.stdout.read()
    bar.close()
    assert proc.wait() == 0, "gap_inverse_runs.c failed"
    maxrun = np.zeros(L, dtype=np.int64)  # (L,)
    at_least = np.zeros((L, rmax + 1), dtype=np.int64)  # (L, rmax + 1)
    longest: dict[int, int] = {}
    for line in out.splitlines():
        tag, *f = line.split()
        x = [int(t) for t in f]
        if tag == "M":
            maxrun[x[0]] = x[1]
        elif tag == "Q":
            at_least[x[0], x[1]] = x[2]
        elif tag == "H":
            longest[x[0]] = x[1]
    return Samples(cls, L, count, maxrun, at_least, longest)


# ---------------------------------------------------------------------------------------------------------------------
# The coding: right halves in the gap trap, and the kit's chart


def driven_rows(half: int, steps: int) -> list[int]:
    """The right half (bit i = column i + 1) at times 0 .. steps - 1, driven by the kit's `altCol` (column 0 black at
    the even steps)."""
    rows, row = [], half
    for t in range(steps):
        rows.append(row)
        center = 1 if t % 2 == 0 else 0
        row = ((row << 1) | center) ^ (row | (row >> 1))
    return rows


def column_one(half: int, steps: int) -> list[int]:
    """The kit's `u R s` = column 1 at the time 2s + 1, for 2s + 1 < steps."""
    rows = driven_rows(half, steps)
    return [rows[2 * s + 1] & 1 for s in range((steps - 1) // 2)]


def sideways_left(half: int, steps: int, depth: int) -> list[list[int]]:
    """Columns 0, -1, ..., -depth of the diagram with the alternating center and the driven right half, solved sideways
    from x_i(t+1) = x_{i-1}(t) xor (x_i(t) or x_{i+1}(t)): cols[k][t] = x_{-k}(t), defined for t < steps - k."""
    rows = driven_rows(half, steps)
    cols = [[1 if t % 2 == 0 else 0 for t in range(steps)]]  # (steps,) column 0
    right = [r & 1 for r in rows]  # (steps,) column 1
    for k in range(1, depth + 1):
        a, b = cols[-1], right
        cols.append([a[t + 1] ^ (a[t] | b[t]) for t in range(len(a) - 1)])  # (steps - k,)
        right = a
    return cols


def chart_check(half: int, steps: int = 200) -> dict[str, int]:
    """On the sideways diagram of a right half, with o = 1 (the center is white at the time 1): the endpoint stream
    e_j = encodePair(x_{-1}, x_{-2}) at the time 2j + 3 is binary, e_j = 1 exactly when u R (j + 1) is black, and the
    kit's `actual_cone_chart`, cone e n j = encodePair(x_{-(n+2)}, x_{-(n+3)}) at the time 2j + n + 2, holds wherever
    both sides are defined. Returns the number of entries checked and of failures."""
    depth = steps // 3
    cols = sideways_left(half, steps, depth)
    u = column_one(half, steps)

    def pair(t: int, k: int) -> int:  # encodePair(x_{-k}, x_{-k-1}) at time t
        return 2 * cols[k][t] + cols[k + 1][t]

    J = (steps - depth - 5) // 2
    e = tuple(pair(2 * j + 3, 1) for j in range(J))
    bad = sum(x not in (1, 2) for x in e) + sum((e[j] == 1) != (u[j + 1] == 1) for j in range(J))
    cone = kit_cone(e)
    checked = 0
    for n in range(depth - 3):
        for j in range(J):
            t = 2 * j + n + 2
            if j + n + 1 >= J or t >= len(cols[n + 3]):
                break
            checked += 1
            bad += cone(n, j) != pair(t, n + 2)
    return {"checked": checked, "failures": bad}


def trap_streams(halves: list[int], steps: int = 6000) -> list[dict[str, int]]:
    """For right halves: the first white step at which the window of columns 1..16 enters the gap trap of
    `gate_census` (black in column 1 and good with no white step since), and whether column 1 at the white steps from
    there on, read as e (1 black, 2 white), is a word of the gap shift."""
    from computations.gate_census import gap_entry
    entry = gap_entry()  # (2^16,)
    out = []
    for half in tqdm(halves, desc="halves", file=sys.stderr, leave=False):
        rows = driven_rows(half, steps)
        s0 = next((s for s in range((steps - 1) // 2) if entry[rows[2 * s + 1] & 0xFFFF]), -1)
        e = [1 if rows[2 * s + 1] & 1 else 2 for s in range(max(s0, 0), (steps - 1) // 2)]
        out.append({"half": half, "entry": s0, "length": len(e), "gap": int(s0 >= 0 and is_gap_stream(e))})
    return out


# ---------------------------------------------------------------------------------------------------------------------
# Reports


def report_counts(rc: RunCounts, coin: np.ndarray, rs: tuple[int, ...]) -> None:
    rec = rc.record()
    n = rc.n
    print(f"{CLASS_NAMES[rc.cls]}: windows of length <= {n + 1}, s <= {2 * n}; words of length {n}: {rc.words[n]:,}")
    print("records R(s):", " ".join(f"{s}:{int(rec[s])}" for s in range(2 * n + 1)))
    top = int(rec.max())
    s_top = [s for s in range(2 * n + 1) if rec[s] == top]
    print(f"longest run {top} at s = {s_top}; witness at s = {s_top[0]}: "
          f"{''.join(map(str, rc.witness[s_top[0]]))} (window from floor(s/2))")
    for r in rs:
        line = []
        for s in range(0, 2 * n + 1, 10):
            line.append(f"{s}:{int(rc.counts[s, r])}/{coin[s, r]:.3g}")
        print(f"N(s, {r}) / coin, every 10th s: " + " ".join(line))
    lam = float(rc.words[n + 1]) / float(rc.words[n])
    print(f"growth of the words {lam:.4f} per symbol; the coin's records grow like (s/2) ln(lambda) / ln(4/lambda) = "
          f"{0.5 * np.log(lam) / np.log(4 / lam):.4f} s (a heuristic)")
    print(f"r: sum of N(s, r) over {n} <= s <= {2 * n} / the coin's; first s with a run >= r; first s where the coin's "
          f"expected number of runs >= r at s' <= s reaches 1; runs >= r over s <= {2 * n}, actual and the coin's")
    cum = np.cumsum(coin, axis=0)  # (2n + 1, rmax + 1)
    for r in range(1, min(top + 3, rc.rmax) + 1):
        ratio = rc.counts[n:, r].sum() / coin[n:, r].sum()
        first = int(np.argmax(rec >= r)) if (rec >= r).any() else -1
        expect = int(np.argmax(cum[:, r] >= 1)) if cum[-1, r] >= 1 else -1
        print(f"  {r}: {ratio:.3f}; {first}; {expect}; {int(rc.counts[:, r].sum())}, {cum[-1, r]:.3g}")
    for r in rs:
        for lo, hi in ((20, n), (n, 2 * n)):
            if rc.counts[lo:hi + 1, r].sum() > 0:
                print(f"growth per two steps of s of N(s, {r}) on [{lo}, {hi}]: {growth(rc.counts, r, lo, hi):.4f}; "
                      f"coin: {growth(coin, r, lo, hi):.4f}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("mode", choices=["check", "exhaust", "controls", "sample"])
    parser.add_argument("--n", type=int, default=90)
    parser.add_argument("--rmax", type=int, default=40)
    parser.add_argument("--count", type=int, default=100_000)
    parser.add_argument("--length", type=int, default=400)
    parser.add_argument("--threads", type=int, default=2)
    a = parser.parse_args()
    if a.mode == "check":
        rng = np.random.default_rng(3)
        halves = [0] + [int(x) for x in rng.integers(1, 1 << 20, size=199)]
        for half in halves[:6]:
            print(f"half {half}: chart {chart_check(half)}")
        res = trap_streams(halves)
        inside = [r for r in res if r["entry"] >= 0]
        print(f"{len(inside)} of {len(res)} halves enter the gap trap by step 6000; the stream after entry is a gap "
              f"word in {sum(r['gap'] for r in inside)} of them; latest entry s = {max(r['entry'] for r in inside)}, "
              f"shortest stream after entry {min(r['length'] for r in inside)} symbols")
        print("the halves outside:", [r["half"] for r in res if r["entry"] < 0], "; the empty half enters at s =",
              res[0]["entry"], "with", res[0]["length"], "symbols after")
    elif a.mode == "exhaust":
        rc = c_counts(GAP, a.n, a.rmax, a.threads)
        assert (rc.words[1:a.n + 1] == language_counts(GAP, a.n)[1:].astype(np.int64)).all()
        report_counts(rc, coin_counts(GAP, a.n, a.rmax), (1, 3, 5, 7))
    elif a.mode == "controls":
        for cls, n in ((BINARY, 26), (HARD_CORE, 36)):
            rc = c_counts(cls, n, a.rmax, a.threads)
            report_counts(rc, coin_counts(cls, n, a.rmax), (3, 5, 7))
    else:
        lam = gap_lambda()
        print(f"lambda = {lam:.6f}, entropy {np.log2(lam):.4f} bits per symbol")
        for cls in (GAP, HARD_CORE, BINARY):
            sm = sample_runs(cls, a.length, a.count, 1, a.rmax, a.threads)
            cut = a.length - 40
            print(f"{CLASS_NAMES[cls]}: {a.count:,} streams of length {a.length}; longest run at s by blocks of 40 "
                  f"(s < {cut}): " + " ".join(f"{s}-{s + 39}:{int(sm.maxrun[s:s + 40].max())}"
                                             for s in range(0, cut, 40)))
            for r in (3, 5, 7):
                rates = [sm.at_least[s:s + 40, r].sum() / (40 * a.count) for s in range(0, cut, 40)]
                print(f"  P(run >= {r} at s) by blocks of 40: " + " ".join(f"{p:.2e}" for p in rates))
            print("  longest run per stream:", dict(sorted(sm.longest.items())))


if __name__ == "__main__":
    main()
