"""The front walk through the single cell's settled left diagonals, and the routes to linear settling it tests.

The left diagonals D_j(t) = cell(t, j - t) obey D_{j+2}(t+1) = D_j(t) xor (D_{j+1}(t) or D_{j+2}(t)). The front walk
starts at time w_1 = 1 on diagonal 1; on diagonal i from time w_i it slides to the first black cell r >= w_i of D_i and
steps to w_{i+1} = r + 1, or, if D_i is white from w_i on, to w_{i+1} = w_i. On the space-time diagram it moves straight
down from a black cell and down-left from a white one. `Rule30Open.Diagonals.FrontWalker` proves that the pair
(D_j, D_{j+1}) repeats from w_{j+1} (`pair_repeats_of_walk`); the kit's main branch has the same recursion as
`Rule30FrontLaw.frontBound`. So the onset T_j of D_j is at most w_j, and every cell the walk reads is in the periodic
part of its diagonal.

- `walk_from_tail`: the walk, read from the onsets and the last rows of `settled_slope.stream` (each read is checked to
  be at or after the onset, where the last rows give the value);
- `walk_offset`: the least delta with w_{j+1} <= ceil(num j / den) + delta, the hypothesis of the slope theorems;
- `step_table`: the steps w_{j+1} - w_j grouped by least period, against the reset costs c_j = g_j + 1;
- `front_law`: the front law at the true onsets. With S_j = max(T_{j-1}, T_j) and r the first black cell of D_j at or
  after S_j, T_{j+1} <= r + 1 =: C_{j+1}, with equality exactly when the defect D_{j+1}(S_j + p) xor D_{j+1}(S_j) is 1
  (if D_j is white from S_j, C_{j+1} = S_j and T_{j+1} <= S_j);
- `phase_chi2`, `pair_types`, `window_max`, `step_pairs`: the tests of the three leads (phase of the onsets modulo the
  period, finite sets of pair types up to a time shift, local bounds on the walk).

    python -m computations.front_walker --depth 200000   # about 3 min, 0.2 GB
"""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass

import numpy as np
from tqdm.auto import tqdm

from computations.settled_slope import least_periods, stream, white_runs


def read(tail: np.ndarray, steps: int, period: int, j: int, t: int) -> int:
    """D_j(t) for t at or after the onset of D_j (with respect to `period`), from the last rows."""
    # tail: (window, n)
    window = tail.shape[0]
    return int(tail[(t - (steps - window)) % period, j])


def first_black(tail: np.ndarray, steps: int, period: int, j: int, s: int) -> int:
    """The least g >= 0 with D_j(s + g) = 1, or -1 if D_j is white on s .. s + period - 1 (then white from s on)."""
    # tail: (window, n)
    for g in range(period):
        if read(tail, steps, period, j, s + g):
            return g
    return -1


def walk_from_tail(onset: np.ndarray, tail: np.ndarray, steps: int, period: int) -> np.ndarray:
    """The front walk w_0 = 0, w_1 = 1, w_{j+1} = (first black of D_j at or after w_j) + 1, or w_j if there is none."""
    # onset: (n,); tail: (window, n)
    n = len(onset)
    w = np.zeros(n, dtype=np.int64)  # (n,)
    w[1] = 1
    for j in range(1, n - 1):
        assert w[j] >= onset[j], "the walk reads only settled cells"
        g = first_black(tail, steps, period, j, int(w[j]))
        w[j + 1] = w[j] if g < 0 else w[j] + g + 1
    return w  # (n,)


def walk_direct(D: np.ndarray) -> np.ndarray:
    """The same walk on a full table D[j, t] of the diagonals, scanning each diagonal forward from w_j; a diagonal with
    no black cell left in the table counts as white. An independent check of `walk_from_tail` on small tables."""
    # D: (depth, steps)
    depth, steps = D.shape
    w = np.zeros(depth, dtype=np.int64)  # (depth,)
    w[1] = 1
    for j in range(1, depth - 1):
        black = np.flatnonzero(D[j, w[j]:])  # (k,)
        w[j + 1] = w[j] if len(black) == 0 else w[j] + black[0] + 1
    return w  # (depth,)


def walk_offset(w: np.ndarray, num: int, den: int) -> int:
    """The least delta >= 0 with w_{j+1} <= ceil(num j / den) + delta for every j < len(w) - 1."""
    # w: (n,)
    j = np.arange(len(w) - 1, dtype=np.int64)  # (n - 1,)
    return max(0, int((w[1:] - (num * j + den - 1) // den).max()))


@dataclass(frozen=True, slots=True)
class StepRow:
    period: int  # least period of the diagonals in the row
    count: int  # diagonals (white ones left out)
    mean_step: float  # mean of w_{j+1} - w_j over them
    max_step: int
    mean_cost: float  # mean of the reset cost c_j = g_j + 1 over them
    mean_phase_gap: float  # mean over them of 1 + the gap to the next black cell from a uniform phase
    mean_after_black: float  # the same over the phases s with D_{j-1}(s - 1) = 1, where the walk arrives
    one_step: float  # fraction of steps of length 1


def phase_gaps(word: np.ndarray) -> np.ndarray:
    """For each phase s of a periodic word, the least g >= 0 with word[(s + g) % p] = 1."""
    # word: (p,), not all white
    p = len(word)
    gaps = np.zeros(p, dtype=np.int64)  # (p,)
    for s in range(p):
        while not word[(s + gaps[s]) % p]:
            gaps[s] += 1
    return gaps  # (p,)


def step_table(w: np.ndarray, period: np.ndarray, white: np.ndarray, tail: np.ndarray) -> list[StepRow]:
    """The steps of the walk grouped by the least period of the diagonal they cross (diagonals 1 .. n - 2)."""
    # w, period, white: (n,); tail: (window, n)
    n = len(w)
    step = np.diff(w)  # (n - 1,): step[j] = w_{j+1} - w_j, read on diagonal j
    rows: list[StepRow] = []
    for p in sorted(set(period[1:n - 1][white[1:n - 1] >= 0].tolist())):
        sel = np.flatnonzero((period == p) & (white >= 0))  # (k,)
        sel = sel[(sel >= 1) & (sel < n - 1)]  # (k',)
        uniform, after = [], []
        for j in tqdm(sel, desc=f"period {p}", unit="diagonal", file=sys.stderr, mininterval=5,
                      disable=len(sel) < 10000):
            gaps = phase_gaps(tail[:64, j])  # (64,): 64 rows cover every period that occurs
            uniform.append(gaps.mean())
            if white[j - 1] >= 0:  # behind a white diagonal the walk does not arrive after a black cell
                after.append(gaps[np.roll(tail[:64, j - 1], 1) == 1].mean())  # phases s with D_{j-1}(s - 1) = 1
        rows.append(StepRow(p, len(sel), float(step[sel].mean()), int(step[sel].max()), float((white[sel] + 1).mean()),
                            1 + float(np.mean(uniform)), 1 + float(np.mean(after)), float((step[sel] == 1).mean())))
    return rows


@dataclass(frozen=True, slots=True)
class FrontLaw:
    bound: np.ndarray  # (n - 2,) C_{j+1} for j = 1 .. n - 2
    defect: np.ndarray  # (n - 2,) T_{j+1} = C_{j+1}
    advance: np.ndarray  # (n - 2,) T_{j+1} - S_j
    gap: np.ndarray  # (n - 2,) C_{j+1} - S_j - 1, the gap from S_j to the next black cell of D_j (-1: white)


def front_law(onset: np.ndarray, tail: np.ndarray, steps: int, period: int) -> FrontLaw:
    """The front law at the true onsets: C_{j+1} = r + 1 for the first black r >= S_j = max(T_{j-1}, T_j) of D_j."""
    # onset: (n,); tail: (window, n)
    n = len(onset)
    S = np.maximum(onset[:n - 2], onset[1:n - 1])  # (n - 2,): S_j for j = 1 .. n - 2
    gap = np.array([first_black(tail, steps, period, j, int(S[j - 1])) for j in range(1, n - 1)], dtype=np.int64)
    bound = np.where(gap < 0, S, S + gap + 1)  # (n - 2,)
    later = onset[2:]  # (n - 2,): T_{j+1}
    assert (later <= bound).all(), "the front law bounds every onset"
    return FrontLaw(bound, later == bound, later - S, gap)


def phase_chi2(x: np.ndarray, p: int) -> float:
    """The chi-square statistic of the residues of x modulo p against the uniform distribution (p - 1 degrees of
    freedom)."""
    # x: (k,)
    c = np.bincount(x % p, minlength=p).astype(np.float64)  # (p,)
    return float(((c - c.mean()) ** 2 / c.mean()).sum())


def pair_types(tail: np.ndarray, lo: int, hi: int, p: int) -> int:
    """The number of distinct pairs (D_j, D_{j+1}), lo <= j < hi, of period p, up to a time shift."""
    # tail: (window, n)
    rows = tail[:p, lo:hi + 1].astype(np.int64)  # (p, hi - lo + 1)
    weight = (1 << np.arange(p, dtype=np.int64))[:, None]  # (p, 1)
    a = (rows[:, :-1] * weight).sum(axis=0)  # (hi - lo,)
    b = (rows[:, 1:] * weight).sum(axis=0)  # (hi - lo,)
    full = (1 << p) - 1
    codes = [(((a >> r) | (a << (p - r))) & full) << p | (((b >> r) | (b << (p - r))) & full) for r in range(p)]
    return len(np.unique(np.min(np.array(codes), axis=0)))  # codes: (p, hi - lo)


def window_max(step: np.ndarray, m: int) -> int:
    """The largest sum of m consecutive steps."""
    # step: (k,)
    c = np.concatenate([[0], np.cumsum(step)])  # (k + 1,)
    return int((c[m:] - c[:-m]).max())


def step_pairs(step: np.ndarray, top: int) -> np.ndarray:
    """M[a - 1, b - 1] = the number of consecutive steps (a, b), with steps above `top` counted as `top`."""
    # step: (k,), every entry >= 1
    s = np.minimum(step, top) - 1  # (k,)
    M = np.zeros((top, top), dtype=np.int64)  # (top, top)
    np.add.at(M, (s[:-1], s[1:]), 1)
    return M


BLOCKS: list[tuple[int, int]] = [(8, 400), (400, 53207), (53207, 87867), (87867, 200000)]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--depth", type=int, default=200000)
    parser.add_argument("--steps", type=int, default=0, help="default 3 depth / 2 + 600")
    args = parser.parse_args()
    steps = args.steps or 3 * args.depth // 2 + 600
    d = stream(args.depth, steps)
    n = args.depth + 1
    assert (d.onset <= steps - 4 * d.period).all()
    period = least_periods(d.tail)  # (n,)
    white = white_runs(d.tail)  # (n,)
    w = walk_from_tail(d.onset, d.tail, steps, d.period)  # (n,)
    j = np.arange(n)  # (n,)
    step = np.diff(w)  # (n - 1,)
    print(f"walk: T_j <= w_j for every j <= {args.depth}: {bool((d.onset <= w).all())}; "
          f"w_(j+1) = w_j exactly at j = {np.flatnonzero(step == 0).tolist()}")
    print(f"w_J = {w[-1]} at J = {args.depth}, w_J / J = {w[-1] / args.depth:.4f}; "
          f"largest w_j / j for j >= 1000: {(w[1000:] / j[1000:]).max():.4f}")
    for num, den in [(2, 1), (41, 20), (21, 10)]:
        print(f"  w_(j+1) <= ceil({num} j / {den}) + delta for j < {args.depth}: delta = {walk_offset(w, num, den)}")
    for J in [1000, 10000, 50000, 100000, args.depth]:
        if J <= args.depth:
            print(f"  largest w_j - 2 j over j <= {J}: {int((w[1:J + 1] - 2 * j[1:J + 1]).max())}")
    print(f"{'period':>6} {'count':>7} {'mean step':>9} {'max':>4} {'1-steps':>7} {'uniform':>7} {'after':>6} "
          f"{'mean c':>7}")
    for r in step_table(w, period, white, d.tail):
        print(f"{r.period:>6} {r.count:>7} {r.mean_step:9.4f} {r.max_step:>4} {r.one_step:7.4f} "
              f"{r.mean_phase_gap:7.3f} {r.mean_after_black:6.3f} {r.mean_cost:7.3f}")
    body = step[400:][step[400:] > 0]  # (k,): steps past depth 400, white diagonals left out
    print(f"{len(body)} steps past depth 400: frequencies of k = 1 .. 7: "
          f"{[round(float((body == k).mean()), 4) for k in range(1, 8)]}; mean {body.mean():.4f}, standard error "
          f"{body.std() / np.sqrt(len(body)):.4f}")
    M = step_pairs(body, 8)  # (8, 8)
    print("P(next step 1 | step k), k = 1 .. 8+:", np.round(M[:, 0] / M.sum(axis=1), 3).tolist())
    print("smallest count of a pair of steps (a, b) with a, b <= 6:", int(M[:6, :6].min()))
    print("largest sum of m consecutive steps past depth 400:",
          {m: window_max(body, m) for m in [1, 2, 4, 8, 16, 32, 64, 128, 1024]})
    f = front_law(d.onset, d.tail, steps, d.period)
    print(f"front law at the true onsets: T_(j+1) = C_(j+1) (defect 1) for {f.defect.mean():.4f} of j; "
          f"T_(j+1) - S_j from {int(f.advance.min())} to {int(f.advance.max())}, mean {f.advance.mean():.3f}; "
          f"T_(j+1) - T_j from {int(np.diff(d.onset).min())} to {int(np.diff(d.onset).max())}")
    print(f"mean gap from S_j to the next black cell (past depth 400): {f.gap[399:][f.gap[399:] >= 0].mean():.4f}; "
          f"from w_j: {(body - 1).mean():.4f}")
    for lo, hi in BLOCKS:
        if hi <= n:
            p = int(period[hi - 2])
            print(f"depths {lo} .. {hi - 1}: T_j mod {p} chi2 {phase_chi2(d.onset[lo:hi], p):.1f}, "
                  f"w_j mod {p} chi2 {phase_chi2(w[lo:hi], p):.1f} ({p - 1} degrees of freedom); "
                  f"mean T increment {(d.onset[hi - 1] - d.onset[lo]) / (hi - 1 - lo):.4f}, "
                  f"mean w step {(w[hi - 1] - w[lo]) / (hi - 1 - lo):.4f}")
    for lo, hi, p in [(400, 53206, 16), (53208, 58285, 16), (58287, 87865, 16), (87867, args.depth - 1, 32)]:
        if lo < hi < n - 1:
            print(f"pairs j = {lo} .. {hi - 1} of period {p}: {hi - lo} pairs, {pair_types(d.tail, lo, hi, p)} types "
                  f"up to a time shift")
    for x in [399, 53207, 58286, 87866]:
        if x + 2000 < n:
            a, b = max(x - 2000, 1), x + 2000
            print(f"around the white diagonal {x}: mean T increment {(d.onset[x] - d.onset[a]) / (x - a):.4f} before, "
                  f"{(d.onset[b] - d.onset[x]) / (b - x):.4f} after; mean w step {(w[x] - w[a]) / (x - a):.4f} before, "
                  f"{(w[b] - w[x]) / (b - x):.4f} after")


if __name__ == "__main__":
    main()
