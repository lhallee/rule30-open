"""Three heuristics for when the left diagonals settle, tested on the onsets: a density budget for the reset gaps, the
decay of the damage from one flipped cell, and a doubling law T_{2j} <= 2 T_j + K.

A seed row is white left of a black cell lo, with cells x_1, x_2, ... right of it (the single cell has every x_i = 0).
Its left diagonals D_j(t) = cell(t, lo - t + j) obey D_{j+2}(t+1) = D_j(t) xor (D_{j+1}(t) or D_{j+2}(t)), and the
vector v_t with bit j = D_j(t) evolves by v -> (v << 2) xor ((v << 1) | v), from v_0 = 1 + sum_i x_i 2^i. The onset T_j
is the least T from which D_j repeats with period 64 (`seed_onsets.scalar_onsets`, `settled_slope.stream`).

- `diagonal_rows`, `table_onsets`, `transient_density`: the table D[j, t], its onsets, and the density of black cells
  of D_j on [start_j, T_j). The reset identity (if D_{j+1}(r) = 1 and D_{j+1} is white on (r, t], then
  D_{j+2}(t + 1) = 1 xor D_j(r) xor ... xor D_j(t)) suggests T_j / j = 1 / rho_j for the density rho_j of the transient.
- `damage_run`, `damage_survey`: a seed and the seed with cell x_k flipped, run together; for each diagonal, the last
  time + 1 at which the two differ, or -1 if they still differ in the last 64 times (then they differ forever: both
  repeat with period 64 there). `diagonal_shift` reads the time shift h with D_j(t) = S_j(t + h) against the single
  cell's S_j on the last rows.
- `doubling_excess`, `base_ratio`, `dispersion`, `frontier`: the doubling law and the spread of the onsets.

    python -m computations.onset_heuristics density                                   # about 1 s
    python -m computations.onset_heuristics damage --depth 40 --pairs 300 --flip 40   # about 2 s
    python -m computations.onset_heuristics damage --depth 450 --pairs 200 --flip 8   # about 40 s
    python -m computations.onset_heuristics doubling --depth 200000                   # about 2.5 min, 0.2 GB
"""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass

import numpy as np
from tqdm.auto import tqdm

from computations.seed_onsets import scalar_onsets
from computations.settled_slope import stream

PERIOD = 64


def diagonal_rows(v0: int, depth: int, steps: int) -> np.ndarray:
    """D[j, t] for j <= depth and t < steps, from the vector v0 (bit j = D_j(0))."""
    n = depth + 1
    mask = (1 << n) - 1
    v = v0 & mask
    D = np.zeros((n, steps), dtype=np.uint8)  # (depth + 1, steps)
    for t in range(steps):
        raw = np.frombuffer(v.to_bytes((n + 7) // 8, "little"), dtype=np.uint8)  # (ceil(n / 8),)
        D[:, t] = np.unpackbits(raw, bitorder="little")[:n]
        v = ((v << 2) ^ ((v << 1) | v)) & mask
    return D  # (depth + 1, steps)


def table_onsets(D: np.ndarray, period: int = PERIOD) -> np.ndarray:
    """The least T with D_j(t + period) = D_j(t) for T <= t < steps - period, for each row of the table."""
    # D: (n, steps)
    change = D[:, period:] != D[:, :-period]  # (n, steps - period)
    steps = change.shape[1]
    last = steps - 1 - np.argmax(change[:, ::-1], axis=1)  # (n,): the last change, if any
    return np.where(change.any(axis=1), last + 1, 0)  # (n,)


def transient_density(D: np.ndarray, onset: np.ndarray, js: np.ndarray, start: np.ndarray) -> np.ndarray:
    """The fraction of black cells of D_j on [start_j, T_j) for each j in js (nan if the interval is empty)."""
    # D: (n, steps); onset: (n,); js: (m,); start: (m,)
    out = np.full(len(js), np.nan)  # (m,)
    for i, (j, s) in enumerate(zip(js, start)):
        if onset[j] > s:
            out[i] = D[j, s:onset[j]].mean()
    return out  # (m,)


def density_report(depth: int = 260, steps: int = 3000, lo: int = 50, hi: int = 200) -> dict[str, tuple[float, ...]]:
    """For the single cell and j in [lo, hi]: the mean, least and largest rho_j on [0, T_j), [ceil(j/2), T_j) and
    [j, T_j), the fraction of j with rho_j <= 0.52, and the fraction with 1 / rho_j within 15% of T_j / j; and the
    mean, least and largest T_j / j."""
    D = diagonal_rows(1, depth, steps)  # (depth + 1, steps)
    onset = table_onsets(D)  # (depth + 1,)
    assert onset.max() < steps - 4 * PERIOD
    js = np.arange(lo, hi + 1)  # (m,)
    ratio = onset[js] / js  # (m,)
    out: dict[str, tuple[float, ...]] = {"T/j": (ratio.mean(), ratio.min(), ratio.max())}
    for name, start in [("[0, T)", np.zeros_like(js)), ("[j/2, T)", (js + 1) // 2), ("[j, T)", js)]:
        rho = transient_density(D, onset, js, start)  # (m,)
        ok = ~np.isnan(rho)  # (m,)
        track = np.abs(1 / rho[ok] - ratio[ok]) <= 0.15 * ratio[ok]  # (k,)
        out[name] = (float(np.nanmean(rho)), float(np.nanmin(rho)), float(np.nanmax(rho)),
                     float((rho[ok] <= 0.52).mean()), float(track.mean()))
    return out


def damage_run(v0: int, w0: int, depth: int, steps: int, window: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Run two vectors together: the last time + 1 at which diagonal j differs (0 if never), and the last `window` rows
    of each, row r holding the diagonals at time steps - window + r."""
    n = depth + 1
    mask = (1 << n) - 1
    v, w = v0 & mask, w0 & mask
    last = np.zeros(n, dtype=np.int64)  # (n,)
    tails = np.zeros((2, window, n), dtype=np.uint8)  # (2, window, n)
    for t in range(steps):
        d = v ^ w
        while d:
            low = d & -d
            last[low.bit_length() - 1] = t + 1
            d ^= low
        if t >= steps - window:
            for k, x in enumerate((v, w)):
                raw = np.frombuffer(x.to_bytes((n + 7) // 8, "little"), dtype=np.uint8)  # (ceil(n / 8),)
                tails[k, t - (steps - window)] = np.unpackbits(raw, bitorder="little")[:n]
        v = ((v << 2) ^ ((v << 1) | v)) & mask
        w = ((w << 2) ^ ((w << 1) | w)) & mask
    return last, tails[0], tails[1]  # (n,), (window, n), (window, n)


def least_period(column: np.ndarray) -> int:
    """The least p dividing the length with column(t + p) = column(t) cyclically."""
    # column: (window,)
    n = len(column)
    return next(p for p in range(1, n + 1) if n % p == 0 and np.array_equal(column, np.roll(column, -p)))


def diagonal_shift(tail: np.ndarray, single: np.ndarray, j: int) -> int:
    """The least h >= 0 with D_j(t) = S_j(t + h) on the last rows (both tails cover whole periods and end at the same
    time), or -1 if there is none."""
    # tail: (window, n); single: (window, n)
    s = single[:, j]  # (window,)
    p = least_period(s)
    return next((h for h in range(p) if np.array_equal(tail[:, j], np.roll(s, -h))), -1)


@dataclass(frozen=True, slots=True)
class Damage:
    """A sample of seeds with one cell flipped."""

    flip: np.ndarray  # (pairs,) the flipped cell k
    clear: np.ndarray  # (pairs, depth + 1) last time + 1 of a difference on D_j (0 if none, -1 if forever)
    later: np.ndarray  # (pairs, depth + 1) the later onset max(T_j, T'_j)
    shift: np.ndarray  # (pairs, 2, depth + 1) time shift of D_j against the single cell, for each seed of the pair


def damage_survey(depth: int, pairs: int, flip: int, seed: int = 2, progress: bool = True) -> Damage:
    """Seeds with fair cells x_1 .. x_depth, each against itself with x_k flipped for k uniform in 1 .. flip."""
    steps = 4 * depth + 400
    steps -= steps % PERIOD
    rng = np.random.default_rng(seed)
    single = damage_run(1, 1, depth, steps, PERIOD)[1]  # (PERIOD, depth + 1)
    ks = np.zeros(pairs, dtype=np.int64)  # (pairs,)
    clear = np.zeros((pairs, depth + 1), dtype=np.int64)  # (pairs, depth + 1)
    later = np.zeros((pairs, depth + 1), dtype=np.int64)  # (pairs, depth + 1)
    shift = np.zeros((pairs, 2, depth + 1), dtype=np.int64)  # (pairs, 2, depth + 1)
    for i in tqdm(range(pairs), desc=f"flipped seeds, depth {depth}", file=sys.stderr, mininterval=5,
                  disable=not progress):
        x = int.from_bytes(rng.bytes(depth // 8 + 1), "little") & ((1 << depth) - 1)
        k = int(rng.integers(1, flip + 1))
        v0 = 1 | (x << 1)
        w0 = v0 ^ (1 << k)
        last, tv, tw = damage_run(v0, w0, depth, steps, PERIOD)  # (depth + 1,), (PERIOD, depth + 1) twice
        T = np.maximum(scalar_onsets(v0, depth, steps, PERIOD), scalar_onsets(w0, depth, steps, PERIOD))  # (n,)
        assert T.max() < steps - PERIOD, "horizon too short for the onsets"
        ks[i] = k
        clear[i] = np.where(last > steps - PERIOD, -1, last)
        later[i] = T
        shift[i, 0] = [diagonal_shift(tv, single, j) for j in range(depth + 1)]
        shift[i, 1] = [diagonal_shift(tw, single, j) for j in range(depth + 1)]
    return Damage(ks, clear, later, shift)


def doubling_excess(T: np.ndarray, J: int) -> tuple[int, int, int]:
    """The largest and least T_{2j} - 2 T_j over 1 <= j <= J, and the j of the largest."""
    # T: (n,), n > 2 J
    j = np.arange(1, J + 1)  # (J,)
    d = T[2 * j] - 2 * T[j]  # (J,)
    return int(d.max()), int(d.min()), int(j[d.argmax()])


def base_ratio(T: np.ndarray, K: int, lo: int, hi: int) -> tuple[float, int]:
    """The least (T_j + K) / j over lo <= j <= hi, and its j: the slope a doubling law with constant K gives from one
    base index."""
    # T: (n,)
    j = np.arange(lo, hi + 1)  # (m,)
    r = (T[j] + K) / j  # (m,)
    return float(r.min()), int(j[r.argmin()])


def dispersion(T: np.ndarray, lo: int, hi: int, m: int) -> tuple[float, float]:
    """Mean and variance of T_{j+m} - T_j over lo <= j <= hi - m, each divided by m."""
    # T: (n,)
    S = T[lo + m:hi + 1].astype(np.int64) - T[lo:hi + 1 - m]  # (hi - lo + 1 - m,)
    return float(S.mean() / m), float(S.var() / m)


def frontier(T: np.ndarray) -> tuple[int, int, float]:
    """F(t) = the largest J with T_j <= t for every j <= J. The largest number of diagonals F gains at one time, the
    longest wait between gains, and J / max_{j <= J} T_j at the last J."""
    # T: (n,)
    M = np.maximum.accumulate(T)  # (n,)
    times, counts = np.unique(M, return_counts=True)  # (k,), (k,)
    return int(counts.max()), int(np.diff(times).max()), float((len(T) - 1) / M[-1])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("what", choices=["density", "damage", "doubling"])
    parser.add_argument("--depth", type=int, default=0)
    parser.add_argument("--pairs", type=int, default=300)
    parser.add_argument("--flip", type=int, default=40)
    args = parser.parse_args()
    if args.what == "density":
        for name, row in density_report().items():
            print(name, [round(x, 4) for x in row])
    elif args.what == "damage":
        depth = args.depth or 40
        d = damage_survey(depth, args.pairs, args.flip)
        print(f"every diagonal of every seed is the single cell's shifted in time: {bool((d.shift >= 0).all())}")
        forever = d.clear == -1  # (pairs, depth + 1)
        differ = d.shift[:, 0] != d.shift[:, 1]  # (pairs, depth + 1)
        print(f"D_j differs forever exactly when the shifts differ: {bool((forever == differ).all())}")
        for j in sorted({3, 8, 29, 40, 100, 399, 400, depth}):
            if j <= depth:
                rows = d.flip <= j  # (pairs,)
                print(f"  depth {j}: differs forever for {forever[rows, j].mean():.3f} of {int(rows.sum())} pairs")
        p, j = np.nonzero((d.clear > 0) & (np.arange(depth + 1) >= d.flip[:, None]))  # (e,), (e,)
        c, m = d.clear[p, j], d.later[p, j]  # (e,), (e,)
        print(f"{len(c)} cleared diagonals at or past the flip: clear <= later onset for all: {bool((c <= m).all())}; "
              f"equal for {(c == m).mean():.3f}; mean later onset - clear {(m - c).mean():.2f}, max {(m - c).max()}")
        gap = j - d.flip[p]  # (e,)
        fit = np.polyfit(gap, c, 1)  # (2,)
        print(f"clearing time against j - k: slope {fit[0]:.3f}, intercept {fit[1]:.2f}; largest clear / j "
              f"{(c / np.maximum(j, 1)).max():.3f}")
    else:
        depth = args.depth or 200000
        d = stream(depth, 3 * depth // 2 + 600)
        T = d.onset.astype(np.int64)  # (depth + 1,)
        K = doubling_excess(T, 256)[0]
        print(f"K = max T_2j - 2 T_j over j <= 256: {K}; "
              f"least (T_j + K) / j over 16 <= j <= 256: {base_ratio(T, K, 16, 256)}")
        for J in [256, 1000, 4000, 10000, 50000, depth // 2]:
            if 2 * J <= depth:
                print(f"  j <= {J}: T_2j - 2 T_j from {doubling_excess(T, J)[1]} to {doubling_excess(T, J)[0]} "
                      f"(at j = {doubling_excess(T, J)[2]})")
        Kall = doubling_excess(T, depth // 2)[0]
        print(f"with K = {Kall}: least (T_j + K) / j over 16 <= j <= 256 {base_ratio(T, Kall, 16, 256)}, "
              f"over 16 <= j <= {depth // 2} {base_ratio(T, Kall, 16, depth // 2)}")
        for lo, hi in [(400, 53206), (87867, depth - 1)]:
            if hi <= depth:
                for m in [1, 4, 16, 64, 256, 1024, 4096]:
                    mean, var = dispersion(T, lo, hi, m)
                    print(f"  depths {lo} to {hi}, m = {m}: mean / m {mean:.4f}, variance / m {var:.3f}")
        print("frontier: largest gain at one time, longest wait, J / max T:", frontier(T))


if __name__ == "__main__":
    main()
