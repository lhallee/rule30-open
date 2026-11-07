"""Admissible drivers counted by their black cells, against the mean count over a uniformly random left half.

The setting of `driver_density`: a driver c(0) = 1, c(1), c(2), ... is admissible from a left half x when, with x
driven by c, c(t + 1) = not x_{-1}(t) whenever c(t) = 1. For a word w = c(0 .. n - 1), b(w) is the number of black
cells among c(0 .. n - 2), the letters that fix the next one. N_n(b) is the number of admissible words of length n from
the white start with b(w) = b. Column -1 under a fixed word is a bijective function of the cells -1 .. -(n - 1) (the
kit's `Rule30DrivenLeft.permutive`), so a word is admissible from exactly 2^((n - 1) - b(w)) of the 2^(n - 1) fillings
of those cells, and over a uniformly random left half the mean of N_n(b) is E_n(b) = 2 binom(n - 2, b - 1) 2^-b.

1. `count_layers`: N_n(b) for every n <= nmax in one pass, by dynamic programming over the states (left half at time
   t, c(t)). Each state carries its count vector packed into one Python integer: field b, of nmax bits, counts the
   words that reach the state with b black cells among c(0 .. t - 1), so the layer at time t gives N_(t + 1) exactly.
   A word of length at most nmax reads column -1 only up to time nmax - 2, which depends on the cells
   -1 .. -(nmax - 1 - t) at time t; the cells beyond are cleared and the states that then agree are merged.
2. `ratio_row`, `sweep`: the ratio N_n(b) / E_n(b), its largest value over b and over the dense tail b >= 0.68 (n - 1),
   the largest b with N_n(b) > 0 and the largest b with E_n(b) >= 1, and the mean and variance of b under the center
   column with column 1 replaced by fair coins, which gives each admissible word the probability
   2^-(white cells among c(0 .. n - 2)); `sweep` keeps the largest ratios over a range of n. `tail` prints N_n(b) and
   E_n(b) at one n, and `halves` the same ratios from uniformly random left halves.
3. `best_from`: the most black cells among c(0 .. T) over the drivers admissible from a given left half, exactly or with
   a beam that keeps the states with the largest counts (a lower bound, attained by a driver), with the steps of
   `driver_density`; `random` runs it from uniformly random halves and from the white start.

    python -m computations.driver_counts sweep                        # n <= 120, about 5 s
    python -m computations.driver_counts sweep --nmax 150             # n <= 150, about 1 min, 2 GB
    python -m computations.driver_counts tail --n 100 --start 60      # about 1 s
    python -m computations.driver_counts halves                       # 8 random halves at n = 100, about 4 s
    python -m computations.driver_counts random                       # 3 random halves to T = 1,000, about 1 min
"""

from __future__ import annotations

import argparse
import math
import sys
from collections.abc import Iterator, Sequence
from dataclasses import dataclass
from fractions import Fraction

import numpy as np
from tqdm.auto import tqdm

from computations.driver_density import dedupe_max, successors
from computations.run_mechanism import driven_step

ONE = np.uint64(1)
TAIL = Fraction(17, 25)  # the dense tail of the ratios: b >= 0.68 (n - 1)


# ---------------------------------------------------------------------------------------------------------------------
# The first moment
# ---------------------------------------------------------------------------------------------------------------------


def mean_count(n: int, b: int) -> Fraction:
    """E_n(b) = 2 binom(n - 2, b - 1) 2^-b, the mean of N_n(b) over a uniformly random left half, for n >= 2: the
    binom(n - 2, b - 1) choices of c(1 .. n - 2), the free last letter, and the chance 2^-b that b forced values come
    out right."""
    if b < 1 or b > n - 1:
        return Fraction(0)
    return Fraction(2 * math.comb(n - 2, b - 1), 2 ** b)


def entropy(d: float) -> float:
    """The binary entropy h(d) in bits."""
    if d <= 0.0 or d >= 1.0:
        return 0.0
    return -d * math.log2(d) - (1.0 - d) * math.log2(1.0 - d)


def threshold() -> tuple[float, float]:
    """d*, the root of h(d) = d in (1/2, 1), by bisection, and kappa = 1 + log2(d* / (1 - d*)), the slope of d - h(d)
    at d*."""
    lo, hi = 0.5, 1.0  # h(d) - d is positive at 1/2 and negative near 1, and decreasing on (1/3, 1)
    for _ in range(200):
        mid = (lo + hi) / 2
        if entropy(mid) > mid:
            lo = mid
        else:
            hi = mid
    d = (lo + hi) / 2
    return d, 1.0 + math.log2(d / (1.0 - d))


# ---------------------------------------------------------------------------------------------------------------------
# Exact counts by dynamic programming
# ---------------------------------------------------------------------------------------------------------------------
# A left half is a multiword integer as in run_mechanism: bit k - 1 of X[i] is cell -k at time t. c[i] is c(t), P[i] the
# packed count vector of the state: the sum over b of 2^(field b) times the number of words that reach it with b black
# cells among c(0 .. t - 1).


def words_for(nmax: int) -> int:
    """64-bit words that hold the cells -1 .. -nmax."""
    return nmax // 64 + 1


def pack_half(cells: Sequence[int], nmax: int) -> np.ndarray:
    """A left half from its cells: element k - 1 of `cells` is cell -k; the cells beyond are white."""
    X = np.zeros(words_for(nmax), dtype=np.uint64)  # (W,)
    for k, v in enumerate(cells[:64 * len(X)]):
        if v:
            X[k // 64] |= ONE << np.uint64(k % 64)
    return X  # (W,)


def random_half(nmax: int, rng: np.random.Generator) -> np.ndarray:
    """A left half with the cells -1 .. -64W independent fair coins."""
    W = words_for(nmax)
    return pack_half(rng.integers(0, 2, size=64 * W).tolist(), nmax)  # (W,)


def keep_cells(X: np.ndarray, cells: int) -> np.ndarray:
    """X with the cells beyond -cells cleared."""
    # X: (m, W)
    W = X.shape[1]
    if cells >= 64 * W:
        return X  # (m, W)
    cells = max(cells, 0)
    mask = np.zeros(W, dtype=np.uint64)  # (W,)
    mask[:cells // 64] = np.uint64(2**64 - 1)
    if cells % 64:
        mask[cells // 64] = np.uint64(2 ** (cells % 64) - 1)
    return X & mask  # (m, W)


def merge(X: np.ndarray, c: np.ndarray, P: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Merge equal states (X, c), adding their packed count vectors."""
    # X: (m, W) uint64; c: (m,) uint8; P: (m,) object
    order = np.lexsort([X[:, j] for j in range(X.shape[1])] + [c])  # (m,)
    Xs, cs = X[order], c[order]  # (m, W), (m,)
    new = np.ones(len(order), dtype=bool)  # (m,)
    new[1:] = (cs[1:] != cs[:-1]) | (Xs[1:] != Xs[:-1]).any(axis=1)
    first = np.flatnonzero(new)  # (k,)
    return Xs[first], cs[first], np.add.reduceat(P[order], first)  # (k, W), (k,), (k,) object


@dataclass
class Layer:
    n: int  # word length; the layer is the time n - 1
    states: int  # distinct states at time n - 1, after the cells that no longer matter are cleared
    counts: list[int]  # counts[b] = N_n(b) for b = 0 .. n - 1


def count_layers(nmax: int, start: np.ndarray | None = None, progress: bool = False) -> Iterator[Layer]:
    """Yield the exact counts N_n(b) of the admissible words of length n, for n = 1 .. nmax, from the white start or
    from the left half `start` (a (W,) array from `pack_half` or `random_half`), every word starting with c(0) = 1."""
    W = words_for(nmax)
    field = nmax  # a count of words of length n <= nmax is at most 2^(n - 1) < 2^nmax, so no field overflows
    full = (1 << field) - 1
    X = np.zeros((1, W), dtype=np.uint64) if start is None else start[None, :W].copy()  # (1, W)
    X = keep_cells(X, nmax - 1)  # (1, W)
    c = np.ones(1, dtype=np.uint8)  # (1,)
    P = np.array([1], dtype=object)  # (1,), one word with no letter counted yet
    for t in tqdm(range(nmax), desc="word counts", file=sys.stderr, disable=not progress):
        total = sum(P.tolist())
        yield Layer(t + 1, len(c), [(total >> (field * b)) & full for b in range(t + 1)])
        if t == nmax - 1:
            return
        white = c == 0  # (m,)
        Xw = driven_step(X[white], 0)  # (mw, W)
        Xb = X[~white]  # (mb, W)
        forced = (ONE ^ (Xb[:, 0] & ONE)).astype(np.uint8)  # (mb,), not cell -1 at time t
        Xb = driven_step(Xb, 1)  # (mb, W)
        Pw = P[white]  # (mw,) object
        Pb = P[~white] << field  # (mb,) object, c(t) = 1 is counted
        mw = len(Xw)
        Xn = keep_cells(np.concatenate([Xw, Xw, Xb]), nmax - 2 - t)  # (2 mw + mb, W)
        cn = np.concatenate([np.zeros(mw, np.uint8), np.ones(mw, np.uint8), forced])  # (2 mw + mb,)
        X, c, P = merge(Xn, cn, np.concatenate([Pw, Pw, Pb]))


def word_counts(n: int, start: np.ndarray | None = None) -> list[int]:
    """N_n(b) for b = 0 .. n - 1, from the white start or from `start` (built for at least n cells)."""
    *_, last = count_layers(n, start)
    return last.counts


# ---------------------------------------------------------------------------------------------------------------------
# Ratios to the first moment
# ---------------------------------------------------------------------------------------------------------------------


@dataclass
class RatioRow:
    n: int
    total: int  # admissible words of length n
    top: Fraction  # the largest N_n(b) / E_n(b) over b
    top_b: int  # the b where it is attained
    tail: Fraction | None  # the largest ratio over b >= 0.68 (n - 1) with E_n(b) > 0, if there is such b
    tail_b: int | None
    densest: int  # the largest b with N_n(b) > 0
    mean_densest: int  # the largest b with E_n(b) >= 1
    mass: Fraction  # sum over b of N_n(b) 2^(b - (n - 1)): the total probability of the process, 1
    mean: Fraction  # the mean of b under the process (n / 2 for 1 + Bin(n - 2, 1/2))
    variance: Fraction  # its variance ((n - 2) / 4 for 1 + Bin(n - 2, 1/2))


def ratio_row(n: int, counts: Sequence[int]) -> RatioRow:
    """The ratios N_n(b) / E_n(b) of one layer (n >= 3), and the moments of b under the process with column 1 random,
    which gives each admissible word the probability 2^-(white cells among c(0 .. n - 2))."""
    ratios = [(Fraction(counts[b]) / mean_count(n, b), b) for b in range(1, n)]
    top, top_b = max(ratios)
    tail = [(r, b) for r, b in ratios if b >= TAIL * (n - 1)]
    tail_top, tail_b = max(tail) if tail else (None, None)
    densest = max(b for b in range(n) if counts[b] > 0)
    mean_densest = max(b for b in range(1, n) if mean_count(n, b) >= 1)
    prob = [Fraction(counts[b] << b, 1 << (n - 1)) for b in range(n)]
    mass = sum(prob, Fraction(0))
    mean = sum((b * p for b, p in enumerate(prob)), Fraction(0))
    variance = sum((b * b * p for b, p in enumerate(prob)), Fraction(0)) - mean * mean
    return RatioRow(n, sum(counts), top, top_b, tail_top, tail_b, densest, mean_densest, mass, mean, variance)


@dataclass
class Sweep:
    rows: list[RatioRow]  # one per n = 3 .. nmax
    top: tuple[Fraction, int, int]  # the largest ratio over nmin <= n <= nmax and every b, with n and b
    tail: tuple[Fraction, int, int]  # the largest ratio over the same n and b >= 0.68 (n - 1), with n and b
    small: tuple[Fraction, int, int]  # the largest ratio over 3 <= n < nmin and every b, with n and b
    last: list[int]  # N_nmax(b) for b = 0 .. nmax - 1


def sweep(nmax: int, nmin: int = 20, start: np.ndarray | None = None, progress: bool = False) -> Sweep:
    """`ratio_row` for every n = 3 .. nmax in one pass, and the largest ratios over nmin <= n <= nmax and below nmin
    (3 < nmin <= nmax)."""
    rows: list[RatioRow] = []
    last: list[int] = [1]
    for layer in count_layers(nmax, start, progress):
        if layer.n >= 3:
            rows.append(ratio_row(layer.n, layer.counts))
        last = layer.counts
    top = max((r.top, r.n, r.top_b) for r in rows if r.n >= nmin)
    tail = max((r.tail, r.n, r.tail_b) for r in rows if r.n >= nmin and r.tail is not None and r.tail_b is not None)
    small = max((r.top, r.n, r.top_b) for r in rows if r.n < nmin)
    return Sweep(rows, top, tail, small, last)


# ---------------------------------------------------------------------------------------------------------------------
# The most black cells from a given left half
# ---------------------------------------------------------------------------------------------------------------------


def best_from(steps: int, start: np.ndarray | None = None, beam: int | None = None,
              progress: bool = False) -> list[int]:
    """M(t) for t = 0 .. steps: the most black cells among c(0 .. t) over the drivers with c(0) = 1 admissible from the
    white start or from `start` (exact when `beam` is None; otherwise the `beam` states with the largest counts are
    kept, a lower bound attained by a driver). The cells that no longer matter by time `steps` are cleared."""
    W = words_for(steps + 1)
    X = np.zeros((1, W), dtype=np.uint64) if start is None else start[None, :W].copy()  # (1, W)
    X = keep_cells(X, steps)  # (1, W)
    c = np.ones(1, dtype=np.uint8)  # (1,)
    V = np.ones((1, 1), dtype=np.int16)  # (1, 1), the most black cells among c(0 .. t)
    out = [1]
    for t in tqdm(range(steps), desc="best driver", file=sys.stderr, disable=not progress):
        X, c, V, _ = successors(X, c, V, None, t)
        X = keep_cells(X, steps - t - 1)  # column -1 at times t + 1 .. steps - 1 reads the cells -1 .. -(steps - t - 1)
        # the cells beyond -(t + 1) at time t + 1 do not depend on the driver, so equal states agree on them
        X, c, V, _ = dedupe_max(X, c, V, None, min(W, (t + 1) // 64 + 1))
        if beam is not None and len(c) > beam:
            keep = np.sort(np.argpartition(-V[:, 0], beam - 1)[:beam])  # (beam,)
            X, c, V = X[keep], c[keep], V[keep]
        out.append(int(V[:, 0].max()))
    return out


# ---------------------------------------------------------------------------------------------------------------------
# Command line
# ---------------------------------------------------------------------------------------------------------------------


def _ratio(r: Fraction | None) -> str:
    return "-" if r is None else f"{float(r):.4f}"


def run_sweep(args: argparse.Namespace) -> None:
    d, kappa = threshold()
    print(f"d* = {d:.7f} (h(d*) = d*), kappa = {kappa:.4f}; the mean count of all words grows by "
          f"log2(3/2) = {math.log2(1.5):.4f} per letter")
    print("loss rho - h(rho) that a bound N_n(b) <= 2^(theta n) E_n(b) for b >= rho (n - 1) may take: "
          + ", ".join(f"{rho}: {rho - entropy(rho):.4f}" for rho in (0.8, 0.85, 0.9, 0.95)))
    result = sweep(args.nmax, args.nmin, progress=True)
    print("n  words  log2(words)/n  largest ratio (b, b/(n-1))  largest tail ratio (b)  densest b (b/(n-1))  "
          "densest b with E >= 1  coin process: mass, mean - n/2, variance/(n-2)")
    for r in result.rows:
        if r.n % args.every == 0 or r.n == args.nmax:
            print(f"{r.n:>3} {r.total:>26,} {math.log2(r.total) / r.n:.4f}  {_ratio(r.top)} ({r.top_b}, "
                  f"{r.top_b / (r.n - 1):.3f})  {_ratio(r.tail)} ({r.tail_b})  "
                  f"{r.densest} ({r.densest / (r.n - 1):.4f})"
                  f"  {r.mean_densest}  {r.mass}, {float(r.mean - Fraction(r.n, 2)):.4f}, "
                  f"{float(r.variance / (r.n - 2)):.4f}")
    tails = [r for r in result.rows if r.n >= args.late and r.tail is not None]
    if tails:
        print(f"largest tail ratio for {args.late} <= n <= {args.nmax}: between "
              f"{float(min(r.tail for r in tails if r.tail is not None)):.4f} and "
              f"{float(max(r.tail for r in tails if r.tail is not None)):.4f}")
    for name, (ratio, n, b) in (("every b", result.top), ("b >= 0.68 (n - 1)", result.tail)):
        print(f"largest ratio over {args.nmin} <= n <= {args.nmax}, {name}: {float(ratio):.4f} at n = {n}, b = {b}")
    ratio, n, b = result.small
    print(f"largest ratio over 3 <= n < {args.nmin}: {float(ratio):.4f} at n = {n}, b = {b}")
    late = [r for r in result.rows if r.n >= args.late]
    if late:
        worst = max(late, key=lambda r: r.top)
        print(f"largest ratio over {args.late} <= n <= {args.nmax}: {float(worst.top):.4f} at n = {worst.n} "
              f"(b/(n-1) = {worst.top_b / (worst.n - 1):.3f}); every largest ratio there is at b/(n-1) in "
              f"[{min(r.top_b / (r.n - 1) for r in late):.3f}, {max(r.top_b / (r.n - 1) for r in late):.3f}]")


def run_tail(args: argparse.Namespace) -> None:
    counts = word_counts(args.n)
    print(f"n = {args.n}: b, N_n(b), E_n(b), ratio")
    for b in range(args.start if args.start else int(TAIL * (args.n - 1)), args.n):
        e = mean_count(args.n, b)
        if counts[b] > 0 or e >= Fraction(1, 100):
            print(f"{b:>4} {counts[b]:>16,} {float(e):>16.4f} {float(Fraction(counts[b]) / e):>10.4f}")


def run_halves(args: argparse.Namespace) -> None:
    rng = np.random.default_rng(args.seed)
    densities = [float(d) for d in args.densities.split(",")]
    print(f"N_n(b; x) / E_n(b) at n = {args.n} and b = round(d (n - 1)), and the largest ratios over "
          f"{args.nmin} <= n' <= {args.n}: over every b, and over b >= 0.68 (n' - 1)")
    halves = [("white", None)] + [(f"random {i}", random_half(args.n, rng)) for i in range(args.halves)]
    at = [round(d * (args.n - 1)) for d in densities]
    for name, half in halves:
        result = sweep(args.n, args.nmin, half)
        cells = "  ".join(f"{d}: {float(Fraction(result.last[b]) / mean_count(args.n, b)):.3f}"
                          for d, b in zip(densities, at))
        print(f"{name:>9}: {cells}  |  every b: {float(result.top[0]):.3f} (n' = {result.top[1]}), "
              f"tail: {float(result.tail[0]):.3f} (n' = {result.tail[1]})", flush=True)


def run_random(args: argparse.Namespace) -> None:
    rng = np.random.default_rng(args.seed)
    halves = [("white", None)] + [(f"random {i}", random_half(args.steps + 1, rng)) for i in range(args.halves)]
    marks = [t for t in range(0, args.steps + 1, args.every) if t > 0]
    for name, half in halves:
        exact = best_from(args.exact, half)
        line = best_from(args.steps, half, beam=args.beam, progress=True)
        cells = "  ".join(f"T={t}: {line[t]} ({line[t] / (t + 1):.4f})" for t in marks)
        print(f"{name:>9}: exact M({args.exact}) = {exact[-1]};  beam {args.beam}: {cells}", flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("sweep", help="N_n(b) / E_n(b) for every n <= nmax")
    p.add_argument("--nmax", type=int, default=120)
    p.add_argument("--nmin", type=int, default=20)
    p.add_argument("--late", type=int, default=60)
    p.add_argument("--every", type=int, default=10)
    p.set_defaults(func=run_sweep)
    p = sub.add_parser("tail", help="N_n(b) against E_n(b) for the dense b at one n")
    p.add_argument("--n", type=int, default=100)
    p.add_argument("--start", type=int, default=0)
    p.set_defaults(func=run_tail)
    p = sub.add_parser("halves", help="the same ratios from random left halves against the white start")
    p.add_argument("--n", type=int, default=100)
    p.add_argument("--nmin", type=int, default=20)
    p.add_argument("--halves", type=int, default=8)
    p.add_argument("--densities", default="0.34,0.5,0.6,0.65,0.68,0.7")
    p.add_argument("--seed", type=int, default=2026)
    p.set_defaults(func=run_halves)
    p = sub.add_parser("random", help="the most black cells from random left halves against the white start")
    p.add_argument("--steps", type=int, default=1000)
    p.add_argument("--beam", type=int, default=20000)
    p.add_argument("--exact", type=int, default=60)
    p.add_argument("--halves", type=int, default=3)
    p.add_argument("--every", type=int, default=200)
    p.add_argument("--seed", type=int, default=12345)
    p.set_defaults(func=run_random)
    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
