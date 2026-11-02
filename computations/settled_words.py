"""The settled words of the single cell's left diagonals: what they are, how each follows from the two before, and how
long their white runs get.

The left diagonals D_j(t) = cell(t, j - t) of the single black cell obey D_{j+2}(t+1) = D_j(t) xor (D_{j+1}(t) or
D_{j+2}(t)). Each repeats from its onset; its *settled word* is one period of it, read from a common time (a multiple of
every period after every onset), so that the words of different depths are aligned. `settled_slope.stream` gives the
last rows of the run, from which:

- `settled_table`: for every depth j, the least period P_j, the word up to rotation (its least rotation), the weight,
  the longest cyclic white run g_j and black run b_j, and whether D_j is anti-periodic (D_j(t + P_j/2) = not D_j(t)).
- `pair_next` and `pair_prev`: on aligned words of a common period P, the next word C from (A, B) (B not white: C is
  the unique P-periodic solution of C(t+1) = A(t) xor (B(t) or C(t)), started at a black cell of B), and A back from
  (B, C) (A(t) = C(t+1) xor (B(t) or C(t))). So (A, B) -> (B, C) is a bijection from the pairs whose second word is not
  white onto the pairs whose first word is not white; `check_pair_map` checks every depth against the run.
- `regimes`: the stretches between white diagonals. Each is the path of that bijection from a pair whose first word
  is white to a pair whose second word is white; `regime_rows` counts its depths, its distinct words and pairs up to
  rotation, and its longest runs.
- `class_chi_square` and `weight_correlations`: the words of a regime against fair words of its period.
- `run_law`: the exact law of the longest cyclic white run of a word of P fair bits, and `max_run_quantiles` the law
  of the largest of the runs of independent such words, one per settled diagonal up to depth j: the heuristic model
  that W_j = max(g_1, ..., g_j) is compared with.
- `run_transfer`: the run lemmas of `Rule30Open.Diagonals.RunTransfer` on the words: g_{j+2} <= a_j + 1 with a_j the
  longest cyclic run on which D_j = D_{j+1}, and b_{j+2} <= g_j + 1.
- `window_fit`: the slope of the window bounds of `seed_certificate` on stretches of depths, and the least C with
  V_j <= gamma j + C + kappa W_j over a depth range.

    python -m computations.settled_words --depth 200000             # every table, about 3 min, 0.2 GB
    python -m computations.settled_words --depth 87866 --fit 0,2,4,6  # also the window bounds against W_j, about 13 min
"""

from __future__ import annotations

import argparse
import math
import sys
from dataclasses import dataclass

import numpy as np
from tqdm.auto import tqdm

from computations.settled_slope import least_periods, stream

U64 = np.uint64


# ---------------------------------------------------------------------------------------------------------------------
# Words as integers: bit r is the cell at time base + r, r < P


def mask(P: int) -> np.uint64:
    """The P low bits."""
    return U64((1 << P) - 1) if P < 64 else U64(0xFFFFFFFFFFFFFFFF)


def words_from_tail(tail: np.ndarray, P: int) -> np.ndarray:
    """The aligned word of length P of every diagonal: bit r is D_j at the time of row r of `tail`."""
    # tail: (window, n)
    assert P <= 64 and P <= tail.shape[0]
    weights = np.left_shift(np.ones(P, dtype=U64), np.arange(P, dtype=U64))  # (P,)
    return (tail[:P].astype(U64) * weights[:, None]).sum(axis=0, dtype=U64)  # (n,)


def rotate(w: np.ndarray, k: int | np.ndarray, P: int) -> np.ndarray:
    """The words read from time k on: bit r of the result is bit (r + k) mod P of w."""
    # w: (n,)
    k = np.asarray(k, dtype=U64) % U64(P)  # () or (n,)
    m = mask(P)
    lo = w >> k
    hi = np.where(k == 0, U64(0), (w << ((U64(P) - k) % U64(64))) & m)  # (n,)
    return (lo | hi) & m  # (n,)


def least_rotation(w: np.ndarray, P: int) -> np.ndarray:
    """The least of the P rotations of each word, as an integer: the word up to rotation."""
    # w: (n,)
    best = w.copy()  # (n,)
    for k in range(1, P):
        best = np.minimum(best, rotate(w, k, P))
    return best  # (n,)


def least_pair_rotation(a: np.ndarray, b: np.ndarray, P: int) -> np.ndarray:
    """The least of (rot(a, k) << P) | rot(b, k) over the P common rotations: the pair up to a common time shift."""
    # a, b: (n,)
    assert 2 * P <= 64
    best = (a << U64(P)) | b  # (n,)
    for k in range(1, P):
        best = np.minimum(best, (rotate(a, k, P) << U64(P)) | rotate(b, k, P))
    return best  # (n,)


def cyclic_run(w: np.ndarray, P: int, bit: int) -> np.ndarray:
    """The longest cyclic run of cells equal to `bit` in each word of length P (P for a constant word)."""
    # w: (n,)
    assert 2 * P <= 64
    m = mask(P)
    x = w if bit else (~w) & m  # (n,): ones where the cell is `bit`
    full = x == m  # (n,)
    x = x | (x << U64(P))  # (n,): the word twice, so runs across the end are whole
    run = np.zeros(len(w), dtype=np.int64)  # (n,)
    while (x != 0).any():
        run += x != 0
        x = x & (x >> U64(1))
    return np.where(full, P, np.minimum(run, P))  # (n,)


def weight(w: np.ndarray) -> np.ndarray:
    """The number of black cells of each word."""
    # w: (n,)
    b = np.ascontiguousarray(w).view(np.uint8).reshape(len(w), 8)  # (n, 8)
    return np.unpackbits(b, axis=1).sum(axis=1).astype(np.int64)  # (n,)


def anti_periodic(w: np.ndarray, P: int) -> np.ndarray:
    """Whether each word of length P (P even) is its own complement after P/2 steps."""
    # w: (n,)
    if P % 2:
        return np.zeros(len(w), dtype=bool)
    return rotate(w, P // 2, P) == ((~w) & mask(P))  # (n,)


# ---------------------------------------------------------------------------------------------------------------------
# The table of settled words


@dataclass(frozen=True, slots=True)
class SettledTable:
    period: np.ndarray  # (n,) least period P_j (a power of two)
    word: np.ndarray  # (n,) uint64, the aligned word of length P_j
    canon: np.ndarray  # (n,) uint64, its least rotation
    weight: np.ndarray  # (n,) black cells per period
    white: np.ndarray  # (n,) longest cyclic white run g_j (P_j = 1 for a white diagonal, whose word is 0)
    black: np.ndarray  # (n,) longest cyclic black run b_j
    anti: np.ndarray  # (n,) bool, D_j(t + P_j / 2) = not D_j(t)


def settled_table(tail: np.ndarray) -> SettledTable:
    """The settled word of every diagonal, from rows that cover four of its periods."""
    # tail: (window, n)
    period = least_periods(tail)  # (n,)
    assert (period > 0).all(), "a diagonal has no period within a quarter of the rows"
    n = tail.shape[1]
    word = np.zeros(n, dtype=U64)  # (n,)
    canon = np.zeros(n, dtype=U64)  # (n,)
    white = np.zeros(n, dtype=np.int64)  # (n,)
    black = np.zeros(n, dtype=np.int64)  # (n,)
    anti = np.zeros(n, dtype=bool)  # (n,)
    for P in sorted(set(period.tolist())):
        sel = np.flatnonzero(period == P)  # (k,)
        w = words_from_tail(tail[:, sel], P)  # (k,)
        word[sel], canon[sel] = w, least_rotation(w, P)
        white[sel], black[sel] = cyclic_run(w, P, 0), cyclic_run(w, P, 1)
        anti[sel] = anti_periodic(w, P)
    return SettledTable(period, word, canon, weight(word), white, black, anti)


# ---------------------------------------------------------------------------------------------------------------------
# The pair map


def pair_next(a: np.ndarray, b: np.ndarray, P: int) -> tuple[np.ndarray, np.ndarray]:
    """For aligned words a = D_j, b = D_{j+1} of period P: the P-periodic word c with c(t+1) = a(t) xor (b(t) or c(t)),
    and whether it is unique (b not white). It is computed one time at a time from the black cell r of b of least
    index, where c(r + 1) = not a(r)."""
    # a, b: (n,)
    ok = b != 0  # (n,)
    low = np.where(ok, b & (~b + U64(1)), U64(1))  # (n,): the lowest black cell of b
    r = np.log2(low.astype(np.float64)).astype(np.int64)  # (n,)
    s = (r + 1) % P  # (n,): new time 0 is old time r + 1, so old r is new P - 1
    a2, b2 = rotate(a, s, P), rotate(b, s, P)  # (n,), (n,)
    one = U64(1)
    cur = ((a2 >> U64(P - 1)) & one) ^ one  # (n,): c at new time 0
    c2 = cur.copy()  # (n,)
    for t in range(P - 1):
        cur = ((a2 >> U64(t)) & one) ^ (((b2 >> U64(t)) & one) | cur)
        c2 |= cur << U64(t + 1)
    return rotate(c2, (P - s) % P, P), ok  # (n,), (n,)


def pair_prev(b: np.ndarray, c: np.ndarray, P: int) -> np.ndarray:
    """The word a with c(t+1) = a(t) xor (b(t) or c(t)) for every t: a(t) = c(t+1) xor (b(t) or c(t))."""
    # b, c: (n,)
    return rotate(c, 1, P) ^ (b | c)  # (n,)


@dataclass(frozen=True, slots=True)
class PairCheck:
    period: int  # the common period P of the aligned words
    forward: int  # depths j at which D_{j+1} is not white and pair_next gives D_{j+2}
    backward: int  # depths at which pair_prev gives D_j from D_{j+1}, D_{j+2}
    white_steps: int  # depths at which D_{j+1} is white (the forward map has two candidates)
    failures: int  # depths at which a check fails


def check_pair_map(tail: np.ndarray, P: int) -> PairCheck:
    """Checks the pair map at every depth, on the aligned words of the common period P."""
    # tail: (window, n)
    w = words_from_tail(tail, P)  # (n,)
    a, b, c = w[:-2], w[1:-1], w[2:]  # (n - 2,) each
    nxt, ok = pair_next(a, b, P)  # (n - 2,), (n - 2,)
    fwd = ok & (nxt == c)  # (n - 2,)
    back = pair_prev(b, c, P) == a  # (n - 2,)
    fail = int((ok & ~fwd).sum() + (~back).sum())
    return PairCheck(P, int(fwd.sum()), int(back.sum()), int((~ok).sum()), fail)


# ---------------------------------------------------------------------------------------------------------------------
# Regimes between white diagonals


def regimes(table: SettledTable) -> list[tuple[int, int]]:
    """The stretches [w + 1, w'] between consecutive white diagonals w < w' (and from depth 0, and to the last depth)."""
    wd = np.flatnonzero(table.weight == 0).tolist()
    cuts = [-1] + wd + [len(table.period) - 1]
    return [(lo + 1, hi) for lo, hi in zip(cuts[:-1], cuts[1:]) if lo + 1 <= hi]


@dataclass(frozen=True, slots=True)
class RegimeRow:
    first: int  # the first depth (just after a white diagonal) and the last (a white diagonal, or the last depth)
    last: int
    period: int  # the common period of the regime
    depths: int
    words: int  # distinct words up to rotation
    pairs: int  # distinct pairs (D_{j-1}, D_j) up to a common rotation, j in the regime past its first depth
    repeated_pairs: int  # depths whose pair occurred before in the regime
    max_white: int  # largest g_j over the non-white diagonals
    max_black: int  # largest b_j
    weight_one: int  # diagonals with one black cell in the regime's period P (white run P - 1)
    anti: int  # diagonals whose aligned word of the regime's period P is anti-periodic: w(t + P/2) = not w(t)


def regime_rows(tail: np.ndarray, table: SettledTable) -> list[RegimeRow]:
    """One row per regime, on the aligned words of the regime's common period."""
    # tail: (window, n)
    rows: list[RegimeRow] = []
    for lo, hi in regimes(table):
        P = int(table.period[lo:hi + 1].max())
        assert (P % table.period[lo:hi + 1] == 0).all(), "periods in a regime divide its largest"
        w = words_from_tail(tail[:, lo:hi + 1], P)  # (k,)
        canon = least_rotation(w, P)  # (k,)
        nw = table.weight[lo:hi + 1] > 0  # (k,)
        if 2 * P <= 64 and hi > lo:
            pk = least_pair_rotation(w[:-1], w[1:], P)  # (k - 1,)
            npairs = len(np.unique(pk))
            rep = len(pk) - npairs
        else:
            npairs, rep = -1, -1
        rows.append(RegimeRow(lo, hi, P, hi - lo + 1, len(np.unique(canon)), npairs, rep,
                              int(table.white[lo:hi + 1][nw].max()) if nw.any() else 0,
                              int(table.black[lo:hi + 1].max()), int((weight(w) == 1).sum()),
                              int(anti_periodic(w, P).sum())))
    return rows


def class_chi_square(w: np.ndarray, P: int) -> tuple[float, int]:
    """The chi-square statistic of the counts of the words up to rotation against fair words of P bits (a class of
    size s has probability s / 2^P), and its degrees of freedom (the number of classes less one)."""
    # w: (k,)
    assert P <= 20
    classes, size = np.unique(least_rotation(np.arange(1 << P, dtype=U64), P), return_counts=True)  # (m,), (m,)
    obs = np.bincount(np.searchsorted(classes, least_rotation(w, P)), minlength=len(classes))  # (m,)
    exp = len(w) * size / float(1 << P)  # (m,)
    return float(((obs - exp) ** 2 / exp).sum()), len(classes) - 1


def weight_correlations(w: np.ndarray, lags: tuple[int, ...] = (1, 2, 3)) -> list[float]:
    """The correlation of the weights of the words at depths j and j + lag."""
    # w: (k,)
    x = weight(w).astype(np.float64)  # (k,)
    return [float(np.corrcoef(x[:-lag], x[lag:])[0, 1]) for lag in lags]


# ---------------------------------------------------------------------------------------------------------------------
# The longest-run law of fair words, and the model for W_j


def run_law(P: int) -> list[int]:
    """count[k] = the number of words of P bits whose longest cyclic white run is exactly k (k = P: the white word),
    exactly, by the run that wraps around the end."""
    out: list[int] = []
    for k in range(P + 1):
        # words with a black cell and every cyclic white run < k + 1, minus those with every run < k
        out.append(_runs_below(P, k + 1) - _runs_below(P, k))
    out[P] += 1  # the white word
    return out


def _runs_below(P: int, k: int) -> int:
    """The number of words of P bits with a black cell and every cyclic white run shorter than k."""
    if k <= 0:
        return 0
    # N[L]: strings of length L that start and end with a black cell and have every white run < k
    N = [0] * (P + 1)
    N[1] = 1
    for L in range(2, P + 1):
        N[L] = sum(N[L - 1 - z] for z in range(0, min(k - 1, L - 2) + 1))
    # the white run that wraps has a cells at the start and b at the end, a + b < k
    return sum((m + 1) * N[P - m] for m in range(0, min(k - 1, P - 1) + 1))


def regime_period(table: SettledTable) -> np.ndarray:
    """The common period of the regime of each depth."""
    out = np.zeros(len(table.period), dtype=np.int64)  # (n,)
    for lo, hi in regimes(table):
        out[lo:hi + 1] = int(table.period[lo:hi + 1].max())
    return out  # (n,)


def max_run_quantiles(table: SettledTable, depths: list[int], qs: tuple[float, ...] = (0.01, 0.5, 0.99)) -> np.ndarray:
    """Row r: for each q, the least k with Pr[max g <= k] >= q at depth depths[r], when each non-white diagonal i <= j
    is a word of P(i) fair bits conditioned to have a black cell, P(i) the common period of its regime."""
    reg = regime_period(table)  # (n,)
    nonwhite = table.weight > 0  # (n,)
    periods = sorted(set(reg[nonwhite].tolist()))
    K = max(periods) + 1
    logF = {}  # P -> (K,) log Pr[g <= k | not white]
    for P in periods:
        law = np.array(run_law(P)[:P], dtype=np.float64)  # (P,): k = 0 .. P - 1
        cdf = np.cumsum(law) / law.sum()  # (P,)
        logF[P] = np.log(np.concatenate([cdf, np.ones(K - P)]))  # (K,)
    out = np.zeros((len(depths), len(qs)), dtype=np.int64)  # (len(depths), len(qs))
    for r, j in enumerate(depths):
        tot = np.zeros(K)  # (K,)
        for P in periods:
            tot += np.count_nonzero(nonwhite[1:j + 1] & (reg[1:j + 1] == P)) * logF[P]
        cdf = np.exp(tot)  # (K,)
        out[r] = [int(np.argmax(cdf >= q)) for q in qs]
    return out


def white_records(table: SettledTable) -> list[tuple[int, int, int, int]]:
    """(j, W_j, P_j, weight of D_j) at each depth where W_j = max(g_1, ..., g_j) grows."""
    g = np.where(table.weight == 0, 0, table.white)  # (n,)
    W = np.maximum.accumulate(g)  # (n,)
    rec = np.flatnonzero(np.diff(W) > 0) + 1  # (k,)
    return [(int(j), int(W[j]), int(table.period[j]), int(table.weight[j])) for j in rec]


# ---------------------------------------------------------------------------------------------------------------------
# The run lemmas on the words


@dataclass(frozen=True, slots=True)
class RunTransfer:
    agree: np.ndarray  # (n - 2,) a_j: longest cyclic run of times with D_j = D_{j+1}
    white_ok: int  # depths with g_{j+2} <= a_j + 1
    white_tight: int  # depths with equality (D_{j+2} not white)
    black_ok: int  # depths with b_{j+2} <= g_j + 1
    black_tight: int
    depths: int


def run_transfer(tail: np.ndarray, P: int) -> RunTransfer:
    """The two run lemmas, on the aligned words of the common period P, at every depth."""
    # tail: (window, n)
    w = words_from_tail(tail, P)  # (n,)
    g = cyclic_run(w, P, 0)  # (n,)
    b = cyclic_run(w, P, 1)  # (n,)
    a = cyclic_run(w[:-2] ^ w[1:-1], P, 0)  # (n - 2,)
    g2, b2 = g[2:], b[2:]  # (n - 2,)
    nonwhite = w[2:] != 0  # (n - 2,)
    return RunTransfer(a, int((g2 <= a + 1).sum()), int((nonwhite & (g2 == a + 1)).sum()),
                       int((b2 <= g[:-2] + 1).sum()), int(((b2 > 0) & (b2 == g[:-2] + 1)).sum()), len(a))


# ---------------------------------------------------------------------------------------------------------------------
# The window bounds against W_j


def window_fit(V: np.ndarray, U: np.ndarray, W: np.ndarray, stretches: list[tuple[int, int]],
               gammas: list[float], kappas: list[int]) -> tuple[list[float], np.ndarray]:
    """The least-squares slope of U_j on each stretch [lo, hi], and C[g, k] = the least integer C with
    V_j <= gammas[g] j + C + kappas[k] W_j for every j."""
    # V, U, W: (J + 1,)
    j = np.arange(len(V), dtype=np.float64)  # (J + 1,)
    slopes = [float(np.polyfit(j[lo:hi + 1], U[lo:hi + 1], 1)[0]) for lo, hi in stretches]
    C = np.zeros((len(gammas), len(kappas)), dtype=np.int64)  # (len(gammas), len(kappas))
    for gi, gam in enumerate(gammas):
        for ki, kap in enumerate(kappas):
            C[gi, ki] = math.ceil(float((V - gam * j - kap * W).max()) - 1e-9)
    return slopes, C


# ---------------------------------------------------------------------------------------------------------------------


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--depth", type=int, default=200000)
    parser.add_argument("--fit", default="", help="window widths h for the fit of the window bounds against W_j")
    args = parser.parse_args()
    steps = 3 * args.depth // 2 + 600
    d = stream(args.depth, steps)
    assert d.onset.max() <= steps - 4 * 64, "an onset is too close to the end of the run"
    table = settled_table(d.tail)
    Pc = int(table.period.max())
    print(f"diagonals 0 .. {args.depth}; least periods {sorted(set(table.period.tolist()))}; "
          f"white diagonals {np.flatnonzero(table.weight == 0).tolist()}")

    pc = check_pair_map(d.tail, Pc)
    print(f"pair map on aligned words of period {Pc}: forward {pc.forward}, backward {pc.backward}, "
          f"white steps {pc.white_steps}, failures {pc.failures}")

    print("by regime: common period, depths, distinct words and pairs up to rotation, pairs met before, largest runs, "
          "words with one black cell, anti-periodic words and their expected number for fair words")
    print(f"{'regime':>17} {'P':>3} {'depths':>7} {'words':>6} {'pairs':>7} {'rep':>4} {'max g':>5} {'max b':>5} "
          f"{'wt 1':>5} {'anti':>5} {'fair':>6}")
    rows = regime_rows(d.tail, table)
    for r in rows:
        print(f"{r.first:>7} .. {r.last:>6} {r.period:>3} {r.depths:>7} {r.words:>6} {r.pairs:>7} {r.repeated_pairs:>4}"
              f" {r.max_white:>5} {r.max_black:>5} {r.weight_one:>5} {r.anti:>5} {r.depths * 2.0 ** (-(r.period // 2)):>6.1f}")

    for r in rows:
        if r.period > 16:
            M = 2.0 ** r.period / r.period  # about the number of classes up to rotation
            expect = r.depths - M * (1 - math.exp(r.depths * math.log1p(-1 / M)))
            print(f"  {r.first} .. {r.last}: {r.depths - r.words} words met before up to rotation; fair words of "
                  f"{r.period} bits would give about {expect:.1f}")
    print("regimes of more than 1,000 depths with P <= 16: chi-square of the words up to rotation against fair words, "
          "and the correlation of the weights at lags 1, 2, 3")
    for lo, hi in regimes(table):
        P = int(table.period[lo:hi + 1].max())
        if hi - lo >= 1000 and P <= 16:
            w = words_from_tail(d.tail[:, lo:hi + 1], P)  # (k,)
            chi, dof = class_chi_square(w, P)
            corr = weight_correlations(w)
            print(f"  {lo} .. {hi}: chi-square {chi:.1f} on {dof} degrees of freedom "
                  f"(z = {(chi - dof) / math.sqrt(2 * dof):+.2f}); weight correlations "
                  + ", ".join(f"{c:+.4f}" for c in corr))

    reg = regime_period(table)  # (n,)
    print("longest cyclic white run g_j by regime period: observed count, and expected for fair words with a black cell")
    for P in sorted(set(reg[table.weight > 0].tolist()) - {1}):
        sel = (reg == P) & (table.weight > 0)  # (n,)
        obs = np.bincount(table.white[sel], minlength=P)  # (P,)
        law = np.array(run_law(P)[:P], dtype=np.float64)  # (P,)
        exp = law / law.sum() * sel.sum()  # (P,)
        top = int(np.flatnonzero(obs).max())
        print(f"  P = {P:>2}, {int(sel.sum())} diagonals")
        print("    k       " + " ".join(f"{k:>7}" for k in range(1, top + 1)))
        print("    observed" + " ".join(f"{int(obs[k]):>7}" for k in range(1, top + 1)))
        print("    expected" + " ".join(f"{exp[k]:>7.1f}" for k in range(1, top + 1)))

    recs = white_records(table)
    q = max_run_quantiles(table, [j for j, *_ in recs] + [args.depth])
    print("records of W_j: depth, W_j, P_j, weight, log2 j, model quantiles 1%, 50%, 99% of W_j (last row: the last depth "
          "and its regime period)")
    for (j, Wj, P, wt), row in zip(recs + [(args.depth, recs[-1][1], int(regime_period(table)[-1]), -1)], q):
        print(f"  {j:>7} {Wj:>3} {P:>3} {wt:>3} {math.log2(j):6.2f}   {row[0]:>3} {row[1]:>3} {row[2]:>3}")

    rt = run_transfer(d.tail, Pc)
    print(f"run lemmas at {rt.depths} depths: g_(j+2) <= a_j + 1 at {rt.white_ok} (equal at {rt.white_tight}); "
          f"b_(j+2) <= g_j + 1 at {rt.black_ok} (equal at {rt.black_tight}); largest a_j {int(rt.agree.max())}")

    if args.fit:
        from computations.seed_certificate import window_bounds_c
        assert args.depth <= 87866, "the window bounds use period 16"
        g = np.where(table.weight == 0, 0, table.white)  # (n,)
        W = np.maximum.accumulate(g)  # (n,)
        stretches = [(63, 398), (659, 10000), (10000, 40000), (40000, args.depth)]
        stretches = [(lo, min(hi, args.depth)) for lo, hi in stretches if lo < args.depth]
        gammas, kappas = [1.5, 1.55, 1.6, 1.7, 2.0, 2.05], [0, 1, 2, 4]
        for h in tqdm([int(x) for x in args.fit.split(",")], desc="window", file=sys.stderr):
            run = window_bounds_c(args.depth, h, 16, threads=2)
            slopes, C = window_fit(run.onset, run.bound, W, stretches, gammas, kappas)
            print(f"h = {h}: slope of U_j on " + ", ".join(f"[{lo}, {hi}] {s:.4f}" for (lo, hi), s in zip(stretches, slopes)))
            for gi, gam in enumerate(gammas):
                print(f"    V_j <= {gam} j + C + kappa W_j needs C = " +
                      ", ".join(f"{int(C[gi, ki])} (kappa {k})" for ki, k in enumerate(kappas)))


if __name__ == "__main__":
    main()
