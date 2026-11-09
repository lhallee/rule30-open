"""The light lines of Rule 30's light-like map G(y)_i = y_i xor (y_{i+1} or y_{i+2}) under the uniform measure, and
of its siblings H(y)_i = y_i xor eta(y_{i+1}, y_{i+2}).

A light line is t -> (G^t y)_j, Rule 30 read along a right diagonal. Lines j + 1 and j + 2 drive line j: it changes
at t exactly when eta(c^{j+1}_t, c^{j+2}_t) = 1. eta is a truth table, bit (2u + v) = eta(u, v): 14 is Rule 30 (or),
8 Rule 120 (and), 4 Rule 180 (u and not v), 13 Rule 45 (u or not v); 7, 1, 2, 11 are their complement conjugates.

- `light_step`, `light_lines`: the map on a batch of half-lines, and their first light lines.
- `rho_bruteforce`: rho(k) = E (-1)^{c_0 xor c_k}, the autocorrelation of a light line, over all 2^(2k+1) inputs.
- `letter_law`: the exact law of the letter process (eta(c^j, c^{j+1}), c^j) on times 0..K-1, by the column
  transducer in pure Python (counts out of 4^K); `exact` runs the same iteration in C (light_line.c) to K <= 31.
- `light_words`, `minimal_forbidden`: the words a light line shows, by brute force; 00100 and 11011 never occur.
- `back_solutions`: the four preimages of a finite image, for the 010 synchronization that makes G invertible.
- `constant_probability`: the probability that light line 0 is constant up to time T, by brute force; for Rule 180
  it is 2/3 + 4^-T / 3.
- `monte_carlo`: twisted correlations E chi_S(G^k y) chi_R(y) from random rows, in C.
- `level_transitive`: the action of group 2369 (the frozen-boundary steps) on the cells next to a cut.

    python -m computations.light_line --exact 29                # the exact law to K = 29: rho, entropy; 45 s, < 10 GB
    python -m computations.light_line --siblings 22             # rho(k) to k = 22 for the four sibling classes; 10 s
    python -m computations.light_line --mc 20 1100 240 --masks 1   # rho(k) to k = 1024 from 2^20 lines; 3 min
    python -m computations.light_line --mc 18 600 48 --masks 1,3,5,7,9,11,13,15   # 64 twisted correlations; 70 s
    python -m computations.light_line --forbidden 10 --rule180 12 --transitive 22   # about 50 s together
"""

from __future__ import annotations

import argparse
import itertools
import math
import os
import subprocess
from fractions import Fraction

import numpy as np
from tqdm.auto import tqdm

RULE30, RULE120, RULE180, RULE45 = 14, 8, 4, 13


def eta_of(tt: int, u: np.ndarray, v: np.ndarray) -> np.ndarray:
    """eta(u, v) for the truth table tt, elementwise on 0/1 arrays of any shape."""
    out = np.zeros_like(u)  # same shape as u
    for a, b in itertools.product((0, 1), repeat=2):
        if (tt >> (2 * a + b)) & 1:
            out |= ((u == a) & (v == b)).astype(u.dtype)
    return out


def light_step(rows: np.ndarray, tt: int = RULE30) -> np.ndarray:
    """One step of H on a batch of half-lines: rows (M, n) -> (M, n - 2), the cells whose cone is inside."""
    return rows[:, :-2] ^ eta_of(tt, rows[:, 1:-1], rows[:, 2:])


def light_lines(rows: np.ndarray, T: int, j: int = 0, tt: int = RULE30) -> np.ndarray:
    """The light line j up to time T of every half-line of the batch rows (M, n), n >= j + 2T + 1: (M, T + 1)."""
    out = [rows[:, j]]  # T + 1 arrays (M,)
    for _ in range(T):
        rows = light_step(rows, tt)
        out.append(rows[:, j])
    return np.stack(out, axis=1)


def all_rows(n: int) -> np.ndarray:
    """Every row of n cells: (2^n, n), row r has cell i equal to bit i of r."""
    r = np.arange(1 << n, dtype=np.int64)  # (2^n,)
    return ((r[:, None] >> np.arange(n)[None, :]) & 1).astype(np.uint8)


def rho_bruteforce(k: int, tt: int = RULE30) -> Fraction:
    """rho(k) = E (-1)^{c_0 xor c_k} for light line 0, over all inputs y_0 .. y_2k."""
    c = light_lines(all_rows(2 * k + 1), k, 0, tt)  # (2^(2k+1), k + 1)
    n = c.shape[0]
    return Fraction(n - 2 * int((c[:, 0] ^ c[:, k]).sum()), n)


def _transduce(w: tuple[int, ...], p: int, tt: int) -> tuple[int, ...]:
    """The column transducer: input letters (A, B) of level j + 1 as 2A + B, state p = c^j; output letters of level j."""
    out = []
    for x in w:
        A, B = x >> 1, x & 1
        out.append(2 * ((tt >> (2 * p + B)) & 1) + p)
        p ^= A
    return tuple(out)


def letter_law(K: int, tt: int = RULE30) -> dict[tuple[int, ...], int]:
    """The exact law of the letters (eta(c^j_t, c^{j+1}_t), c^j_t), t < K, as counts out of 4^K: mu_K is the
    transducer applied twice to mu_{K-1} with any letter appended (the appended letter is outside the light cone)."""
    law: dict[tuple[int, ...], int] = {(): 1}
    for k in range(1, K + 1):
        cur = {w + (0,): c for w, c in law.items()}
        for _ in range(2):
            nxt: dict[tuple[int, ...], int] = {}
            for w, c in cur.items():
                for p in (0, 1):
                    o = _transduce(w, p, tt)
                    nxt[o] = nxt.get(o, 0) + c
            cur = nxt
        law = cur
    return law


def law_statistics(law: dict[tuple[int, ...], int], K: int) -> tuple[int, float, int, int, int]:
    """Support size, entropy in bits, and the numerators over 4^K of rho(K), rhoPi(K) and rhoDet(K)."""
    D = 4 ** K
    H = -sum(c / D * math.log2(c / D) for c in law.values())
    r1 = sum(c * (-1) ** sum(x >> 1 for x in w) for w, c in law.items())
    r2 = sum(c * (-1) ** sum(1 ^ (x & 1) for x in w) for w, c in law.items())
    r3 = sum(c * (-1) ** sum(1 ^ ((x >> 1) & (1 ^ (x & 1))) for x in w) for w, c in law.items())
    return len(law), H, r1, r2, r3


def _binary() -> str:
    """computations/light_line.c, compiled once (`seed_onsets.compiled`)."""
    from computations.seed_onsets import compiled
    return str(compiled("light_line", ("-O3", "-fopenmp", "-w")))


def exact(Kmax: int, tt: int = RULE30) -> list[tuple[int, int, float, int, int, int]]:
    """The exact law in C for K = 1 .. Kmax <= 31: (K, support, entropy bits, rho, rhoPi, rhoDet numerators / 4^K)."""
    run = subprocess.run([_binary(), "exact", str(tt), str(Kmax)], stdout=subprocess.PIPE, text=True, check=True)
    out = []
    for line in run.stdout.split("\n"):
        if line:
            K, supp, ok, H, r1, r2, r3 = line.split()
            assert ok == "1", "the counts do not add up to 4^K"
            out.append((int(K), int(supp), float(H), int(r1), int(r2), int(r3)))
    return out


def monte_carlo(wlog: int, T: int, reps: int, lags: list[int], masks: list[int], seed: int = 7,
                threads: int = 3) -> dict[tuple[int, int, int], tuple[float, float]]:
    """E chi_S(G^k y) chi_R(y) for S, R in masks (subsets of {0,1,2,3} as bit masks containing 0), from reps random
    rows of 2^wlog light lines over T steps: {(S, R, k): (mean, standard error over the rows)}."""
    env = {**os.environ, "MASKS": ",".join(map(str, masks)), "OMP_NUM_THREADS": str(threads)}
    run = subprocess.run([_binary(), "mc", str(wlog), str(T), str(reps), str(seed), *map(str, lags)],
                         stdout=subprocess.PIPE, text=True, check=True, env=env)
    out = {}
    for line in run.stdout.split("\n"):
        if line:
            S, R, k, s1, s2 = line.split()
            m = float(s1) / reps
            v = max(float(s2) / reps - m * m, 0.0)
            out[int(S), int(R), int(k)] = (m, math.sqrt(v / (reps - 1)))
    return out


def light_words(k: int, tt: int = RULE30) -> set[int]:
    """The words c_0 .. c_{k-1} (bit t = c_t) that light line 0 shows, over all inputs y_0 .. y_{2k-2}."""
    c = light_lines(all_rows(2 * k - 1), k - 1, 0, tt)  # (2^(2k-1), k)
    codes = (c.astype(np.int64) << np.arange(k)[None, :]).sum(axis=1)  # (2^(2k-1),)
    return set(np.unique(codes).tolist())


def minimal_forbidden(kmax: int, tt: int = RULE30) -> list[str]:
    """The minimal words that no light line shows, up to length kmax, written c_0 c_1 ...."""
    words = {k: light_words(k, tt) for k in tqdm(range(1, kmax + 1), desc="light words", leave=False)}
    out = []
    for k in range(2, kmax + 1):
        for code in range(1 << k):
            if code not in words[k] and (code & ((1 << (k - 1)) - 1)) in words[k - 1] and (code >> 1) in words[k - 1]:
                out.append("".join(str((code >> t) & 1) for t in range(k)))
    return out


def back_solutions(z: list[int]) -> list[list[int]]:
    """The four half-line words y_0 .. y_{n+1} with G(y)_i = z_i for i < n, one for each boundary pair (y_n, y_{n+1})."""
    n = len(z)
    out = []
    for p, q in itertools.product((0, 1), repeat=2):
        y = [0] * n + [p, q]
        for i in range(n - 1, -1, -1):
            y[i] = z[i] ^ (y[i + 1] | y[i + 2])
        out.append(y)
    return out


def constant_probability(T: int, tt: int = RULE180) -> Fraction:
    """The probability that light line 0 is constant on times 0 .. T, over all inputs y_0 .. y_2T."""
    c = light_lines(all_rows(2 * T + 1), T, 0, tt)  # (2^(2T+1), T + 1)
    return Fraction(int((c == c[:, :1]).all(axis=1).sum()), c.shape[0])


def level_transitive(n: int) -> bool:
    """Whether the three frozen-boundary steps x -> x xor (2x or 4x or s), s in {0, 1, 3}, act transitively on Z/2^n."""
    x = np.arange(1 << n, dtype=np.int64)  # (2^n,)
    perms = [(x ^ ((2 * x) | (4 * x) | s)) & ((1 << n) - 1) for s in (0, 1, 3)]  # 3 x (2^n,)
    seen = np.zeros(1 << n, dtype=bool)  # (2^n,)
    seen[0] = True
    frontier = np.array([0])
    while frontier.size:
        nxt = np.unique(np.concatenate([p[frontier] for p in perms]))
        frontier = nxt[~seen[nxt]]
        seen[frontier] = True
    return bool(seen.all())


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--exact", type=int, help="exact law of the letter process to this K (<= 31)")
    ap.add_argument("--eta", type=int, default=RULE30, help="truth table of eta (14 = Rule 30)")
    ap.add_argument("--siblings", type=int, help="rho(k) to this k for Rules 30, 120, 180, 45")
    ap.add_argument("--mc", type=int, nargs=3, metavar=("WLOG", "T", "REPS"), help="Monte Carlo correlations")
    ap.add_argument("--masks", default="1", help="comma separated masks for --mc")
    ap.add_argument("--forbidden", type=int, help="minimal forbidden words of the light line to this length")
    ap.add_argument("--rule180", type=int, help="P(line 0 of Rule 180 constant to T) for T up to this")
    ap.add_argument("--transitive", type=int, help="level transitivity of group 2369 to this level")
    a = ap.parse_args()
    if a.exact:
        prevH = 0.0
        for K, supp, H, r1, r2, r3 in exact(a.exact, a.eta):
            D = 4 ** K
            print(f"K={K:2d} support={supp:>10d} H={H:.9f} H_K-H_(K-1)={H - prevH:.6f} "
                  f"rho={r1}/4^{K}={r1 / D:+.9e} rhoPi={r2 / D:+.6e} rhoDet={r3 / D:+.6e}")
            prevH = H
    if a.siblings:
        for tt, name in ((RULE30, "Rule 30"), (RULE120, "Rule 120"), (RULE180, "Rule 180"), (RULE45, "Rule 45")):
            rows = exact(a.siblings, tt)
            print(name, " ".join(f"{K}:{r1 / 4 ** K:+.4g}" for K, _, _, r1, _, _ in rows))
    if a.mc:
        lags = list(range(1, 41)) + [44, 48, 56, 64, 80, 96, 128, 160, 192, 256, 320, 384, 448, 512, 640, 768, 896, 1024]
        lags = [k for k in lags if k < a.mc[1]]
        res = monte_carlo(*a.mc, lags, [int(m) for m in a.masks.split(",")])
        for (S, R, k), (m, e) in sorted(res.items()):
            print(f"S={S} R={R} k={k} {m:+.4e} +- {e:.1e}")
    if a.forbidden:
        print("minimal forbidden words:", minimal_forbidden(a.forbidden))
    if a.rule180:
        for T in range(1, a.rule180 + 1):
            p = constant_probability(T)
            print(T, p, p == Fraction(2, 3) + Fraction(1, 3 * 4 ** T))
    if a.transitive:
        print("level transitive to", a.transitive, all(level_transitive(n) for n in range(1, a.transitive + 1)))


if __name__ == "__main__":
    main()
