"""Right-edge cycles of the single cell to n = 84, the exact laws of a stall, and the checks behind the routes to
L_n / n unbounded.

In the frame of its right edge the single black cell is the orbit h(t) = Phi^t(1) of Phi(y) = y xor (2y or 4y) (the
kit's `TFunction`); bit j of h(t) is the cell (t, t - j), on the right diagonal R_j, whose least period is
P_j = 2^(e_j). L_n = P_(n-1) is the cycle length of 1 modulo 2^n; J_k = W(2^k), the white run beside the right edge at
time 2^k, is the last diagonal whose period divides 2^k (the kit's `Rule30RightPeriods.per_iff_gap`); the stall at
period 2^(k+1) is the run of diagonals J_k + 1, ..., J_(k+1) of that least period, of length d_k = J_(k+1) - J_k.
K_j is the Mahler degree of R_j on one period, and v_j = P_j - 1 - K_j its difference order (the kit's
`Rule30DifferenceOrder.order`). The input of R_j is g_j = R_(j-1) or R_(j-2): R_j(t + 1) = R_j(t) xor g_j(t).

* `runs`: J_k for k <= K and the rows h(2^k) and h(-2^k), by `right_edge_runs.c`, which iterates Phi modulo 2^128 to
  time 2^K; `runs_python` is the same with Python integers, the independent check for small K, and `orbit` computes
  h(tau) for negative tau by inverting Phi bit by bit. `cycle_exponents` reads the exponents a_n of L_n = 2^(a_n),
  n <= J_K + 1, off the J_k (`two_index.doubling_levels` and `longest_flat_stretch` read the doublings off them), and
  `Runs.agreement` gives v_2(h(2^k) - h(-2^k)).
* `lift`: the diagonals R_0, R_1, ... over one period by level lifting, for Rule 30's gate (or) and, as controls,
  Rule 150's (xor) and Rule 90's (the older input alone).
* `mahler_top`: K(f) by the top-bit decomposition K(f) = H + K(f(. + H) xor f), in about 2P steps.
* `stall_laws`: per diagonal j, the period, the doubling flag, K_j, v_j and the Mahler degree of the input, with the
  checks of item 5(a), Theorem A, Lemma 2 and Theorem B of the entry, the stall anatomy, and the candidate lemmas (the
  or and max inequalities of bit filling, P_j - K_j <= 2 at the second diagonal after a doubling).
* `weight_rules`: the GF(2)-linear rules with at most three terms among 18 parities of weights over one period, and a
  constant, that give the doubling bit at every diagonal of a range.
* `phis`: the isometries phi_k of the renormalization modulo 2^m, by `right_edge_runs.c`; `phi_python` checks them.
* `seeds_swap`, `linear_tops`: the two barriers. Phi swaps the 2-adic integers 1/3 and -1/3, and Rules 150 and 90 have
  linear cycle lengths.

The defaults of the commands, with their running times on one core:

    python -m computations.right_edge_runs runs --k-max 36          # J_k, k <= 36 (n <= 84): about 2 min
    python -m computations.right_edge_runs laws --diagonals 66      # the laws to j = 65 (period 2^27): about 5 s, 1.5 GB
    python -m computations.right_edge_runs weights --diagonals 66   # the rule search on 3 <= j <= 64: about 5 s, 2 GB
    python -m computations.right_edge_runs phi --k-max 18           # phi_k modulo 16: under a second
    python -m computations.right_edge_runs barriers                 # the seeds 1/3, -1/3, Rules 150 and 90: a second
"""

from __future__ import annotations

import argparse
import functools
import itertools
import subprocess
import time
from collections.abc import Iterator
from dataclasses import dataclass, field
from pathlib import Path

import numpy as np
from tqdm.auto import tqdm

from computations.seed_onsets import compiled
from computations.two_index import doubling_levels

MASK128 = (1 << 128) - 1


# ---------------------------------------------------------------------------------------------------------------------
# The rows of the right edge


def phi(y: int, mask: int = MASK128) -> int:
    """One step of the right edge, Phi(y) = y xor (2y or 4y), modulo mask + 1."""
    return (y ^ ((y << 1) | (y << 2))) & mask


def phi_inverse(z: int, bits: int) -> int:
    """Phi^(-1)(z) modulo 2^bits, bit by bit from the right edge: y_j = z_j xor (y_(j-1) or y_(j-2))."""
    y, last, before = 0, 0, 0
    for j in range(bits):
        bit = ((z >> j) & 1) ^ (last | before)
        y |= bit << j
        last, before = bit, last
    return y


def orbit(tau: int, bits: int) -> int:
    """h(tau) = Phi^tau(1) modulo 2^bits for any integer tau, backward by `phi_inverse` (for small |tau|)."""
    mask = (1 << bits) - 1
    y = 1 & mask
    for _ in range(abs(tau)):
        y = phi(y, mask) if tau > 0 else phi_inverse(y, bits)
    return y


def v2(x: int, cap: int = 1 << 30) -> int:
    """The 2-adic valuation of x, or `cap` for x = 0."""
    return (x & -x).bit_length() - 1 if x else cap


@dataclass(frozen=True, slots=True)
class Runs:
    """The rows of the right edge at the powers of two, from one run of Phi to time 2^K."""

    white: list[int]  # J_k = W(2^k), k = 0 .. K
    rows: list[int]  # h(2^k) modulo 2^128, k = 0 .. K
    back: list[int]  # h(2^K - 2^k) modulo 2^128, k = 0 .. K - 1: this is h(-2^k) modulo 2^(J_K + 1)

    @property
    def stalls(self) -> list[int]:
        """d_k = J_(k+1) - J_k, k = 0 .. K - 1: the number of diagonals of least period 2^(k+1)."""
        return [b - a for a, b in zip(self.white, self.white[1:])]

    def agreement(self) -> list[int]:
        """v_2(h(2^k) - h(-2^k)) for k = 0 .. K - 2, read modulo 2^(J_K + 1) (Theorem C(ii): J_(k+1) + 1)."""
        bits = self.white[-1] + 1
        mask = (1 << bits) - 1
        return [v2((self.rows[k] - self.back[k]) & mask, bits) for k in range(len(self.back) - 1)]


def _binary(optimize: bool = True) -> Path:
    """right_edge_runs.c, beside this module, compiled by `seed_onsets.compiled` (kept per source and flags)."""
    return compiled("right_edge_runs", ("-O2" if optimize else "-O0", "-w"))


def runs(k_max: int, progress: bool = False, optimize: bool = True) -> Runs:
    """J_k, h(2^k) and h(2^K - 2^k) for k <= K = k_max by `right_edge_runs.c` (progress on stderr)."""
    out = subprocess.run([str(_binary(optimize)), "runs", str(k_max)], stdout=subprocess.PIPE,
                         stderr=None if progress else subprocess.DEVNULL, text=True, check=True).stdout
    white, rows, back = [0] * (k_max + 1), [0] * (k_max + 1), [0] * k_max
    for line in out.splitlines():
        kind, k, *rest = line.split()
        if kind == "row":
            white[int(k)], rows[int(k)] = int(rest[0]), int(rest[1], 16)
        else:
            back[int(k)] = int(rest[0], 16)
    return Runs(white, rows, back)


def runs_python(k_max: int) -> Runs:
    """The same rows by Python integers modulo 2^128, one step at a time: the independent check for small k_max."""
    times = sorted({1 << k for k in range(k_max + 1)} | {(1 << k_max) - (1 << k) for k in range(k_max)})
    seen: dict[int, int] = {}
    y, t = 1, 0
    for target in times:
        while t < target:
            y = phi(y)
            t += 1
        seen[target] = y
    rows = [seen[1 << k] for k in range(k_max + 1)]
    return Runs([v2(r - 1, 128) - 1 for r in rows], rows, [seen[(1 << k_max) - (1 << k)] for k in range(k_max)])


def cycle_exponents(white: list[int]) -> list[int]:
    """The exponents a_n of L_n = 2^(a_n), n = 1 .. J_K + 1, from J_0 .. J_K: L_n <= 2^k iff J_k >= n - 1."""
    return [next(k for k, w in enumerate(white) if w >= n - 1) for n in range(1, white[-1] + 2)]


def longest_flat_stretch(lengths: list[int]) -> tuple[int, int]:
    """The longest run of consecutive levels n >= 2 at which L_n = L_(n-1), as (length, first level), from
    lengths[i] = L_(i+1) (`two_index.longest_flat_run` gives the length alone)."""
    best, start, run = 0, 0, 0
    for n in range(2, len(lengths) + 1):
        run = run + 1 if lengths[n - 1] == lengths[n - 2] else 0
        if run > best:
            best, start = run, n - run + 1
    return best, start


# ---------------------------------------------------------------------------------------------------------------------
# The isometries of the renormalization


def phis(k_max: int, bits: int = 4, optimize: bool = True) -> list[tuple[int, list[int]]]:
    """(nu_k, [phi_k(y) mod 2^bits for y < 2^bits]) for k = 0 .. k_max, by `right_edge_runs.c`, where
    nu_k = J_k + 1 and phi_k(y) = (Phi^(2^k)(1 + 2^nu_k y) - 1) / 2^nu_k."""
    out = subprocess.run([str(_binary(optimize)), "phi", str(k_max), str(bits)], stdout=subprocess.PIPE,
                         stderr=subprocess.DEVNULL, text=True, check=True).stdout
    table: list[tuple[int, list[int]]] = []
    for line in out.splitlines():
        _, _, nu, *values = line.split()
        table.append((int(nu), [int(v) for v in values]))
    return table


def phi_python(k: int, bits: int) -> tuple[int, list[int]]:
    """nu_k and phi_k modulo 2^bits by Python integers: the independent check for small k."""
    y = 1
    for _ in range(1 << k):
        y = phi(y)
    nu = v2(y - 1, 128)
    mask = (1 << (nu + bits)) - 1
    out: list[int] = []
    for x in range(1 << bits):
        z = 1 + (x << nu)
        for _ in range(1 << k):
            z = phi(z, mask)
        out.append(((z - 1) >> nu) & ((1 << bits) - 1))
    return nu, out


def is_affine(values: list[int], bits: int) -> bool:
    """Whether y -> values[y] is y -> a y + b modulo 2^bits for some a and b."""
    m = 1 << bits
    b = values[0]
    a = (values[1] - b) % m
    return all(values[y] == (a * y + b) % m for y in range(m))


# ---------------------------------------------------------------------------------------------------------------------
# Level lifting


def tile(f: np.ndarray, size: int) -> np.ndarray:
    """f, whose length divides size, repeated to length size."""
    # f: (p,)
    return f if f.size == size else np.tile(f, size // f.size)  # (size,)


def lift(diagonals: int, max_log: int = 40, gate: str = "or",
         progress: bool = False) -> Iterator[tuple[int, np.ndarray, bool]]:
    """(j, R_j over one period, whether the period doubled) for j = 0 .. diagonals - 1, stopping before a period would
    pass 2^max_log.

    R_j(t + 1) = R_j(t) xor g(R_(j-1)(t), R_(j-2)(t)) with R_j(0) = [j = 0] and R_(-1) = R_(-2) white; g is or for
    Rule 30, xor for Rule 150 and the older input alone for Rule 90. The input is summed over the longer period P of
    the two before: R_j has period P if the input has an even number of black cells in P, and least period 2P if odd.
    For Rule 30 the array is the least period (the kit's `Rule30RightPeriods.inp_least_period` and `S_rule`); for the
    linear rules it may be a multiple of it (`least_period`)."""
    prev2 = np.zeros(1, dtype=np.uint8)  # (1,), R_(-1)
    prev1 = np.ones(1, dtype=np.uint8)  # (1,), R_0
    yield 0, prev1, False
    for j in tqdm(range(1, diagonals), desc="diagonals", disable=not progress, leave=False):
        size = max(prev1.size, prev2.size)
        a, b = tile(prev1, size), tile(prev2, size)  # (P,), (P,)
        if gate == "or":
            inp = a | b  # (P,)
        elif gate == "xor":
            inp = a ^ b  # (P,)
        elif gate == "older":
            inp = b.copy()  # (P,)
        else:
            raise ValueError(gate)
        doubled = bool(np.count_nonzero(inp) & 1)
        if doubled:
            if 2 * size > 1 << max_log:
                return
            inp = np.concatenate((inp, inp))  # (2P,)
        diag = np.empty_like(inp)  # (P',)
        diag[0] = 0
        np.bitwise_xor.accumulate(inp[:-1], out=diag[1:])
        yield j, diag, doubled
        prev2, prev1 = prev1, diag


def least_period(f: np.ndarray) -> int:
    """The least period of f, whose length is a power of two and a period, by halving while the halves agree."""
    # f: (P,)
    size = f.size
    while size > 1 and np.array_equal(f[: size // 2], f[size // 2: size]):
        size //= 2
    return size


def mahler_top(f: np.ndarray) -> int:
    """K(f), the largest k with a nonzero Mahler coefficient of f on Z/P, P = len(f) a power of two (-1 for f = 0).

    With H = P/2 and Df = f(. + H) xor f: K(f) = H + K(Df) if Df is not 0, and K(f) = K(f on [0, H)) if it is (the
    top-bit decomposition, Lemma 1 of the entry); about 2P operations."""
    # f: (P,) uint8
    if not f.any():
        return -1
    top = 0
    while f.size > 1:
        half = f.size // 2
        d = f[:half] ^ f[half:]  # (half,)
        if d.any():
            top += half
            f = d
        else:
            f = f[:half]  # (half,)
    return top


def antiderivative(g: np.ndarray) -> np.ndarray:
    """S g(t) = g(0) xor ... xor g(t - 1) for t < len(g), with S g(0) = 0."""
    # g: (H,)
    out = np.zeros_like(g)  # (H,)
    if g.size > 1:
        np.bitwise_xor.accumulate(g[:-1], out=out[1:])
    return out


# ---------------------------------------------------------------------------------------------------------------------
# The laws of a stall and the candidate lemmas


@dataclass(frozen=True, slots=True)
class Diagonal:
    """One right diagonal R_j over its least period."""

    j: int
    period: int  # P_j
    doubled: bool  # P_j = 2 P_(j-1)
    top: int  # K_j, the Mahler degree of R_j on one period
    input_top: int  # K(g_j), the Mahler degree of g_j = R_(j-1) or R_(j-2) on its period P_(j-1); -1 for j = 0
    odd: bool  # R_j has an odd number of black cells in one period

    @property
    def order(self) -> int:
        """v_j = P_j - 1 - K_j, the kit's `Rule30DifferenceOrder.order` of R_j at its period."""
        return self.period - 1 - self.top


@dataclass(slots=True)
class Check:
    """The number of diagonals where a law or a candidate was tested, and the diagonals where it fails."""

    count: int = 0
    failures: list[int] = field(default_factory=list)

    def record(self, j: int, holds: bool) -> None:
        self.count += 1
        if not holds:
            self.failures.append(j)


@dataclass(frozen=True, slots=True)
class Stall:
    """The stall opened by the doubling diagonal m = J_k + 1, k >= 1, with its two parities and its length."""

    k: int
    opening: int  # m = J_k + 1
    weight_odd: bool  # R_(J_k) has an odd number of black cells in 2^k (Theorem A(i): d_k = 1)
    rung: tuple[bool, bool] | None  # the parities of the two sums of Theorem B(i); None if m + 1 doubles or is beyond
    length: int | None  # d_k, None when the lifted diagonals end inside the stall

    @property
    def rung_odd(self) -> bool | None:
        """The parity of Theorem B(i), whose oddness makes d_k = 2 when the weight is even."""
        return None if self.rung is None else self.rung[0] != self.rung[1]

    @property
    def predicted(self) -> str:
        """'1', '2' or '>= 3' from the two parities (the stall anatomy), '?' when the rung is not computed."""
        if self.weight_odd:
            return "1"
        if self.rung_odd is None:
            return "?"
        return "2" if self.rung_odd else ">= 3"


LAW_NAMES = ("item 5(a)", "theorem A(i)", "theorem A(ii)", "lemma 2(a)", "lemma 2(b)", "lemma 2(c)", "theorem B(i)",
             "theorem B(ii)")
CANDIDATE_NAMES = ("or inequality", "or inequality below P - 1", "max inequality", "second diagonal P - K <= 2")


@dataclass(frozen=True, slots=True)
class Laws:
    """What `stall_laws` finds on the diagonals it reaches."""

    diagonals: list[Diagonal]
    checks: dict[str, Check]
    or_failures: list[tuple[int, bool]]  # (j, whether K_(j-1) or K_(j-2) = P_(j-1) - 1) where K(g_j) is below the or
    or_equal: list[tuple[int, bool]]  # (j, whether j - 1 doubles) at the non-doubling j with K(g_j) equal to the or
    second_diagonal: list[tuple[int, int]]  # (j, P_j - K_j) at the second diagonal after a doubling, neither doubling
    stalls: list[Stall]


def stall_laws(diagonals: int, max_log: int = 27, progress: bool = False) -> Laws:
    """Lift R_0 .. R_(diagonals - 1) (periods up to 2^max_log) and check, diagonal by diagonal:

    * item 5(a): K_j = P_j / 2 at every doubling diagonal j >= 1, K_j > P_j / 2 at every other diagonal j >= 3;
    * Theorem A at j = n + 1 after a doubling diagonal n >= 2: (i) j doubles iff R_(n-1) has odd weight over its
      period
      iff v_(n-1) = 0; (ii) otherwise D_j = R_j(H) xor S(not R_(n-1)) and K_j = H + K_(n-1) + 1, H = P_(n-1);
    * Lemma 2 at every diagonal i whose stall (the run of diagonals of period P = 2H ending at i - 1) was opened by a
      doubling diagonal m >= 3: (a) Gamma_i = g_i(. + H) xor g_i is D_(i-1)(1 xor R_(i-2)) xor D_(i-2)(1 xor R_(i-1))
      xor D_(i-1) D_(i-2) with D_l = R_l(. + H) xor R_l; (b) i doubles iff Gamma_i has odd weight over H; (c) if i
      does not double, D_i = R_i(H) xor S Gamma_i, Gamma_i is not 0 and K_i = H + 1 + K(Gamma_i);
    * Theorem B at j = n + 2 after a doubling diagonal n >= 2 and a diagonal n + 1 that does not double: (i) j doubles
      iff
      |R_(n+1) on [0, H)| + |R_n D_(n+1) on [0, H)| is odd, H = P_n / 2; (ii) if not and n >= 3,
      K_j = H + 1 + K(not R_(n+1) xor R_n D_(n+1));

    and the candidates K(g_j) >= K_(j-1) or K_(j-2) (bitwise; also restricted to an or below P_(j-1) - 1),
    K(g_j) >= max(K_(j-1), K_(j-2)), and P_j - K_j <= 2 at the second diagonal after a doubling."""
    checks = {name: Check() for name in (*LAW_NAMES, *CANDIDATE_NAMES)}
    lv: list[Diagonal] = []
    or_failures: list[tuple[int, bool]] = []
    or_equal: list[tuple[int, bool]] = []
    second_diagonal: list[tuple[int, int]] = []
    rungs: dict[int, tuple[bool, bool]] = {}  # diagonal n + 2 -> the parities of the two sums of Theorem B(i)
    r2 = np.zeros(1, dtype=np.uint8)  # (1,), R_(j-2)
    r1 = np.zeros(1, dtype=np.uint8)  # (1,), R_(j-1)
    opening = 0  # the last doubling diagonal before j
    for j, r0, doubled in lift(diagonals, max_log, progress=progress):
        size = r0.size
        top = mahler_top(r0)
        q = r1.size
        g = r1 | tile(r2, q) if j >= 1 else np.zeros(0, dtype=np.uint8)  # (q,), the input g_j
        lv.append(Diagonal(j, size, doubled, top, mahler_top(g) if j >= 1 else -1, bool(np.count_nonzero(r0) & 1)))
        # item 5(a)
        if j >= 1 and doubled:
            checks["item 5(a)"].record(j, top == size // 2)
        elif j >= 3:
            checks["item 5(a)"].record(j, top > size // 2)
        # Theorem A at j = n + 1
        n = j - 1
        if n >= 2 and lv[n].doubled:
            s, half = r2, r2.size  # R_(n-1), H = P_(n-1)
            checks["theorem A(i)"].record(j, doubled == lv[n - 1].odd and lv[n - 1].odd == (lv[n - 1].order == 0))
            if not doubled:
                damage = r0[half:] ^ r0[:half]  # (H,)
                expected = r0[half] ^ antiderivative(1 ^ s)  # (H,)
                checks["theorem A(ii)"].record(j, bool(np.array_equal(damage, expected))
                                               and top == half + lv[n - 1].top + 1)
        # Theorem B at j = n + 2
        n = j - 2
        if n >= 2 and lv[n].doubled and not lv[n + 1].doubled:
            half = r1.size // 2
            damage1 = r1[half:] ^ r1[:half]  # (H,), D_(n+1)
            terms = (bool(np.count_nonzero(r1[:half]) & 1), bool(np.count_nonzero(r2[:half] & damage1) & 1))
            rungs[j] = terms
            rung = terms[0] != terms[1]
            gamma = (1 ^ r1[:half]) ^ (r2[:half] & damage1)  # (H,)
            same = bool(np.array_equal(gamma, g[half:] ^ g[:half]))
            checks["theorem B(i)"].record(j, doubled == rung and same)
            if not doubled and n >= 3:
                checks["theorem B(ii)"].record(j, top == half + 1 + mahler_top(gamma))
        # Lemma 2 at i = j, in a stall opened by a doubling diagonal m >= 3
        if j >= 1 and opening >= 3:
            half = q // 2
            r2t = tile(r2, q)  # (q,)
            d1 = r1[half:] ^ r1[:half]  # (H,), D_(i-1)
            d2 = r2t[half:] ^ r2t[:half]  # (H,), D_(i-2)
            gamma = g[half:] ^ g[:half]  # (H,)
            formula = (d1 & (1 ^ r2t[:half])) ^ (d2 & (1 ^ r1[:half])) ^ (d1 & d2)  # (H,)
            checks["lemma 2(a)"].record(j, bool(np.array_equal(gamma, formula)))
            checks["lemma 2(b)"].record(j, doubled == bool(np.count_nonzero(gamma) & 1))
            if not doubled:
                damage = r0[half:] ^ r0[:half]  # (H,)
                checks["lemma 2(c)"].record(j, bool(gamma.any())
                                            and bool(np.array_equal(damage, r0[half] ^ antiderivative(gamma)))
                                            and top == half + 1 + mahler_top(gamma))
        # the candidates
        if j >= 2:
            kg, k1, k2 = lv[j].input_top, lv[j - 1].top, lv[j - 2].top
            either = k1 | k2
            checks["or inequality"].record(j, kg >= either)
            if either < q - 1:
                checks["or inequality below P - 1"].record(j, kg >= either)
            checks["max inequality"].record(j, kg >= max(k1, k2))
            if kg < either:
                or_failures.append((j, either == q - 1))
            if not doubled and kg == either:
                or_equal.append((j, lv[j - 1].doubled))
        if j >= 3 and lv[j - 2].doubled and not lv[j - 1].doubled and not doubled:
            second_diagonal.append((j, size - top))
            checks["second diagonal P - K <= 2"].record(j, size - top <= 2)
        if doubled:
            opening = j
        r2, r1 = r1, r0
    return Laws(lv, checks, or_failures, or_equal, second_diagonal, _stalls(lv, rungs))


def _stalls(lv: list[Diagonal], rungs: dict[int, tuple[bool, bool]]) -> list[Stall]:
    """The stalls opened by the doubling diagonals m >= 2 with diagonal m + 1 lifted."""
    doublings = [x.j for x in lv if x.doubled]
    out: list[Stall] = []
    for i, m in enumerate(doublings):
        if m < 2 or m + 1 >= len(lv):
            continue
        k = lv[m].period.bit_length() - 2  # P_m = 2^(k+1)
        rung = rungs.get(m + 2) if not lv[m + 1].doubled else None
        length = doublings[i + 1] - m if i + 1 < len(doublings) else None
        out.append(Stall(k, m, lv[m - 1].odd, rung, length))
    return out


# ---------------------------------------------------------------------------------------------------------------------
# Weights over one period


WEIGHT_NAMES = ("|R_j|", "|R_j-1|", "|R_j R_j-1|", "|R_j R_j-2|", "|R_j-1 R_j-2|", "|R_j R_j-1 R_j-2|", "|R_j, t odd|",
                "|R_j-1, t odd|", "|R_j R_j-1, t odd|")


def weight_features(r0: np.ndarray, r1: np.ndarray, r2: np.ndarray) -> list[int]:
    """The nine weights of `WEIGHT_NAMES` over one period P_j: R_j (r0) with R_(j-1) (r1) and R_(j-2) (r2) repeated
    to P_j, products cell by cell, and the last three counted at odd times t only."""
    # r0: (P,), r1: (P1,), r2: (P2,)
    size = r0.size
    a = r0.astype(bool)  # (P,)
    b = tile(r1, size).astype(bool)  # (P,)
    c = tile(r2, size).astype(bool)  # (P,)
    odd = np.zeros(size, dtype=bool)  # (P,)
    odd[1::2] = True
    ab = a & b  # (P,)
    return [int(np.count_nonzero(x)) for x in (a, b, ab, a & c, b & c, ab & c, a & odd, b & odd, ab & odd)]


def weight_rules(diagonals: int = 66, max_log: int = 27, terms: int = 3,
                 progress: bool = False) -> tuple[list[int], list[tuple[str, ...]]]:
    """The diagonals j tested and every GF(2)-linear rule with at most `terms` terms among the 18 parities (each
    weight of `weight_features` modulo 2 and its second binary digit) and the constant 1 that gives the doubling bit
    of diagonal j + 1 at every diagonal 3 <= j < the last diagonal lifted."""
    names = [f"{x} mod 2" for x in WEIGHT_NAMES] + [f"digit 2 of {x}" for x in WEIGHT_NAMES] + ["1"]
    feats: list[list[int]] = []
    target: list[int] = []
    tested: list[int] = []
    pending: list[int] | None = None
    r2 = r1 = np.zeros(1, dtype=np.uint8)  # (1,), (1,)
    for j, r0, doubled in lift(diagonals, max_log, progress=progress):
        if pending is not None:
            feats.append(pending)
            target.append(int(doubled))
            tested.append(j - 1)
            pending = None
        if j >= 3:
            w = weight_features(r0, r1, r2)
            pending = [x & 1 for x in w] + [(x >> 1) & 1 for x in w] + [1]
        r2, r1 = r1, r0
    x = np.array(feats, dtype=np.uint8)  # (diagonals tested, 19)
    y = np.array(target, dtype=np.uint8)  # (diagonals tested,)
    rules: list[tuple[str, ...]] = []
    for size in range(1, terms + 1):
        for idx in itertools.combinations(range(x.shape[1]), size):
            if np.array_equal(np.bitwise_xor.reduce(x[:, list(idx)], axis=1), y):
                rules.append(tuple(names[i] for i in idx))
    return tested, rules


# ---------------------------------------------------------------------------------------------------------------------
# The two barriers


def seeds_swap(bits: int = 128) -> bool:
    """Whether Phi maps 1/3 to -1/3 and -1/3 to 1/3 modulo 2^bits (the kit's `Rule30EdgeStaircases.period_two_iff`)."""
    mask = (1 << bits) - 1
    third = pow(3, -1, 1 << bits)
    minus = (-third) & mask
    return phi(third, mask) == minus and phi(minus, mask) == third and third != minus


def seed_cycle_lengths(seed: int, n_max: int) -> list[int]:
    """The cycle length of a seed under Phi modulo 2^n, n = 1 .. n_max, by iterating until it returns."""
    out: list[int] = []
    for n in range(1, n_max + 1):
        mask = (1 << n) - 1
        y, t = phi(seed & mask, mask), 1
        while y != seed & mask:
            y, t = phi(y, mask), t + 1
        out.append(t)
    return out


def linear_tops(diagonals: int, gate: str) -> tuple[list[int], list[int]]:
    """The least periods and Mahler degrees of R_0 .. R_(diagonals - 1) for the gate `xor` (Rule 150) or `older`
    (Rule 90), from the single cell in the frame of the right edge."""
    periods: list[int] = []
    tops: list[int] = []
    for _, r, _ in lift(diagonals, 40, gate):
        p = least_period(r)
        periods.append(p)
        tops.append(mahler_top(r[:p]))
    return periods, tops


def white_runs_of(periods: list[int], k_max: int) -> list[int]:
    """J_k for k <= k_max: the last j with every period P_0 .. P_j dividing 2^k (the periods are powers of two)."""
    out: list[int] = []
    for k in range(k_max + 1):
        j = 0
        while j + 1 < len(periods) and max(periods[: j + 2]) <= 1 << k:
            j += 1
        out.append(j)
    return out


# ---------------------------------------------------------------------------------------------------------------------


def report_runs(k_max: int) -> None:
    """The cycle lengths, white runs, stalls and agreement identity from one run to time 2^k_max."""
    start = time.time()
    r = runs(k_max, progress=True)
    print(f"run to time 2^{k_max}: {time.time() - start:.0f} s")
    exps = cycle_exponents(r.white)
    lengths = [1 << a for a in exps]  # L_1 .. L_(J_K + 1)
    top = len(exps)
    print(f"J_k = W(2^k), k = 0 .. {k_max}: {r.white}")
    print(f"d_k = J_(k+1) - J_k, k = 0 .. {k_max - 1}: {r.stalls}")
    print(f"doubling levels n <= {top}: {doubling_levels(lengths)} ({len(doubling_levels(lengths))} of them)")
    print(f"L_{top} = 2^{exps[-1]}, a_n / n = {exps[-1] / top:.4f}; longest run without a doubling "
          f"(length, first level): {longest_flat_stretch(lengths)}")
    picks = [n for n in (10, 20, 30, 40, 50, 61, 70, 84) if n <= top]
    print("L_n / n:", {n: round((1 << exps[n - 1]) / n, 1) for n in picks})
    print(f"W(2^m) / 2^m at m = {k_max}: {r.white[-1] / (1 << k_max):.3e}; mean growth W(2^m) / m: "
          f"{r.white[-1] / k_max:.3f}")
    agree = r.agreement()
    ok = all(agree[k] == r.white[k + 1] + 1 for k in range(len(agree)))
    print(f"v_2(h(2^k) - h(-2^k)) = J_(k+1) + 1 for k = 0 .. {len(agree) - 1}: {ok}")
    ratios = [(r.white[k + 1] / r.white[k], k) for k in range(1, k_max)]
    print(f"max J_(k+1) / J_k over 1 <= k <= {k_max - 1}: {max(ratios)}; max d_k / J_k over k >= 18: "
          f"{max((r.stalls[k] / r.white[k], k) for k in range(18, k_max)) if k_max > 18 else None}")
    classes: dict[int, list[int]] = {1: [], 2: [], 3: []}
    for k, d in enumerate(r.stalls):
        if k >= 1:
            classes[min(d, 3)].append(k)
    print(f"stalls 1 <= k <= {k_max - 1}: d_k = 1 at {classes[1]}, d_k = 2 at {classes[2]}, d_k >= 3 at {classes[3]} "
          f"(lengths {[r.stalls[k] for k in classes[3]]}); d_0 = {r.stalls[0]}")


def report_laws(diagonals: int, max_log: int) -> None:
    """The laws, the candidates, the orders and the stall anatomy, diagonal by diagonal."""
    start = time.time()
    laws = stall_laws(diagonals, max_log, progress=True)
    last = laws.diagonals[-1]
    print(f"diagonals 0 .. {last.j}, last period 2^{last.period.bit_length() - 1} ({time.time() - start:.0f} s)")
    periods = [x.period for x in laws.diagonals]
    print(f"J_k from the lifted periods, k <= {last.period.bit_length() - 2}: "
          f"{white_runs_of(periods, last.period.bit_length() - 2)}")
    for name, check in laws.checks.items():
        print(f"{name}: tested at {check.count} diagonals, fails at {check.failures}")
    print(f"K(g_j) below K_(j-1) or K_(j-2) at (j, or = P - 1): {laws.or_failures}")
    print(f"non-doubling diagonals with K(g_j) = the or, (j, j - 1 doubles): {laws.or_equal}")
    print(f"second diagonal after a doubling, (j, P_j - K_j): {laws.second_diagonal}")
    print("orders v_j of the non-doubling diagonals, (j, e_j, v_j):",
          [(x.j, x.period.bit_length() - 1, x.order) for x in laws.diagonals if not x.doubled])
    print("double doublings (j - 1, j):", [(x.j - 1, x.j) for x in laws.diagonals[1:]
                                         if x.doubled and laws.diagonals[x.j - 1].doubled])
    rungs = [s.rung for s in laws.stalls if s.rung is not None]
    print(f"the two sums of Theorem B(i) modulo 2 at its {len(rungs)} cases take the values {sorted(set(rungs))}")
    for s in laws.stalls:
        print(f"stall k = {s.k}: opens at {s.opening}, weight odd {s.weight_odd}, rung sums odd {s.rung}, "
              f"predicted d_k {s.predicted}, d_k = {s.length}")


def report_weights(diagonals: int, max_log: int) -> None:
    """The linear-rule search."""
    start = time.time()
    tested, rules = weight_rules(diagonals, max_log, progress=True)
    print(f"diagonals {tested[0]} .. {tested[-1]} ({len(tested)} of them, {time.time() - start:.0f} s); rules with at most "
          f"three terms: {rules}")


def report_phi(k_max: int, bits: int) -> None:
    """The isometries phi_k modulo 2^bits."""
    table = phis(k_max, bits)
    for k, (nu, values) in enumerate(table):
        print(f"k = {k}: nu = {nu}, phi_k mod 2^{bits} = {values}")
    distinct = len({tuple(v) for _, v in table})
    affine = [k for k, (_, v) in enumerate(table) if is_affine(v, bits)]
    print(f"{distinct} distinct maps for k = 0 .. {len(table) - 1}; affine modulo 2^{bits} at k = {affine}")
    stalls = [v2(v[v[0]], bits) for _, v in table]
    print(f"v_2(phi_k^2(0)) modulo 2^{bits} (d_k when below {bits}): {stalls}")


def report_barriers() -> None:
    """The seeds 1/3 and -1/3, and Rules 150 and 90."""
    third = pow(3, -1, 1 << 12)
    print(f"Phi swaps 1/3 and -1/3 modulo 2^128: {seeds_swap(128)}; their cycle lengths modulo 2^n, n <= 12: "
          f"{seed_cycle_lengths(third, 12)}, {seed_cycle_lengths(-third % (1 << 12), 12)}")
    periods, tops = linear_tops(64, "xor")
    ok = all(tops[j] == j and periods[j] == 1 << (j.bit_length()) for j in range(64))
    print(f"Rule 150, j < 64: K_j = j and P_j = 2^ceil(log2(j + 1)): {ok}; J_k, k <= 5: {white_runs_of(periods, 5)}")
    periods, tops = linear_tops(64, "older")
    ok = all(tops[2 * m] == m and tops[2 * m + 1] == -1 for m in range(32))
    print(f"Rule 90, j < 64: K_(2m) = m and R_(2m+1) white: {ok}; J_k, k <= 5: {white_runs_of(periods, 5)}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("runs", help="J_k by direct iteration modulo 2^128 to time 2^k_max")
    p.add_argument("--k-max", type=int, default=36)
    p = sub.add_parser("laws", help="the laws of a stall and the candidate lemmas by level lifting")
    p.add_argument("--diagonals", type=int, default=66)
    p.add_argument("--max-log", type=int, default=27)
    p = sub.add_parser("weights", help="the GF(2)-linear rules among weight parities")
    p.add_argument("--diagonals", type=int, default=66)
    p.add_argument("--max-log", type=int, default=27)
    p = sub.add_parser("phi", help="the isometries phi_k modulo 2^bits")
    p.add_argument("--k-max", type=int, default=18)
    p.add_argument("--bits", type=int, default=4)
    sub.add_parser("barriers", help="the seeds 1/3, -1/3 and Rules 150 and 90")
    args = parser.parse_args()
    if args.command == "runs":
        report_runs(args.k_max)
    elif args.command == "laws":
        report_laws(args.diagonals, args.max_log)
    elif args.command == "weights":
        report_weights(args.diagonals, args.max_log)
    elif args.command == "phi":
        report_phi(args.k_max, args.bits)
    else:
        report_barriers()


if __name__ == "__main__":
    main()
