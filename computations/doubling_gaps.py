"""The gap after a period doubling: how many depths separate a doubling white diagonal from the next white diagonal,
over every word the doubling can start from.

At a white diagonal w of the single cell (D_w eventually white) the period doubles exactly when D_{w-1} has odd weight
per period (`Rule30Open.Diagonals.LeftMemory`); then Y = D_{w+1} is anti-periodic, Y(t + p) = not Y(t), of period
P = 2p. On aligned words of period P the regime that follows is the orbit of the pair map F(A, B) = (B, C) of
`settled_words` from (0, Y) to the first pair (X, 0) whose second word is white; its gap is the number of depths from w
to that next white diagonal. m(p) is the least gap over every anti-periodic Y of least period 2p.

- `anti_classes`: one word per rotation class of the anti-periodic words of least period 2p (the gap is invariant
  under rotation, since F commutes with it).
- `census`: the gap of every class, by `settled_words.pair_next` in numpy for p <= 6 and by `doubling_gaps.c` (a
  segmented prefix XOR in log2 P rounds of rotations) for p >= 7, both in lockstep up to a cap; m(p) and the minimizing
  classes.
- `orbit_gap`: one regime of period P <= 128 in C, for the structured families of `families` (blocks, alternating
  blocks, a lifted minimizer, Thue-Morse, random words) up to p = 40.
- `single_cell`: the white diagonals of the single cell to depth 87,870 from `left_diagonals.diagonals`, and for each
  the gap of the model from the cell's own word D_{w+1}, against the next white diagonal of the run.
- `half_damage`: along a regime of period 2p, the half-period damage h_j = D_j xor rot_p(D_j) (its weight, parity and
  number of runs); h_j = 0 means D_j has period p.
- `next_sources` and `predict`: the words that can follow a white diagonal, and the single cell's next white diagonals
  past depth 87,866 by the model, from its own D_87867.
- `backward_words`, `permutive_check`, `odd_gap_radius`: the backward words from a sink (X, 0) as local functions of X;
  at an odd gap g the source condition is a right-permutive rule of radius (g - 3)/2, which bounds the least period.
- `source_graph`: for a gap g, the shift of finite type of the sink words of the regimes with gap g, and its two-track
  graph for anti-periodic sources; where that graph is a union of cycles, their lengths are the only possible periods.
- `scalar_regime`: an independent check, the diagonal recursion run cell by cell on periodic inputs from a white start,
  without the periodic solver.

    python -m computations.doubling_gaps --census 1-16 --cap 10000000   # m(p) to p = 16, about 6 min, 1 thread
    python -m computations.doubling_gaps --families 40 --cap 10000000   # the family gaps to p = 40, about 3 min
    python -m computations.doubling_gaps --single-cell --cap 100000     # the single cell's regimes, about 10 s
    python -m computations.doubling_gaps --predict --cap 274877906944   # past depth 87,866, about 1 min
    python -m computations.doubling_gaps --sources 5-49                 # source graphs to g = 49, 3 min, 3.6 GB
    python -m computations.doubling_gaps --damage 5-12 --cap 60000      # the half damage on the minimizing orbits
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

import numpy as np
from tqdm.auto import tqdm

from computations.settled_words import pair_next

U64 = np.uint64


# ---------------------------------------------------------------------------------------------------------------------
# Words as Python integers: bit t is the cell at time t mod P


def rot(y: int, k: int, P: int) -> int:
    """The word read from time k on: bit t of the result is bit (t + k) mod P of y."""
    k %= P
    m = (1 << P) - 1
    return ((y >> k) | (y << (P - k))) & m if k else y


def least_period(y: int, P: int) -> int:
    """The least q dividing P with y invariant under rotation by q."""
    return next(q for q in range(1, P + 1) if P % q == 0 and rot(y, q, P) == y)


def anti_word(lo: int, p: int) -> int:
    """The anti-periodic word of period 2p whose first half is lo: Y(t + p) = not Y(t)."""
    return lo | ((~lo & ((1 << p) - 1)) << p)


def is_anti(y: int, p: int) -> bool:
    """Whether y, of period 2p, is anti-periodic with half-period p."""
    return rot(y, p, 2 * p) == (~y & ((1 << (2 * p)) - 1))


def weight(y: int) -> int:
    """The number of black cells."""
    return bin(y).count("1")


def anti_classes(p: int) -> list[int]:
    """The least rotation of each rotation class of anti-periodic words of least period 2p, in increasing order."""
    P = 2 * p
    reps = set()
    for lo in range(1 << p):
        y = anti_word(lo, p)
        if least_period(y, P) == P:
            reps.add(min(rot(y, k, P) for k in range(P)))
    return sorted(reps)


# ---------------------------------------------------------------------------------------------------------------------
# Regimes in numpy (settled_words.pair_next) and cell by cell


def gaps_numpy(P: int, ys: np.ndarray, cap: int) -> np.ndarray:
    """The gap of the regime from (0, Y) for each Y, cap + 1 where no white word is reached within cap steps; all
    regimes are walked in lockstep."""
    # ys: (n,) uint64 words of period P <= 32
    assert P <= 32
    a = np.zeros(len(ys), dtype=U64)  # (n,)
    b = ys.astype(U64)  # (n,)
    gap = np.full(len(ys), cap + 1, dtype=np.int64)  # (n,)
    alive = np.arange(len(ys))  # (k,) the regimes still walking
    for k in range(1, cap + 1):
        if alive.size == 0:
            break
        c, _ = pair_next(a[alive], b[alive], P)  # (k,)
        a[alive], b[alive] = b[alive], c
        hit = c == 0  # (k,)
        gap[alive[hit]] = k + 1
        alive = alive[~hit]
    return gap  # (n,)


def scalar_regime(y: int, P: int, depth: int) -> list[int]:
    """The words D_w, D_{w+1}, ..., D_{w+depth} of a regime from D_w = 0, D_{w+1} = y, computed without the periodic
    solver: each D_{j+2} is run cell by cell from the value 0 at time 0 on 3P + 1 periods of D_j and D_{j+1}, by
    D_{j+2}(t+1) = D_j(t) xor (D_{j+1}(t) or D_{j+2}(t)), and its word is read in the last period. A diagonal is reset
    at every black cell of the one before, so the run is periodic after its first period with a black cell."""
    words = [0, y]
    T = (3 * P + 1) * P
    for _ in range(depth - 1):
        a, b = words[-2], words[-1]
        c = [0] * (T + 1)  # (T + 1,) the run of D_{j+2}
        for t in range(T):
            c[t + 1] = ((a >> (t % P)) & 1) ^ (((b >> (t % P)) & 1) | c[t])
        start = T - P  # a multiple of P
        words.append(sum(c[start + r] << r for r in range(P)))
    return words


def scalar_gap(y: int, P: int, cap: int) -> int:
    """The gap of the regime from (0, y) by `scalar_regime`, cap + 1 if no white word within cap depths."""
    words = scalar_regime(y, P, cap)
    return next((g for g in range(2, len(words)) if words[g] == 0), cap + 1)


# ---------------------------------------------------------------------------------------------------------------------
# The C program


def _binary(optimize: bool = True) -> Path:
    """computations/doubling_gaps.c, compiled once and kept for later processes (`seed_onsets.compiled`)."""
    from computations.seed_onsets import compiled
    return compiled("doubling_gaps", ("-O2" if optimize else "-O0", "-w"))


def census_c(p: int, cap: int, progress: bool = True, optimize: bool = True) -> tuple[np.ndarray, np.ndarray]:
    """The census by the C program: the least rotation of every class and its gap (cap + 1 if not reached)."""
    run = subprocess.run([str(_binary(optimize)), "census", str(p), str(cap)], stdout=subprocess.PIPE,
                         stderr=None if progress else subprocess.DEVNULL, text=True, check=True)
    lines = run.stdout.split("\n")
    n = int(lines[0].split()[1])
    ys = np.zeros(n, dtype=U64)  # (n,)
    gap = np.zeros(n, dtype=np.int64)  # (n,)
    for i, line in enumerate(lines[1:n + 1]):
        h, g = line.split()
        ys[i], gap[i] = int(h, 16), int(g)
    order = np.argsort(ys)  # (n,) the classes in increasing order, as `anti_classes` gives them
    return ys[order], gap[order]


def orbit_gap(P: int, y: int, cap: int, progress: bool = False, optimize: bool = True) -> tuple[int, int]:
    """The gap of one regime of period P <= 128 from (0, y) by the C program (cap + 1 if not reached), and X, the first
    word of the pair (X, 0) where it ends (D_{w'-1}; the last pair reached if the cap stops it)."""
    run = subprocess.run([str(_binary(optimize)), "orbit", str(P), str(cap), format(y, "x")], stdout=subprocess.PIPE,
                         stderr=None if progress else subprocess.DEVNULL, text=True, check=True)
    out = dict(line.split() for line in run.stdout.strip().split("\n"))
    return int(out["gap"]), int(out["end"], 16)


# ---------------------------------------------------------------------------------------------------------------------
# The census


@dataclass(frozen=True, slots=True)
class Census:
    p: int
    cap: int
    classes: np.ndarray  # (n,) uint64, least rotation of each class of anti-periodic words of least period 2p
    gap: np.ndarray  # (n,) gap of the regime from (0, Y), cap + 1 where the cap stops it

    @property
    def m(self) -> int:
        """The least gap (cap + 1 if no class reaches a white word within the cap)."""
        return int(self.gap.min())

    def minimizers(self) -> list[int]:
        """The classes of least gap."""
        return [int(y) for y in self.classes[self.gap == self.gap.min()]]

    def reached(self) -> int:
        """The classes whose regime ends within the cap."""
        return int((self.gap <= self.cap).sum())


def census(p: int, cap: int, progress: bool = True) -> Census:
    """The gap of every class of anti-periodic words of least period 2p: numpy for p <= 6, C for p >= 7."""
    if p <= 6:
        ys = np.array(anti_classes(p), dtype=U64)  # (n,)
        return Census(p, cap, ys, gaps_numpy(2 * p, ys, cap))
    ys, gap = census_c(p, cap, progress)
    return Census(p, cap, ys, gap)


def geometric_reached(p: int, n: int, cap: int) -> float:
    """A heuristic: the expected number of the n classes whose regime ends within cap steps if each step ends it with
    probability 2^-2p (a fair second word is white with probability 2^-P)."""
    return n * (1.0 - (1.0 - 2.0 ** (-2 * p)) ** cap)


# ---------------------------------------------------------------------------------------------------------------------
# Structured families


def _from_half(bits: list[int], p: int) -> int:
    """The anti-periodic word whose first half is the given cells."""
    return anti_word(sum(b << t for t, b in enumerate(bits[:p])), p)


def thue_morse(n: int) -> list[int]:
    """The first n terms of the Thue-Morse sequence."""
    return [bin(t).count("1") % 2 for t in range(n)]


def families(p: int, seed: int = 1) -> dict[str, int]:
    """One anti-periodic word of period 2p per family, given by its first half: the block 1^p (Y = 1^p 0^p; a word
    with one black cell in its first half is a rotation of it), alternating blocks (1^k 0^k)^* cut to p cells for
    k = 1, 2, 3, the minimizer 1^5 0^5 of p = 5 repeated (k = 5), the p = 7 minimizer's first half repeated, two black
    cells at 0 and p // 2, Thue-Morse, and a random half (seeded, a control)."""
    rng = np.random.default_rng(seed + 1000 * p)
    m7 = [(0x477 >> t) & 1 for t in range(7)]
    out = {
        "block": _from_half([1] * p, p),
        "alt1": _from_half([1 - (t % 2) for t in range(p)], p),
        "alt2": _from_half([1 - (t // 2) % 2 for t in range(p)], p),
        "alt3": _from_half([1 - (t // 3) % 2 for t in range(p)], p),
        "alt5": _from_half([1 - (t // 5) % 2 for t in range(p)], p),
        "min7": _from_half([m7[t % 7] for t in range(p)], p),
        "two": _from_half([1 if t in (0, p // 2) else 0 for t in range(p)], p),
        "thue": _from_half(thue_morse(p), p),
        "random": _from_half([int(x) for x in rng.integers(0, 2, size=p)], p),
    }
    return out


@dataclass(frozen=True, slots=True)
class FamilyGap:
    family: str
    p: int
    word: int
    least_period: int  # of the word, 2p unless the family degenerates
    gap: int  # cap + 1 if not reached


def family_gaps(pmax: int, cap: int, progress: bool = True) -> list[FamilyGap]:
    """The gap of each family word for p = 1 .. pmax (by C), one regime each."""
    rows = []
    jobs = [(p, name, y) for p in range(1, pmax + 1) for name, y in families(p).items()]
    for p, name, y in tqdm(jobs, desc="families", unit="regime", file=sys.stderr, disable=not progress):
        lp = least_period(y, 2 * p)
        g = orbit_gap(2 * p, y, cap)[0] if lp == 2 * p else 0
        rows.append(FamilyGap(name, p, y, lp, g))
    return rows


# ---------------------------------------------------------------------------------------------------------------------
# The single cell


@dataclass(frozen=True, slots=True)
class CellRegime:
    white: int  # depth w of a white diagonal
    period: int  # the common period P of D_{w-1} and D_{w+1} read in the window (the larger of the two)
    weight_before: int  # black cells of D_{w-1} per its period
    y: int  # D_{w+1} as a word of period P, read from the window's first time
    next_white: int | None  # the next white diagonal of the run, None if past the depth read
    model_gap: int  # the gap of the model from (0, y), cap + 1 if not reached
    end: int  # the model's D_{w'-1} at the next white diagonal (by C, for P > 16; 0 otherwise)


def single_cell(steps: int = 150000, depth: int = 87870, cap: int = 100000, last: bool = True,
                progress: bool = True) -> list[CellRegime]:
    """The white diagonals of the single cell below `depth`, from the last 128 of `steps` steps, and the model's gap
    from each one's own word D_{w+1} (for the last one only if `last`; its model gap is 0 otherwise)."""
    from computations.left_diagonals import diagonals, eventual_period
    D = diagonals(steps, depth, 128) if progress else _quiet_diagonals(steps, depth)  # (depth, 128)
    whites = [j for j in range(1, depth - 1) if not D[j].any()]
    rows = []
    for i, w in enumerate(whites):
        P = max(eventual_period(D[w - 1]), eventual_period(D[w + 1]))
        y = sum(int(D[w + 1, t]) << t for t in range(P))
        wb = int(D[w - 1, :eventual_period(D[w - 1])].sum())
        nxt = whites[i + 1] if i + 1 < len(whites) else None
        g, end = 0, 0
        if nxt is not None or last:
            if P <= 16:
                g = int(gaps_numpy(P, np.array([y], dtype=U64), cap)[0])
            else:
                g, end = orbit_gap(P, y, cap, progress=progress)
        rows.append(CellRegime(w, P, wb, y, nxt, g, end))
    return rows


def _quiet_diagonals(steps: int, depth: int) -> np.ndarray:
    """`left_diagonals.diagonals` without its progress bar."""
    import os
    from computations import left_diagonals
    with open(os.devnull, "w") as null:
        old, sys.stderr = sys.stderr, null
        try:
            return left_diagonals.diagonals(steps, depth, 128)  # (depth, 128)
        finally:
            sys.stderr = old


def next_sources(x: int, P: int) -> list[tuple[int, int]]:
    """The words Y = D_{w+1} (with their period) that can follow a white diagonal w whose D_{w-1} is x, of period P:
    Y(t + 1) = Y(t) xor x(t) (`LeftMemory.D_shift_of_white`). For odd weight Y is anti-periodic of period 2P and its
    complement is its rotation by P, so one word stands for both; for even weight Y has period P and its two values,
    complements of each other, start different regimes (the bit between them comes from the transient)."""
    Q = 2 * P if weight(x) % 2 else P
    y, cur = 0, 0
    for t in range(Q - 1):
        cur ^= (x >> (t % P)) & 1
        y |= cur << (t + 1)
    return [(y, Q)] if Q == 2 * P else [(y, P), (y ^ ((1 << P) - 1), P)]


def predict(cap: int = 2**38, progress: bool = True) -> list[tuple[int, int, int, int]]:
    """The single cell's next white diagonals past depth 87,866 by the model: from the cell's own D_87867, the white
    diagonal where its regime ends, then each continuation from there. Rows (white depth, weight of D_{w-1}, period
    after it, branch), the branch numbering the complementary starts of a period-keeping white diagonal."""
    last = single_cell(cap=cap, progress=progress)[-1]
    w1 = last.white + last.model_gap
    rows = [(w1, weight(last.end), 2 * last.period if weight(last.end) % 2 else last.period, 0)]
    for b, (y, Q) in enumerate(next_sources(last.end, last.period)):
        g, end = orbit_gap(Q, y, cap, progress=progress)
        rows.append((w1 + g, weight(end), 2 * Q if weight(end) % 2 else Q, b))
    return rows


# ---------------------------------------------------------------------------------------------------------------------
# Mechanism: the half-period damage


@dataclass(frozen=True, slots=True)
class Damage:
    weight: np.ndarray  # (g + 1,) weight of h_j = D_j xor rot_p(D_j), j = w .. w + g
    runs: np.ndarray  # (g + 1,) number of cyclic runs of black cells of h_j (0 for h_j = 0)
    word_weight: np.ndarray  # (g + 1,) weight of D_j


def _runs(h: int, P: int) -> int:
    """The number of cyclic runs of black cells of h."""
    if h == 0 or h == (1 << P) - 1:
        return 0 if h == 0 else 1
    return weight(h & ~rot(h, P - 1, P))  # cells that are black after a white cell


def half_damage(y: int, p: int, steps: int) -> Damage:
    """The half-period damage along the regime from (0, y) of period 2p, for `steps` depths after w or to its end.
    h_j = D_j xor rot_p(D_j) is constant (all black) exactly when D_j is anti-periodic, and 0 exactly when D_j has
    period p; it is symmetric, h_j = rot_p(h_j), so its weight is even."""
    P = 2 * p
    a, b = np.zeros(1, dtype=U64), np.array([y], dtype=U64)  # (1,), (1,)
    words = [0, y]
    for _ in range(steps - 1):
        c, _ok = pair_next(a, b, P)  # (1,)
        a, b = b, c
        words.append(int(c[0]))
        if int(c[0]) == 0:
            break
    hs = [w ^ rot(w, p, P) for w in words]
    return Damage(np.array([weight(h) for h in hs]), np.array([_runs(h, P) for h in hs]),
                  np.array([weight(w) for w in words]))


# ---------------------------------------------------------------------------------------------------------------------
# The backward words from a sink are local; at an odd gap the source condition is right-permutive


def backward_words(x: int, P: int, n: int) -> list[int]:
    """E_0 = 0, E_1 = x, and E_{i+2} = pair_prev(E_{i+1}, E_i): E_i = D_{w'-i} for the regime ending at the sink
    (D_{w'-1}, D_{w'}) = (x, 0). E_{i+2}(t) = E_i(t+1) xor (E_{i+1}(t) or E_i(t)), so E_i(t) depends on x(t .. t + r_i)
    with r_i = floor((i - 1)/2), and for odd i it is x(t + r_i) xor a function of x(t .. t + r_i - 1)."""
    E = [0, x]
    for _ in range(n - 1):
        E.append(rot(E[-2], 1, P) ^ (E[-1] | E[-2]))
    return E


def odd_gap_radius(g: int) -> int:
    """At an odd gap g the source is E_g = 0, which (with E_{g-1} = Y not white) is E_{g-2} all black, a
    right-permutive condition of radius (g - 3)/2: the window of x of that length fixes the next cell, so the least
    period of x, which is 2p, is at most 2^((g - 3)/2)."""
    assert g % 2 == 1 and g >= 3
    return (g - 3) // 2


def even_weight(k: int) -> int:
    """The number of windows x(0 .. k-1) with E_{2k}(0) = 1. E_{2k} reads exactly these k cells and, for k >= 2, has
    full algebraic degree, so this number is odd: E_{2k} is not balanced and so is permutive in no cell."""
    P = k + 2  # long enough that E_{2k}(0) does not wrap around the period
    return sum(backward_words(w, P, 2 * k)[2 * k] & 1 for w in range(1 << k))


def permutive_check(i: int, P: int) -> bool:
    """Checks on every word x of period P (P > i) that E_i(t) depends only on x(t .. t + r_i), r_i = floor((i-1)/2),
    and for odd i flips with x(t + r_i)."""
    r = (i - 1) // 2
    for x in range(1 << P):
        e = backward_words(x, P, i)[i]
        for t in range(P):
            far = [s for s in range(P) if (s - t) % P > r]
            for s in far:  # flipping a cell outside the window keeps E_i(t)
                e2 = backward_words(x ^ (1 << s), P, i)[i]
                if ((e ^ e2) >> t) & 1:
                    return False
            if i % 2 == 1:
                e2 = backward_words(x ^ (1 << ((t + r) % P)), P, i)[i]
                if not ((e ^ e2) >> t) & 1:
                    return False
    return True


# ---------------------------------------------------------------------------------------------------------------------
# The sink words of every regime with gap g: a shift of finite type, and its two-track form for anti-periodic sources


def _last_two(X: np.ndarray, n: int) -> tuple[np.ndarray, np.ndarray]:
    """E_{n-1} and E_n of `backward_words` on finite windows: X holds cells x(0 .. L-1) of every window, and row t of
    E_i is E_i(t), for the t whose cells x(t .. t + r_i) lie in the window."""
    # X: (L, N) uint8
    a = np.zeros((X.shape[0] + 1, X.shape[1]), dtype=np.uint8)  # (L + 1, N) E_0 = 0, defined everywhere
    b = X  # (L, N) E_1 = x
    for _ in range(2, n + 1):
        m = min(a.shape[0] - 1, b.shape[0])
        a, b = b, a[1:m + 1] ^ (b[:m] | a[:m])  # (m, N)
    return a, b


def _cycles(succ: dict[tuple[int, ...] | int, list]) -> list[int] | None:
    """The cycle lengths of a graph in which every node has at most one successor (None if a node has two)."""
    if any(len(v) > 1 for v in succ.values()):
        return None
    lens, seen = [], set()
    for start in succ:
        path, x = [], start
        while x not in seen:
            seen.add(x)
            path.append(x)
            if not succ.get(x):
                break
            x = succ[x][0]
        if x in path:
            lens.append(len(path) - path.index(x))
    return sorted(lens)


@dataclass(frozen=True, slots=True)
class SourceGraph:
    g: int
    R: int  # windows of R + 1 cells; E_{g-1} reads x(t .. t + R)
    windows: int  # windows of R + 1 cells on a bi-infinite x with E_{g-2}(x) all black
    one_cycles: list[int] | None  # cycle lengths of that shift (None if it branches)
    two_states: int  # pairs of R-cell windows on bi-infinite two-track walks with Y(x') = not Y(x)
    two_cycles: list[int] | None  # cycle lengths of the two-track graph (None if it branches)


def source_graph(g: int) -> SourceGraph:
    """A set of words that contains the sink words x of the regimes with gap g. Read backward from the sink (x, 0), the
    words E_i = D_{w'-i} are local functions of x, and if the regime starts at the white diagonal w = w' - g then
    E_{g-2} is all black and E_{g-1} = D_{w+1} is not white (`D_{w+2}` is black behind a white `D_w`). The converse
    fails when some E_i, 0 < i < g, is white too (then g spans two regimes, as the cycles at g = 26 do). E_{g-2} and
    E_{g-1} read x(t .. t + R), R = floor((g - 2)/2). So x is a periodic point of the shift of finite type of the
    bi-infinite words with E_{g-2} all black; its windows that lie on a bi-infinite path are `windows`. A source
    anti-periodic with half-period p is a pair of such words, x and x' = rot_p(x), with E_{g-1}(x') = not E_{g-1}(x)
    at every time: a bi-infinite walk in the two-track graph. When that graph is a union of disjoint cycles, the least
    period 2p of such an x is a cycle length."""
    R = (g - 2) // 2
    L, S = R + 1, 1 << R
    cols = np.arange(1 << L, dtype=np.int64)  # (N,) the windows of L cells, cell s at bit s
    X = ((cols[None, :] >> np.arange(L)[:, None]) & 1).astype(np.uint8)  # (L, N)
    e2, e1 = _last_two(X, g - 1)  # E_{g-2}, E_{g-1}
    ok = e2[0] == 1  # (N,)
    src, dst = cols & (S - 1), cols >> 1  # (N,), (N,): the window's first and last R cells
    alive = np.ones(S, dtype=bool)  # (S,)
    while True:
        e = ok & alive[src] & alive[dst]  # (N,)
        out = np.zeros(S, dtype=bool)
        inn = np.zeros(S, dtype=bool)
        out[src[e]] = True
        inn[dst[e]] = True
        nxt = alive & out & inn
        if np.array_equal(nxt, alive):
            break
        alive = nxt
    wins = np.flatnonzero(ok & alive[src] & alive[dst])  # (w,)
    one = _cycles({int(u): [] for u in np.flatnonzero(alive)} | _succ(src[wins], dst[wins]))
    y = e1[0]  # (N,) E_{g-1}(0) of each window
    two: dict[tuple[int, ...], list[tuple[int, ...]]] = {}
    for a in wins:
        for b in wins:
            if y[a] != y[b]:
                two.setdefault((int(src[a]), int(src[b])), []).append((int(dst[a]), int(dst[b])))
    nodes = set(two) | {v for vs in two.values() for v in vs}
    while True:
        inn2 = {v for u in nodes for v in two.get(u, []) if v in nodes}
        out2 = {u for u in nodes if any(v in nodes for v in two.get(u, []))}
        trimmed = nodes & inn2 & out2
        if trimmed == nodes:
            break
        nodes = trimmed
    succ2 = {u: [v for v in two.get(u, []) if v in nodes] for u in nodes}
    return SourceGraph(g, R, len(wins), one, len(nodes), _cycles(succ2))


def _succ(src: np.ndarray, dst: np.ndarray) -> dict[int, list[int]]:
    """The successor lists of a graph given by its edges."""
    # src, dst: (e,)
    out: dict[int, list[int]] = {}
    for u, v in zip(src.tolist(), dst.tolist()):
        out.setdefault(u, []).append(v)
    return out


# ---------------------------------------------------------------------------------------------------------------------


def _range(s: str) -> list[int]:
    lo, _, hi = s.partition("-")
    return list(range(int(lo), int(hi or lo) + 1))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--census", type=str, help="range of p, e.g. 1-14")
    parser.add_argument("--families", type=int, help="largest p of the families")
    parser.add_argument("--single-cell", action="store_true")
    parser.add_argument("--predict", action="store_true", help="the model's next white diagonals past 87,866")
    parser.add_argument("--damage", type=str, help="range of p for the half damage on the minimizing orbits")
    parser.add_argument("--sources", type=str, help="range of gaps g for the source graphs, e.g. 5-49")
    parser.add_argument("--cap", type=int, default=10**7)
    args = parser.parse_args()

    if args.census:
        print("| p | classes | m(p) | minimizers (hex, least rotation) | reached within cap | geometric heuristic |")
        for p in _range(args.census):
            c = census(p, args.cap)
            mins = ", ".join(format(y, "x") for y in c.minimizers()) if c.m <= args.cap else "-"
            print(f"| {p} | {len(c.classes)} | {c.m if c.m <= args.cap else '>' + str(args.cap)} | {mins} | "
                  f"{c.reached()} | {geometric_reached(p, len(c.classes), args.cap):.1f} |", flush=True)
    if args.families:
        rows = family_gaps(args.families, args.cap)
        names = list(families(1).keys())
        print("| p | " + " | ".join(names) + " |")
        for p in range(1, args.families + 1):
            cells = []
            for name in names:
                r = next(r for r in rows if r.p == p and r.family == name)
                cells.append("deg" if r.least_period != 2 * p else (str(r.gap) if r.gap <= args.cap else ">cap"))
            print(f"| {p} | " + " | ".join(cells) + " |", flush=True)
        small = [r for r in rows if r.least_period == 2 * r.p and r.gap < 7 * r.p]
        print("family words with gap < 7p:", [(r.family, r.p, r.gap) for r in small])
    if args.single_cell:
        for r in single_cell(cap=args.cap):
            print(f"white {r.white}: D_(w-1) weight {r.weight_before}, P {r.period}, Y {r.y:x}, next white "
                  f"{r.next_white}, actual gap {None if r.next_white is None else r.next_white - r.white}, "
                  f"model gap {r.model_gap if r.model_gap <= args.cap else '>' + str(args.cap)}")
    if args.predict:
        for w, wt, Q, b in predict(cap=args.cap):
            print(f"branch {b}: white diagonal {w}, D_(w-1) of weight {wt}, period {Q} after it")
    if args.sources:
        print("| g | windows | one-track cycles | two-track states | two-track cycles (2p) |")
        for g in tqdm(_range(args.sources), desc="gaps", unit="g", file=sys.stderr):
            sg = source_graph(g)
            one = "branches" if sg.one_cycles is None else ", ".join(map(str, sg.one_cycles)) or "-"
            two = "branches" if sg.two_cycles is None else ", ".join(map(str, sg.two_cycles)) or "-"
            print(f"| {g} | {sg.windows} | {one} | {sg.two_states} | {two} |", flush=True)
    if args.damage:
        for p in _range(args.damage):
            c = census(p, args.cap, progress=False)
            for y in c.minimizers():
                d = half_damage(y, p, c.m)
                zeros = np.flatnonzero(d.weight == 0)  # (z,)
                print(f"p {p} Y {y:x} gap {c.m}: h = 0 at {len(zeros)} depths, h all black at "
                      f"{int((d.weight == 2 * p).sum())}, mean weight {d.weight.mean():.2f}, max runs {d.runs.max()}, "
                      f"last ten weights {d.weight[-10:].tolist()}")


if __name__ == "__main__":
    main()
