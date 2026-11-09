"""The relaxed driver game G: exact values, a beam, the lemmas behind them and the explicit orbit every bound contains.

The left half x (cells -1, -2, ...; bit k - 1 of an integer is cell -k, as in `run_mechanism`) starts white. At each
time t the controller picks e(t) in {0, 1}, with e(t) = 1 only when cell -1 is white, and the left half takes one
Rule 30 step with cell 0 equal to e(t). The payoff of a play of T moves is the number of t < T with e(t) = 1, and E(T)
is its largest value over all plays. For a driver c of Lambda_L (`driver_density`) the play e(t) = c(t) and c(t + 1)
drives the same left half, so G relaxes the driver game of `driver_density`.

1. `values`: E(t) for t <= T by the cut dynamic program of `relaxed_game.c` (T <= 255); `values_python`, the same
   without the cut in Python, and `brute_values`, every play enumerated with the rule applied cell by cell, check it.
2. `reach`, `windows`, `costs`: the reachable sets (their sizes and largest phase-A prefixes), the most ones in a window
   of moves from any state reachable at time s, and the fewest zeros of the moves that lead to a long prefix.
3. `beam`: the W states with the largest payoffs kept after each step, with a play that attains the last count (a
   lower bound on E(T)); `play_stats` counts its runs, its forced zeros and its skips.
4. `greedy_play` and `held_black_column`: the play with e = 1 whenever allowed, which is Rule 30 on the half line
   beside a cell held black; its payoff is the number of white cells of column -1.
5. `accounting`: the identity L8 between the zeros of a play, the white cells of column -2 and the wasteful skips.
6. `charging_ratio` and `covering_constant`: the two-sided charging property CP of a play and the constant of L9.
7. `check_*`: the exhaustive and random checks of the lemmas L1 to L7 on the stated widths.
8. `lambda_values`: over Lambda_L, the most black cells M(T) and the most times with c(t) = c(t + 1) = 1, the count of
   Proposition 3(e) of `driver_counts` and the payoff of G on the plays that come from Lambda_L.

    python -m computations.relaxed_game values                                  # E(t) to t = 150, about 15 s
    python -m computations.relaxed_game values --steps 180                      # to t = 180, about 4 min, 2 GB
    python -m computations.relaxed_game beam                                    # T = 1,000, width 20,000, 20 s
    python -m computations.relaxed_game beam --steps 3000 --width 60000         # about 6 min, 1 GB
    python -m computations.relaxed_game beam --steps 180 --width 20000 --check  # the beam against E(t), 1 min
    python -m computations.relaxed_game greedy                                  # B1's orbit to t = 40,000, 5 s
    python -m computations.relaxed_game lemmas                                  # L1 to L7, about 1 min
    python -m computations.relaxed_game reach                                   # N(t) and prefixes to 100, 10 s
    python -m computations.relaxed_game reach --steps 120                       # to t = 120, about 1 min, 1 GB
    python -m computations.relaxed_game windows                                 # s = 30, 60, 90, about 10 s
    python -m computations.relaxed_game windows --times 120 --width 30          # about 1 min
    python -m computations.relaxed_game costs                                   # s = 60, about 10 s
    python -m computations.relaxed_game costs --times 100 --width 44 --cells 64 # about 2 min
    python -m computations.relaxed_game costs --times 120 --width 32 --cells 48 # about 4 min, 2 GB
    python -m computations.relaxed_game lambda                                  # Lambda_L to T = 60, 5 s
    python -m computations.relaxed_game lambda --steps 100                      # to T = 100, about 1 min
"""

from __future__ import annotations

import argparse
import itertools
import random
import subprocess
import sys
from collections import Counter
from collections.abc import Iterator, Sequence
from dataclasses import dataclass
from pathlib import Path

import numpy as np
from tqdm.auto import tqdm

from computations.seed_onsets import compiled

PHASE_A = int("10" * 65536, 2)  # bit k - 1 set exactly for even k <= 131,072: the phase-A pattern of cells -1, -2, ...


# ---------------------------------------------------------------------------------------------------------------------
# 1. The game
# ---------------------------------------------------------------------------------------------------------------------


def step(x: int, e: int) -> int:
    """One move: the left half x takes a Rule 30 step with cell 0 equal to e (cell -k becomes cell -(k + 1) xor
    (cell -k or cell -(k - 1)))."""
    return (x >> 1) ^ (x | ((x << 1) | e))


def legal(x: int, e: int) -> bool:
    """Whether the move e is allowed from x: e = 1 needs cell -1 white."""
    return e == 0 or not x & 1


def prefix(x: int) -> int:
    """m(x), the phase-A prefix: the largest m with cell -j black exactly for even j, 1 <= j <= m (cells beyond the
    stored ones are white, so m is at most the support plus one)."""
    n = x.bit_length() + 2
    assert n <= PHASE_A.bit_length(), "a left half of at most 131,070 cells"
    d = x ^ (PHASE_A & ((1 << n) - 1))  # nonzero: one of the cells -(n - 1), -n is white where phase A is black
    return (d & -d).bit_length() - 1


def play_rows(play: Sequence[int]) -> list[int]:
    """The left halves x(0), ..., x(T) of a play e(0), ..., e(T - 1); raises ValueError on an illegal move."""
    x, rows = 0, [0]
    for t, e in enumerate(play):
        if not legal(x, e):
            raise ValueError(f"e({t}) = 1 with cell -1 black")
        x = step(x, e)
        rows.append(x)
    return rows


def cell(x: int, k: int) -> int:
    """Cell -k of the left half x (k >= 1)."""
    return (x >> (k - 1)) & 1


# ---------------------------------------------------------------------------------------------------------------------
# 2. The C program
# ---------------------------------------------------------------------------------------------------------------------


def _binary() -> Path:
    """relaxed_game.c, beside this file, compiled by `seed_onsets.compiled` (kept per source, flags and machine)."""
    return compiled("relaxed_game", ("-O2", "-w"))


def _lines(args: Sequence[object], total: int, desc: str, progress: bool) -> Iterator[list[str]]:
    """Run the C program with `args` and yield its output lines split into fields, with a progress bar over `total`
    lines."""
    with subprocess.Popen([str(_binary()), *map(str, args)], stdout=subprocess.PIPE, text=True) as proc:
        assert proc.stdout is not None
        for line in tqdm(proc.stdout, total=total, desc=desc, file=sys.stderr, disable=not progress, leave=False):
            yield line.split()
    if proc.returncode:
        raise RuntimeError(f"relaxed_game {' '.join(map(str, args))} exited with {proc.returncode}")


def values(T: int, progress: bool = False) -> list[int]:
    """[E(0), E(1), ..., E(T)] by the cut dynamic program (T <= 255): the states at time t are cut to the cells
    -1 .. -(T - t), which decide every later move."""
    out = [0]
    for f in _lines(("value", T), T, "values", progress):
        out.append(int(f[2]))
    return out


def values_states(T: int, progress: bool = False) -> list[int]:
    """The number of cut states after each step of `values(T)` (index t - 1 for time t)."""
    return [int(f[1]) for f in _lines(("value", T), T, "values", progress)]


@dataclass(frozen=True, slots=True)
class ReachRow:
    t: int
    states: int  # N(t), the number of left halves reachable at time t
    best: int  # E(t)
    longest: int  # the largest phase-A prefix over them, the longest run of ones that can start at t


def reach(T: int, progress: bool = False) -> list[ReachRow]:
    """For t = 1 .. T (T <= 318): the uncut reachable sets, their sizes, E(t) and their largest prefixes."""
    return [ReachRow(*map(int, f)) for f in _lines(("reach", T), T, "reach", progress)]


def windows(s: int, w: int, progress: bool = False) -> list[int]:
    """[G(s, s + 1), ..., G(s, s + w)]: the most ones in i moves from any state reachable at time s."""
    return [int(f[2]) for f in _lines(("window", s, w), w, f"windows s={s}", progress)]


def costs(s: int, w: int, cells: int, progress: bool = False) -> list[list[int]]:
    """For i = 1 .. w, the list [z_1, z_2, ...]: z_k is the fewest zeros of i moves from a state reachable at time s
    that end at a state with prefix >= k (read on the cells - i that stay exact); the list stops at the first k that
    no play reaches."""
    return [list(map(int, f[2:])) for f in _lines(("cost", s, w, cells), w, f"costs s={s}", progress)]


@dataclass(frozen=True, slots=True)
class Beam:
    best: list[int]  # (T + 1,) the beam's largest payoff after each step, best[0] = 0
    play: list[int]  # a play of T moves that attains best[T]


def beam(T: int, width: int, progress: bool = False) -> Beam:
    """Keep the `width` states with the largest payoffs after each step (ties broken by a hash of the state)."""
    best, play = [0], []
    for f in _lines(("beam", T, width), T + 1, f"beam W={width}", progress):
        if f[0] == "play":
            play = [int(ch) for ch in f[1]]
        else:
            best.append(int(f[1]))
    return Beam(best, play)


# ---------------------------------------------------------------------------------------------------------------------
# Independent checks of the values
# ---------------------------------------------------------------------------------------------------------------------


def values_python(T: int) -> list[int]:
    """[E(0), ..., E(T)] by the same dynamic program without the cut, over Python integers."""
    states, out = {0: 0}, [0]
    for _ in range(T):
        new: dict[int, int] = {}
        for x, v in states.items():
            for e in (0, 1) if not x & 1 else (0,):
                y = step(x, e)
                if new.get(y, -1) < v + e:
                    new[y] = v + e
        states = new
        out.append(max(states.values()))
    return out


def list_step(cells: list[int], e: int) -> list[int]:
    """One move on a left half held as a list (element k - 1 is cell -k), the rule applied cell by cell; the list
    grows by one cell, so it holds the whole support."""
    ext = [e] + cells + [0, 0]  # ext[k] is cell -k
    return [ext[k + 1] ^ (ext[k] | ext[k - 1]) for k in range(1, len(cells) + 2)]


def brute_values(T: int) -> list[int]:
    """[E(0), ..., E(T)] by enumerating every play of T moves, depth first, with `list_step`."""
    best = [0] * (T + 1)

    def go(cells: list[int], t: int, v: int) -> None:
        best[t] = max(best[t], v)
        if t == T:
            return
        for e in (0, 1) if cells[0] == 0 else (0,):
            go(list_step(cells, e), t + 1, v + e)

    go([0], 0, 0)
    return best


# ---------------------------------------------------------------------------------------------------------------------
# 3. Plays: runs, zeros, the accounting identity L8 and the charging property of L9
# ---------------------------------------------------------------------------------------------------------------------


def runs(play: Sequence[int], bit: int) -> list[tuple[int, int]]:
    """The maximal runs of `bit` in a play, as (start, length)."""
    out, t = [], 0
    for b, grp in itertools.groupby(play):
        n = len(list(grp))
        if b == bit:
            out.append((t, n))
        t += n
    return out


@dataclass(frozen=True, slots=True)
class Accounting:
    T: int
    ones: int  # the payoff
    forced: int  # zeros with cell -1 black
    skips: int  # zeros with cell -1 white
    wasteful: int  # W: skips at t <= T - 2 with cell -2 black
    last_skip: int  # 1 if the move at T - 1 is a skip
    white_two: int  # Y: times t <= T - 2 with cell -2 white


def accounting(play: Sequence[int]) -> Accounting:
    """The counts of L8 for a play, read off its rows."""
    rows = play_rows(play)
    T = len(play)
    skip = [not rows[t] & 1 and play[t] == 0 for t in range(T)]
    return Accounting(
        T=T,
        ones=sum(play),
        forced=sum(rows[t] & 1 for t in range(T)),
        skips=sum(skip),
        wasteful=sum(1 for t in range(T - 1) if skip[t] and cell(rows[t], 2)),
        last_skip=int(T > 0 and skip[T - 1]),
        white_two=sum(1 for t in range(T - 1) if not cell(rows[t], 2)),
    )


def accounting_holds(a: Accounting) -> bool:
    """L8: zeros = Y + 2W + [skip at T - 1], and zeros = forced + skips."""
    zeros = a.T - a.ones
    return zeros == a.forced + a.skips == a.white_two + 2 * a.wasteful + a.last_skip


def next_level(play: Sequence[int]) -> list[int]:
    """The play e_1(t) = cell -1 and not cell -2 that drives the cells <= -2 of a play's left halves: they read cell -1
    only through cell -2 or cell -1, which is cell -2 or e_1, so they are game G one cell further out."""
    rows = play_rows(play)
    return [cell(rows[t], 1) & (1 - cell(rows[t], 2)) for t in range(len(play))]


def charging_ratio(play: Sequence[int], lam: int, kmin: int, side: str = "both") -> float:
    """The least (zeros in the window of R) / k over the maximal runs R = [a, a + k) of ones with k >= kmin: the window
    is [a - lam k, a + k + lam k) for "both", [a - lam k, a) for "before" and [a + k, a + k + lam k) for "after", cut
    to [0, T). Infinity if no run is that long."""
    T = len(play)
    zeros = np.concatenate([[0], np.cumsum(1 - np.asarray(play, dtype=np.int64))])  # (T + 1,) zeros before each time
    lo_hi = {"both": lambda a, k: (a - lam * k, a + k + lam * k), "before": lambda a, k: (a - lam * k, a),
             "after": lambda a, k: (a + k, a + k + lam * k)}[side]
    best = float("inf")
    for a, k in runs(play, 1):
        if k < kmin:
            continue
        lo, hi = lo_hi(a, k)
        lo, hi = max(lo, 0), min(hi, T)
        best = min(best, int(zeros[hi] - zeros[lo]) / k)
    return best


def covering_constant(lam: float, eps: float, C: float, K: int) -> float:
    """K' of L9: if every run of k >= K ones has at least eps k - C zeros within lam k of it, the ones number at most
    K' (Z + 1), Z the zeros."""
    return (6 * lam + 4) * (1 + C) / eps + K - 1


@dataclass(frozen=True, slots=True)
class PlayStats:
    ones: int
    run_count: int
    run_mean: float
    run_longest: int
    run_lengths: dict[int, int]  # length -> number of runs of ones
    gap_count: int
    gap_mean: float
    gap_lengths: dict[int, int]  # length -> number of runs of zeros
    accounting: Accounting


def play_stats(play: Sequence[int]) -> PlayStats:
    ones, zeros = [k for _, k in runs(play, 1)], [k for _, k in runs(play, 0)]
    return PlayStats(sum(play), len(ones), float(np.mean(ones)), max(ones), dict(sorted(Counter(ones).items())),
                     len(zeros), float(np.mean(zeros)), dict(sorted(Counter(zeros).items())), accounting(play))


# ---------------------------------------------------------------------------------------------------------------------
# 4. The greedy play and the half line beside a cell held black (B1)
# ---------------------------------------------------------------------------------------------------------------------


def greedy_play(T: int) -> list[int]:
    """e(t) = 1 whenever cell -1 is white, for t < T."""
    x, play = 0, []
    for _ in range(T):
        e = 1 - (x & 1)
        play.append(e)
        x = step(x, e)
    return play


def held_black_column(T: int, k: int = 1, progress: bool = False) -> np.ndarray:
    """Column -k at times 0 .. T - 1 of Rule 30 on the cells <= -1 beside cell 0 held black, from white."""
    col = np.zeros(T, dtype=np.uint8)  # (T,)
    x = 0
    for t in tqdm(range(T), desc="held black", file=sys.stderr, disable=not progress, leave=False):
        col[t] = (x >> (k - 1)) & 1
        x = step(x, 1)
    return col  # (T,)


def least_period(word: np.ndarray, pmax: int) -> int | None:
    """The least p <= pmax with word[i] = word[i - p] for every i >= p, or None."""
    # word: (n,)
    return next((p for p in range(1, min(pmax, len(word) - 1) + 1) if np.array_equal(word[p:], word[:-p])), None)


# ---------------------------------------------------------------------------------------------------------------------
# 5. Lambda_L: the plays that come from drivers, and the count of Proposition 3(e)
# ---------------------------------------------------------------------------------------------------------------------


def lambda_values(T: int, progress: bool = False) -> tuple[list[int], list[int]]:
    """Over the drivers c of Lambda_L (c(0) = 1; c(t + 1) = not cell -1 at t whenever c(t) = 1), the lists
    [M(0), ..., M(T)] of the most black cells among c(0 .. t) and [D(0), ..., D(T)] of the most times s < t with
    c(s) = c(s + 1) = 1, by a dynamic program over the states (left half, c(t)) with both counts kept per state."""
    states: dict[tuple[int, int], tuple[int, int]] = {(0, 1): (1, 0)}  # (x, c) -> (most black, most doubled)
    M, D = [1], [0]
    for _ in tqdm(range(T), desc="Lambda_L", file=sys.stderr, disable=not progress, leave=False):
        new: dict[tuple[int, int], tuple[int, int]] = {}
        for (x, c), (b, d) in states.items():
            y = step(x, c)
            for c2 in ((1 - (x & 1),) if c else (0, 1)):
                old = new.get((y, c2), (-1, -1))
                new[(y, c2)] = (max(old[0], b + c2), max(old[1], d + (c & c2)))
        states = new
        M.append(max(v[0] for v in states.values()))
        D.append(max(v[1] for v in states.values()))
    return M, D


def driver_play(c: Sequence[int]) -> list[int]:
    """The play e(t) = c(t) and c(t + 1), t < len(c) - 1, of a driver."""
    return [c[t] & c[t + 1] for t in range(len(c) - 1)]


def random_driver(T: int, rng: random.Random, p_black: float = 0.8) -> list[int]:
    """A driver c(0 .. T) of Lambda_L, black with probability p_black where the value is free."""
    x, c = 0, [1]
    for _ in range(T):
        cur = c[-1]
        c.append(1 - (x & 1) if cur else int(rng.random() < p_black))
        x = step(x, cur)
    return c


# ---------------------------------------------------------------------------------------------------------------------
# 6. The lemmas L1 to L7: exhaustive checks on rows of a given width, and checks on random plays
# ---------------------------------------------------------------------------------------------------------------------


def check_run_lemma(n: int) -> int:
    """L1 on every row with support in cells -1 .. -n: e = 1 can be played exactly m(x) times in a row, the prefix
    falling by one at each, and cell -1 is black after them. Returns the number of rows."""
    for x in range(1 << n):
        m, y = prefix(x), x
        for i in range(m):
            assert prefix(y) == m - i and legal(y, 1), (x, i)
            y = step(y, 1)
        assert y & 1, x
    return 1 << n


def alternating_segments(row: Sequence[int]) -> list[tuple[int, int]]:
    """The maximal alternating segments [p, q] of a list (indices increase to the right)."""
    segs, p = [], 0
    for i in range(1, len(row) + 1):
        if i == len(row) or row[i] == row[i - 1]:
            segs.append((p, i - 1))
            p = i
    return segs


def rule_image(row: Sequence[int]) -> list[int | None]:
    """One Rule 30 step of a finite list; the two end cells, which need cells outside, are None."""
    return [None] + [row[i - 1] ^ (row[i] | row[i + 1]) for i in range(1, len(row) - 1)] + [None]


def check_erosion(n: int) -> dict[int, int]:
    """L2 and L3 on every word of n cells, for every maximal alternating segment [p, q] with q - p >= 2, p >= 1 and
    q + 6 <= n - 1 (so that the next row is known to q + 5): one step keeps p + 1 .. q - 1, flips p, and moves the right
    end by the case table of L3, so the rightmost black cell of the segment advances by 0, 2 or 4. Returns the number of
    segments with each advance."""
    adv: Counter[int] = Counter()
    for bits in itertools.product((0, 1), repeat=n):
        nxt = rule_image(bits)
        for p, q in alternating_segments(bits):
            if p < 1 or q - p < 2 or q + 6 > n - 1:
                continue
            assert all(nxt[i] == bits[i] for i in range(p + 1, q)) and nxt[p] == 1 - bits[p]
            r = q - 1
            while nxt[r + 1] is not None and nxt[r + 1] != nxt[r]:
                r += 1
            tail = bits[q + 2:q + 6]
            if bits[q] == 0:
                expected = q - 1
            elif tail[0] or tail[1]:
                expected = q + 1
            elif tail[2]:
                expected = q + 2
            else:
                expected = q + 4 if tail[3] else q + 3
            assert r == expected, (bits, p, q, r)
            old = q if bits[q] else q - 1
            adv[(r if nxt[r] else r - 1) - old] += 1
    assert set(adv) <= {0, 2, 4}, adv
    return dict(sorted(adv.items()))


def p_value(x: int, k: int) -> int:
    """P at distance k >= 1 from cell 0: cell -k xor [k even], 0 on phase A."""
    return cell(x, k) ^ (1 - k % 2)


def random_play_rows(T: int, rng: random.Random) -> tuple[list[int], list[int]]:
    """A play of T moves with e(t) a fair coin where it is free, and its rows."""
    x, play, rows = 0, [], [0]
    for _ in range(T):
        e = rng.randint(0, 1) if not x & 1 else 0
        play.append(e)
        x = step(x, e)
        rows.append(x)
    return play, rows


def check_moving_frame(trials: int, T: int, seed: int = 1) -> int:
    """L4 on random plays: with P_n(t) = cell -(n - t) at time t xor [(n - t) even] and P_t(t) = not e(t),
    P_n(t + 1) = P_n(t) xor [cells n - 1 and n - 2 white at time t] for every n >= t + 2 (here up to t + 41). Returns
    the number of cells checked."""
    rng, checked = random.Random(seed), 0
    for _ in range(trials):
        play, rows = random_play_rows(T, rng)
        for t in range(T):
            x, y, e = rows[t], rows[t + 1], play[t]
            col = [e] + [cell(x, k) for k in range(1, 43)]  # col[k] is cell -k at time t
            for k in range(2, 42):  # n = t + k
                white = int(col[k - 1] == col[k - 2] == 0)
                assert p_value(y, k - 1) == p_value(x, k) ^ white, (t, k)
                checked += 1
    return checked


def check_walls(n: int) -> int:
    """The rest-frame form of L4 on every word of n cells: with walls d(i) = [x(i) = x(i + 1)],
    d'(i) = d(i - 1) xor ([x(i + 1) = 0] and (d(i) xor d(i + 1))) wherever the next row is known."""
    checked = 0
    for x in itertools.product((0, 1), repeat=n):
        y = rule_image(x)
        for i in range(2, n - 3):
            d = [int(x[j] == x[j + 1]) for j in (i - 1, i, i + 1)]
            assert int(y[i] == y[i + 1]) == d[0] ^ ((1 - x[i + 1]) & (d[1] ^ d[2]))
            checked += 1
    return checked


def check_front_speed(n: int) -> int:
    """Moving frame, every row with support in cells -1 .. -n and every legal move: a run of equal P of length >= 3
    whose near end is at distance >= 2 and whose far end is at distance <= n - 2 keeps its far end (the cell beyond it
    keeps the other value), and its near end moves toward the head by at most 3 cells. Returns the number of runs."""
    checked = 0
    for x in range(1 << n):
        for e in (0, 1) if not x & 1 else (0,):
            y = step(x, e)
            P = [None] + [p_value(x, k) for k in range(1, n + 3)]  # P[k] at distance k, time t
            Q = [None] + [p_value(y, k) for k in range(1, n + 3)]  # at time t + 1
            k = 2
            while k <= n:
                if P[k] == P[k - 1]:
                    k += 1
                    continue
                b = k
                while b + 1 <= n + 2 and P[b + 1] == P[k]:
                    b += 1
                if b - k + 1 >= 3 and b <= n - 2:
                    # the moving index of distance b at t is distance b - 1 at t + 1
                    assert Q[b - 1] == P[k] and Q[b] != P[k], (x, e, k, b)
                    a2 = b - 1
                    while a2 - 1 >= 1 and Q[a2 - 1] == P[k]:
                        a2 -= 1
                    assert (a2 + 1) - k >= -3, (x, e, k, b, a2)
                    checked += 1
                k = b + 1
    return checked


def check_shielding(trials: int, T: int, seed: int = 2) -> int:
    """L5 on random plays: at each time, take the nearest three cells at distances k - 2, k - 1, k with equal P; every
    flip of a nearer cell (distance 1 .. k - 3), with every legal move, leaves the cells at distance >= k - 1 at the
    next time unchanged. Returns the number of flips checked."""
    rng, checked = random.Random(seed), 0
    for _ in range(trials):
        play, rows = random_play_rows(T, rng)
        for t in range(T):
            x = rows[t]
            k = next((k for k in range(3, t + 5) if p_value(x, k - 2) == p_value(x, k - 1) == p_value(x, k)), None)
            if k is None:  # no three equal cells: the white beyond the support alternates in P
                continue
            base = step(x, play[t]) >> (k - 2)
            for j in range(1, k - 2):
                z = x ^ (1 << (j - 1))
                for e in (0, 1) if not z & 1 else (0,):
                    assert step(z, e) >> (k - 2) == base, (t, k, j)
                    checked += 1
    return checked


def check_trapezoid(n: int) -> int:
    """L6(a) on every word y of n cells with image z: wherever z alternates on [p, q] with q - p >= 4, y alternates on
    [p - 1, q - 4] in the phase of z. Returns the number of intervals [p, q] checked."""
    checked = 0
    for y in itertools.product((0, 1), repeat=n):
        z = rule_image(y)
        for p in range(1, n - 1):
            q = p
            while z[q + 1] is not None and z[q + 1] != z[q]:
                q += 1
            for qq in range(p + 4, q + 1):
                assert all(y[i] == z[p] ^ ((i - p) & 1) for i in range(p - 1, qq - 3)), (y, p, qq)
                checked += 1
    return checked


def check_boundary_trapezoid(n: int) -> int:
    """L6(b) on every left half y with support in cells -1 .. -n and every legal move: if the next half has prefix
    m >= 4, y is in phase A on the cells -4 .. -(m + 1). Returns the number of (half, move) pairs."""
    checked = 0
    for y in range(1 << n):
        for e in (0, 1) if not y & 1 else (0,):
            m = prefix(step(y, e))
            assert all(cell(y, j) == 1 - j % 2 for j in range(4, m + 2)), (y, e, m)
            checked += 1
    return checked


def slope_bound(a: int) -> float:
    """L7: m(x(a)) <= (3a + 9)/5 in every play."""
    return (3 * a + 9) / 5


# ---------------------------------------------------------------------------------------------------------------------
# Command line
# ---------------------------------------------------------------------------------------------------------------------


def _ints(text: str) -> list[int]:
    return [int(a) for a in text.split(",") if a]


def run_values(args: argparse.Namespace) -> None:
    E = values(args.steps, progress=True)
    print("T E(T) E(T)/T")
    for T in range(args.every, args.steps + 1, args.every):
        print(T, E[T], f"{E[T] / T:.4f}")
    even = [(E[T] / T, T) for T in range(args.low, args.steps + 1) if T % 2 == 0]
    if even:
        print(f"even T from {args.low} to {args.steps}: E(T)/T from {min(even)[0]:.4f} (T = {min(even)[1]}) "
              f"to {max(even)[0]:.4f} (T = {max(even)[1]})")
    print("E(T) for every T:", " ".join(map(str, E[1:])))


def run_beam(args: argparse.Namespace) -> None:
    b = beam(args.steps, args.width, progress=True)
    print("T beam ratio gain")
    for T in range(args.every, args.steps + 1, args.every):
        print(T, b.best[T], f"{b.best[T] / T:.4f}", b.best[T] - b.best[T - args.every])
    assert sum(b.play) == b.best[-1] and len(play_rows(b.play)) == args.steps + 1
    s = play_stats(b.play)
    a = s.accounting
    print(f"play: {s.ones} ones in {s.run_count} runs, mean {s.run_mean:.2f}, longest {s.run_longest}; "
          f"runs of length 1 to 6: {[s.run_lengths.get(k, 0) for k in range(1, 7)]}")
    print(f"      {s.gap_count} runs of zeros, mean {s.gap_mean:.2f}; of length 1 to 6: "
          f"{[s.gap_lengths.get(k, 0) for k in range(1, 7)]}")
    print(f"      {a.T - a.ones} zeros: {a.forced} forced, {a.skips} skips ({a.wasteful} wasteful, last move a skip: "
          f"{a.last_skip}); white cells of column -2 at t <= T - 2: {a.white_two}; L8 holds: {accounting_holds(a)}")
    for side, kmin in (("both", 4), ("before", 4), ("before", 8), ("after", 4)):
        ratios = [charging_ratio(b.play, lam, kmin, side) for lam in (1, 2, 3)]
        print(f"      least zeros/k in the window {side}, runs k >= {kmin}, lambda = 1, 2, 3: "
              + ", ".join(f"{r:.3f}" for r in ratios))
    if args.check:
        E = values(min(args.steps, args.check), progress=True)
        bad = [T for T in range(2, len(E), 2) if E[T] != b.best[T]]
        print(f"beam equals E(T) at {len(range(2, len(E), 2)) - len(bad)} of the even T <= {len(E) - 1}; "
              f"differs at {bad}")
    if args.out:
        Path(args.out).write_text("".join(map(str, b.play)) + "\n")


def run_greedy(args: argparse.Namespace) -> None:
    play = greedy_play(max(args.checkpoints))
    ones = np.cumsum(play)  # (T,)
    for T in args.checkpoints:
        print(f"greedy play: {ones[T - 1]} ones in {T} moves, {ones[T - 1] / T:.4f}")
    col = held_black_column(args.steps, progress=True)  # (T,)
    for T in (1000, 5000, 10000, 20000, 40000):
        if T <= args.steps:
            print(f"held black, column -1: {int(col[:T].sum())} black among the first {T}, {col[:T].mean():.4f}")
    tail = col[-args.tail:]  # (tail,)
    print(f"least period <= {args.pmax} of the last {len(tail)} values: {least_period(tail, args.pmax)}")
    print("first 64 values:", "".join(map(str, col[:64])))
    from computations.driver_density import greedy_driver  # the greedy driver of Lambda_L, for S_B
    c = greedy_driver(max(args.checkpoints))
    for T in args.checkpoints:
        print(f"greedy driver of Lambda_L: {sum(c[:T + 1])} black among c(0 .. {T}), {sum(c[:T + 1]) / (T + 1):.4f}")


def run_lemmas(args: argparse.Namespace) -> None:
    print(f"L1, every row of width {args.run_width}: {check_run_lemma(args.run_width)} rows", flush=True)
    adv = check_erosion(args.erosion_width)
    print(f"L2, L3, every word of {args.erosion_width} cells: {sum(adv.values())} segments, advances {adv}", flush=True)
    print(f"L4, {args.trials} random plays of {args.steps} moves: {check_moving_frame(args.trials, args.steps)} cells",
          flush=True)
    print(f"L4 in the rest frame (walls), every word of {args.erosion_width - 4} cells: "
          f"{check_walls(args.erosion_width - 4)} cells", flush=True)
    print(f"front speed, every row of width {args.front_width}: {check_front_speed(args.front_width)} runs", flush=True)
    print(f"L5, {args.trials} random plays of {args.steps} moves: {check_shielding(args.trials, args.steps)} flips",
          flush=True)
    print(f"L6(a), every word of {args.trap_width} cells: {check_trapezoid(args.trap_width)} intervals", flush=True)
    print(f"L6(b), every row of width {args.trap_width}: {check_boundary_trapezoid(args.trap_width)} pairs", flush=True)
    rows = reach(args.reach, progress=True)
    worst = max(r.longest - slope_bound(r.t) for r in rows)
    print(f"L7, every state reachable at t <= {args.reach}: largest m(x(t)) - (3t + 9)/5 = {worst:.1f}; largest prefix "
          + ", ".join(f"{r.longest} at t = {r.t}" for r in rows if r.t in (60, 100, args.reach)))


def run_reach(args: argparse.Namespace) -> None:
    rows = reach(args.steps, progress=True)
    print("t N(t) log2 N(t) E(t) largest prefix")
    for r in rows:
        if r.t % args.every == 0 or r.t == args.steps:
            print(r.t, r.states, f"{np.log2(r.states):.2f}", r.best, r.longest)
    if args.steps >= 20:
        a, b = rows[-11], rows[-1]
        print(f"log2 N grows by {(np.log2(b.states) - np.log2(a.states)) / 10:.3f} per step from t = {a.t} to {b.t}")


def run_windows(args: argparse.Namespace) -> None:
    for s in _ints(args.times):
        G = windows(s, args.width, progress=True)
        print(f"s = {s}: G(s, s + w) for w = 5, 10, ...:", " ".join(f"{w}:{G[w - 1]}" for w in range(5, args.width + 1, 5)),
              f"; excess over {args.rate} w at w = 30: {G[29] - args.rate * 30:.2f}" if args.width >= 30 else "")


def run_costs(args: argparse.Namespace) -> None:
    for s in _ints(args.times):
        table = costs(s, args.width, args.cells, progress=True)
        cols = [k for k in range(2, args.width // 2 + 1, 2)]
        print(f"s = {s}: fewest zeros in the 2k moves before a prefix >= k, k = {cols}:",
              [table[2 * k - 1][k - 1] if len(table[2 * k - 1]) >= k else None for k in cols])


def run_lambda(args: argparse.Namespace) -> None:
    M, D = lambda_values(args.steps, progress=True)
    E = values(args.steps, progress=True)
    print("T E(T) D(T) M(T) (E(T) + T + 2)/2")
    for T in range(args.every, args.steps + 1, args.every):
        print(T, E[T], D[T], M[T], (E[T] + T + 2) / 2)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("values")
    p.add_argument("--steps", type=int, default=140)
    p.add_argument("--every", type=int, default=20)
    p.add_argument("--low", type=int, default=100)
    p.set_defaults(func=run_values)
    p = sub.add_parser("beam")
    p.add_argument("--steps", type=int, default=1000)
    p.add_argument("--width", type=int, default=20000)
    p.add_argument("--every", type=int, default=250)
    p.add_argument("--check", type=int, default=0, help="compare with E(T) for even T up to this bound (<= 255)")
    p.add_argument("--out", default="")
    p.set_defaults(func=run_beam)
    p = sub.add_parser("greedy")
    p.add_argument("--steps", type=int, default=40000)
    p.add_argument("--checkpoints", type=_ints, default=[100, 1000, 3000, 20000])
    p.add_argument("--tail", type=int, default=20000)
    p.add_argument("--pmax", type=int, default=5000)
    p.set_defaults(func=run_greedy)
    p = sub.add_parser("lemmas")
    p.add_argument("--run-width", type=int, default=16)
    p.add_argument("--erosion-width", type=int, default=18)
    p.add_argument("--front-width", type=int, default=14)
    p.add_argument("--trap-width", type=int, default=16)
    p.add_argument("--trials", type=int, default=60)
    p.add_argument("--steps", type=int, default=80)
    p.add_argument("--reach", type=int, default=100)
    p.set_defaults(func=run_lemmas)
    p = sub.add_parser("reach")
    p.add_argument("--steps", type=int, default=100)
    p.add_argument("--every", type=int, default=10)
    p.set_defaults(func=run_reach)
    p = sub.add_parser("windows")
    p.add_argument("--times", default="30,60,90")
    p.add_argument("--width", type=int, default=40)
    p.add_argument("--rate", type=float, default=0.665)
    p.set_defaults(func=run_windows)
    p = sub.add_parser("costs")
    p.add_argument("--times", default="60")
    p.add_argument("--width", type=int, default=40)
    p.add_argument("--cells", type=int, default=60)
    p.set_defaults(func=run_costs)
    p = sub.add_parser("lambda")
    p.add_argument("--steps", type=int, default=60)
    p.add_argument("--every", type=int, default=10)
    p.set_defaults(func=run_lambda)
    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
