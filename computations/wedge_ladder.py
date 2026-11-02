"""The chart between the zero-driven left half of the kit's `Q01` and the kit's wedge streams, by forward simulation.

The zero-driven left half runs rule 30 on the columns p < 0 with column 0 held white (kit `Rule30DrivenLeft.L` with the
driver `fun _ => false`). For a start s, H(t, p) is the cell at step t and column p. The endpoint stream is
e_j = pair(H(2j + 1, -1), H(2j + 1, -2)), with the kit's encoding pair(a, b) = 2a + b. `Rule30Open.PeriodTwo.WedgeLadderQ01`
proves that while column -1 is black at the even steps, peel^d(inverse e)(t) = pair(H(t, -(2d + t + 2)), H(t, -(2d + t + 3)))
(`zpeel_chart`), and that e_j is binary when column -1 is black at step 2j + 2 (`zend_binary`); since column 0 is
white, the converse holds too, by the same update.

So a start whose leftmost black cell is at -m, m = 2n + 2, has wedge n e t = pair(1, 0) = 2 at every t the chart reaches,
and a start with leftmost black cells at -m and -(m - 1), m = 2n + 3, has wedge n e t = pair(1, 1) = 3. Its endpoint is a
forced run of `computations.wedge_hypotheses` for the value c = 2 or 3, and it stays binary exactly as long as column -1
stays black at the even steps. This module checks that by simulation against the forced runs of `wedge_hypotheses`,
an independent computation (backward, through the antidiagonals of the cone).

`starts(n, c)` builds every such start whose column -1 is black at the even steps 0 .. m - 2 from the column itself, by
left permutivity (kit `Rule30DrivenLeft.barrier_exists`: the column at steps 0 .. m - 2 fixes the cells -1 .. -(m - 1)):
2^n starts for c = 2 (the odd steps 1 .. 2n - 1 are free) and the starts among 2^(n + 1) with cell -(m - 1) black for
c = 3. `ladder(n, c)` runs them forward, reads the endpoint, and compares it with the forced run of its first n symbols.

    python -m computations.wedge_ladder --n 3 12     # n = 3 .. 12, both values of c: a few seconds
"""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass

import numpy as np
from tqdm.auto import tqdm

from computations import wedge_hypotheses as wh


def width(n: int, c: int) -> int:
    """The position m of the leftmost black cell of the starts that chart to depth n and value c."""
    return 2 * n + 2 + (1 if c == 3 else 0)


def starts_from_column(col: np.ndarray) -> np.ndarray:
    """The cells -1 .. -(K + 1) of the start whose column -1 reads col at steps 0 .. K (column 0 white)."""
    # col: (B, K + 1) column -1 at steps 0 .. K
    B, K1 = col.shape
    cur = col.astype(bool)  # (B, K + 1): column -1 at steps 0 .. K
    right = np.zeros_like(cur)  # (B, K + 1): column 0, white
    out = np.zeros((B, K1), dtype=bool)  # (B, K + 1): cell -(i + 1) of the start
    out[:, 0] = cur[:, 0]
    for i in range(1, K1):
        # column -(i + 1) at steps 0 .. K - i: H(t, p - 1) = H(t + 1, p) xor (H(t, p) or H(t, p + 1))
        nxt = cur[:, 1:] ^ (cur[:, :-1] | right[:, :-1])  # (B, K + 1 - i)
        right, cur = cur[:, :-1], nxt
        out[:, i] = cur[:, 0]
    return out


def starts(n: int, c: int) -> np.ndarray:
    """Every start with leftmost black cell at -m (and, for c = 3, cell -(m - 1) black) whose column -1 is black at the
    even steps 0 .. m - 2. Row b, entry i is cell -(i + 1)."""
    m = width(n, c)
    K = m - 2
    odd = list(range(1, K + 1, 2))  # the free steps
    free = ((np.arange(1 << len(odd))[:, None] >> np.arange(len(odd))[None, :]) & 1).astype(bool)  # (2^f, f)
    col = np.ones((free.shape[0], K + 1), dtype=bool)  # (2^f, K + 1)
    col[:, odd] = free
    cells = starts_from_column(col)  # (2^f, m - 1)
    s = np.concatenate([cells, np.ones((cells.shape[0], 1), dtype=bool)], axis=1)  # (2^f, m)
    if c == 3:
        s = s[s[:, m - 2]]
    return s


def simulate(s: np.ndarray, steps: int) -> np.ndarray:
    """The zero-driven left half from the starts s for `steps` steps. Entry [b, t, i] is H(t, -(i + 1))."""
    # s: (B, m)
    B, m = s.shape
    W = m + steps + 2
    row = np.zeros((B, W + 1), dtype=bool)  # (B, W + 1): columns -1 .. -W, then a white guard
    row[:, :m] = s
    out = np.zeros((B, steps + 1, W), dtype=bool)  # (B, steps + 1, W)
    out[:, 0] = row[:, :W]
    for t in range(steps):
        rightn = np.concatenate([np.zeros((B, 1), dtype=bool), row[:, :W]], axis=1)  # (B, W + 1): column p + 1
        leftn = np.concatenate([row[:, 1:], np.zeros((B, 1), dtype=bool)], axis=1)  # (B, W + 1): column p - 1
        row = leftn ^ (row | rightn)  # (B, W + 1)
        row[:, W] = False
        out[:, t + 1] = row[:, :W]
    return out


def first_white_even(h: np.ndarray) -> np.ndarray:
    """The first even step at which column -1 is white (steps + 1 if none)."""
    # h: (B, T + 1, W)
    col = h[:, ::2, 0]  # (B, T // 2 + 1)
    white = ~col
    first = np.where(white.any(axis=1), 2 * white.argmax(axis=1), h.shape[1])  # (B,)
    return first


def endpoint(h: np.ndarray) -> np.ndarray:
    """e_j = pair(H(2j + 1, -1), H(2j + 1, -2)) for every odd step in range."""
    # h: (B, T + 1, W)
    odd = h[:, 1::2]  # (B, J, W)
    return (2 * odd[:, :, 0].astype(np.uint8) + odd[:, :, 1].astype(np.uint8))  # (B, J)


@dataclass(frozen=True, slots=True)
class Ladder:
    n: int
    c: int
    m: int
    count: int  # number of starts
    prefixes: int  # distinct free prefixes e_0 .. e_{n-1} among them
    agree: bool  # every endpoint equals the forced run of its prefix, up to its first non-binary symbol
    steps_match: bool  # first white even step = 2K + 2, K the number of binary symbols of the forced run
    latest: int  # the latest first white even step over the starts
    max_reach: int  # max K over the forced runs of wedge_hypotheses (M(n, c) = max_reach - n)


def ladder(n: int, c: int) -> Ladder:
    """Run every start of `starts(n, c)` forward and compare its endpoint with `wedge_hypotheses.forced_word`."""
    m = width(n, c)
    cap = 4 * n + 8
    s = starts(n, c)  # (B, m)
    h = simulate(s, 2 * cap + 4)  # (B, T + 1, W)
    fw = first_white_even(h)  # (B,)
    e = endpoint(h)  # (B, J)
    agree = True
    steps_match = True
    prefixes = set()
    for b in range(s.shape[0]):
        pre = int(sum(((int(e[b, i]) - 1) & 1) << i for i in range(n)))
        prefixes.add(pre)
        word = wh.forced_word(n, c, pre, cap=cap)  # (K,)
        K = len(word)
        if tuple(int(x) for x in e[b, :K]) != word:
            agree = False
        if K < cap and int(fw[b]) != 2 * K + 2:
            steps_match = False
    reach = int(wh.forced_runs(n, c, cap=cap).reach.max())
    return Ladder(n, c, m, int(s.shape[0]), len(prefixes), agree, steps_match, int(fw.max()), reach)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--n", nargs=2, type=int, default=[3, 10])
    a = ap.parse_args()
    print("n  c  m  starts  prefixes  agree  steps  latest-white-step  2m  M(n,c)  BWH(n,c)")
    for n in tqdm(range(a.n[0], a.n[1] + 1), desc="n", file=sys.stderr):
        for c in (2, 3):
            r = ladder(n, c)
            M = r.max_reach - n
            print(r.n, r.c, r.m, r.count, r.prefixes, r.agree, r.steps_match, r.latest, 2 * r.m, M,
                  "holds" if M < n + 2 else "fails", flush=True)


if __name__ == "__main__":
    main()
