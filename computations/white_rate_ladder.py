"""The white rate at the first rungs of the right ladder: the kick-free sub-game, the fewest kicks, and a forcing word.

At level k of [the right ladder](../findings/diagonals/right-ladder.md) the left half (cells -1, -2, ...) and cells
1 .. k run exactly from the single cell, and cell k + 1 is a free word f. A *kick* is a time t >= 1 with c(t) = 1 and
x_(-1)(t) = 0, that is c(t) = c(t + 1) = 1. Without kicks the left half from time 1 on is the zero-boundary half line
(Rule 30 on cells <= -1 with cell 0 held white) started from one black cell at -1
([the white rate](../negative-results/diagonals/white-rate-ladder.md)).

* `zero_boundary_columns`: columns -1 and -2 of that half line at times 1 .. T.
* `kick_free_white`: at level 1, the most white cells among c(1 .. T) over the plays with no kick after time 0, by a
  dynamic program over the four states (c, x_1) reading column -1.
* `fewest_kicks`: the fewest kicks at times 1 .. T over the plays of level k, by a dynamic program over
  (left half, c, x_1 .. x_k), with a bound on the kicks kept.
* `forces_kick`: whether a word read in column -1 forces a kick from every state (c, x_1 .. x_k) and every free word.

    python -m computations.white_rate_ladder kickfree --steps 1000000   # the kick-free sub-game to 10^6 (about 45 s)
    python -m computations.white_rate_ladder kicks --steps 150          # fewest kicks at levels 1, 2, 3 (seconds)
    python -m computations.white_rate_ladder force --word 0010000      # the forcing word at levels 1 to 5 (seconds)
"""

from __future__ import annotations

import argparse
from itertools import product

import numpy as np
from tqdm.auto import tqdm


def zero_boundary_columns(T: int, progress: bool = False) -> tuple[np.ndarray, np.ndarray]:
    """Columns -1 and -2 of Rule 30 on the cells <= -1 with cell 0 held white, started at time 1 from one black cell
    at -1; entry t of each array is the cell at time t (entry 0 unused). The row is an integer with bit j the cell
    -(j + 1), and one step is (x >> 1) xor (x or (x << 1)): bit j reads bits j + 1 (cell -j - 2), j and j - 1."""
    y = np.zeros(T + 2, dtype=np.uint8)  # (T + 2,): column -1
    z = np.zeros(T + 2, dtype=np.uint8)  # (T + 2,): column -2
    x = 1
    for t in tqdm(range(1, T + 2), desc="zero-boundary half line", disable=not progress, leave=False):
        y[t] = x & 1
        z[t] = (x >> 1) & 1
        x = (x >> 1) ^ (x | (x << 1))
    return y, z


def kick_free_white(y: np.ndarray, T: int, checkpoints: tuple[int, ...] = ()) -> dict[int, int]:
    """The most white cells among c(1 .. t) over the kick-free plays of level 1, at t = T and at each checkpoint;
    y is column -1 of the zero-boundary half line (`zero_boundary_columns`). The states are (c, x_1) with the fewest
    black centers; c(1) = 1 and x_1(1) is free."""
    # y: (T + 2,)
    big = 1 << 60
    cost = {(1, 0): 1, (1, 1): 1}
    out: dict[int, int] = {}
    for t in range(1, T):
        yt, nxt = int(y[t]), int(y[t + 1])
        new: dict[tuple[int, int], int] = {}
        for (c, x1), v in cost.items():
            cn = yt ^ (c | x1)
            if cn == 1 and nxt == 0:
                continue  # a kick at time t + 1
            for f in (0, 1):
                key = (cn, c ^ (x1 | f))
                new[key] = min(new.get(key, big), v + cn)
        cost = new
        if t + 1 in checkpoints:
            out[t + 1] = (t + 1) - min(cost.values())
    out[T] = T - min(cost.values())
    return out


def fewest_kicks(k: int, T: int, bound: int) -> int | None:
    """The fewest kicks at times 1 .. T over the plays of level k (cells 1 .. k exact, cell k + 1 free), or None if
    every play has more than `bound` kicks. States are (left half, c, x_1 .. x_k): the left half is an integer with
    bit j the cell -(j + 1), and bit i - 1 of R is x_i."""
    states = {(0, 1, 0): 0}
    mask = (1 << k) - 1
    for t in range(T + 1):
        new: dict[tuple[int, int, int], int] = {}
        for (x, c, R), v in states.items():
            nv = v + int(t >= 1 and c == 1 and not (x & 1))
            if nv > bound:
                continue
            if t == T:
                new[(0, 0, 0)] = min(new.get((0, 0, 0), bound + 1), nv)
                continue
            for f in (0, 1):
                x1 = (R & 1) if k >= 1 else f
                cn = (x & 1) ^ (c | x1)
                xn = (x >> 1) ^ (x | ((x << 1) | c))
                Rn = ((((R << 1) | c) & mask) ^ (R | ((R | (f << k)) >> 1))) & mask if k >= 1 else 0
                new[(xn, cn, Rn)] = min(new.get((xn, cn, Rn), bound + 1), nv)
        states = new
        if not states:
            return None
    return min(states.values())


def forces_kick(k: int, word: str) -> bool:
    """Whether reading `word` in column -1 forces a kick (c = 1 where the word reads 0) at level k from every state
    (c, x_1 .. x_k) and every free word."""
    ys = [int(ch) for ch in word]
    for c0, *xs0 in product((0, 1), repeat=k + 1):
        for free in product((0, 1), repeat=len(ys)):
            c, xs, kicked = c0, list(xs0), False
            for t, yt in enumerate(ys):
                if c == 1 and yt == 0:
                    kicked = True
                    break
                cn = yt ^ (c | (xs[0] if k else free[t]))
                xs = [(xs[i - 1] if i else c) ^ (xs[i] | (xs[i + 1] if i + 1 < k else free[t])) for i in range(k)]
                c = cn
            if not kicked:
                return False
    return True


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("mode", choices=("kickfree", "kicks", "force"))
    parser.add_argument("--steps", type=int, default=150)
    parser.add_argument("--word", default="0010000")
    args = parser.parse_args()
    if args.mode == "kickfree":
        T = args.steps
        y, z = zero_boundary_columns(T, progress=True)
        falls = int(np.sum((y[1:T] == 1) & (y[2:T + 1] == 0)))
        print(f"column -1 to t = {T}: {falls} falls, {falls / T:.4f} per step; column -2: density {z[1:T].mean():.4f}")
        marks = tuple(m for m in (150, 1000, 10_000, 100_000) if m < T)
        for t, white in sorted(kick_free_white(y, T, marks).items()):
            print(f"t = {t}: most white among c(1 .. t) without kicks {white} ({white / t:.4f})")
    if args.mode == "kicks":
        for k, bound in ((1, 4), (2, 4), (3, 8)):
            print(f"level {k}: fewest kicks at times 1 .. {args.steps}: {fewest_kicks(k, args.steps, bound)}")
    if args.mode == "force":
        for k in range(1, 6):
            print(f"level {k}: {args.word} forces a kick from every state: {forces_kick(k, args.word)}")


if __name__ == "__main__":
    main()
