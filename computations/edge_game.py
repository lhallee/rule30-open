"""The edge game: the least depth gain an adversary can force on the left edge of a difference pattern, as a
measurement.

Two copies X, Y of a Rule 30 row agree left of cell L and differ at L. A state of the game with window k is the cells
of both copies on [L - 1, L + k], equal at L - 1: 2k + 2 bits. One step:

1. A fresh fair cell c1 enters at L - 2 (shared; the settled side, modeled as coins).
2. The adversary, who sees c1, chooses the cell L + k + 1 of each copy (outside the window).
3. Each copy steps by Rule 30, which gives its next row on [L - 1, L + k]. The new edge L' is the first cell where the
   copies differ, and moves by the edge law of `onset_edge.edge_move`.
4. The window moves to [L' - 1, L' + k]. If L' = L - 1, its left cell is a second fresh fair cell c2. If L' > L, the
   adversary chooses the new cells right of L + k, which nothing inside the window fixes; if the copies agree on the
   whole of [L - 1, L + k], the adversary places the edge at L + k + 1 or L + k + 2 and chooses every cell it does
   not know.

The depth gain of a step is L' - L + 1 (the change of the edge's diagonal L + t). The adversary minimizes the long-run
mean gain; its least value v_k is computed by relative value iteration (`game_value`), with the bounds
min (Th - h) <= v_k <= max (Th - h). Outside the window the adversary is free at every step, so it can play every
strategy of the game with window k + 1 and v_k <= v_{k+1}.

`explicit_actions` enumerates each choice by a direct simulation of the rows, independently of the vectorized table;
`brute_force_value` minimizes over every memoryless deterministic adversary (k = 0) and `lp_value` solves the linear
program of the average-cost game over all adversaries (k <= 2), both from `explicit_actions`.

This is a model, not a theorem about the single cell: the cells left of the edge are a fixed periodic word, not fresh
coins against an adversary that sees them.

    python -m computations.edge_game --kmax 8              # v_0 .. v_8, about 15 s
    python -m computations.edge_game --kmin 9 --kmax 10    # v_9, v_10, about 5.5 min, 1.5 GB
"""

from __future__ import annotations

import argparse
import itertools
import sys
from dataclasses import dataclass

import numpy as np
from scipy.optimize import linprog
from tqdm.auto import tqdm


def encode(s: int, x: list[int], y: list[int]) -> int:
    """The state index: bit 0 the shared cell, bit 1 X(L), then X(L + i), Y(L + i) at bits 2i, 2i + 1 for i >= 1."""
    v = s | x[0] << 1
    for i in range(1, len(x)):
        v |= x[i] << (2 * i) | y[i] << (2 * i + 1)
    return v


def decode(v: int, k: int) -> tuple[int, list[int], list[int]]:
    """The shared cell and the cells L .. L + k of X and Y (Y(L) = not X(L))."""
    s, x0 = v & 1, v >> 1 & 1
    x = [x0] + [v >> (2 * i) & 1 for i in range(1, k + 1)]
    y = [1 - x0] + [v >> (2 * i + 1) & 1 for i in range(1, k + 1)]
    return s, x, y


@dataclass(frozen=True, slots=True)
class Table:
    """The game with window k as arrays over (state, c1, boundary choice)."""

    k: int
    left: np.ndarray  # (N,) the shared cell is white: the edge moves left whatever the adversary does
    nxt: np.ndarray  # (N, 2, 2) for a left move: the next state for c1 and c2
    r: np.ndarray  # (N, 2, 4) the retreat r = L' - L >= 0, or k + 1 if the copies agree on [L - 1, L + k]
    low: np.ndarray  # (N, 2, 4) the known low bits of the next state (r <= k), or its shared cell (r = k + 1)


def build_table(k: int) -> Table:
    """The transitions of the game with window k, vectorized over the states."""
    N = 1 << (2 * k + 2)
    v = np.arange(N, dtype=np.int64)  # (N,)
    s = (v & 1).astype(np.int8)  # (N,)
    X = np.zeros((N, k + 1), dtype=np.int8)  # (N, k + 1): X at L .. L + k
    Y = np.zeros((N, k + 1), dtype=np.int8)  # (N, k + 1)
    X[:, 0] = v >> 1 & 1
    Y[:, 0] = 1 - X[:, 0]
    for i in range(1, k + 1):
        X[:, i] = v >> (2 * i) & 1
        Y[:, i] = v >> (2 * i + 1) & 1
    left = s == 0
    nxt = np.zeros((N, 2, 2), dtype=np.int32)
    r = np.zeros((N, 2, 4), dtype=np.int8)
    low = np.zeros((N, 2, 4), dtype=np.int32)
    for c1 in range(2):
        for b in range(4):
            bx, by = b & 1, b >> 1
            oldX = np.column_stack([np.full(N, c1, np.int8), s, X, np.full(N, bx, np.int8)])  # (N, k + 4): L - 2 .. L + k + 1
            oldY = np.column_stack([np.full(N, c1, np.int8), s, Y, np.full(N, by, np.int8)])  # (N, k + 4)
            newX = oldX[:, :-2] ^ (oldX[:, 1:-1] | oldX[:, 2:])  # (N, k + 2): cells L - 1 .. L + k
            newY = oldY[:, :-2] ^ (oldY[:, 1:-1] | oldY[:, 2:])  # (N, k + 2)
            diff = newX != newY  # (N, k + 2)
            any_ = diff.any(axis=1)
            f = np.where(any_, np.argmax(diff, axis=1), k + 2)  # (N,): first difference, index 0 is cell L - 1
            assert (f[left] == 0).all() and (f[~left] >= 1).all()
            rr = f - 1  # (N,): the retreat, k + 1 if none
            r[:, c1, b] = np.where(left, -1, rr)
            del oldX, oldY
            if b == 0:
                for c2 in range(2):  # left move: window L - 2 .. L + k - 1, shared cell c2
                    code = c2 | newX[:, 0].astype(np.int32) << 1
                    for i in range(1, k + 1):
                        code |= newX[:, i].astype(np.int32) << (2 * i) | newY[:, i].astype(np.int32) << (2 * i + 1)
                    nxt[:, c1, c2] = code
            lo = np.zeros(N, dtype=np.int32)  # (N,)
            nX, nY = newX.astype(np.int32), newY.astype(np.int32)  # (N, k + 2)
            for rv in range(k + 1):  # window L + r - 1 .. L + r + k, known up to L + k
                sel = rr == rv
                code = nX[:, rv] | nX[:, rv + 1] << 1  # (N,): shared cell L + r - 1 (index r), X(L + r)
                for i in range(1, k - rv + 1):
                    code |= nX[:, rv + 1 + i] << (2 * i) | nY[:, rv + 1 + i] << (2 * i + 1)
                lo[sel] = code[sel]
            sel = rr == k + 1
            lo[sel] = newX[sel, k + 1]  # the shared cell L + k when the edge is placed at L + k + 1
            low[:, c1, b] = lo
    return Table(k, left, nxt, r, low)


def option_index(t: Table) -> np.ndarray:
    """For each state, c1 and boundary choice, the position of its value in the vector of `option_values`."""
    k = t.k
    N = len(t.left)
    sizes = [N >> (2 * rv) for rv in range(k + 1)]
    offset = np.concatenate([[0], np.cumsum(sizes)]).astype(np.int64)  # (k + 2,)
    r = np.where(t.r < 0, 0, t.r).astype(np.int64)  # (N, 2, 4); left moves are read from `nxt` instead
    return (offset[r] + t.low).astype(np.int64)  # (N, 2, 4)


def option_values(k: int, h: np.ndarray) -> np.ndarray:
    """gain + the least h over the next states an option leaves to the adversary: for a retreat r <= k, 1 + r + the
    least h over the free cells right of L + k; for agreement on the whole window, the better of the edge at L + k + 1
    (shared cell known) and at L + k + 2 (nothing known)."""
    # h: (N,)
    N = len(h)
    parts = [1 + rv + h.reshape(1 << (2 * rv), N >> (2 * rv)).min(axis=0) for rv in range(k + 1)]
    Hs = h.reshape(-1, 2).min(axis=0)  # (2,): least h over the states with a given shared cell
    parts.append(np.minimum(2 + k + Hs, 3 + k + h.min()))
    return np.concatenate(parts)  # (sum of the sizes + 2,)


def bellman(t: Table, idx: np.ndarray, h: np.ndarray) -> np.ndarray:
    """(Th)(state) = E_c1 min over the adversary's choices of (gain + h(next state))."""
    # idx: (N, 2, 4); h: (N,)
    C = option_values(t.k, h)
    out = np.zeros(len(h))  # (N,)
    for c1 in range(2):
        best = C[idx[:, c1, :]].min(axis=1)  # (N,)
        lmove = 0.5 * (h[t.nxt[:, c1, 0]] + h[t.nxt[:, c1, 1]])  # (N,)
        out += 0.5 * np.where(t.left, lmove, best)
    return out  # (N,)


@dataclass(frozen=True, slots=True)
class GameValue:
    k: int
    states: int
    lower: float  # min (Th - h): the value is at least this
    upper: float  # max (Th - h)
    iterations: int
    h: np.ndarray  # (N,) the relative values


def game_value(k: int, tol: float = 1e-10, max_iter: int = 200000, damping: float = 0.5) -> GameValue:
    """The least long-run mean gain v_k by relative value iteration on the damped operator (1 - a) h + a Th, which has
    the same value and removes periodicity; stops when max (Th - h) - min (Th - h) < tol."""
    t = build_table(k)
    idx = option_index(t)  # (N, 2, 4)
    N = 1 << (2 * k + 2)
    h = np.zeros(N)  # (N,)
    it = 0
    for it in range(1, max_iter + 1):
        Th = bellman(t, idx, h)
        g = Th - h  # (N,)
        lo, hi = float(g.min()), float(g.max())
        if hi - lo < tol:
            break
        h = (1 - damping) * h + damping * Th
        h -= h[0]
    return GameValue(k, N, lo, hi, it, h)


def explicit_actions(k: int) -> dict[tuple[int, int], list[tuple[int, tuple[int, ...]]]]:
    """For every state and c1, the adversary's options as (gain, next states), by direct simulation of the rows: a list
    of one next state, or of two equally likely ones (the coin c2 of a left move). Duplicate options are dropped."""
    N = 1 << (2 * k + 2)
    acts: dict[tuple[int, int], list[tuple[int, tuple[int, ...]]]] = {}
    for v in range(N):
        s, x, y = decode(v, k)
        for c1 in range(2):
            opts: set[tuple[int, tuple[int, ...]]] = set()
            for bx, by in itertools.product(range(2), repeat=2):
                ox = {-2: c1, -1: s, k + 1: bx, **{i: x[i] for i in range(k + 1)}}  # cell -> value, cells rel. to L
                oy = {-2: c1, -1: s, k + 1: by, **{i: y[i] for i in range(k + 1)}}
                nx = {p: ox[p - 1] ^ (ox[p] | ox[p + 1]) for p in range(-1, k + 1)}
                ny = {p: oy[p - 1] ^ (oy[p] | oy[p + 1]) for p in range(-1, k + 1)}
                edge = next((p for p in range(-1, k + 1) if nx[p] != ny[p]), None)
                if edge == -1:  # window -2 .. k - 1 with a fresh shared cell
                    nexts = tuple(sorted(encode(c2, [nx[p] for p in range(-1, k)], [ny[p] for p in range(-1, k)])
                                         for c2 in range(2)))
                    opts.add((0, nexts))
                    continue
                if edge is not None:
                    free = edge  # cells k + 1 .. edge + k of both copies are the adversary's
                    for fill in itertools.product(range(2), repeat=2 * free):
                        fx = {**nx, **{k + 1 + i: fill[2 * i] for i in range(free)}}
                        fy = {**ny, **{k + 1 + i: fill[2 * i + 1] for i in range(free)}}
                        w = encode(fx[edge - 1], [fx[edge + i] for i in range(k + 1)],
                                   [fy[edge + i] for i in range(k + 1)])
                        opts.add((1 + edge, (w,)))
                    continue
                for w in range(N):  # agreement on -1 .. k: the edge at k + 1 (shared cell known) or at k + 2
                    if (w & 1) == nx[k]:
                        opts.add((2 + k, (w,)))
                    opts.add((3 + k, (w,)))
            acts[(v, c1)] = sorted(opts)
    return acts


def policy_gain(P: np.ndarray, c: np.ndarray) -> np.ndarray:
    """The long-run mean cost from each state of a Markov chain with transition matrix P and step cost c."""
    # P: (N, N); c: (N,)
    M = 0.5 * (np.eye(len(c)) + P)  # (N, N): the same limit, aperiodic
    for _ in range(60):
        M = M @ M
        M /= M.sum(axis=1, keepdims=True)  # keep the rows stochastic against rounding
    return M @ c  # (N,)


def brute_force_value(k: int) -> tuple[float, int]:
    """The least long-run mean gain over every memoryless deterministic adversary, and the number of adversaries; the
    least over adversaries of the largest mean gain over the starting states (equal for every state when the value
    does not depend on the state)."""
    acts = explicit_actions(k)
    N = 1 << (2 * k + 2)
    keys = sorted(acts)
    best = np.inf
    count = 0
    for choice in itertools.product(*(range(len(acts[key])) for key in keys)):
        count += 1
        P = np.zeros((N, N))
        c = np.zeros(N)
        for key, a in zip(keys, choice):
            g, nexts = acts[key][a]
            c[key[0]] += 0.5 * g
            for w in nexts:
                P[key[0], w] += 0.5 / len(nexts)
        best = min(best, float(policy_gain(P, c).max()))
    return best, count


def lp_value(k: int) -> float:
    """The value of the average-cost game by linear programming over all adversaries: the largest g with
    g + u(v, c1) <= gain + E[u(next, c1')] for every option, u a function of the state and the coin."""
    acts = explicit_actions(k)
    N = 1 << (2 * k + 2)
    nvar = 1 + 2 * N  # g, u(v, c1)
    rows, rhs = [], []
    for (v, c1), opts in acts.items():
        for g, nexts in opts:
            a = np.zeros(nvar)  # (nvar,)
            a[0] = 1.0
            a[1 + 2 * v + c1] += 1.0
            for w in nexts:
                for c in range(2):
                    a[1 + 2 * w + c] -= 0.5 / len(nexts)
            rows.append(a)
            rhs.append(float(g))
    obj = np.zeros(nvar)
    obj[0] = -1.0
    bounds = [(None, None)] + [(0.0, 0.0)] + [(None, None)] * (2 * N - 1)
    res = linprog(obj, A_ub=np.array(rows), b_ub=np.array(rhs), bounds=bounds, method="highs")
    assert res.status == 0
    return float(-res.fun)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--kmin", type=int, default=0)
    parser.add_argument("--kmax", type=int, default=6)
    parser.add_argument("--check", type=int, default=2, help="largest k checked against the linear program")
    args = parser.parse_args()
    print(f"{'k':>3} {'states':>9} {'v_k lower':>12} {'v_k upper':>12} {'1/v_k':>8} {'iterations':>10}")
    prev = None
    for k in tqdm(range(args.kmin, args.kmax + 1), desc="windows", unit="k", file=sys.stderr, disable=args.kmax < 7):
        gv = game_value(k)
        inv = 1 / gv.upper
        drop = "" if prev is None else f"  1/v falls by {prev - inv:.4f}"
        print(f"{k:>3} {gv.states:>9} {gv.lower:12.8f} {gv.upper:12.8f} {inv:8.4f} {gv.iterations:>10}{drop}", flush=True)
        prev = inv
        if k <= args.check:
            lp = lp_value(k)
            print(f"    linear program over all adversaries: {lp:.8f}", flush=True)
        if k == 0:
            bf, count = brute_force_value(0)
            print(f"    brute force over {count} memoryless deterministic adversaries: {bf:.8f}", flush=True)


if __name__ == "__main__":
    main()
