"""The least white density of a strip of J adjacent columns over every Rule 30 orbit, bounded below by a minimum cycle
mean, and the potential that certifies the bound.

The strip's columns a..a+J-1 and kr more columns to its right are the state; the cells a - 1 and a + J + kr are free
inputs at every step. Every orbit's columns follow a path of this graph, so its minimum cycle mean of the white
cells of the strip, per cell, is a lower bound on the lower white density of the strip in every orbit (left
permutivity makes the left input truly free; the right input is an over-approximation, which kr refines).

- `cycle_mean`: Karp's minimum cycle mean, in numpy.
- `potential`: shortest-path potentials for the weight (whites * den - J * num), so that
  phi(next) - phi(now) <= whites * den - J * num on every edge when num/den is at most the cycle mean.
- `extends_right`: whether two given time-periodic columns extend to an orbit to their right with the same period.

    python -m computations.strip_cycle_mean      # J = 2 to kr = 8 and J = 3 to kr = 7, about 10 s
"""

from __future__ import annotations

import itertools
from collections import deque
from fractions import Fraction

import numpy as np
from tqdm.auto import tqdm


def graph(J: int, kr: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Edges (src, dst, white cells of the strip at src) of the strip graph; state index has column a as MSB."""
    W = J + kr
    N = 1 << W
    S = np.array(list(itertools.product((0, 1), repeat=W)), dtype=np.int64)  # (N, W)
    pw = 1 << np.arange(W - 1, -1, -1)  # (W,)
    src, dst, wt = [], [], []
    for fl in (0, 1):
        for fr in (0, 1):
            X = np.concatenate([np.full((N, 1), fl), S, np.full((N, 1), fr)], 1)  # (N, W + 2)
            Nx = X[:, :-2] ^ (X[:, 1:-1] | X[:, 2:])  # (N, W)
            src.append(np.arange(N))
            dst.append(Nx @ pw)
            wt.append((1 - S[:, :J]).sum(1))
    return np.concatenate(src), np.concatenate(dst), np.concatenate(wt)  # each (4 N,)


def cycle_mean(J: int, kr: int, progress: bool = False) -> Fraction:
    """Karp's minimum cycle mean of the white cells per step, divided by J (a density)."""
    src, dst, wt = graph(J, kr)
    N = 1 << (J + kr)
    D = np.full((N + 1, N), np.inf)  # (N + 1, N) least weight of a walk of k edges ending at v
    D[0] = 0
    for k in tqdm(range(1, N + 1), disable=not progress, desc=f"J={J} kr={kr}"):
        np.minimum.at(D[k], dst, D[k - 1][src] + wt)
    best: Fraction | None = None
    for v in range(N):
        if not np.isfinite(D[N, v]):
            continue
        m = max(Fraction(int(D[N, v] - D[k, v]), N - k) for k in range(N) if np.isfinite(D[k, v]))
        best = m if best is None or m < best else best
    assert best is not None
    return best / J


def potential(J: int, kr: int, num: int, den: int) -> dict[int, int]:
    """phi with phi[dst] <= phi[src] + whites * den - J * num on every edge (Bellman-Ford), shifted to min 0."""
    src, dst, wt = graph(J, kr)
    w = wt * den - J * num  # (4 N,)
    N = 1 << (J + kr)
    d = np.zeros(N, dtype=np.int64)  # (N,)
    for _ in range(N + 1):
        nd = d.copy()
        np.minimum.at(nd, dst, d[src] + w)
        if np.array_equal(nd, d):
            break
        d = nd
    else:
        raise ValueError("negative cycle: num/den exceeds the cycle mean")
    d -= d.min()
    return {int(i): int(d[i]) for i in range(N)}


def extends_right(P: int, a: str, b: str) -> bool:
    """Do the time-periodic columns a, b (words of length P, read cyclically) extend to columns b, c, d, ... of an
    orbit, every column of period P? Greatest fixed point over the reachable pairs."""
    M = (1 << P) - 1

    def word(s: str) -> int:
        return sum(int(c) << t for t, c in enumerate(s))

    def valid(u: int, v: int) -> bool:
        return all(((v >> t) & 1) == 0 or ((v >> ((t + 1) % P)) & 1) == 1 - ((u >> t) & 1) for t in range(P))

    def succs(u: int, v: int) -> list[int]:
        base, free = 0, []
        for t in range(P):
            if (v >> t) & 1:
                free.append(t)
            else:
                base |= ((((v >> ((t + 1) % P)) & 1) ^ ((u >> t) & 1)) << t)
        out = []
        for m in range(1 << len(free)):
            w = base
            for i, t in enumerate(free):
                if (m >> i) & 1:
                    w |= 1 << t
            out.append(w & M)
        return out

    start = (word(a), word(b))
    nxt: dict[tuple[int, int], list[tuple[int, int]]] = {}
    dq = deque([start])
    while dq:
        p = dq.popleft()
        if p in nxt:
            continue
        nxt[p] = [(p[1], w) for w in succs(*p)] if valid(*p) else []
        dq.extend(q for q in nxt[p] if q not in nxt)
    alive = {p for p in nxt if nxt[p]}
    while True:
        new = {p for p in alive if any(q in alive for q in nxt[p])}
        if new == alive:
            break
        alive = new
    return start in alive


def main() -> None:
    for kr in range(0, 9):
        print(f"J=2 kr={kr}: {cycle_mean(2, kr, progress=kr >= 7)}")
    for kr in range(0, 8):
        print(f"J=3 kr={kr}: {cycle_mean(3, kr, progress=kr >= 6)}")
    phi = potential(2, 4, 5, 18)
    print("J=2 kr=4 potential for 5/18:", [phi[i] for i in range(64)])
    print("the 9-step minimizing cycle of J=2, kr=4 extends to a time-periodic orbit with period 9:",
          extends_right(9, "011111111", "110101010"))


if __name__ == "__main__":
    main()
