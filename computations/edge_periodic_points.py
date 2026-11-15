"""Periodic points of the right-edge map Phi(y) = y xor (2y or 4y) on the 2-adic integers, by the column graph.

A 2-adic integer y satisfies Phi^L(y) = y exactly when every column b_e(t) = bit e of Phi^t(y) is L-periodic in t. The
columns obey b_e(t + 1) = b_e(t) xor (b_(e-1)(t) or b_(e-2)(t)), with b_(-1) = b_(-2) = 0, so the pairs
(b_(e-1), b_e) of L-periodic columns form a walk in a finite graph on pairs of L-bit words: from (u, v) the equation
w(t + 1) xor w(t) = (u or v)(t) on Z/L is solvable exactly when u or v has an even number of ones, and then has the two
solutions w and its complement. Odd y start at the state (0, 1...1). The periodic points of period dividing L are the
infinite walks from the start, so they are read off the *live* states (states with an infinite forward walk; in a
finite graph, those that reach a cycle).

* `column_successors`, `state_graph`, `live_states`: the graph, its reachable part and its live part.
* `periodic_points`: the odd y modulo 2^bits with Phi^L(y) = y, one per infinite walk (needs finitely many walks).
* `escape_depth`: T, the most edges of a walk that leaves the live part and stays alive in the graph; an odd y other
  than +-1/3 that agrees with one of them to exactly m bits has Phi^L(y) != y modulo 2^n for every n >= m + T + 2.
* `white_run`: J_k, the white cells just left of the single cell's right edge at time 2^k, by Python integers.

    python -m computations.edge_periodic_points --k-max 6     # L = 2, ..., 64: about 5 s
"""

from __future__ import annotations

import argparse
import sys

from tqdm.auto import tqdm


State = tuple[int, int]  # (b_(e-1), b_e): two L-bit words, bit t of a word is the column at time t


def phi(y: int, n: int) -> int:
    """Phi(y) modulo 2^n."""
    return (y ^ ((y << 1) | (y << 2))) & ((1 << n) - 1)


def column_successors(u: int, v: int, L: int) -> list[State]:
    """The states (v, w) with w(t + 1) = w(t) xor (u or v)(t) on Z/L; empty when u or v has an odd weight."""
    full = (1 << L) - 1
    g = (u | v) & full
    if bin(g).count("1") % 2:
        return []
    w, b = 0, 0
    for t in range(L - 1):
        b ^= (g >> t) & 1
        w |= b << (t + 1)
    return [(v, w), (v, w ^ full)]


def start_state(L: int) -> State:
    """(b_(-1), b_0) of an odd y: the white column and the black column."""
    return (0, (1 << L) - 1)


def state_graph(L: int) -> tuple[list[State], dict[State, list[State]]]:
    """The states reachable from the start, in breadth-first order, and the successor lists."""
    start = start_state(L)
    order: list[State] = [start]
    seen: set[State] = {start}
    edges: dict[State, list[State]] = {}
    i = 0
    while i < len(order):
        s = order[i]
        i += 1
        edges[s] = column_successors(s[0], s[1], L)
        for x in edges[s]:
            if x not in seen:
                seen.add(x)
                order.append(x)
    return order, edges


def live_states(order: list[State], edges: dict[State, list[State]]) -> set[State]:
    """The states with an infinite forward walk: prune states without a live successor until none is left."""
    live = set(order)
    preds: dict[State, list[State]] = {s: [] for s in order}
    for s in order:
        for x in edges[s]:
            preds[x].append(s)
    count = {s: len(edges[s]) for s in order}  # live successors, with multiplicity
    stack = [s for s in order if count[s] == 0]
    while stack:
        s = stack.pop()
        if s not in live:
            continue
        live.discard(s)
        for p in preds[s]:
            count[p] -= 1
            if count[p] == 0 and p in live:
                stack.append(p)
    return live


def periodic_points(L: int, bits: int) -> list[int]:
    """The odd y modulo 2^bits with Phi^L(y) = y in the 2-adic integers, one per infinite walk from the start.

    Raises ValueError if some live state other than the start has two live successors (then there are infinitely many)."""
    order, edges = state_graph(L)
    live = live_states(order, edges)
    for s in live:
        if s != start_state(L) and sum(x in live for x in edges[s]) > 1:
            raise ValueError("infinitely many periodic points")
    points: list[int] = []
    for first in edges[start_state(L)]:
        if first not in live:
            continue
        y, s = 1, first
        for e in range(1, bits):
            y |= (s[1] & 1) << e  # bit e of y is b_e(0)
            s = next(x for x in edges[s] if x in live)
        points.append(y)
    return sorted(points)


def escape_depth(L: int) -> int:
    """The most edges of a walk that starts at a non-live successor of a live state and stays in the graph."""
    return max(escape_depth_by_level(L).values())


def escape_depth_by_level(L: int) -> dict[int, int]:
    """The escape depth from the non-live successors of the live states, keyed by the first level j <= 3 of the state.

    Level 0 is the start and level 1 holds the two rain states of level 1. If both remaining live states first occur at
    level 2, the walks of +-1/3 pass through both of them at every level from 2 on, so the value for j = 2 is the
    escape depth after a separation at every level m = j + 1 >= 3, and the value for j = 1 is that for m = 2."""
    order, edges = state_graph(L)
    live = live_states(order, edges)
    dead = [s for s in order if s not in live]
    depth: dict[State, int] = {}
    # the dead states form an acyclic graph: settle them in reverse topological order (iterative depth-first search)
    for root in dead:
        if root in depth:
            continue
        stack: list[tuple[State, int]] = [(root, 0)]
        while stack:
            s, i = stack.pop()
            nxt = [x for x in edges[s] if x not in live]
            if i < len(nxt):
                stack.append((s, i + 1))
                if nxt[i] not in depth:
                    stack.append((nxt[i], 0))
            else:
                depth[s] = max((1 + depth[x] for x in nxt), default=0)
    level: dict[State, int] = {start_state(L): 0}
    frontier = [start_state(L)]
    for j in range(1, 4):
        frontier = [x for s in frontier for x in edges[s] if x in live]
        for x in frontier:
            level.setdefault(x, j)
    out: dict[int, int] = {}
    for s in live:
        for x in edges[s]:
            if x not in live:
                out[level[s]] = max(out.get(level[s], -1), depth[x])
    return out


def rain(n: int) -> tuple[int, int]:
    """(-1/3, 1/3) modulo 2^n."""
    third = pow(3, -1, 1 << n)
    return ((-third) % (1 << n), third)


def white_run(k: int) -> int:
    """J_k: the white cells just left of the right edge of the single cell's row 2^k (Python integers)."""
    t = 1 << k
    n = 2 * t + 1
    y = 1
    for _ in range(t):
        y = phi(y, n)
    j = 1
    while not (y >> j) & 1:
        j += 1
    return j - 1


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--k-max", type=int, default=6, help="periods L = 2^k, 1 <= k <= k_max")
    args = parser.parse_args()
    bits = 64
    for k in tqdm(range(1, args.k_max + 1), desc="periods", file=sys.stderr):
        L = 1 << k
        order, edges = state_graph(L)
        live = live_states(order, edges)
        points = periodic_points(L, bits)
        by_level = escape_depth_by_level(L)
        T = max(by_level.values())
        J = white_run(k) if k <= 10 else -1
        tqdm.write(
            f"L = {L:3d}: reachable {len(order):7d}, live {len(live)}, periodic odd points {len(points)}"
            f" (= +-1/3: {points == sorted(rain(bits))}), escape depth T = {T}, J_k = {J}, T + 2 = {T + 2}"
        )
        tqdm.write(f"         escape depth by level j of the live state left (m = j + 1): {dict(sorted(by_level.items()))}")


if __name__ == "__main__":
    main()
