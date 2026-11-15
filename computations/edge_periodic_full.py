"""The full column graph of the right-edge map against the part reachable from the right edge.

`computations.edge_periodic_points` builds the column graph G_L only from the start (0, 1...1) of an odd seed. Here
every pair of L-bit words is a state, so the live states (those with an infinite forward walk) are the column pairs of
all rows, white right half or not, that come back after L steps moved L cells right; its cycles are the spatially
periodic ones. The classification of periodic points of Phi says that no state reachable from the start is live except
the rain states.

* `full_live_count`: the live states of the full G_L and how many of them are reachable from the start.
* `dead_square_weight`: the weight of the input after the state (u, u), u alternating (the dead branch of period 4).
* `non_antiperiodic_columns`: reachable columns of least period 2^j > 1 that are not complemented by a shift of 2^(j-1).

    python -m computations.edge_periodic_full     # L = 2, 4, 8, 16, 32: under a second
"""

from __future__ import annotations

import sys

from tqdm.auto import tqdm

from computations.edge_periodic_points import State, column_successors, live_states, state_graph


def rotate(w: int, s: int, L: int) -> int:
    """The word t -> w(t + s) on Z/L."""
    full = (1 << L) - 1
    return ((w >> s) | (w << (L - s))) & full


def least_period(w: int, L: int) -> int:
    """The least period of w on Z/L (a power of two since L is)."""
    p = 1
    while rotate(w, p, L) != w:
        p *= 2
    return p


def full_live_count(L: int) -> tuple[int, int]:
    """(live states of the full G_L, live states reachable from the start)."""
    states: list[State] = [(u, v) for u in range(1 << L) for v in range(1 << L)]  # 4^L states
    edges = {s: column_successors(s[0], s[1], L) for s in states}
    live = live_states(states, edges)
    order, _ = state_graph(L)
    return len(live), len(live & set(order))


def dead_square_weight(L: int, a: int = 0) -> int:
    """|w or u| for u = 1010... and w the successor word of (u, u) with w(0) = a: 3L/4 by the block argument; -1 if none."""
    u = int("01" * (L // 2), 2)  # bit t is 1 at even t
    succ = column_successors(u, u, L)
    if not succ:
        return -1  # L = 2: (u, u) has no successor at all
    w = succ[0][1] if (succ[0][1] & 1) == a else succ[1][1]
    return bin(w | u).count("1")


def non_antiperiodic_columns(L: int) -> list[int]:
    """Reachable columns v, least period p > 1, with v(t + p/2) != not v(t) for some t."""
    order, _ = state_graph(L)
    full = (1 << L) - 1
    out: set[int] = set()
    for _, v in order:
        p = least_period(v, L)
        if p > 1 and rotate(v, p // 2, L) != v ^ full:
            out.add(v)
    return sorted(out)


def main() -> None:
    for L in tqdm((2, 4, 8), desc="L", file=sys.stderr):
        live, reach = full_live_count(L)
        bad = non_antiperiodic_columns(L)
        tqdm.write(f"L = {L}: live states of the full graph {live}, reachable and live {reach}; "
                   f"weight after (u, u): {dead_square_weight(L)}; non-antiperiodic reachable columns {len(bad)}")
    for L in (16, 32):
        tqdm.write(f"L = {L}: weight after (u, u): {dead_square_weight(L)}, "
                   f"non-antiperiodic reachable columns {len(non_antiperiodic_columns(L))}")


if __name__ == "__main__":
    main()
