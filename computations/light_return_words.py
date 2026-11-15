"""Periodic points of the right-edge map Phi(y) = y xor (2y or 4y), seen as walks of cyclic words, and the one state
from which every non-rain walk starts.

Bit e of Phi^t(y), as a function of t in Z/L, is the word W_e. They obey W_e(t + 1) = W_e(t) xor (W_(e-1) or
W_(e-2))(t); for odd y, W_(-1) = W_(-2) = 0 and W_0 = 1...1. The state after word e is the pair (W_(e-1), W_e).

* `solve`: the solution with W(0) = 0 of the cyclic difference equation (the other one is its complement).
* `children`: the two successor states, or none when the right side has odd weight.
* `walk_counts`: the number of walks W_0..W_(n-1) from the start, for n = 1..depth.
* `brute_counts`: the number of odd y modulo 2^n with Phi^L(y) = y modulo 2^n, by applying Phi (an independent check).
* `branch_tree`: the size of the tree of walks from the branch state (P, P), P = 0101..., and its depth; finite for
  L = 2, ..., 2^k_max (computed), which is the conjecture for those L.
* `fertility_counts`: the inner nodes of that tree, those with |v| odd, and the violations of the parity of Lemma 3.

    python -m computations.light_return_words --k-max 6
"""

from __future__ import annotations

import argparse
import sys

from tqdm.auto import tqdm


State = tuple[int, int]  # (W_(e-1), W_e), bit t of a word is time t


def solve(right: int, L: int) -> int:
    """The word W with W(0) = 0 and W(t + 1) = W(t) xor right(t) for t < L - 1."""
    word = 0
    bit = 0
    for t in range(L - 1):
        bit ^= (right >> t) & 1
        word |= bit << (t + 1)
    return word


def children(state: State, L: int) -> list[State]:
    """The successor states of (u, v): (v, w) and (v, not w), or none when u or v has odd weight."""
    u, v = state
    right = u | v
    if bin(right).count("1") % 2:
        return []
    w = solve(right, L)
    return [(v, w), (v, w ^ ((1 << L) - 1))]


def walk_counts(L: int, depth: int) -> list[int]:
    """Entry n - 1 is the number of walks W_0..W_(n-1) from the start (0, 1...1), for n = 1..depth."""
    level: dict[State, int] = {(0, (1 << L) - 1): 1}
    counts = [1]
    for _ in range(depth - 1):
        nxt: dict[State, int] = {}
        for state, mult in level.items():
            for child in children(state, L):
                nxt[child] = nxt.get(child, 0) + mult
        level = nxt
        counts.append(sum(level.values()))
    return counts


def phi(y: int, n: int) -> int:
    """Phi(y) modulo 2^n."""
    return (y ^ ((y << 1) | (y << 2))) & ((1 << n) - 1)


def brute_counts(L: int, depth: int) -> list[int]:
    """Entry n - 1 is the number of odd y modulo 2^n with Phi^L(y) = y modulo 2^n, for n = 1..depth."""
    out = []
    for n in range(1, depth + 1):
        count = 0
        for y in range(1, 1 << n, 2):
            z = y
            for _ in range(L):
                z = phi(z, n)
            count += z == y
        out.append(count)
    return out


def alternating(L: int) -> int:
    """The word P = 0101... of length L (P(t) = t mod 2)."""
    return sum(1 << t for t in range(1, L, 2))


def branch_tree(L: int, limit: int = 10**7) -> tuple[int, int] | None:
    """(number of nodes, depth) of the tree of walks from (P, P); None if it has more than `limit` nodes."""
    P = alternating(L)
    level = [(P, P)]
    nodes, depth = 1, 0
    while level:
        nxt = [child for state in level for child in children(state, L)]
        if not nxt:
            return nodes, depth
        depth += 1
        nodes += len(nxt)
        if nodes > limit:
            return None
        level = nxt
    return nodes, depth


def rain_states(L: int) -> set[State]:
    """The four states the rain walks pass through after the start: (1...1, A) and (A, not A), A alternating."""
    full = (1 << L) - 1
    P = alternating(L)
    return {(full, P), (full, P ^ full), (P, P ^ full), (P ^ full, P)}


def fertility_counts(L: int) -> tuple[int, int, int]:
    """Over the whole tree from (P, P): (inner nodes, inner nodes (u, v) with |v| odd, nodes violating Lemma 3).

    Lemma 3: at an inner node with |v| odd exactly one child has children; with |v| even both or neither do.
    """
    P = alternating(L)
    level = [(P, P)]
    inner = odd = bad = 0
    while level:
        nxt: list[State] = []
        for state in level:
            kids = children(state, L)
            if not kids:
                continue
            inner += 1
            has = [bool(children(c, L)) for c in kids]
            if bin(state[1]).count("1") % 2:
                odd += 1
                bad += sum(has) != 1
            else:
                bad += has[0] != has[1]
            nxt.extend(kids)
        level = nxt
    return inner, odd, bad


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--k-max", type=int, default=6)
    args = parser.parse_args(argv)
    for k in tqdm(range(1, args.k_max + 1), desc="periods", file=sys.stderr):
        L = 1 << k
        inner, odd, bad = fertility_counts(L)
        print(f"L = {L:3d}: tree from (P, P): (nodes, depth) = {branch_tree(L)}; inner nodes {inner}, "
              f"with |v| odd {odd}, violations of Lemma 3 {bad}")


if __name__ == "__main__":
    main()
