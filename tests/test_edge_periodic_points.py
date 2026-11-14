"""edge_periodic_points against direct iteration of Phi modulo 2^n: the column graph against the residues fixed by
Phi^L, the periodic points against the residues that survive deep lifting, the escape depth against a brute-force
maximum over all odd residues, and the white runs against the table of right-edge-cycles."""

from __future__ import annotations

import numpy as np

from computations import edge_periodic_points as ep


def fixed_residues(L: int, n: int) -> set[int]:
    """The odd y modulo 2^n with Phi^L(y) = y modulo 2^n, by iterating the closed form on all of them."""
    y0 = np.arange(1, 1 << n, 2, dtype=np.int64)  # shape (2^(n-1),)
    y = y0.copy()
    mask = (1 << n) - 1
    for _ in range(L):
        y = (y ^ ((y << 1) | (y << 2))) & mask
    return {int(v) for v in y0[y == y0]}


def walk_residues(L: int, n: int) -> set[int]:
    """The odd y modulo 2^n read off the walks of n - 1 edges from the start of the column graph."""
    _, edges = ep.state_graph(L)
    frontier = [(ep.start_state(L), 1)]
    for e in range(1, n):
        frontier = [(x, y | ((x[1] & 1) << e)) for s, y in frontier for x in edges[s]]
    return {y for _, y in frontier}


def test_rain_swap() -> None:
    a, b = ep.rain(40)
    assert ep.phi(a, 40) == b and ep.phi(b, 40) == a


def test_graph_matches_direct_iteration() -> None:
    for L in (2, 4, 8, 16):
        for n in range(2, 12):
            assert walk_residues(L, n) == fixed_residues(L, n)


def test_periodic_points_survive_lifting() -> None:
    # residues modulo 2^8 of the odd y with Phi^L(y) = y modulo 2^N, N past the escape depth: only +-1/3 survive
    for L in (2, 4, 8, 16):
        T = ep.escape_depth(L)
        N, n = 8 + T + 2, 8
        deep = {y % (1 << n) for y in fixed_residues(L, N)}
        assert deep == set(ep.rain(n))
        assert ep.periodic_points(L, 30) == sorted(ep.rain(30))


def test_escape_depth_is_sharp() -> None:
    # max over odd y modulo 2^N, not +-1/3 there, of (largest n with Phi^L(y) = y mod 2^n) - m(y) is T + 1
    for L in (2, 4, 8):
        T = ep.escape_depth(L)
        N = 14
        best = 0
        for y in range(1, 1 << N, 2):
            m = max(((y ^ r) & -(y ^ r)).bit_length() - 1 if y != r else N for r in ep.rain(N))
            if m >= N - 1:
                continue
            top = max((n for n in range(1, N + 1) if y % (1 << n) in fixed_residues_cache(L, n)), default=0)
            assert top <= m + T + 1
            best = max(best, top - m)
        assert best == T + 1


_cache: dict[tuple[int, int], set[int]] = {}


def fixed_residues_cache(L: int, n: int) -> set[int]:
    """fixed_residues, memoized."""
    if (L, n) not in _cache:
        _cache[(L, n)] = fixed_residues(L, n)
    return _cache[(L, n)]


def test_white_runs() -> None:
    # W(2^m), m = 0..6, from findings/complexity/right-edge-cycles.md
    assert [ep.white_run(k) for k in range(7)] == [0, 2, 3, 5, 6, 8, 14]


def test_period_four_is_free_modulo_16() -> None:
    # every odd residue modulo 16 has Phi^4(y) = y there, and only half of those modulo 32 do
    assert len(fixed_residues(4, 4)) == 8
    assert len(fixed_residues(4, 5)) == 8
