"""doubling_gaps against a cell-by-cell run of the diagonal recursion, the local backward words, a direct Rule 30 run of
the single cell, and the numbers the entry quotes."""

from __future__ import annotations

import numpy as np

from computations.doubling_gaps import (anti_classes, anti_word, backward_words, census, census_c, families, gaps_numpy,
                                        half_damage, next_sources, source_graph,
                                        is_anti, least_period, orbit_gap, permutive_check, rot, scalar_gap,
                                        single_cell)
from computations.settled_words import pair_next

U64 = np.uint64


def test_census_against_scalar_run() -> None:
    # m(1..3) = 5, 21, 56 over every anti-periodic word of least period 2p, the regime run cell by cell
    for p, m in ((1, 5), (2, 21), (3, 56)):
        words = [anti_word(lo, p) for lo in range(1 << p) if least_period(anti_word(lo, p), 2 * p) == 2 * p]
        assert all(is_anti(y, p) for y in words)
        assert min(scalar_gap(y, 2 * p, m + 2) for y in words) == m
        c = census(p, 200, progress=False)
        assert c.m == m and len(c.classes) == len(anti_classes(p))
        assert all(min(rot(y, k, 2 * p) for k in range(2 * p)) in c.minimizers() for y in words
                   if scalar_gap(y, 2 * p, m) == m)


def test_c_program_against_numpy() -> None:
    c = census(5, 230, progress=False)
    ys, gap = census_c(5, 230, progress=False, optimize=False)
    assert np.array_equal(ys, c.classes) and np.array_equal(gap, c.gap)
    assert c.m == 23 and c.minimizers() == [0x1f]
    g, x = orbit_gap(8, families(4)["block"], 200, optimize=False)
    assert g == 88 and x != 0
    assert orbit_gap(8, 0xf, 50, optimize=False)[0] == 51  # stopped by the cap


def test_white_step_identity() -> None:
    # D_{j+4} white iff D_j = D_{j+1} and D_{j+2}: sinks built backward by the local step, and forward words
    rng = np.random.default_rng(0)
    for P in (4, 6, 8):
        for x in rng.integers(1, 1 << P, size=12):
            E = backward_words(int(x), P, 4)  # E_i = D_{w'-i}
            assert E[4] == E[3] & E[2]
        a = rng.integers(0, 1 << P, size=200).astype(U64)  # (200,)
        b = rng.integers(1, 1 << P, size=200).astype(U64)  # (200,)
        c, _ = pair_next(a, b, P)
        ok = c != 0  # (200,)
        d, _ = pair_next(b[ok], c[ok], P)
        ok2 = d != 0
        e, _ = pair_next(c[ok][ok2], d[ok2], P)
        assert np.array_equal(e == 0, a[ok][ok2] == (b[ok][ok2] & c[ok][ok2]))


def test_permutive_radius() -> None:
    # E_i(t) reads x(t .. t + floor((i-1)/2)) and, for odd i, flips with the last cell
    assert all(permutive_check(i, 7) for i in (3, 4, 5))


def test_single_cell_regimes() -> None:
    rows = single_cell(steps=700, depth=420, cap=400, last=False, progress=False)
    assert [r.white for r in rows] == [2, 7, 28, 399]
    assert [r.model_gap for r in rows[:3]] == [5, 21, 371]
    assert [r.next_white - r.white for r in rows[:3]] == [5, 21, 371]
    assert [r.weight_before % 2 for r in rows] == [1, 1, 1, 1]


def test_half_damage() -> None:
    d = half_damage(0xf, 4, 88)
    assert len(d.weight) == 89 and d.weight[0] == 0 and d.weight[1] == 8 and d.weight[2] == 0 and d.weight[-1] == 0
    assert not ((d.weight[1:] == 0) & (d.weight[:-1] == 0))[1:].any()  # never zero at two consecutive depths
    assert (d.weight % 2 == 0).all()


def test_source_graph_against_regimes() -> None:
    # every regime of period P <= 10 with gap g <= 24 has its least period among the cycles of the source graph of g,
    # and every anti-periodic one has 2p among the two-track cycles
    graphs = {g: source_graph(g) for g in range(5, 25)}
    assert [g for g, s in graphs.items() if s.two_cycles] == [5, 21, 23]
    assert [g for g, s in graphs.items() if s.one_cycles is None] == [8, 14, 16]
    for P in range(2, 11):
        ys = np.arange(1, 1 << P, dtype=U64)  # (2^P - 1,)
        gap = gaps_numpy(P, ys, 24)  # (2^P - 1,)
        for y, g in zip(ys.tolist(), gap.tolist()):
            if g > 24:
                continue
            if g < 5:  # only the black word, gap 3 (D_{w+3} is the complement of Y one step later)
                assert y == (1 << P) - 1 and g == 3
                continue
            lp = least_period(y, P)
            if graphs[g].one_cycles is not None:
                assert lp in graphs[g].one_cycles
            if lp % 2 == 0 and is_anti(rot(y, 0, lp) & ((1 << lp) - 1), lp // 2):
                assert lp in graphs[g].two_cycles


def test_next_sources() -> None:
    # Y(t + 1) = Y(t) xor x(t) behind a white diagonal: anti-periodic of period 2P for odd weight, two complements else
    for x, P in ((0b0111, 4), (0b0011, 4), (0x72fadae3, 32)):
        out = next_sources(x, P)
        for y, Q in out:
            assert all(((y >> ((t + 1) % Q)) & 1) ^ ((y >> t) & 1) == (x >> (t % P)) & 1 for t in range(Q))
        assert len(out) == (1 if bin(x).count("1") % 2 else 2)
        if len(out) == 1:
            assert is_anti(out[0][0], P)
