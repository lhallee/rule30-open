"""Tests for computations/wedge_hypotheses.py: the table of phi, the kit's `smallControl` by the kit's own recursion, the
forced runs against a brute force over every binary word (by the kit's definition, one cone row at a time), and the C
search against the Python one."""

from __future__ import annotations

import functools
import itertools

import numpy as np

from computations import wedge_hypotheses as wh

SMALL_CONTROL = (1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1)  # kit `smallControl`


def recursive_wedge(n: int, e: tuple[int, ...], t: int) -> int:
    """wedge n e t by the kit's recursions on cone and peelPow, as written."""

    @functools.cache
    def cone(t: int, j: int) -> int:
        if t == 0:
            return wh.boundary(e[j])
        if t == 1:
            return wh.phi(e[j], wh.boundary(e[j + 1]))
        return wh.phi(cone(t - 2, j + 1), cone(t - 1, j + 1))

    @functools.cache
    def peel_pow(m: int, s: int) -> int:
        return cone(s, 0) if m == 0 else wh.phi(peel_pow(m - 1, s), peel_pow(m - 1, s + 1))

    return peel_pow(n, t)


def brute_counts(n: int, c: int, hard_core: bool, L: int) -> int:
    """Binary words of length L whose wedge is c at every t < L - n (and, with the guard, with no 1 after a 1 at
    positions >= n), by `kit_wedge` on all of them at once."""
    e = np.array(list(itertools.product((1, 2), repeat=L)), dtype=np.uint8).reshape(-1, L)  # (2^L, L)
    ok = (wh.kit_wedge(n, e) == c).all(axis=1)  # (2^L,)
    if hard_core:
        ok &= ~((e[:, n - 1:L - 1] == 1) & (e[:, n:] == 1)).any(axis=1)
    return int(ok.sum())


def test_phi_bijective_and_square() -> None:
    assert wh.phi_bijective()
    group = wh.phi_group()
    assert len(group) == 8
    edges = set(wh.EDGES)
    assert frozenset((1, 2)) in edges
    for g in group:
        assert {frozenset(g[x] for x in edge) for edge in edges} == edges


def test_small_control() -> None:
    assert [recursive_wedge(5, SMALL_CONTROL, t) for t in range(8)] == [3] * 8
    prefix = sum((s - 1) << i for i, s in enumerate(SMALL_CONTROL[:5]))
    assert wh.forced_word(5, 3, prefix, cap=13) == SMALL_CONTROL
    assert wh.max_constant(5, 3) >= 8


def test_dependence() -> None:
    for t in range(8):
        assert wh.dependence(t, 9, trials=60) == set(range(t // 2, t + 1))


def test_forced_runs_against_brute_force() -> None:
    for n in range(1, 6):
        for c in (2, 3):
            for hard_core in (False, True):
                runs = wh.forced_runs(n, c, hard_core, cap=2 * n + 2)
                for L in range(n, 2 * n + 3):
                    assert runs.counts[L] == brute_counts(n, c, hard_core, L), (n, c, hard_core, L)


def test_witnesses() -> None:
    e = np.array(list(itertools.product((1, 2), repeat=12)), dtype=np.uint8)  # (4096, 12)
    brute = {tuple(int(x) for x in w) for w in e[(wh.kit_wedge(5, e)[:, :7] == 3).all(axis=1)]}
    assert set(wh.bwh_witnesses(5, 3)) == brute and SMALL_CONTROL[:12] in brute  # the kit's `small_bwh_control`
    assert wh.bwh_witnesses(7, 2) == wh.bwh_witnesses(7, 3) == []
    for n in range(1, 5):
        for r in range(3):
            for c in (2, 3):
                assert wh.rw_witnesses(n, r, c) == []


def test_c_against_python() -> None:
    n = 8
    for hard_core in (False, True):
        r = wh.c_runs(n, hard_core, cap=2 * n + 8, dump_from=2 * n - 2, threads=1)
        for c in (2, 3):
            runs = wh.forced_runs(n, c, hard_core, cap=2 * n + 8)
            assert (r.counts[c - 2, n:] == runs.counts[n:]).all()
            assert sorted((p, reach) for cc, p, reach in r.dumped if cc == c) == \
                [(p, int(runs.reach[p])) for p in range(1 << n) if runs.reach[p] >= 2 * n - 2]


def test_edges_and_clumps() -> None:
    n = 6
    for c in (2, 3):
        t = wh.edge_census(n, c)["table"]  # (E, E', a, survived)
        runs = wh.forced_runs(n, c, cap=3 * n + n)
        assert t[..., 1].sum() == runs.counts[n + 1:].sum()  # surviving steps
        for i, edge in enumerate(wh.EDGES):
            assert (t[i, ..., 1 - int(c in edge)] == 0).all()  # a step survives exactly when c is on the edge
        inner = t[:, 2].sum(axis=0)  # (a, survived) on the steps with E' = {1, 2}
        for a in range(4):
            assert inner[a, int((a == 0) != (c == 3))] == 0  # there c = 3 survives exactly when a = 0
    words = {(1, 1, 2), (2, 1, 2), (1, 2, 2), (2, 2, 1)}
    assert wh.head_depth(words, (1, 1, 2), 3) == 1 and wh.head_depth(words, (2, 2, 1), 3) == 0
    assert len(wh.clumps(words, 1)) == 3 and len(wh.clumps(words, 2)) == 2


def test_flip_profile() -> None:
    n, trials = 3, 40
    p = wh.flip_profile(n, trials=trials, seed=5)  # (2n + 2,)
    rng = np.random.default_rng(5)
    e = rng.integers(1, 3, size=(trials, 2 * n + 2), dtype=np.uint8)  # (trials, 2n + 2): the same words
    for j in range(2 * n + 2):
        changed = 0
        for w in e:
            f = w.copy()
            f[j] = 3 - f[j]
            a, b = tuple(int(x) for x in w), tuple(int(x) for x in f)
            changed += any(recursive_wedge(n, a, t) != recursive_wedge(n, b, t) for t in range(n + 2))
        assert p[j] == changed / trials
    assert wh.forgetting_depth(np.array([0.1, 0.4, 0.5, 0.9])) == 2
