"""center_classes against independent checks on small boxes: every row run with `rule30.step` (`stripe_classes.column`),
the kit's stripe relation transcribed literally and tried on every pair (`stripe_classes`), the representative of the
Lean modules (`stripe_classes.rep`), the C census against numpy, and the lemmas of the entry."""

from __future__ import annotations

from collections import Counter
from itertools import product
from pathlib import Path

import numpy as np
import pytest
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components

from computations import seed_onsets
from computations.rule30 import step
from computations.stripe_classes import (class_size_law, classes_all_pairs, column, formula, rep, s01,
                                         stripe_related, stripe_words)

from computations import center_classes as cc

U64 = np.uint64


def labels_of(keys: list[object]) -> np.ndarray:
    """The index of each key among the distinct keys, in order of first appearance."""
    index: dict[object, int] = {}
    return np.array([index.setdefault(k, len(index)) for k in keys], dtype=np.int64)  # (n,)


def pair_labels(n: int, related: object) -> np.ndarray:
    """The components of the graph on 0 .. n - 1 whose edges are the pairs that `related(a, b)` accepts."""
    edges = [(a, b) for a in range(n) for b in range(a + 1, n) if related(a, b)]  # type: ignore[operator]
    a, b = (np.array(e, dtype=np.int64) for e in zip(*edges)) if edges else (np.zeros(0, np.int64),) * 2
    graph = coo_matrix((np.ones(a.size, dtype=np.int8), (a, b)), shape=(n, n))
    return connected_components(graph, directed=False)[1].astype(np.int64)  # (n,)


def test_count_law_against_direct_runs() -> None:
    # every box of up to 7 cells (latest separation 59) and [-4, 4] (latest separation 72): the distinct columns of
    # every row run with rule30.step, the census and N(A, B) agree, and so do the partitions into classes
    boxes = [(W - 1 - B, B) for W in range(1, 8) for B in range(W)] + [(4, 4)]
    for A, B in boxes:
        H = 120 if A + B + 1 > 7 else 80
        direct = labels_of([column(x, A, B, H) for x in range(1 << (A + B + 1))])  # (n,)
        census = cc.box_census(A, B, T1=H, use_c=False)
        assert direct.max() + 1 == census.classes == formula(A, B), (A, B)
        assert cc.same_partition(direct, cc.s01_labels(cc.box_rows(A, B), B)), (A, B)
        assert census.mixed == census.part_misses == census.size_misses == 0 and census.families
        assert census.latest < H


def test_stripe_words() -> None:
    # the kit's tail automaton, run on every word of up to 12 bits, accepts exactly the words its three constructors
    # generate (stripe_classes.stripe_words)
    for L in range(1, 13):
        words = np.arange(1 << L, dtype=U64)  # (2^L,)
        state = np.zeros(words.size, dtype=np.uint8)  # (2^L,)
        for i in range(L):
            state = cc.TAIL[state, ((words >> U64(i)) & U64(1)).astype(np.uint8)]
        accepted = {tuple(bool((w >> i) & 1) for i in range(L)) for w in np.flatnonzero(cc.ACCEPT[state]).tolist()}
        assert accepted == set(stripe_words(L))


def test_s01_keys_against_every_pair() -> None:
    # the keyed classes equal the classes of the literal relation over every pair, at times 0 and 1 and at time 0
    # alone, on every box of up to 6 cells and on [-3, 3]; time 0 alone leaves 12 classes on [-1, 2] and 24 on [-2, 2]
    boxes = [(W - 1 - B, B) for W in range(1, 7) for B in range(W)] + [(3, 3)]
    for A, B in boxes:
        rows = cc.box_rows(A, B)
        n = rows.size
        assert cc.same_partition(cc.s01_labels(rows, B), np.array(classes_all_pairs(A, B)))
        assert cc.same_partition(cc.s01_labels(rows, B, (0,)), pair_labels(n, lambda a, b: stripe_related(a, b, B)))
    assert cc.s01_labels(cc.box_rows(1, 2), 2, (0,)).max() + 1 == 12
    assert cc.s01_labels(cc.box_rows(2, 2), 2, (0,)).max() + 1 == 24


def test_families_and_representatives() -> None:
    # the classes described in the entry, built with no relation and no step of the rule, are the fibers of the
    # representative of the Lean modules on every box of up to 10 cells, and so are the keyed classes
    for W in range(2, 11):
        for B in range(1, W):
            rows = cc.box_rows(W - 1 - B, B)
            fibers = np.array([rep(x, B) for x in range(rows.size)], dtype=np.int64)  # (n,)
            family = cc.family_labels(rows, B)  # (n,)
            assert family.max() + 1 == formula(W - 1 - B, B)
            assert cc.same_partition(family, fibers) and cc.same_partition(cc.s01_labels(rows, B), fibers)
    for lam in (0, 1, 2, 3, 6, 13, 1602, 2741):
        for B in range(1, 9):
            sizes = Counter(np.bincount(cc.family_labels(cc.part_rows(lam, B), B)).tolist())
            assert sizes == class_size_law(B, lam % 4 == 1)
    # the relation itself relates every two rows of a class, with no chain
    label = cc.s01_labels(cc.box_rows(3, 4), 4)
    assert all(s01(a, b, 4) for a, b in product(range(256), repeat=2) if label[a] == label[b])


def test_split_and_survivors() -> None:
    # prefix groups at T1 = 8 need the split; it ends where the prefixes at 400 end, and stops with survivors at T2
    exact = cc.box_census(4, 4, T1=400, use_c=False)
    early = cc.box_census(4, 4, T1=8, use_c=False)
    assert early.split.groups > 0 and early.split.survivors == 0
    assert early.classes == exact.classes == formula(4, 4)
    assert early.latest == exact.latest == exact.lcp_groups == 72
    a, b = early.split.pair or (0, 0)
    ca, cb = column(a, 4, 4, 100), column(b, 4, 4, 100)
    assert next(t for t in range(100) if ca[t] != cb[t]) == 72
    short = cc.box_census(4, 4, T1=8, T2=20, use_c=False)
    assert short.split.survivors > 0 and short.classes is None
    # one quoted number: [-6, 6] has 4,192 classes, the last pair of different classes first differing at t = 294
    six = cc.box_census(6, 6, T1=128, use_c=False)
    assert six.classes == 4192 and six.latest == 294 and six.lcp_edge == 23


def test_parts() -> None:
    # the census of fixed left parts against a direct count of their columns, with the sizes of the class-size law
    for lam, B in ((0, 5), (1, 6), (2, 4), (13, 5), (1602, 4)):
        census = cc.part_census(lam, B, T1=128, use_c=False)
        A = lam.bit_length()
        cols = [column(x, A, B, 160) for x in cc.part_rows(lam, B).tolist()]
        direct = labels_of(cols)  # (2^B,)
        assert direct.max() + 1 == census.classes == cc.part_law(lam, B)
        assert census.sizes == Counter(Counter(direct.tolist()).values()) == class_size_law(B, lam % 4 == 1)
    for A in range(0, 6):
        for B in range(1, 6):
            assert sum(cc.part_law(lam, B) for lam in range(1 << (A + 1))) == formula(A, B)


def test_c_census_against_numpy(monkeypatch: pytest.MonkeyPatch) -> None:
    here = Path(cc.__file__).resolve().parent
    if not (seed_onsets.HERE / "center_classes_census.c").exists():  # the drafted program beside the drafted module
        monkeypatch.setattr(seed_onsets, "HERE", here)
    for mode, first, B in (("box", 3, 4), ("box", 0, 9), ("part", 1602, 7)):
        rows = cc.box_rows(first, B) if mode == "box" else cc.part_rows(first, B)
        g1, e1, l1 = cc.prefix_groups(rows, B, 128)
        g2, e2, l2 = cc.census_c(rows, mode, first, B, 128, optimize=False)
        assert cc.same_partition(g1, g2) and (e1, l1) == (e2, l2)


def test_lemmas() -> None:
    # masking and the distinct right halves of a class, on every pair of one class of [-3, 4]
    A, B, H = 3, 4, 120
    M = A + H + 2
    rows = cc.box_rows(A, B)
    label = cc.s01_labels(rows, B)
    spacetime = []
    for x in range(1 << (A + B + 1)):
        row = sum(1 << (B - k + M) for k in range(A + B + 1) if (x >> k) & 1)
        cells = []
        for _ in range(H):
            cells.append(((row >> (M - 1)) & 1, (row >> M) & 1, (row >> (M + 1)) & 1))  # columns -1, 0, 1
            row = step(row)
        spacetime.append(cells)
    for lab in range(int(label.max()) + 1):
        members = np.flatnonzero(label == lab)  # (k,)
        right = rows[members] & U64((1 << B) - 1)  # (k,), cells 1 .. B
        assert np.unique(right).size == members.size
        for a, b in product(members.tolist(), repeat=2):
            for (l1, c1, r1), (l2, c2, r2) in zip(spacetime[a], spacetime[b]):
                assert c1 == c2 and (l1 ^ l2) == (1 - c1) * (r1 ^ r2)
    # every row of [-A, 0] has its own center column (the right half fixes the row)
    for A in range(1, 8):
        assert len({column(x, A, 0, 2 * A + 4) for x in range(1 << (A + 1))}) == 1 << (A + 1)
