"""Tests for computations.stripe_classes on small boxes, against independent checks: union-find over all pairs, the
center columns by direct simulation, and the C census against Python."""

from __future__ import annotations

from computations.stripe_classes import (class_size_law, class_sizes, classes, classes_all_pairs, column,
                                         distinct_columns, formula, rep, s01, stripe_words)


def test_stripe_words_number_n() -> None:
    for n in range(1, 13):
        words = stripe_words(n)
        assert len(words) == n
        assert sum(1 for w in words if w[0]) == 1  # one ends (cell order) with a black cell
        assert all(w[-1] for w in words)  # all begin (cell order) with a black cell


def test_class_count_and_all_pairs() -> None:
    for W in range(1, 7):
        for A in range(W):
            B = W - 1 - A
            lab = classes(A, B)
            assert len(set(lab)) == formula(A, B)
            pairs = classes_all_pairs(A, B)
            assert len({(a, b) for a, b in zip(lab, pairs)}) == len(set(lab))  # the same partition


def test_classes_are_fibers_of_rep() -> None:
    for W in range(2, 8):
        for A in range(W):
            B = W - 1 - A
            n = 1 << (A + B + 1)
            lab = classes(A, B)
            seen: dict[int, int] = {}
            for x in range(n):
                r = rep(x, B)
                assert r < n and s01(x, r, B) and lab[r] == lab[x]
                assert seen.setdefault(lab[x], r) == r
                assert (x >> B) == (r >> B)  # the representative keeps the left part (cells <= 0)


def test_columns_constant_on_classes_and_counted() -> None:
    for W in range(1, 7):
        for A in range(W):
            B = W - 1 - A
            cols = [column(x, A, B, 128) for x in range(1 << (A + B + 1))]
            assert all(cols[x] == cols[rep(x, B)] for x in range(len(cols)))
            assert len(set(cols)) == formula(A, B)


def test_c_census_matches_python() -> None:
    for A, B in [(0, 3), (2, 2), (3, 1), (1, 4)]:
        cols = {column(x, A, B, 128) for x in range(1 << (A + B + 1))}
        assert distinct_columns(A, B, 128) == len(cols) == formula(A, B)


def test_class_size_law() -> None:
    """The law against the classes of the union-find, and the law's own totals: 2^B rows and 2^(B-1) + 1 classes per
    left part, or 2^(B-1) when the left part ends in 0 1."""
    for B in range(1, 12):
        for ends01 in (False, True):
            law = class_size_law(B, ends01)
            assert sum(k * m for k, m in law.items()) == 1 << B
            assert sum(law.values()) == (1 << (B - 1)) + (0 if ends01 else 1)
    for W in range(2, 9):
        for A in range(W - 1):
            B = W - 1 - A
            for lam, sizes in class_sizes(A, B).items():
                assert sizes == class_size_law(B, lam % 4 == 1)
