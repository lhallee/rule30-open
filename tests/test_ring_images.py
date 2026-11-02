"""Checks of computations/ring_images.py: the count of missed rows from the transfer matrices against enumeration of
every row of small rings, and the ring step against a direct cell-by-cell rule."""

from __future__ import annotations

import numpy as np

from computations import ring_images as r


def direct_step(row: int, width: int, rule: int) -> int:
    """One step of `rule` on a ring, cell by cell, a second implementation."""
    out = 0
    for i in range(width):
        left, center, right = (row >> ((i - 1) % width)) & 1, (row >> i) & 1, (row >> ((i + 1) % width)) & 1
        out |= ((rule >> (4 * left + 2 * center + right)) & 1) << i
    return out


def test_ring_step_matches_direct() -> None:
    for width in (3, 5, 8):
        rows = np.arange(1 << width, dtype=np.int64)  # (2^W,)
        for rule in (30, 90, 150):
            fast = r.ring_step(rows, width, rule)  # (2^W,)
            assert fast.tolist() == [direct_step(int(x), width, rule) for x in rows]


def test_missed_rows_match_enumeration() -> None:
    n2, n3 = r.pair_matrix(), r.triple_matrix()  # (12, 12), (24, 24)
    t2, t3 = r.walk_traces(n2, 14), r.walk_traces(n3, 14)
    for width in range(3, 15):
        counts = r.preimage_counts(width, 30)  # (2^W,)
        missed = (1 << width) - int(np.count_nonzero(counts))
        assert missed == r.missed_rows(width) == t2[width - 1] // 2 - t3[width - 1] // 6
        assert int(counts.max()) == (3 if width % 3 == 0 else 2)
        pairs = int((counts * (counts - 1)).sum())
        assert pairs == t2[width - 1]
    assert [r.missed_rows(w) for w in (16, 20, 24)] == [2337, 19305, 159536]


def test_characteristic_polynomials() -> None:
    # x^8 (x - 1)(x^3 - x^2 - 2) and x^18 (x^3 - 1)^2
    assert r.characteristic_polynomial(r.pair_matrix()) == [1, -2, 1, -2, 2] + [0] * 8
    assert r.characteristic_polynomial(r.triple_matrix()) == [1, 0, 0, -2, 0, 0, 1] + [0] * 18
    t2, t3 = r.walk_traces(r.pair_matrix(), 40), r.walk_traces(r.triple_matrix(), 40)
    assert t2 == [p + 1 for p in r.power_sums(40)]
    assert t3 == [6 if w % 3 == 0 else 0 for w in range(1, 41)]


def test_rule_90_loses_one_or_two_bits() -> None:
    for width in range(3, 13):
        assert r.image_size(width, 90) == 1 << (width - 1 - (width + 1) % 2)
