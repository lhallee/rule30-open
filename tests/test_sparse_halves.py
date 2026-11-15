"""Tests of computations.sparse_halves: the certificates of `SparseRight` against integer rows stepped one at a time
and checked column by column."""

from __future__ import annotations

import numpy as np

from computations import absorption, sparse_halves
from references import least_depth_slow


def test_sparse_halves() -> None:
    """The certificates of `SparseRight`: packing round-trips, each first black cell lists one entry per second cell up
    to its step plus depth plus 13, and sampled entries are the first step at which integer rows stepped one at a time
    meet the family, at the least depth there, checked column by column."""
    rng = np.random.default_rng(31)
    entries = [(int(t), int(k)) for t, k in zip(rng.integers(0, 2000, 50), rng.integers(0, 64, 50), strict=True)]
    assert sparse_halves.decode(sparse_halves.encode(entries[0], entries[1:]), 50) == entries
    wall = absorption.kit_wall()  # (4, 2^13)
    word, phase = "0111", 2
    certs = sparse_halves.certificates(word, phase, wall)
    assert len(certs) == 30
    samples = []
    for p1, ((t, k), pairs) in enumerate(certs, start=1):
        assert len(pairs) == max(0, t + k + 13 - p1)
        samples.append((1 << (p1 - 1), t, k))
        for j in rng.choice(len(pairs), size=min(3, len(pairs)), replace=False).tolist():
            samples.append(((1 << (p1 - 1)) | (1 << (p1 + j)), *pairs[j]))
    for half, t, k in samples:
        row = half
        for s in range(t):
            assert least_depth_slow(word, row, (s + phase) % 4, wall) < 0
            row = ((row << 1) | int(word[(s + phase) % 4])) ^ (row | (row >> 1))
        assert least_depth_slow(word, row, (t + phase) % 4, wall) == k
    assert sparse_halves.bound(certs) == 623
