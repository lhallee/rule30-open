"""The rank certificate of ThreeRuns against a naive fixed point and a direct run."""

from __future__ import annotations

import numpy as np

from computations.three_runs import BLOCK, WORDS, completes, ranks, step


def naive_step(w: int, width: int, center: int, beyond: int) -> int:
    """One step of a window of columns 1..width, cell by cell."""
    cells = [center] + [(w >> i) & 1 for i in range(width)] + [beyond]
    new = [cells[i - 1] ^ (cells[i] | cells[i + 1]) for i in range(1, width + 1)]
    return sum(b << i for i, b in enumerate(new))


def naive_successors(p: int, s: int, w: int, width: int) -> list[tuple[bool, tuple[int, int, int]]]:
    out = []
    for x in (0, 1):
        v = naive_step(w, width, int(BLOCK[p]), x)
        if p == 1:
            out.append((not completes(s, w & 1), ((p + 1) % 3, ((s << 1) | (w & 1)) & 7, v)))
        else:
            out.append((True, ((p + 1) % 3, s, v)))
    return out


def test_step() -> None:
    w = np.arange(1 << 6, dtype=np.int64)
    for c in (0, 1):
        for x in (0, 1):
            assert step(w, 6, c, x).tolist() == [naive_step(int(v), 6, c, x) for v in range(1 << 6)]


def test_ranks_match_naive() -> None:
    """At width 7 the good set and the ranks equal the naive greatest fixed point and backward layers."""
    width = 7
    good, rank = ranks(width)
    states = {(p, s, w) for p in range(3) for s in range(8) for w in range(1 << width)}
    keep = set(states)
    while True:
        drop = {st for st in keep if any(not ok or nx not in keep for ok, nx in naive_successors(*st, width))}
        if not drop:
            break
        keep -= drop
    assert keep == {(p, s, w) for p, w, s in zip(*np.nonzero(good))}
    layer, k = {st: 0 for st in keep}, 0
    while True:
        add = {st for st in states - layer.keys() if all(nx in layer for _, nx in naive_successors(*st, width))}
        if not add:
            break
        k += 1
        layer.update({st: k for st in add})
    assert all(rank[p, w, s] == layer.get((p, s, w), -1) for p, s, w in states)


def test_direct_run() -> None:
    """A random half driven by 001 avoids the words at the second white step from index 14 on."""
    rng = np.random.default_rng(3)
    for ph in range(3):
        row = int(rng.integers(0, 1 << 62)) | (int(rng.integers(0, 1 << 62)) << 62)
        reads = []
        for t in range(400):
            if (t + ph) % 3 == 1:
                reads.append(row & 1)
            c = int(BLOCK[(t + ph) % 3])
            row = ((row << 1) | c) ^ (row | (row >> 1))
        text = "".join(map(str, reads))[14:]
        assert not any(word in text for word in WORDS)
