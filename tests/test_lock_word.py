"""Tests of computations.lock_word: lock words, unreachable windows and avoid growth against the family test,
forward searches and direct counts."""

from __future__ import annotations

import numpy as np

from computations import absorption, lock_certificate
from computations.rule30 import distinct


def test_lock_word() -> None:
    """The lock words of `LockWord`: the trap agrees with `absorption.family_depth`, the depth-first family test, on
    every window; each word, run through the successor table from every start phase on 64 sampled windows, ends them in
    the trap, and the bit slices, with which `slice_check` finds every window in the trap, agree with that run there."""
    from computations import lock_word
    wall = absorption.kit_wall()  # (4, 2^13)
    rng = np.random.default_rng(5)
    for word, (width, _, _, _) in lock_word.LEAST.items():
        member = lock_word.trap(word, width, wall)  # (4, 2^W)
        assert int(member.sum()) == 109
        states = np.arange(1 << width, dtype=np.uint64)  # (2^W,)
        for ph in range(4):
            depth = absorption.family_depth(word, states, ph, wall)  # (2^W,)
            assert np.array_equal(member[ph], (depth >= 0) & (depth <= width - 13))
        values = lock_word.universal_word(word, member)
        successors = lock_certificate.successor_table(word, width)  # (4, 2, 2^W)
        slices = lock_word.slice_run(word, width, values)
        size = 1 << width
        for start in range(4):
            sample = rng.integers(0, size, 64)  # (64,)
            windows = sample.copy()  # (64,)
            for t, value in enumerate(values):
                windows = successors[(start + t) % 4, value][windows]  # (64,)
            assert member[(start + len(values)) % 4][windows].all()
            for r, end in zip(sample.tolist(), windows.tolist(), strict=True):
                bit = start * size + r
                assert sum(((slices[j] >> bit) & 1) << j for j in range(width)) == end
        assert lock_word.slice_check(word, width, values, member, slices)


def test_lock_unreachable() -> None:
    """`lock_word.unreachable` against a forward search: beside an alternating center, at width 19, the set reached
    from a window marked unreachable, with both values of column 20 at every step, never meets the trap, and the set
    reached from a window marked reachable does (one of each, sampled); under 0111 at width 13 no window is
    unreachable."""
    from computations import lock_word
    wall = absorption.kit_wall()  # (4, 2^13)
    assert not lock_word.unreachable("0111", 13, wall).any()
    width = 19
    out = lock_word.unreachable("0101", width, wall)  # (4, 2^W)
    member = lock_word.trap("0101", width, wall)  # (4, 2^W)
    successors = lock_certificate.successor_table("0101", width)  # (4, 2, 2^W)

    def meets_trap(window: int) -> bool:
        seen = np.zeros((4, 1 << width), dtype=bool)  # (4, 2^W)
        seen[0, window] = True
        frontier = [np.array([window], dtype=np.int64)] + [np.zeros(0, dtype=np.int64)] * 3  # by phase
        while any(f.size for f in frontier):
            if any(member[ph][frontier[ph]].any() for ph in range(4)):
                return True
            nxt = []
            for ph in range(4):
                prev = frontier[(ph - 1) % 4]  # (m,), at phase ph - 1
                step = distinct(successors[(ph - 1) % 4][:, prev].ravel())  # (k,)
                step = step[~seen[ph][step]]
                seen[ph][step] = True
                nxt.append(step)
            frontier = nxt
        return False

    rng = np.random.default_rng(7)
    bad = np.flatnonzero(out[0])  # (n,)
    good = np.flatnonzero(~out[0])  # (m,)
    assert not meets_trap(int(rng.choice(bad)))
    assert meets_trap(int(rng.choice(good)))


def test_lock_avoid_growth() -> None:
    """`lock_word.avoid_growth` against a direct count: under 0111 at width 13, the number of sequences of column 14
    that keep the worst window out of the certificate of 13 cells (the locked nodes of `locks.lock_info` there, as
    `test_period_rate` checks) for L steps, counted step by step, grows by the same factor per step between L = 250 and
    L = 400; it is the rate 1.969279 that `locks.profile` gives for the share 5.8% of locked nodes."""
    from computations import coin_lock, lock_word
    member = coin_lock.certificate("0111", 13)  # (4, 2^13)
    assert round(float(member.mean()), 4) == 0.0584
    successors = lock_certificate.successor_table("0111", 13)  # (4, 2, 2^13)
    # the successor of window s at phase ph under each value, as a position in the counts of every phase laid end to end
    later = ((np.arange(4) + 1) % 4)[:, None, None] * (1 << 13) + successors  # (4, 2, 2^13)
    outside = ~member  # (4, 2^13)
    counts = np.where(member, 0.0, 1.0)  # (4, 2^13), sequences of length 0 that keep each window out
    worst = []
    for _ in range(1, 401):  # sequences of length 1 to 400
        flat = counts.reshape(-1)  # (4 2^13,)
        nxt = (flat[later[:, 0]] + flat[later[:, 1]]) * outside  # (4, 2^13), every phase at once
        scale = nxt.max()
        counts = nxt / scale
        worst.append(np.log(scale))
    rate = np.exp(np.mean(worst[250:]))
    growth = lock_word.avoid_growth("0111", member)
    assert abs(rate - growth) < 1e-3 and round(growth, 6) == 1.969279
