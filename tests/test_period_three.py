"""Tests of computations.period_three: driven right halves, entry statistics and rates against cell arrays stepped
directly, hand-computed values and the kit's trap t001."""

from __future__ import annotations

import numpy as np

from computations import period_three


def test_period_three() -> None:
    """Column 1 of driven right halves against cell arrays stepped with the center as column 0, for both words and
    every phase; `settled_periods` on sequences with a known transient and period; and the counts the negative result
    quotes, at small sizes: under 011 no right half of up to 6 cells has column 1 at the white times settled after 3,000
    steps, while under 001 the white half has settled with period 14 samples, the 21 steps of the kit's trap."""
    rng = np.random.default_rng(41)
    halves = [0, 1, 5, 0b1011, int(rng.integers(0, 1 << 20))]
    steps = 300
    for word in period_three.WORDS:
        for phase in range(3):
            column = period_three.column_one(word, halves, phase, steps)  # (steps, n)
            for i, half in enumerate(halves):
                cells = np.zeros(21 + steps + 2, dtype=bool)  # (m,), column j + 1 at index j + 1, the center at 0
                cells[1:21] = [(half >> j) & 1 for j in range(20)]
                for t in range(steps):
                    assert column[t, i] == cells[1]
                    cells[0] = word[(t + phase) % 3] == "1"
                    left = np.concatenate([[False], cells[:-1]])  # (m,)
                    right = np.concatenate([cells[1:], [False]])  # (m,)
                    cells = left ^ (cells | right)
    block = np.array([1, 0, 0, 1, 1, 0, 1], dtype=np.uint8)  # (7,), primitive
    seqs = np.stack([np.concatenate([rng.integers(0, 2, 100).astype(np.uint8), np.tile(block, 43)]),
                     rng.integers(0, 2, 401).astype(np.uint8)], axis=1)  # (401, 2)
    assert period_three.settled_periods(seqs, 100).tolist() == [7, 0]
    _, periods = period_three.report("011", list(range(64)), 0, 3000)
    assert (periods == 0).all()
    _, periods = period_three.report("001", [0], 0, 6000)
    assert periods.tolist() == [14]


def test_in_sorted_and_settled_from() -> None:
    """`in_sorted` against set membership on random values, empty keys included; and `settled_from` against column 1
    read from integer rows stepped one at a time: the white time of the first sample from which every sample equals
    the one `period` samples before, the last white time when the samples never settle."""
    rng = np.random.default_rng(44)
    keys = np.unique(rng.integers(0, 1 << 12, 300).astype(np.uint64))  # (k,), sorted and distinct
    values = rng.integers(0, 1 << 12, 2000).astype(np.uint64)  # (2000,)
    members = set(keys.tolist())
    assert period_three.in_sorted(values, keys).tolist() == [v in members for v in values.tolist()]
    assert not period_three.in_sorted(values, keys[:0]).any()
    for word, half, phase, steps, period in (("001", 0, 0, 1600, 14), ("001", 5, 2, 1600, 14), ("011", 9, 1, 600, 5)):
        row, column = half, []
        for t in range(steps):
            column.append(row & 1)
            row = ((row << 1) | int(word[(t + phase) % 3])) ^ (row | (row >> 1))
        times = [t for t in range(steps) if word[(t + phase) % 3] == "0"]
        samples = [column[t] for t in times]
        first = max([i + 1 for i in range(period, len(samples)) if samples[i] != samples[i - period]], default=0)
        want = times[min(first, len(times) - 1)]
        assert period_three.settled_from(word, half, phase, steps, period) == want, (word, half, phase)


def test_constant_rate() -> None:
    """`constant_rate` against values computed by hand on three entry steps, and against the exponential law on a
    large sample of exponential entry times."""
    ratio, left = period_three.constant_rate(np.array([1261, 1262, 1266]), start=1260, at=1264)
    assert abs(ratio - 3 / 2) < 1e-12 and abs(left - np.exp(-4 / 3)) < 1e-12
    rng = np.random.default_rng(43)
    done = 1260 + rng.exponential(20000.0, 200000)  # (200000,)
    ratio, left = period_three.constant_rate(done)
    assert abs(ratio - 1 / np.log(2)) < 0.02
    assert abs(left / np.exp(-(100000 - 1260) / 20000.0) - 1) < 0.05


def test_t001_entries() -> None:
    """Entry into the kit's trap t001, read from its source: the white half enters at step 1,270, 1,269 or 1,268 by
    phase, as the kit's `t001_reached` and `EmptyRight.emptyRight_001` state, and halves 1 and 3 at step 1,267 (half 2,
    with column 2 black, enters only at step 35,536, in the census's reproduce command); integer rows stepped one at a time stay in the trap for 300 steps after
    entry with random cells beyond column 47, as the trap's closure requires; and `periodic_extent` agrees with the
    same rows, covering the trap's 38 periodic columns once the white half is in."""
    keys = set(period_three.trap_keys().tolist())
    assert len(keys) == 815
    assert period_three.trap_entries([0], 0, 2000, period_three.trap_keys()).tolist() == [1270]
    assert period_three.trap_entries([0, 0], 1, 2000, period_three.trap_keys()).tolist() == [1269, 1269]
    assert period_three.trap_entries([0], 2, 2000, period_three.trap_keys()).tolist() == [1268]
    # half 2 enters at step 35,536, which the census's reproduce command runs
    assert period_three.trap_entries([0, 1, 3], 0, 2000, period_three.trap_keys()).tolist() == [1270, 1267, 1267]
    rng = np.random.default_rng(42)
    mask = (1 << period_three.TRAP_WIDTH) - 1
    row = 0
    for t in range(1270):
        row = ((row << 1) | int("001"[t % 3])) ^ (row | (row >> 1))
    for trial in range(3):
        noisy = (row & mask) | (int(rng.integers(0, 1 << 62)) << period_three.TRAP_WIDTH)
        for t in range(1270, 1570):
            assert ((noisy & mask) * 4 + t % 3) in keys, (trial, t)
            noisy = ((noisy << 1) | int("001"[t % 3])) ^ (noisy | (noisy >> 1))
    history = [0]
    for t in range(2000):
        history.append(((history[-1] << 1) | int("001"[t % 3])) ^ (history[-1] | (history[-1] >> 1)))
    for t in (500, 2000):
        repeats = [all((history[t] >> p) & 1 == (history[t - 21 * k] >> p) & 1 for k in range(1, 6)) for p in range(128)]
        extent = repeats.index(False) if False in repeats else 128
        assert period_three.periodic_extent(0, 0, t + 1, [t]) == [extent]
    assert extent >= 38  # the trap's 38 columns of period 21


def test_beyond_stats() -> None:
    """`period_three.beyond_stats` against a direct count: right halves stepped cell by cell under 001, stopped at their
    first step in `t001` (its states with their labels modulo 3), the cell beyond a window of 10 cells counted by the
    phase and the last 3 cells of the window."""
    from collections import Counter
    from computations import lock_chain, period_three

    inside = {(strip, label % 3) for strip, label in lock_chain.t001_states()}
    width, context, steps, phase = 10, 3, 400, 1
    want = Counter()
    for half in range(16):
        cells = [(half >> i) & 1 for i in range(steps + 64)]  # cells 1, 2, ...
        for t in range(steps):
            drive = (t + phase) % 3
            if (sum(cells[i] << i for i in range(47)), drive) in inside:
                break
            near = sum(cells[width - context + i] << i for i in range(context))
            want[(drive, near, cells[width])] += 1
            # only cells 1 .. 47 + steps - t now reach cells 1 .. 47 by the last step: the light cone
            row = [int("001"[drive])] + cells[:47 + steps - t] + [0]
            cells = [row[i - 1] ^ (row[i] | row[i + 1]) for i in range(1, len(row) - 1)]
    got = period_three.beyond_stats(list(range(16)), phase, steps, width, context, period_three.trap_keys())
    assert all(got[d, n, v] == want[(d, n, v)] for d in range(3) for n in range(1 << context) for v in (0, 1))
    assert got.sum() == sum(want.values()) > 0


def test_cut_entries() -> None:
    """`period_three.cut_entries` against right halves stepped cell by cell under 001, the six halves at once as rows of
    a bool array, each width's first step found by looking up the window and the phase modulo 3 among `t001`'s states
    cut to that width; at 47 cells it is `trap_entries`."""
    from computations import lock_chain, period_three

    widths, steps, count = (12, 20, 28, 47), 1400, 6
    states = lock_chain.t001_states()
    cuts = [{(strip & ((1 << w) - 1), label % 3) for strip, label in states} for w in widths]
    keys = period_three.trap_keys()
    weights = 1 << np.arange(max(widths), dtype=np.uint64)  # (47,), the value of each cell of the window
    for phase in range(3):
        got = period_three.cut_entries(list(range(count)), phase, steps, widths, keys)  # (6, 4)
        cells = np.zeros((count, steps + 64), dtype=bool)  # (6, n), cells 1, 2, ... of each half
        cells[:, :3] = (np.arange(count)[:, None] >> np.arange(3)[None, :]) & 1
        want = [[-1] * len(widths) for _ in range(count)]
        for t in range(steps):
            if min(min(w) for w in want) >= 0:
                break  # every width found, so later steps change nothing
            drive = (t + phase) % 3
            values = (cells[:, :max(widths)].astype(np.uint64) * weights).sum(axis=1)  # (6,)
            for half, value in enumerate(values.tolist()):
                for j, w in enumerate(widths):
                    if want[half][j] < 0 and (value & ((1 << w) - 1), drive) in cuts[j]:
                        want[half][j] = t
            column = np.full((count, 1), "001"[drive] == "1")  # (6, 1)
            row = np.concatenate([column, cells, np.zeros((count, 1), dtype=bool)], axis=1)  # (6, n + 2)
            cells = row[:, :-2] ^ (row[:, 1:-1] | row[:, 2:])  # (6, n)
        assert got.tolist() == want
        assert (got[:, -1] == period_three.trap_entries(list(range(6)), phase, steps, keys)).all()
        assert (np.diff(np.where(got < 0, steps, got), axis=1) >= 0).all()  # a wider cut is entered no sooner


def test_coin_entries() -> None:
    """`period_three.coin_entries` at 10 cells against the coin's exact mean first step in `t001` cut to 10 cells, the
    sum over k of the chance of staying out for k steps (`coin_lock.coin_step`), from the same windows and phases."""
    from computations import coin_lock, lock_certificate, period_three

    width, keys = 10, period_three.trap_keys()
    member = np.zeros((3, 1 << width), dtype=bool)  # (3, 2^10)
    member[(keys & np.uint64(3)).astype(np.int64), ((keys >> np.uint64(2)) & np.uint64((1 << width) - 1)).astype(
        np.int64)] = True
    successors = lock_certificate.successor_table("001", width)  # (3, 2, 2^10)
    out, mean = np.where(member, 0.0, 1.0), np.zeros((3, 1 << width))  # (3, 2^10) each
    while out.max() > 1e-12:
        mean += out
        out = coin_lock.coin_step("001", member, out, successors)
    rng = np.random.default_rng(5)
    for phase in range(3):
        first = period_three.coin_entries([h for h in range(16) for _ in range(500)], phase, 10 ** 5, width, keys, rng)
        exact = mean[phase, :16].mean()
        assert (first >= 0).all() and abs(first.mean() - exact) < 0.05 * exact
