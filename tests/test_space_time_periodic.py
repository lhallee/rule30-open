"""Tests of computations.space_time_periodic: the backgrounds and the column map against brute force over rings."""

from __future__ import annotations

import numpy as np


def test_space_time_periodic() -> None:
    """The backgrounds of `space_time_periodic` against brute force: for every ring of up to 9 cells, every row whose
    orbit under Rule 30 returns within 6 steps has a temporal period P <= 6, and its least spatial period is the length
    of a cycle of `column_map` for P; conversely each cycle of length up to 16 is such a row, by a direct run of the
    ring (`ring_period`). The backgrounds of period 4 are the white row, the stripe and the kit's ether, of spatial
    period 7, and the walls of periods 9 and 10 lie on cycles of the lengths their chains repeat with (period 11, whose
    4^11 states take 0.4 s to square, is the entry's reproduce command `--table`); at period 10 the windows of 11 cells
    right of the columns of the background of 155 cells close into walls at 35 of its 150 columns of period 10
    (`background_walls`; the rings of up to 16 cells, the walls at 16 cells, period 12 and its witnesses are the entry's
    reproduce command); every row repeating with a period dividing P, read from the cycles, matches the counts of A New
    Kind of Science for P up to 8."""
    import itertools
    from computations import space_time_periodic as stp
    from computations.cyclic_words import least_period, least_rotation

    def least_spatial(cells: tuple[int, ...]) -> int:
        return min(d for d in range(1, len(cells) + 1) if len(cells) % d == 0 and cells == cells[d:] + cells[:d])

    lengths = {period: {length for length, _, _ in stp.backgrounds(period)} for period in range(1, 7)}
    for size in range(1, 10):  # every ring of `size` cells run directly, all at once, as `ring_period` runs one
        start = np.array(list(itertools.product((0, 1), repeat=size)), dtype=np.uint8)  # (2^size, size)
        row, first = start.copy(), np.zeros(len(start), dtype=np.int64)  # (2^size, size), (2^size,), 0 for none yet
        for t in range(1, 7):
            row = np.roll(row, 1, axis=1) ^ (row | np.roll(row, -1, axis=1))  # cell i reads cells i - 1, i, i + 1
            first[(first == 0) & (row == start).all(axis=1)] = t
        for cells, period in zip(start.tolist(), first.tolist(), strict=True):
            if period:
                assert least_spatial(tuple(cells)) in lengths[period], (cells, period)
        assert all(stp.ring_period(cells, 6) == (period or None)  # every 37th ring of each size, one ring at a time
                   for cells, period in zip(start[::37].tolist(), first[::37].tolist(), strict=True))
    for period in range(1, 7):
        nodes, label = stp.cycles(period)  # (c,), (c,)
        for lab in set(label.tolist()):
            states = [int(lab)]
            while (nxt := int(stp.column_map(period)[states[-1]])) != states[0]:
                states.append(nxt)
            row = [(state >> period) & 1 for state in reversed(states)]  # left to right, at step 0
            ring = stp.ring_period(row, period)
            assert ring is not None and period % ring == 0
    assert [(length, count) for length, count, _ in stp.backgrounds(4)] == [(1, 1), (2, 1), (7, 4)]
    found = {period: {length for length, _, _ in stp.backgrounds(period)} for period in (9, 10)}
    assert 135 in found[9] and 155 in found[10]
    assert stp.witnesses(8) == {("01", 2), ("0001", 4)}
    # the walls at the background's edge, at 11 cells (16 cells, 60 of the 150, is the entry's reproduce command)
    assert stp.background_walls(10, 11) == [(30, 30, 0), (90, 85, 0), (155, 150, 35)]
    # every row that repeats with a period dividing P, from each cycle's row run directly and read in every rotation: as
    # many as the states on cycles, against the list of A New Kind of Science, which the second count matches only at
    # periods 1 to 4, 6 and 7
    for period in range(1, 9):
        nodes, label = stp.cycles(period)  # (c,), (c,)
        f = stp.column_map(period)  # (4^P,)
        rows: set[tuple[int, ...]] = set()
        for lab in set(label.tolist()):
            states = [int(lab)]
            while (nxt := int(f[states[-1]])) != states[0]:
                states.append(nxt)
            row = np.array([(state >> period) & 1 for state in reversed(states)], dtype=np.uint8)  # (S,)
            start = row.copy()  # (S,)
            for _ in range(period):
                rows.update(tuple(np.roll(row, k).tolist()) for k in range(row.size))
                row = np.roll(row, 1) ^ (row | np.roll(row, -1))
            assert np.array_equal(row, start)
        assert len(rows) == stp.counts(period)[0]
    found_counts = [stp.counts(period) for period in range(1, 9)]  # periods 9 and 10: the entry's reproduce command
    assert [rows for rows, _ in found_counts] == [3, 3, 15, 31, 48, 99, 108, 119]
    assert [cells for _, cells in found_counts] == [3, 3, 15, 10, 48, 99, 18, 94]
    # the witness for 0001, run directly: on the ring of the background, a column repeats 0001 with period 4 while the
    # column left of it takes both values at one phase of it
    nodes, label = stp.cycles(8)  # (c,), (c,)
    f = stp.column_map(8)  # (4^8,)
    start = next(int(n) for n in nodes.tolist() if least_rotation(stp.word_of(n >> 8, 8)) == "00010001"
                 and least_period(stp.word_of(int(f[n]) >> 8, 8)) == 8)
    states = [start]
    while (nxt := int(f[states[-1]])) != start:
        states.append(nxt)
    row = np.array([(state >> 8) & 1 for state in reversed(states)], dtype=np.uint8)  # (S,), the column of start last
    history = []
    for _ in range(16):
        history.append(row.copy())
        row = np.roll(row, 1) ^ (row | np.roll(row, -1))
    column, left = [int(r[-1]) for r in history], [int(r[-2]) for r in history]
    assert column[:4] * 4 == column and any(left[ph] != left[ph + 4] for ph in range(12))
