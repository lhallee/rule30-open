"""The census of rows finite on both sides at the onset (`computations.finite_onset`), against the big-integer Psi of
`computations.coupled` and against direct runs of whole finite rows."""

from __future__ import annotations

import numpy as np

from computations import coupled, finite_onset


def center_column(left: int, width: int, center: int, right: int, cells: int, steps: int) -> list[int]:
    """The center column at times 0 .. steps - 1 of the finite row with `left` at depths 1 .. width (bit j - 1 is
    depth j), `center` at cell 0 and `right` at columns 1 .. cells (bit i - 1 is column i), by stepping whole
    integers."""
    offset = width + steps + 2  # bit offset + x is cell x
    state = (center << offset) | (right << (offset + 1))
    for j in range(width):
        state |= ((left >> j) & 1) << (offset - j - 1)
    column = []
    for _ in range(steps):
        column.append((state >> offset) & 1)
        state = (state << 1) ^ (state | (state >> 1))  # new cell x = cell x - 1 xor (cell x or cell x + 1)
    return column


def test_slices_match_big_integers() -> None:
    """The bit-sliced Psi equals `coupled.psi` for every right half, for blocks of several periods and phases."""
    for word, phase, cells, depth in (("01", 1, 7, 150), ("011", 2, 4, 90), ("00101", 3, 6, 120),
                                      ("0010011", 5, 8, 100)):
        rows = finite_onset.unpack(finite_onset.psi_slices(word, phase, cells, depth), 1 << cells)  # (depth, 2^k)
        for right in range(1 << cells):
            assert finite_onset.as_int(rows[:, right]) == coupled.psi(word, phase, right, depth)


def test_best_left_half_against_whole_rows() -> None:
    """Over every left half of at most eight cells, run as a whole finite row, the longest time the center stays on
    the block is the first black depth of Psi beyond eight, and the left half that attains it is Psi cut to eight
    cells: the census's reading of Psi, checked by direct simulation."""
    width, steps = 8, 40
    for word in ("01", "001", "011", "00101"):
        for phase in range(len(word)):
            target = [int(word[(t + phase) % len(word)]) for t in range(steps)]
            rows = finite_onset.unpack(finite_onset.psi_slices(word, phase, 3, steps), 8)  # (steps, 8)
            for right in range(8):
                best, best_left = -1, -1
                for left in range(1 << width):
                    column = center_column(left, width, target[0], right, 3, steps)
                    alive = next((t for t in range(steps) if column[t] != target[t]), steps)
                    if alive > best:
                        best, best_left = alive, left
                blacks = [j + 1 for j in range(width, steps) if rows[j, right]]
                assert best == (blacks[0] if blacks else steps)
                assert best_left == finite_onset.as_int(rows[:width, right])


def test_classify_statistics() -> None:
    """The census's longest white run and last black depth against `coupled.white_runs` and `int.bit_length` on each
    Psi, and the census's white tail on a row that is finite by construction: with the center column of a finite row
    as the word, Psi of its right half is its left half."""
    word, phase, cells, depth = "011", 1, 5, 200
    census = finite_onset.classify(word, phase, cells, depth)
    runs, lasts = [], []
    for right in range(1 << cells):
        row = coupled.psi(word, phase, right, depth)
        records = coupled.white_runs(row, depth)
        runs.append(records[-1][0] if records else 0)
        lasts.append(row.bit_length())
    assert census.longest_run == max(runs) and census.last_black == min(lasts)
    assert census.white_tail == [] and census.aperiodic == 1 << cells

    rng = np.random.default_rng(3)
    left, right, middle = int(rng.integers(1 << 12)), 0b10110, 1
    column = center_column(left, 12, middle, right, 5, 129)
    finite = "".join(map(str, column))  # a word as long as the times the census reads
    census = finite_onset.classify(finite, 0, 5, 128)
    assert right in census.white_tail
    assert coupled.psi(finite, 0, right, 128) == left


def test_locks_persist_or_break() -> None:
    """For 0011 the white right half locks (Psi repeats with period 7 from a small depth, as `coupled` finds), and the
    lock persists four times deeper; for 0001011 a right half whose Psi repeats with period 15 over depths 512 to 1024
    stops repeating at depth 2,193, read off the big-integer Psi."""
    census = finite_onset.classify("0011", 2, 2, 256)
    zero = next(entry for entry in census.locked if entry[0] == 0)
    assert zero[1:] == coupled.eventual_period(coupled.psi("0011", 2, 0, 256), 256, 128)
    assert finite_onset.lock_fate("0011", 2, 0, zero[1], zero[2], 1024) is None

    census = finite_onset.classify("0001011", 0, 9, 1024)
    entry = next(entry for entry in census.locked if entry[0] == 261)
    assert entry[2] == 15
    bits = format(coupled.psi("0001011", 0, 261, 4096), "b").zfill(4096)[::-1]  # depth 1 first
    first_break = next(j for j in range(entry[1] - 1, 4096 - 15) if bits[j] != bits[j + 15]) + 15 + 1
    assert finite_onset.lock_fate("0001011", 0, 261, entry[1], 15, 4096) == first_break == 2193
