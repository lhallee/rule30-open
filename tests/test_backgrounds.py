"""Tests of computations.backgrounds: the column under the edge of a row periodic to the left and white to the right,
against Rule 30 run directly on the cells of the row, and the column periods that the periodic-backgrounds finding
quotes."""

from __future__ import annotations

import itertools
import numpy as np

from computations import backgrounds


def direct_columns(rows: list[tuple[list[int], list[int]]], steps: int) -> np.ndarray:
    """Cell 0 at times 0 .. steps - 1 for each row, run with Rule 30 on a window of cells: cell -k is bit k of
    prefix + period repeated, and the cells right of 0 are white. Errors from the window's two ends move one cell per
    step, so the window [-steps - 1, steps] keeps cell 0 exact for `steps` steps."""
    width = 2 * steps + 2  # cells -steps - 1 .. steps, cell x at index x + steps + 1
    origin = steps + 1
    cells = np.zeros((len(rows), width), dtype=bool)  # (r, width)
    for i, (prefix, period) in enumerate(rows):
        bits = list(prefix)
        while len(bits) < origin + 1:
            bits += period
        cells[i, :origin + 1] = bits[:origin + 1][::-1]  # cell -k at index origin - k
    column = np.zeros((len(rows), steps), dtype=np.uint8)  # (r, steps)
    for t in range(steps):
        column[:, t] = cells[:, origin]
        left = np.zeros_like(cells)  # (r, width), cell x - 1
        left[:, 1:] = cells[:, :-1]
        right = np.zeros_like(cells)  # (r, width), cell x + 1
        right[:, :-1] = cells[:, 1:]
        cells = left ^ (cells | right)  # (r, width)
    return column  # (r, steps)


def least_form(prefix: list[int], period: list[int]) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """The eventually periodic sequence prefix + period repeated, with its least period and least preperiod, read
    from a sample long enough to hold both twice."""
    sample = list(prefix)
    while len(sample) < len(prefix) + 3 * len(period):
        sample += period
    p = next(d for d in range(1, len(period) + 1)
             if all(sample[i] == sample[i + d] for i in range(len(prefix), len(sample) - d)))
    m = next(m for m in range(len(prefix) + 1) if all(sample[i] == sample[i + p] for i in range(m, len(sample) - p)))
    return tuple(sample[:m]), tuple(sample[m:m + p])


def least_column_period(column: np.ndarray, max_period: int) -> int | None:
    """The least p up to `max_period` with which the second half of the column repeats, read entry by entry."""
    # column: (steps,)
    tail = column[len(column) // 2:].tolist()
    for p in range(1, max_period + 1):
        if all(tail[i] == tail[i + p] for i in range(len(tail) - p)):
            return p
    return None


def test_columns_against_direct_runs() -> None:
    """`background_column` is cell 0 of the row run directly, for every row with a period word of up to 4 cells and a
    prefix of up to 2, and `column_period` reads the least period of its second half."""
    rows = [(list(prefix), list(word)) for q in range(1, 5) for word in itertools.product((0, 1), repeat=q)
            for length in range(3) for prefix in itertools.product((0, 1), repeat=length)]
    steps = 128
    direct = direct_columns(rows, steps)  # (r, steps)
    for (prefix, period), column in zip(rows, direct, strict=True):
        assert backgrounds.background_column(prefix, period, steps).tolist() == column.tolist(), (prefix, period)
        assert backgrounds.column_period(column, 64) == least_column_period(column, 64), (prefix, period)


def test_periodic_columns_survey() -> None:
    """`periodic_columns` lists each row of period word up to 5 cells and prefix up to 1 cell once, in its least form,
    exactly when its directly run column repeats over the second half of 256 steps, with that least period."""
    steps = 256
    forms = {least_form(list(prefix), list(word)) for q in range(1, 6) for word in itertools.product((0, 1), repeat=q)
             for length in range(2) for prefix in itertools.product((0, 1), repeat=length)}
    rows = [(list(prefix), list(period)) for prefix, period in sorted(forms)]
    direct = direct_columns(rows, steps)  # (r, steps)
    want = {(tuple(prefix), tuple(period), p) for (prefix, period), column in zip(rows, direct, strict=True)
            if (p := least_column_period(column, 64)) is not None}
    found = backgrounds.periodic_columns(5, 1, steps)
    assert len(found) == len(want)
    assert {(tuple(prefix), tuple(period), p) for prefix, period, p in found} == want
    assert {least_form(prefix, period) for prefix, period, _ in found} == {(a, b) for a, b, _ in want}


def test_quoted_periods() -> None:
    """The finding's table over 2,048 steps, on the rows of each background with no prefix, every rotation of its
    word: white and the stripe give a constant column, the ether words 0000001, 0010011 and 0111111 columns of periods
    4 and 8, 0000111 and 0011111 of period 8, and a sample of other backgrounds no period up to 64."""
    steps = 2048

    def periods(word: str) -> set[int | None]:
        rotations = (word[r:] + word[:r] for r in range(len(word)))
        columns = (backgrounds.background_column([], [int(c) for c in w], steps) for w in rotations)  # (steps,) each
        return {backgrounds.column_period(column, 64) for column in columns}

    assert periods("0") == {1} and periods("01") == {1}
    for word in ("0000001", "0010011", "0111111"):
        assert periods(word) - {None} == {4, 8}, word
    for word in ("0000111", "0011111"):
        assert periods(word) - {None} == {8}, word
    for word in ("001", "011", "0001", "0011", "00101", "001011"):  # one rotation each
        column = backgrounds.background_column([], [int(c) for c in word], steps)  # (steps,)
        assert backgrounds.column_period(column, 64) is None, word


def test_prefix_growth() -> None:
    """`prefix_growth` against the least preperiod of the row at each time, read from Rule 30 run directly: the frame's
    bit k at time n is cell n - k."""
    steps = 40
    for prefix, period in (([], [0, 0, 0, 0, 0, 0, 1]), ([0], [0, 1, 1]), ([1, 0], [0, 0, 1, 1, 1, 1, 1])):
        grown = backgrounds.prefix_growth(list(prefix), list(period), steps)
        q = len(period)
        span = len(prefix) + 2 * steps + 6 * q  # bits of the frame kept at each time
        origin = span + steps + 1  # cell 0 at this index; cells left of index steps + 1 - n are exact at time n
        bits = list(prefix)
        while len(bits) < origin + 1:
            bits += period
        cells = np.zeros(origin + steps + 2, dtype=bool)  # (cells,), white right of cell 0
        cells[:origin + 1] = bits[:origin + 1][::-1]
        for n in range(steps + 1):
            frame = [int(cells[origin + n - k]) for k in range(span)]  # bit k is cell n - k
            assert len(least_form(frame[:span - 3 * q], frame[span - 3 * q:span - 2 * q])[0]) == grown[n], (prefix, n)
            left = np.zeros_like(cells)  # (cells,)
            left[1:] = cells[:-1]
            right = np.zeros_like(cells)  # (cells,)
            right[:-1] = cells[1:]
            cells = left ^ (cells | right)
