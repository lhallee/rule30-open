"""Tests of computations.long_window: the windows of `LongWindow` and `WideWindow` against integer rows stepped one at
a time and every earlier factor."""

from __future__ import annotations

import numpy as np

from computations import long_window


def test_long_window(center_rows: tuple[bytes, dict[int, int]]) -> None:
    """The window of `LongWindow`: the packed center cells and the three checkpoint rows against the integer rows
    stepped one at a time (`center_rows`), and the new factor against the set of every earlier factor, read as
    strings."""
    bits, checkpoints = long_window.simulate()
    cells, rows = center_rows
    column = np.frombuffer(cells, dtype=np.uint8) - 48  # (N,)
    assert np.array_equal(np.frombuffer(format(bits, f"0{long_window.N}b")[::-1].encode(), dtype=np.uint8) - 48, column)
    assert checkpoints == rows and sorted(checkpoints) == [16384, 32768, 49152]
    length = long_window.new_factor(bits)
    text = cells.decode()
    for size, new in ((length - 1, False), (length, True)):
        start = long_window.N - size
        earlier = {text[j:j + size] for j in range(start)}
        assert (text[start:] not in earlier) == new, size
    assert length == 19


def test_wide_window(center_rows: tuple[bytes, dict[int, int]]) -> None:
    """The window of `WideWindow`, at 32,768 cells instead of 262,144 (the same functions, `long_window.simulate` and
    `new_factor`): the packed center cells and the checkpoint row against the integer rows stepped one at a time
    (`center_rows`, whose seed is 32,768 bits higher: a row is the same shifted while no cell has reached bit 0), and
    the new factor of length 18 against the sets of earlier factors."""
    n = 2 * 16384
    bits, checkpoints = long_window.simulate(n)
    cells, rows = center_rows
    column = np.frombuffer(cells[:n], dtype=np.uint8) - 48  # (n,)
    assert np.array_equal(np.frombuffer(format(bits, f"0{n}b")[::-1].encode(), dtype=np.uint8) - 48, column)
    assert sorted(checkpoints) == [16384]
    for t, row in checkpoints.items():
        assert rows[t] & ((1 << (long_window.N - n)) - 1) == 0 and row == rows[t] >> (long_window.N - n), t
    text = cells[:n].decode()
    for size, new in ((17, False), (18, True)):
        start = n - size
        earlier = {text[j:j + size] for j in range(start)}
        assert (text[start:] not in earlier) == new, size
    assert long_window.new_factor(bits, n) == 18
