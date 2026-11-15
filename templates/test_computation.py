"""Tests of computations.<module>: <what each test checks it against>.

Copy to tests/test_<module>.py. Check the computation against something independent (a second implementation, a known
sequence, a direct run with `step`, or a number its entry quotes), on cases small enough that the whole suite stays
under a minute.
"""

from __future__ import annotations

import numpy as np

from computations import example as module  # replace `example` with <module>, the module under test
from computations.rule30 import step


def test_running_density_against_direct_rows() -> None:
    """The density of every prefix against center cells read from rows stepped one at a time with `step`."""
    n = 256
    row, cells = 1 << n, []  # the black cell at bit n leaves room for n steps of the left edge
    for _ in range(n):
        cells.append((row >> n) & 1)
        row = step(row)
    expected = np.cumsum(cells) / np.arange(1, n + 1)  # (n,)
    assert np.array_equal(module.running_density(np.array(cells)), expected)
