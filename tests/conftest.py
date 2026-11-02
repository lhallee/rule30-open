"""Settings and fixtures shared by every test: one thread for the linear algebra libraries, the objects of the imports
frozen out of the garbage collector's passes, and the center column stepped once for the tests of its long windows and
the diagonals to depth 10,000 run once for the tests that quote them.

The suite runs serially on one core. OpenBLAS starts a thread per core by default, and on a machine whose other cores
are busy those threads wait on each other: `np.linalg.eigvals` of a 700 by 700 matrix takes about 8 s with four threads
under load and 0.45 s with one. The variables are read when numpy loads, so they are set here, before any test module
imports it; if numpy is already loaded, `threadpoolctl` limits the running pools instead, when it is installed.
"""

from __future__ import annotations

import gc
import os
import sys
from typing import TYPE_CHECKING

import pytest

if TYPE_CHECKING:
    from computations.settled_slope import Diagonals

for _name in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_name, "1")
if "numpy" in sys.modules:
    try:
        from threadpoolctl import threadpool_limits
    except ImportError:
        pass
    else:
        threadpool_limits(1)


def pytest_collection_finish(session: pytest.Session) -> None:
    """Move the objects that importing the modules and collecting the tests made to the collector's permanent
    generation, so that its full collections during and after the run, which pytest forces twice at the end, do not
    traverse them again: about 0.2 s of the run."""
    gc.freeze()


@pytest.fixture(scope="session")
def center_rows() -> tuple[bytes, dict[int, int]]:
    """The first 65,536 center cells, as the digits 0 and 1 (byte t is the center at step t), and the rows at steps
    16,384, 32,768 and 49,152 with the seed at bit 65,536, from rows stepped as integers one at a time: the reference
    that the tests of `long_window` and of the literals of `LongWindow` share, run once."""
    n = 65536
    # the row at step t is `row << (n - t - 1)`: its cells left of the light cone, n - t - 1 and below, are 0, so the
    # integer holds the 2t + 2 cells of the cone and the center is its bit t + 1
    row, cells, rows = 1 << 1, bytearray(n), {}
    for t in range(n):
        if t and t % 16384 == 0:
            rows[t] = row << (n - t - 1)
        cells[t] = 48 + ((row >> (t + 1)) & 1)
        row = (row << 2) ^ ((row << 1) | row)  # one step, then one cell further left: shifted by n - t - 2
    return bytes(cells), rows


@pytest.fixture(scope="session")
def deep_diagonals() -> Diagonals:
    """`settled_slope.stream` of the diagonals to depth 10,000 over 15,600 steps, read-only, for the quoted numbers of
    `test_settled_slope.py`, `test_front_walker.py` and `test_onset_heuristics.py`, which read the same run."""
    from computations.settled_slope import stream
    d = stream(10000, 15600, progress=False)
    d.onset.flags.writeable = d.tail.flags.writeable = False
    return d
