"""The longest runs from a late onset (`computations.late_onset`) against stepping each row as an integer, the
left-permutive row that follows any target, and the optional SAT search against the bit slices."""

from __future__ import annotations

import numpy as np
import pytest

from computations import late_onset


def test_runs_against_integer_rows() -> None:
    """The bit-sliced longest runs equal those of every row stepped as a whole integer, for columns beyond the
    support too, a periodic target and two random ones."""
    cells, steps, max_onset, margin = 6, 36, 16, 3
    targets = [late_onset.periodic_target("011", 1, steps)] + late_onset.random_targets(2, steps)
    runs = late_onset.runs_for_targets(cells, steps, max_onset, targets, margin)  # (3, onsets, columns)
    want = np.zeros_like(runs)  # (3, onsets, columns)
    for row in range(1, 1 << cells):
        for c, column in enumerate(range(-margin, cells + margin)):
            values = late_onset.simulate_column(row, cells, column, steps)
            for k, target in enumerate(targets):
                agree = [v == w for v, w in zip(values, target)]
                for onset in range(max_onset):
                    length = next((i for i, ok in enumerate(agree[onset:]) if not ok), steps - onset)
                    want[k, onset, c] = max(want[k, onset, c], length)
    assert (runs == want).all()


def test_free_bits_follow_any_target() -> None:
    """The row built cell by cell from the right follows any target of its width in column w - 1 + T0 from every
    onset, so over the columns of the light cone the longest run is at least w at every onset."""
    rng = np.random.default_rng(5)
    for _ in range(20):
        width, onset = int(rng.integers(3, 12)), int(rng.integers(0, 30))
        target = rng.integers(0, 2, width).tolist()
        row = late_onset.free_bit_row(target, onset)
        assert row < 1 << width
        assert late_onset.simulate_column(row, width, width - 1 + onset, onset + width)[onset:] == target
    cells, steps, max_onset = 6, 30, 12
    targets = [late_onset.periodic_target(w, p, steps) for w in late_onset.WORDS for p in range(len(w))]
    runs = late_onset.runs_for_targets(cells, steps, max_onset, targets, margin=max_onset)
    assert (runs.max(axis=2) >= cells).all()


def test_sat_against_bit_slices() -> None:
    """The SAT search of the middle column gives the bit slices' longest run (python-sat, optional)."""
    pytest.importorskip("pysat")
    for cells, onset in ((8, 0), (8, 13), (9, 30)):
        for target in (late_onset.periodic_target("01", 1, onset + cells + 20),
                       late_onset.periodic_target("011", 2, onset + cells + 20),
                       late_onset.random_targets(1, onset + cells + 20, seed=cells + onset)[0]):
            cap = cells + 15
            runs = late_onset.runs_for_targets(cells, onset + cap + 1, onset + 1, [target])
            assert late_onset.sat_longest(cells, target, onset, cap)[0] == min(int(runs[0, onset, cells // 2]), cap)
