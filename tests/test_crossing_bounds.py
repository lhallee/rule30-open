"""The crossing-sequence bounds against brute force, against random machines, and against the controls."""

from __future__ import annotations

import numpy as np

from computations import crossing_bounds
from computations.rule30 import center_column


def test_split_matrix_indexing() -> None:
    """Rows are the low digits and columns the digits above the cut, with the top digit 1."""
    cells = center_column(1 << 8)  # (256,)
    matrix = crossing_bounds.split_matrix(cells, 7, 3)  # (8, 8)
    assert matrix.shape == (8, 8)
    for a in range(8):
        for b in range(8):
            n = a + 8 * (8 + b)  # digits above the cut: 1 then b, six digits in all with the cut at 3
            assert matrix[a, b] == 1 - 2 * int(cells[n])


def test_operator_norm_squared() -> None:
    """The Gram eigenvalue against the singular value, on a wide and on a tall matrix."""
    rng = np.random.default_rng(1)
    for shape in [(5, 40), (40, 5)]:
        matrix = rng.choice([-1, 1], size=shape).astype(np.int8)  # shape
        assert abs(crossing_bounds.operator_norm_squared(matrix) - np.linalg.norm(matrix.astype(float), 2) ** 2) < 1e-8


def test_controls() -> None:
    """Thue-Morse has rank 1 matrices, so norm^2 is 2^(ell-1) and the bound is 0; random signs sit near the Bai-Yin
    value, and the center column does too."""
    ell = 14
    top = 1 << ell
    thue = crossing_bounds.cut_norms(crossing_bounds.thue_morse(top), ell)  # (13,)
    assert np.allclose(thue, 2.0 ** (ell - 1))
    assert crossing_bounds.mean_time_bound(thue, ell, 2) < 1e-9
    for cells in [crossing_bounds.random_cells(top, 0), center_column(top)]:
        ratios = crossing_bounds.norm_ratios(crossing_bounds.cut_norms(cells, ell), ell)  # (13,)
        assert 0.8 < ratios.min() and ratios.max() < 2.0


def test_bound_shape() -> None:
    """More states weaken the bound, and a larger norm weakens it."""
    ell = 16
    base = 4.0 * 2 ** (ell // 2)
    assert crossing_bounds.mean_crossings_bound(base, ell, 2) > crossing_bounds.mean_crossings_bound(base, ell, 8)
    assert crossing_bounds.mean_crossings_bound(base, ell, 2) > crossing_bounds.mean_crossings_bound(8 * base, ell, 2)
    assert crossing_bounds.mean_crossings_bound(2.0 ** (ell - 1), ell, 2) < 1e-9


def test_lemma_on_random_machines() -> None:
    """The lemma on machines nobody designed: for every cut and every L, the number of inputs with at most L crossings is
    at most (the count of sequences of length <= L) times the squared norm of the machine's own answer matrix, and every
    set of inputs with one crossing sequence is a rectangle."""
    rng = np.random.default_rng(7)
    ell = 7
    checked = 0
    for _ in range(400):
        last_state = int(rng.integers(1, 3))
        machine = crossing_bounds.random_machine(rng, last_state, 1)
        runs = [crossing_bounds.run_machine(machine, (1 << (ell - 1)) + low, ell, 300) for low in range(1 << (ell - 1))]
        if any(run is None for run in runs):
            continue
        answers = np.array([run[0] for run in runs], dtype=np.uint8)  # (64,)
        padded = np.zeros(1 << ell, dtype=np.uint8)  # (128,)
        padded[1 << (ell - 1):] = answers
        checked += 1
        for cut in range(1, ell):
            matrix = crossing_bounds.split_matrix(padded, ell, cut)  # (2^cut, 2^(ell-1-cut))
            norm_squared = crossing_bounds.operator_norm_squared(matrix)
            groups: dict[tuple[int, ...], list[tuple[int, int]]] = {}
            for low in range(1 << (ell - 1)):
                a, b = low % (1 << cut), low >> cut
                groups.setdefault(tuple(runs[low][2][cut - 1]), []).append((a, b))
            for sequence, members in groups.items():
                rows = {a for a, _ in members}
                cols = {b for _, b in members}
                assert len(members) == len(rows) * len(cols)  # a rectangle
                assert len(members) <= norm_squared + 1e-6
            states = last_state + 1
            for length in range(0, 6):
                count = sum(len(m) for s, m in groups.items() if len(s) <= length)
                assert count <= sum(states**j for j in range(length + 1)) * norm_squared + 1e-6
    assert checked >= 20
