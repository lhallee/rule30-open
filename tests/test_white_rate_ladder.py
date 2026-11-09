"""white_rate_ladder against independent checks: the zero-boundary half line run cell by cell, and the two dynamic
programs against every free word run through the right ladder's own simulation (`right_ladder.simulate`)."""

from __future__ import annotations

from itertools import product

import numpy as np

from computations import right_ladder as rl
from computations import white_rate_ladder as wr


def free_words(n: int) -> np.ndarray:
    """Every free word of length n, one per row."""
    return np.array(list(product((0, 1), repeat=n)), dtype=np.uint8)  # (2^n, n)


def test_zero_boundary_columns() -> None:
    # Rule 30 on the cells -1 .. -40 with cell 0 held white, from one black cell at -1, one cell at a time
    y, z = wr.zero_boundary_columns(30)
    row = {-1: 1}
    for t in range(1, 31):
        assert (y[t], z[t]) == (row.get(-1, 0), row.get(-2, 0))
        row = {i: row.get(i - 1, 0) ^ (row.get(i, 0) | (row.get(i + 1, 0) if i + 1 <= -1 else 0)) for i in range(-40, 0)}


def test_kick_free_against_every_word() -> None:
    # the most white cells among c(1 .. T) over the plays of level 1 with no kick at times 1 .. T
    for T in range(2, 11):
        c = rl.simulate(1, free_words(T + 1))  # (2^(T+1), T + 2): c(0 .. T + 1)
        kicks = ((c[:, 1:T + 1] == 1) & (c[:, 2:T + 2] == 1)).any(axis=1)  # (2^(T+1),)
        white = (c[~kicks, 1:T + 1] == 0).sum(axis=1)  # (n,)
        y, _ = wr.zero_boundary_columns(T + 1)
        assert wr.kick_free_white(y, T)[T] == int(white.max()), T


def test_fewest_kicks_against_every_word() -> None:
    for k in (1, 2):
        for T in range(3, 10):
            c = rl.simulate(k, free_words(T + 1))  # (2^(T+1), T + 2)
            kicks = ((c[:, 1:T + 1] == 1) & (c[:, 2:T + 2] == 1)).sum(axis=1)  # (2^(T+1),)
            assert wr.fewest_kicks(k, T, 20) == int(kicks.min()), (k, T)


def test_forcing_word() -> None:
    assert not wr.forces_kick(1, "0010000") and not wr.forces_kick(2, "0010000")
    assert all(wr.forces_kick(k, "0010000") for k in (3, 4))
    assert not wr.forces_kick(2, "1111") and not wr.forces_kick(1, "0")
