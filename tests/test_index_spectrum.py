"""Checks of computations/index_spectrum.py against direct sums on small truth tables, and of the controls."""

from __future__ import annotations

import numpy as np

from computations import index_spectrum as s
from computations.rule30 import center_column


def test_transforms_match_direct_sums() -> None:
    rng = np.random.default_rng(3)
    bits = 6
    table = rng.integers(0, 2, 1 << bits, dtype=np.uint8)  # (64,)
    signs = 1 - 2 * table.astype(np.int64)  # (64,)
    n = np.arange(1 << bits)  # (64,)
    pc = s.popcounts(1 << bits)  # (64,)
    walsh = s.walsh(table)  # (64,)
    mod3 = s.mod3_transform(table)  # (64,)
    anf = s.moebius(table)  # (64,)
    best = 0.0
    for subset in range(1 << bits):
        overlap = pc[n & subset]  # (64,)
        assert walsh[subset] == int((signs * (1 - 2 * (overlap & 1))).sum())
        assert abs(mod3[subset] - (signs * s.OMEGA ** overlap).sum()) < 1e-9
        assert anf[subset] == int(table[n[(n & subset) == n]].sum() & 1)
        if subset:
            for residue in range(3):
                best = max(best, abs(float((signs * ((overlap % 3 == residue) - 1 / 3)).mean())))
    assert abs(s.mod3_bias(table) - best) < 1e-12
    assert s.monomial_profile(table)[0] == int(np.count_nonzero(anf))


def test_controls_and_center() -> None:
    bits = 10
    assert s.walsh_bias(s.thue_morse_table(bits)) == 1.0
    assert s.monomial_profile(s.rudin_shapiro_table(bits)) == (bits - 1, 2)
    assert abs(s.mod3_bias(s.mod3_table(bits)) - 4 / 9) < 0.01
    table = s.index_function(center_column(1 << bits), bits)  # (1024,)
    assert s.monomial_profile(table) == (524, 10)
    assert round(s.walsh_bias(table), 4) == 0.1113
    assert round(s.mod3_bias(table), 4) == 0.0736
