"""Tests for computations/gap_inverse_runs.py: the rows of a window against the kit's recursion `cone e t j` on random
gap words, the run counts against a brute force over every gap word of length 25 (the kit's recursion row by row on
whole words, distinct windows), the longest run found on a whole word, the C search against the Python one, the C
sampler against the exhaustive records, the grammar against its word counts, and the kit's chart on a sideways
diagram."""

from __future__ import annotations

import numpy as np

from computations import gap_inverse_runs as g
from computations.wedge_hypotheses import kit_inverse


def random_gap_word(rng: np.random.Generator, length: int) -> tuple[int, ...]:
    """A random word of the gap shift: blocks 122 and 12222 from a random offset, cut to `length`."""
    e: list[int] = []
    while len(e) < length + 5:
        e += [1, 2, 2] if rng.random() < 0.6 else [1, 2, 2, 2, 2]
    k = int(rng.integers(0, 5))
    return tuple(e[k:k + length])


def test_window_rows_against_kit_cone() -> None:
    rng = np.random.default_rng(0)
    checked = 0
    for _ in range(12):
        L = int(rng.integers(8, 31))
        e = random_gap_word(rng, L)
        assert g.is_gap_stream(e)
        cone = g.kit_cone(e)
        h = int(rng.integers(0, L // 2))
        rows = g.window_rows(e[h:])
        for i, row in enumerate(rows):
            assert len(row) == 2 * i + 1
            for t in range(2 * i + 1):
                if h + i - t >= 0:  # cone(t, h + i - t), defined since its last symbol is e_{h+i}
                    assert row[t] == cone(t, h + i - t)
                    checked += 1
            if i >= h:
                assert row[h + i] == cone(h + i, 0)  # the inverse at h + i
    assert checked > 1000


def test_counts_against_brute_force_and_c() -> None:
    L, n, rmax = 25, 13, 12
    brute = g.brute_counts(g.GAP, L, rmax)  # (L + 1, rmax + 1)
    rc = g.run_counts(g.GAP, n, rmax)
    for s in range(2 * n + 1):
        for r in range(1, rmax + 1):
            if s + r <= L:
                assert brute[s, r] == rc.counts[s, r], (s, r)
    assert rc.record()[17] == 8 and rc.witness[17] == (2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2)
    c = g.c_counts(g.GAP, n, rmax, threads=1, progress=False)
    assert (c.counts == rc.counts).all() and c.witness == rc.witness
    assert (c.words[1:] == g.language_counts(g.GAP, n + 1)[1:].astype(np.int64)).all()
    hc = g.run_counts(g.HARD_CORE, 6, rmax)
    assert (g.c_counts(g.HARD_CORE, 6, rmax, threads=1, progress=False).counts == hc.counts).all()
    hb = g.brute_counts(g.HARD_CORE, 12, rmax)
    assert all(hb[s, r] == hc.counts[s, r] for s in range(13) for r in range(1, rmax + 1) if s + r <= 12)


def test_grammar_and_coin() -> None:
    for cls in (g.GAP, g.BINARY, g.HARD_CORE):
        counts = g.language_counts(cls, 12)
        assert all(counts[m] == len(g.factor_words(cls, m)) for m in range(13))
    words = g.factor_words(g.GAP, 12)
    assert all(g.is_gap_stream(w) for w in words) and not g.is_gap_stream((1, 2, 1))
    lam = g.gap_lambda()
    assert abs(lam ** 5 - lam ** 2 - 1) < 1e-12 and abs(lam - 1.19386) < 1e-5
    coin = g.coin_counts(g.GAP, 10, 4)
    assert coin[7, 3] == 2 * len(g.factor_words(g.GAP, 4 + 3)) / 64


def test_sampler_within_exhaustive_records() -> None:
    n = 15
    rec = g.run_counts(g.GAP, n, 30).record()  # (2n + 1,)
    sm = g.sample_runs(g.GAP, 2 * n, 400, seed=2, rmax=30, threads=1, progress=False)
    assert sum(sm.longest.values()) == 400
    assert all(sm.maxrun[s] <= rec[s] for s in range(2 * n))
    assert sm.maxrun[17] == 8  # the run of length 8 at s = 17 is common enough to be drawn


def test_kit_chart_on_sideways_diagram() -> None:
    for half in (0, 0b1011):
        res = g.chart_check(half, 90)
        assert res["failures"] == 0 and res["checked"] > 300


def test_run_of_fifteen_at_149() -> None:
    """The longest run of the search to s = 180, checked on a whole gap word by the kit's recursion."""
    window = "122221222212212222122122122122122122122122221221221221221222212222122122122221221221221222"
    e = [1, 2, 2] * 23 + [1, 2, 2, 2, 2] + [int(ch) for ch in window]  # the window at floor(149 / 2) = 74
    assert len(e) == 164 and g.is_gap_stream(e)
    inv = kit_inverse(np.array([e], dtype=np.uint8))[0]  # (164,)
    assert inv[148] == 0 and (inv[149:164] == 3).all()
