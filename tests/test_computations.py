"""Each computation against an independent implementation, a known sequence, or the numbers its entry quotes."""

from __future__ import annotations

import numpy as np
import pytest

from pathlib import Path

from computations import algebra, frames, game, held_map, left_diagonals, linear_complexity, sensitivity
from computations.rule30 import center_column, spacetime, step


ROOT = Path(__file__).resolve().parents[1]


def single_column(n: int) -> np.ndarray:
    """The center column by direct evolution of a bool array, independent of the integer rows."""
    cells = np.zeros(2 * n + 1, dtype=bool)  # (2n + 1,)
    cells[n] = True
    return spacetime(cells, n - 1)[:, n].astype(np.uint8)  # (n,)


def test_center_column() -> None:
    """The integer rows against direct evolution, and the first ten cells against OEIS A051023, as the Lean spot check
    states them."""
    assert np.array_equal(center_column(300), single_column(300))
    assert center_column(10).tolist() == [1, 1, 0, 1, 1, 1, 0, 0, 1, 1]


@pytest.mark.parametrize("k", range(6))
def test_seed_extensions(k: int) -> None:
    """The seeds (10)^k 1 and (10)^k 11 keep the center column and differ from the single cell's rows exactly where
    `sigma_difference` and `tau_difference` say."""
    steps, origin = 200, 220
    width = 2 * origin + 1
    for extra in (False, True):
        cells = np.zeros(width, dtype=bool)  # (width,), cell x at index origin + x
        cells[origin:origin + 2 * k + 1:2] = True
        if extra:
            cells[origin + 2 * k + 1] = True
        single = np.zeros(width, dtype=bool)  # (width,)
        single[origin] = True
        rows, reference = spacetime(cells, steps), spacetime(single, steps)  # (steps + 1, width) each
        assert np.array_equal(rows[:, origin], reference[:, origin])
        for t in range(steps + 1):
            offsets = {int(x) - origin - t for x in np.flatnonzero(rows[t] != reference[t])}
            if not extra:
                expected = set(range(2, 2 * k + 1, 2)) if t % 2 == 0 else (
                    {0, *range(1, 2 * k, 2), 2 * k} if k > 0 else set())
            else:
                expected = {*range(2, 2 * k + 1, 2), 2 * k + 1} if t % 2 == 0 else {0, *range(1, 2 * k + 2, 2)}
            assert offsets == expected, (k, extra, t)


def test_seed_past() -> None:
    """rho_k = Phi^-k(1) for k to 100: Phi^k(rho_k) = 1, the period word dies on a ring in exactly k steps, and the
    periods and preperiods are those the frames finding quotes."""
    periods, preperiods = {}, {}
    for k, prefix, period in frames.seed_past(100):
        frames.check_past(k, prefix, period)
        periods[k], preperiods[k] = len(period), len(prefix)
    starts = {p: min(k for k in periods if periods[k] == p) for p in set(periods.values())}
    assert starts == {1: 1, 3: 2, 6: 4, 12: 10, 24: 18, 48: 66}
    assert preperiods[28] == 0 and preperiods[30] == 4 and preperiods[66] == 188
    ((_, prefix, period),) = frames.seed_past(1)
    assert (prefix, period) == ([], [1]) and frames.phi((1 << 16) - 1, 16) == 1  # rho_1 = -1, the black half-line


def test_psi() -> None:
    """Psi(1) is the center column, and Psi preserves the first bit at which two numbers differ."""
    bits = 64
    psi_one = frames.psi(1, bits)
    assert [(psi_one >> t) & 1 for t in range(bits)] == center_column(bits).tolist()
    rng = np.random.default_rng(30)
    for _ in range(200):
        a = int(rng.integers(0, 1 << 62))
        n = int(rng.integers(0, 40))
        b = a ^ (1 << n) ^ (int(rng.integers(0, 1 << 20)) << (n + 1))
        difference = frames.psi(a, bits) ^ frames.psi(b, bits)
        assert difference & -difference == 1 << n


def test_left_diagonals() -> None:
    """The white diagonals and period records below depth 700 after 1,200 steps: depths 2, 7, 28 and 399, and records
    at 3, 8, 29 and 400, as Wolfram's notes give them."""
    white, records = left_diagonals.survey(left_diagonals.diagonals(1200, 700, 128))
    assert [(d.depth, d.previous_period, d.previous_weight, d.next_period) for d in white] == [
        (2, 1, 1, 2), (7, 2, 1, 4), (28, 4, 3, 8), (399, 8, 3, 16)]
    assert records == {1: 1, 3: 2, 8: 4, 29: 8, 400: 16}


def test_sensitivity() -> None:
    """A flip at -d reaches the center at exactly t = d; flips at +1 and +2 never do; from the right the median
    arrival over d = 3 .. 256 is about 2.5 d."""
    assert all(sensitivity.arrival(-d, 200) == d for d in range(1, 65))
    assert sensitivity.arrival(1, 3000) is None and sensitivity.arrival(2, 3000) is None
    ratios = np.array([sensitivity.arrival(d, 8 * d + 50) / d for d in range(3, 257)])  # (254,)
    assert ratios.min() >= 1 and 2.3 < float(np.median(ratios)) < 2.7


def test_degree() -> None:
    """The center cell at time t has degree 2t - 1, with the single top monomial over cells -t + 2 .. t for t >= 3, and
    the monomial counts the structure finding quotes; the Moebius transform inverts back to the truth table."""
    counts = {3: 30, 4: 122, 5: 346, 6: 1360, 7: 4852, 8: 23094}
    for t in range(2, 9):
        anf = algebra.center_anf(t)  # (2^(2t + 1),)
        degree, top = algebra.degree_and_top(anf)
        assert degree == 2 * t - 1
        if t >= 3:
            assert top == [sum(1 << (x + t) for x in range(-t + 2, t + 1))]
            assert int(anf.sum()) == counts[t]
    table = algebra.center_truth_table(3)  # (128,)
    assert np.array_equal(algebra.moebius(algebra.moebius(table)), table)


def test_duhamel() -> None:
    """The center column as 1 plus the Rule 150 kernel applied to the earlier adjacent black pairs."""
    assert np.array_equal(algebra.duhamel_center(96), center_column(96))


def test_held_map() -> None:
    """The vectorized search against Python integers for every support to 12 in both phases, and at support 20 the
    latest first failures the period-two finding quotes, 37 at odd checks and 30 at even."""
    for support in range(1, 13):
        for phase in (0, 1):
            expected = []
            for U in range(1 << (support - 1), 1 << support):
                V, t = U, 0
                while not ((t + phase) % 2 == 1 and V & 1 == 0) and t < 63:
                    V, t = held_map.held(V), t + 1
                expected.append(t)
            assert held_map.first_failures(support, phase).tolist() == expected, (support, phase)
    assert [int(held_map.first_failures(20, phase).max()) for phase in (0, 1)] == [37, 30]


def test_linear_complexity() -> None:
    """Berlekamp-Massey recovers an LFSR's order and a period's bound, and puts the center column at n / 2."""
    lfsr = [1, 0, 0, 1, 1]
    while len(lfsr) < 200:
        lfsr.append(lfsr[-3] ^ lfsr[-5])  # x^5 + x^2 + 1
    assert linear_complexity.complexity_profile(np.array(lfsr))[-1] == 5
    assert linear_complexity.complexity_profile(np.array([0, 0, 1, 1] * 50))[-1] == 3
    profile = linear_complexity.complexity_profile(center_column(4096))  # (4096,)
    assert np.abs(profile - np.arange(1, 4097) / 2).max() <= 12


def column_minus_one(pattern: str, right: np.ndarray, steps: int) -> np.ndarray:
    """Column -1, c_(t+1) xor (c_t or cell 1), for t < steps, of a finite right half driven by a center repeating
    `pattern`."""
    # right: (r,)
    c = np.array([int(pattern[t % len(pattern)]) for t in range(steps + 1)], dtype=bool)  # (steps + 1,)
    row = np.concatenate([right.astype(bool), np.zeros(steps + 2, dtype=bool)])  # (r + steps + 2,), cells 1, 2, ...
    out = np.zeros(steps, dtype=bool)  # (steps,)
    for t in range(steps):
        out[t] = c[t + 1] ^ (c[t] | row[0])
        left = np.concatenate([[c[t]], row[:-1]])  # (r + steps + 2,)
        right_cells = np.concatenate([row[1:], [False]])  # (r + steps + 2,)
        row = left ^ (row | right_cells)
    return out  # (steps,)


def test_game() -> None:
    """The game excludes the constant blocks, 0 1^9 and 0^6 1^2 and leaves 01 open; on real right halves driven by
    0^6 1^2 column -1 is eventually periodic, as the game says; and the certificates in FiniteGame.lean are the ones
    `game_certificate` builds."""
    assert game.bad_pairs("0", 4) == 0 and game.bad_pairs("1", 4) == 0
    assert game.bad_pairs("0111111111", 6) == 0 and game.bad_pairs("00000011", 6) == 0
    assert game.bad_pairs("01", 8) > 0
    assert game.necklaces(4) == ["0001", "0011", "0111"]
    rng = np.random.default_rng(7)
    for _ in range(20):
        column = column_minus_one("00000011", rng.integers(0, 2, size=40), 800)  # (800,)
        tail = column[400:].reshape(-1, 8)  # (50, 8), one period a row
        assert (tail == tail[0]).all()
    lean = (ROOT / "Rule30Open" / "Columns" / "FiniteGame.lean").read_text(encoding="utf-8")
    for pattern, width in (("01111111", 5), ("00000011", 6)):
        assert game.lean_certificate(pattern, width) in lean, pattern
    with pytest.raises(ValueError, match="not a function of the phase"):
        game.game_certificate("01", 8)


def test_step_is_rule_30() -> None:
    """The integer step is Wolfram's code 30 on every neighborhood: neighborhood 4l + 2c + r maps to bit 4l + 2c + r
    of 30."""
    for neighborhood in range(8):
        left, center, right = neighborhood >> 2, (neighborhood >> 1) & 1, neighborhood & 1
        row = (left << 1) | (center << 2) | (right << 3)  # cells x - 1, x, x + 1 at bits 1, 2, 3
        assert (step(row) >> 2) & 1 == (30 >> neighborhood) & 1
