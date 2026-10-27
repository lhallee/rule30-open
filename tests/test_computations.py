"""Each computation against an independent implementation, a known sequence, or the numbers its entry quotes."""

from __future__ import annotations

import numpy as np
import pytest

from pathlib import Path

from computations import (algebra, deformation, frames, game, held_map, left_diagonals, linear_complexity,
                          lock_certificate, right_half, sensitivity)
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


CORE_0001 = [{1: 0, 2: 0, 3: 1}, {1: 0, 2: 1, 3: 1}, {1: 1, 2: 1, 3: 0}, {1: 1, 2: 0, 3: 1}]  # 001, 011, 110, 101


def driven_rows(word: str, start: int, steps: int, width: int) -> np.ndarray:
    """Columns 1 .. width at times 0 .. steps - 1 of a right half driven by a center repeating `word`, by direct
    evolution of a bool array long enough that its white right end is exact."""
    size = start.bit_length() + steps + 2
    row = np.array([(start >> i) & 1 for i in range(size)], dtype=bool)  # (size,), cells 1 .. size
    out = np.zeros((steps, width), dtype=np.uint8)  # (steps, width)
    for t in range(steps):
        out[t] = row[:width]
        left = np.concatenate([[word[t % len(word)] == "1"], row[:-1]])  # (size,)
        right = np.concatenate([row[1:], [False]])  # (size,)
        row = left ^ (row | right)
    return out  # (steps, width)


def stays_inside(word: str, member: np.ndarray) -> bool:
    """Every window of each phase's set, stepped as a full integer row with `rule30.step`, lands in the next phase's
    set for both values of the cell beyond the window."""
    # member: (period, 2^W)
    period, size = member.shape
    width = size.bit_length() - 1
    for ph in range(period):
        for state in np.flatnonzero(member[ph]).tolist():
            for beyond in (0, 1):
                row = int(word[ph]) | (state << 1) | (beyond << (width + 1))  # center at bit 0, column j at bit j
                if not member[(ph + 1) % period][(step(row) >> 1) & (size - 1)]:
                    return False
    return True


@pytest.fixture(scope="module")
def certificate() -> np.ndarray:
    """The greatest invariant set of 0001 at width 16, seeded with the three-column core."""
    member, _ = lock_certificate.greatest_invariant_set("0001", CORE_0001, 16)  # (4, 2^16)
    return member  # (4, 2^16)


def test_driven_spacetime() -> None:
    """The integer spacetime against direct evolution of a bool array, and its column 1 against `column_one`."""
    for start in right_half.random_starts(3, 64):
        rows = lock_certificate.spacetime("0001", start, 300, 20)  # (300, 20)
        assert np.array_equal(rows, driven_rows("0001", start, 300, 20))
        assert np.array_equal(rows[:, 0], right_half.column_one("0001", start, 300))


def test_phase_tables() -> None:
    """The empty start's table under 0001 has the core 0011, 0110, 1101 in columns 1 to 3, 28 forced cells in columns
    1 to 11 shared by three starts, and the forced cells the rule does not derive in three-valued logic are the ones
    the certificate finding lists; the tables of 0011 and 0111 are the 0001 table from column 2, and from column 4
    with the phases rotated by two."""
    base = lock_certificate.phase_table("0001", 0, 6000, 1000, 40)  # (40, 4)
    assert [lock_certificate.column_text(base, c) for c in (1, 2, 3)] == ["0011", "0110", "1101"]
    assert lock_certificate.core_seed(base, 3) == CORE_0001
    forced, agree = lock_certificate.forced_lattice("0001", right_half.random_starts(2, 64), 6000, 1000, 40)
    assert agree and (forced >= 0).sum(axis=1)[:12].tolist() == [4, 4, 4, 2, 1, 2, 1, 3, 2, 2, 3, 0]
    assert lock_certificate.underived_cells("0001", forced[:12]) == [[6, 8], [4, 8, 9], [5, 7, 10, 11], []]
    assert np.array_equal(lock_certificate.phase_table("0011", 0, 6000, 1000, 39), base[1:])
    assert np.array_equal(lock_certificate.phase_table("0111", 0, 6000, 1000, 37), np.roll(base[3:], 2, axis=1))


def test_affine_hull() -> None:
    """The hull's basis and constraint columns against brute force over all vectors of 8 bits."""
    rng = np.random.default_rng(30)
    width = 8
    for _ in range(20):
        codes = rng.integers(0, 1 << width, size=int(rng.integers(1, 5)))  # (n,), at most 4 points: some constraints
        base, basis = lock_certificate.affine_hull(codes)
        span = {0}
        for code in codes.tolist():
            span |= {x ^ code ^ base for x in span}
        assert len(span) == 1 << len(basis)
        orthogonal = [y for y in range(1 << width) if all(((y & v).bit_count() & 1) == 0 for v in span)]
        support = sorted({j + 1 for y in orthogonal for j in range(width) if (y >> j) & 1})
        assert lock_certificate.constraint_columns(basis, width) == support


def test_certificate(certificate: np.ndarray) -> None:
    """Seeded with the core, the greatest invariant set of 0001 is empty at width 14 and has 433, 533, 344 and 605
    windows at width 16, every one inside the core and stepping into the next phase's set for both beyond cells."""
    # certificate: (4, 2^16)
    empty, _ = lock_certificate.greatest_invariant_set("0001", CORE_0001, 14)  # (4, 2^14)
    assert not empty.any()
    assert certificate.sum(axis=1).tolist() == [433, 533, 344, 605]
    windows = np.arange(1 << 16)  # (2^16,)
    for ph in range(4):
        core = sum(value << (column - 1) for column, value in CORE_0001[ph].items())
        assert ((windows[certificate[ph]] & 0b111) == core).all()
    assert stays_inside("0001", certificate)


def test_core_persists_after_entry(certificate: np.ndarray) -> None:
    """Thirty of the 31 starts enter the width-16 set by step 207, and in a direct simulation columns 1 to 3 then read
    the core at every one of the next 2,000 steps; start 4 does not enter within 2,000 steps."""
    # certificate: (4, 2^16)
    for i, start in enumerate(right_half.random_starts(30, 64)):
        entry = lock_certificate.entry_time("0001", certificate, start, 2000)
        if i == 4:
            assert entry is None
            continue
        assert entry is not None and entry <= 207, i
        rows = driven_rows("0001", start, entry + 2000, 3)[entry:]  # (2000, 3)
        core = np.array([[CORE_0001[(entry + t) % 4][c] for c in (1, 2, 3)] for t in range(2000)])  # (2000, 3)
        assert np.array_equal(rows, core), i


def test_jen_certificates() -> None:
    """Seeded only with column 1 at the white phases, the certificate of 0111 exists at width 14 (column 1 white at
    phase 0 on all of it) and that of 0001 at width 16 extends the core set at phases 2 and 3; both are invariant."""
    seeds = lock_certificate.jen_seeds("0111")
    assert seeds == [[{1: 0}, {}, {}, {}], [{1: 1}, {}, {}, {}]]
    member = np.logical_or.reduce([lock_certificate.greatest_invariant_set("0111", seed, 14)[0]
                                   for seed in seeds])  # (4, 2^14)
    assert member.sum(axis=1).tolist() == [878, 1544, 1110, 1366]
    assert not (np.flatnonzero(member[0]) & 1).any()
    assert stays_inside("0111", member)
    member = np.logical_or.reduce([lock_certificate.greatest_invariant_set("0001", seed, 16)[0]
                                   for seed in lock_certificate.jen_seeds("0001")])  # (4, 2^16)
    assert member.sum(axis=1).tolist() == [433, 533, 944, 701]
    assert stays_inside("0001", member)


def test_forced_entry(certificate: np.ndarray) -> None:
    """From a window where entry is forced, random beyond cells, stepped with integer rows, reach the set within 30
    periods; and the counts the certificate finding quotes."""
    # certificate: (4, 2^16)
    forced = lock_certificate.forced_entry("0001", certificate)  # (4, 2^16)
    assert forced.sum(axis=1).tolist() == [2212, 2066, 1730, 1647]
    rng = np.random.default_rng(30)
    for _ in range(300):
        ph = int(rng.integers(0, 4))
        window = int(rng.choice(np.flatnonzero(forced[ph])))
        for _ in range(4 * 30):
            if certificate[ph][window]:
                break
            row = int("0001"[ph]) | (window << 1) | (int(rng.integers(0, 2)) << 17)  # center, window, beyond cell
            window, ph = (step(row) >> 1) & 0xFFFF, (ph + 1) % 4
        assert certificate[ph][window]


def test_deformation() -> None:
    """The deformed center cell's T-degrees and term counts for t <= 12; at T = 1 it is Rule 30's center column and at
    T = 0 Rule 150's whole row."""
    table = deformation.center_degrees(12)
    assert [degree for degree, _ in table] == [0, 1, 0, 3, 6, 10, 16, 27, 44, 70, 114, 190]
    assert [terms for _, terms in table] == [1, 2, 1, 3, 5, 6, 10, 15, 21, 38, 54, 102]
    rows = deformation.deformed_rows(16)
    assert [rows[t].get(0, 0).bit_count() & 1 for t in range(17)] == center_column(17).tolist()
    cells = np.zeros(35, dtype=bool)  # (35,), cell x at index x + 17
    cells[17] = True
    for t in range(17):
        assert [int(x) - 17 for x in np.flatnonzero(cells)] == sorted(x for x, cell in rows[t].items() if cell & 1)
        cells = np.concatenate([[False], cells[:-1]]) ^ cells ^ np.concatenate([cells[1:], [False]])  # (35,), Rule 150
