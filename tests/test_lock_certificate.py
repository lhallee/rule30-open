"""Tests of computations.lock_certificate: phase tables, invariant sets and certificate tables against direct
evolution of bool arrays, brute force and integer rows stepped with `step`."""

from __future__ import annotations

import numpy as np
import pytest

from computations import lock_certificate, right_half
from computations.rule30 import step
from references import CORE_0001, ROOT


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


def driven_rows_many(word: str, starts: list[int], steps: int, width: int) -> np.ndarray:
    """`driven_rows` for several halves at once, one row of a bool array each, each row cut every step to the cells
    that can still reach columns 1 .. width before the last step: a cell reaches the one left of it in one step, so the
    row at step t is exact where it is needed if it keeps width + steps - t cells."""
    size = max(start.bit_length() for start in starts) + steps + 2
    rows = np.array([[(start >> i) & 1 for i in range(size)] for start in starts], dtype=bool)  # (k, size)
    out = np.zeros((len(starts), steps, width), dtype=np.uint8)  # (k, steps, width)
    for t in range(steps):
        out[:, t] = rows[:, :width]
        rows = rows[:, :width + steps - t]  # (k, n)
        center = np.full((len(starts), 1), word[t % len(word)] == "1")  # (k, 1)
        left = np.concatenate([center, rows[:, :-1]], axis=1)  # (k, n)
        right = np.concatenate([rows[:, 1:], np.zeros((len(starts), 1), dtype=bool)], axis=1)  # (k, n)
        rows = left ^ (rows | right)
    return out  # (k, steps, width)


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


def test_driven_spacetime() -> None:
    """The integer spacetime against direct evolution of a bool array, and its column 1 against `column_one`; the
    evolution of the four halves at once, cut to the cells that can still reach the columns read (`driven_rows_many`),
    gives the same rows."""
    starts = right_half.random_starts(3, 64)
    many = driven_rows_many("0001", starts, 300, 20)  # (4, 300, 20)
    for i, start in enumerate(starts):
        rows = lock_certificate.spacetime("0001", start, 300, 20)  # (300, 20)
        assert np.array_equal(rows, driven_rows("0001", start, 300, 20)) and np.array_equal(rows, many[i])
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
    """Thirty of the 31 starts enter the width-16 set by step 207, and in a direct simulation of the 31 at once
    (`driven_rows_many`) columns 1 to 3 then read the core at every one of the next 2,000 steps; start 4 does not enter
    within 2,000 steps."""
    # certificate: (4, 2^16)
    starts = right_half.random_starts(30, 64)
    entries = [lock_certificate.entry_time("0001", certificate, start, 2000) for start in starts]
    assert entries[4] is None and all(entry is not None and entry <= 207 for i, entry in enumerate(entries) if i != 4)
    runs = driven_rows_many("0001", starts, 207 + 2000, 3)  # (31, 2207, 3)
    for i, entry in enumerate(entries):
        if entry is not None:
            core = np.array([[CORE_0001[(entry + t) % 4][c] for c in (1, 2, 3)] for t in range(2000)])  # (2000, 3)
            assert np.array_equal(runs[i, entry:entry + 2000], core), i


def test_jen_certificates() -> None:
    """Seeded only with column 1 at the white phases, the certificate of 0111 exists at width 14 (column 1 white at
    phase 0 on all of it) and that of 0001 at width 16 extends the core set at phases 2 and 3; both are invariant.
    `jen_sets` keeps the greatest invariant set of each seed, which the coin certificates and `certificate_tables`
    read again."""
    seeds = lock_certificate.jen_seeds("0111")
    assert seeds == [[{1: 0}, {}, {}, {}], [{1: 1}, {}, {}, {}]]
    sets = lock_certificate.jen_sets("0111", 14)  # (4, 2^14) each, `greatest_invariant_set` of each seed, kept
    assert len(sets) == 2 and all(np.array_equal(sets[i], lock_certificate.greatest_invariant_set("0111", seed, 14)[0])
                                  for i, seed in enumerate(seeds))
    member = np.logical_or.reduce(sets)  # (4, 2^14)
    assert member.sum(axis=1).tolist() == [878, 1544, 1110, 1366]
    assert not (np.flatnonzero(member[0]) & 1).any()
    assert stays_inside("0111", member)
    member = np.logical_or.reduce(lock_certificate.jen_sets("0001", 16))  # (4, 2^16)
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


def test_period_four_certificate_traps(monkeypatch: pytest.MonkeyPatch) -> None:
    """`lock_certificate.certificate_tables`: the certificates of 0001 at width 16 and of 0011 and 0111 at width 14 have
    2,611, 1,915 and 4,898 windows, each is a lock by `lock_chain.is_lock`, a direct check with the rule, and
    `lean_certificates`, restricted to the certificate of 0011, is text of `PeriodFourCertificate.lean` (the kernel
    checks all three)."""
    import sys
    from computations import lock_certificate, lock_chain
    sizes = []
    for word, width in lock_certificate.CERTIFICATES:
        t = lock_certificate.certificate_tables(word, width)
        sizes.append(len(t["states"]))
        assert t["word"] == word and lock_chain.is_lock(word, t["states"], width)
    assert sizes == [2611, 1915, 4898]
    lean = (ROOT / "Rule30Open" / "Columns" / "PeriodFourCertificate.lean").read_text(encoding="utf-8")
    digits = sys.get_int_max_str_digits()
    sys.set_int_max_str_digits(0)
    monkeypatch.setattr(lock_certificate, "CERTIFICATES", [("0011", 14)])
    try:
        assert lock_certificate.lean_certificates() in lean
    finally:
        sys.set_int_max_str_digits(digits)
