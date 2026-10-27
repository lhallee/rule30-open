"""The Lean theorems with a computable statement, checked against direct evolution at small sizes, and each module's
spot check against the same computation, so a definition that drifted from Rule 30 would show here too."""

from __future__ import annotations

import numpy as np

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def module(name: str) -> str:
    """The source of a Lean module, by its path under Rule30Open/."""
    return (ROOT / "Rule30Open" / f"{name}.lean").read_text(encoding="utf-8")


def held(U: int) -> int:
    """Rule 30 left of a column held at 0, bit j the cell j + 1 places away (Lean: `heldNat`)."""
    return (U >> 1) ^ (U | (U << 1))


def test_held_column() -> None:
    """While the cell next to it reads 1 at each 1 of the column, the half left of an alternating column evolves
    exactly as beside a column held at 0 (`period_two_held`), for every half to support 10 in both phases; the held
    step is the integer map (`heldNat_testBit`); and the orbit of 1 is the spot check `heldNat_orbit_one`."""
    for support in range(1, 11):
        n = 1 << (support - 1)
        steps = 3 * support + 10
        driven = np.zeros((n, support + steps + 2), dtype=bool)  # (n, cells -1 .. -(support + steps + 2))
        driven[:, :support - 1] = (np.arange(n)[:, None] >> np.arange(support - 1)[None, :]) & 1
        driven[:, support - 1] = True
        for phase in (0, 1):
            row, held_row = driven.copy(), driven.copy()  # (n, w) each
            alive = np.ones(n, dtype=bool)  # (n,)
            for t in range(steps):
                center = (t + phase) % 2 == 1
                if center:
                    alive &= row[:, 0]
                assert np.array_equal(row[alive], held_row[alive]), (support, phase, t)
                left = np.concatenate([row[:, 1:], np.zeros((n, 1), dtype=bool)], axis=1)  # (n, w), cells -(j + 1)
                row = left ^ (row | np.concatenate([np.full((n, 1), center), row[:, :-1]], axis=1))
                left = np.concatenate([held_row[:, 1:], np.zeros((n, 1), dtype=bool)], axis=1)  # (n, w)
                held_row = left ^ (held_row | np.concatenate([np.zeros((n, 1), dtype=bool), held_row[:, :-1]], axis=1))
    width = 12
    bits = (np.arange(1 << width)[:, None] >> np.arange(width + 2)[None, :]) & 1  # (4096, 14), bit j of U
    lower = np.concatenate([np.zeros((1 << width, 1), dtype=np.int64), bits[:, :-1]], axis=1)  # (4096, 14), bit j - 1
    upper = np.concatenate([bits[:, 1:], np.zeros((1 << width, 1), dtype=np.int64)], axis=1)  # (4096, 14), bit j + 1
    stepped = (upper ^ (bits | lower)) @ (1 << np.arange(width + 2))  # (4096,)
    U = np.arange(1 << width)  # (4096,)
    assert np.array_equal(stepped, (U >> 1) ^ (U | (U << 1)))
    orbit = [1]
    for _ in range(7):
        orbit.append(held(orbit[-1]))
    assert "= [" + ", ".join(map(str, orbit)) + "]" in module("PeriodTwo/HeldColumn")


def test_held_countdown() -> None:
    """A half agreeing with domain A (-1/3) on exactly its k lowest bits stays odd for exactly k steps of the held map
    (`held_countdown`), and k is the 2-adic valuation of 3U + 1, for every U < 2^14; the spot check is the orbit of
    85; and an even half agreeing with -2/3 on exactly m >= 2 bits agrees with it on exactly m - 2 two steps later
    (`held_agree_stepB`)."""
    domain = sum(1 << j for j in range(0, 16, 2))  # -1/3 to 16 bits
    for U in range(1, 1 << 14):
        k = ((3 * U + 1) & -(3 * U + 1)).bit_length() - 1  # v2(3U + 1)
        assert ((U ^ domain) & ((1 << k) - 1)) == 0 and (U ^ domain) >> k & 1 == 1, U
        V = U
        for s in range(k):
            assert V & 1, (U, s)
            V = held(V)
        assert V & 1 == 0, U
    orbit = [85]
    for _ in range(8):
        orbit.append(held(orbit[-1]))
    assert "85 % 2) = [" + ", ".join(str(V & 1) for V in orbit) + "]" in module("PeriodTwo/Domains")
    for E in range(2, 1 << 14, 2):
        m = ((3 * E + 2) & -(3 * E + 2)).bit_length() - 1  # v2(3E + 2), the bits E shares with -2/3
        if m >= 2:
            V = held(held(E))
            assert ((3 * V + 2) & -(3 * V + 2)).bit_length() - 1 == m - 2, E


def test_run_countdown() -> None:
    """In the orbits of random rows with a leftmost 1, a column reading 1 at b + 1 steps from s and then 0 has, at s,
    cells left of it that read 0 1 0 1 ... on exactly their b nearest cells (`run_countdown`), at every column and every
    such s; and the spot check `run_countdown_spot` is the single cell's center at steps 3 to 6."""
    rng = np.random.default_rng(11)
    steps, edge = 60, 70  # the leftmost 1 at cell 70 never reaches the row's left end
    width = edge + 2 * steps + 40  # cells x < width - 1 - t are exact at step t
    runs = 0
    for _ in range(40):
        row = np.zeros(width, dtype=bool)  # (width,)
        row[edge] = True
        row[edge + 1:] = rng.integers(0, 2, width - edge - 1).astype(bool)
        rows = [row]
        for _ in range(steps):
            r = rows[-1]  # (width,)
            rows.append(np.concatenate([[False], r[:-2] ^ (r[1:-1] | r[2:]), [False]]))
        space = np.array(rows)  # (steps + 1, width)
        pattern = np.arange(width) % 2 == 1  # (width,), domain B: 0 1 0 1 ... read from the column
        for k in range(edge + 1, width - steps - 2):
            column = space[:, k]  # (steps + 1,)
            for s in range(steps):
                if not column[s]:
                    continue
                b = int(np.argmin(column[s:])) - 1  # the run from s is b + 1 long
                if b < 0:
                    continue
                left = space[s, k - 1::-1]  # (k,), cells k - 1, k - 2, ...
                agree = int(np.argmin(left == pattern[:k]))
                assert agree == b, (k, s, b, agree)
                runs += 1
    assert runs > 10_000
    single = np.zeros(2 * 8 + 1, dtype=bool)  # (17,)
    single[8] = True
    space = [single]
    for _ in range(6):
        r = space[-1]  # (17,)
        space.append(np.concatenate([[False], r[:-2] ^ (r[1:-1] | r[2:]), [False]]))
    center = [space[3 + i][8] for i in range(4)]
    near = [space[3][8 - 1 - j] for j in range(3)]
    text = ("= [" + ", ".join("true" if bit else "false" for bit in center) + "] ∧\n"
            + "      (List.range 3).map (fun j => leftOf single 3 0 j) = ["
            + ", ".join("true" if bit else "false" for bit in near) + "]")
    assert text in module("Columns/RunCountdown")


def test_rule210_checkerboard() -> None:
    """Under Rule 210 beside an alternating column, every left half on the space-time checkerboard's color away from
    the column's 1s keeps cell -1 at 0 at each 1 of the column (`orbit210_checkerboard`, `rule210_finite_half`), for
    every such half to support 13 in both phases; and the spot check `orbit210_single` is the orbit of a single 1 next
    to the column."""
    support, steps = 13, 60
    for phase in (0, 1):
        free = [j for j in range(support) if (j + phase) % 2 == 0]  # bit j is cell -(j + 1)
        n = 1 << len(free)
        row = np.zeros((n, support + steps + 2), dtype=bool)  # (n, cells -1 .. -(support + steps + 2))
        row[:, free] = (np.arange(n)[:, None] >> np.arange(len(free))[None, :]) & 1
        rows = []
        for t in range(steps):
            center = (t + phase) % 2 == 1
            if center:
                assert not row[:, 0].any(), (phase, t)
            rows.append(row[1 if phase == 0 else 0, :6].copy())  # (6,), the half with only cell -1 (phase 0)
            left = np.concatenate([row[:, 1:], np.zeros((n, 1), dtype=bool)], axis=1)  # (n, w), cells -(j + 2)
            right = np.concatenate([np.full((n, 1), center), row[:, :-1]], axis=1)  # (n, w), cells -j, the column at 0
            row = left ^ (~row & right)
        if phase == 0:
            lean = module("Analogs/Rule210")
            texts = ["[" + ", ".join("true" if bit else "false" for bit in r) + "]" for r in rows[:5]]
            assert all(text in lean for text in texts)
            assert sorted(lean.index(text) for text in texts) == [lean.index(text) for text in texts]


def test_held150() -> None:
    """Rule 150 beside a held 0, G(U) = (U >> 1) xor U xor (U << 1), reads 0 next to the column at some even step from 4
    on and some odd step from 5 on, for every U < 2^12 (`held150_even_steps`, `held150_odd_steps`); at steps 4r and
    4r + 2 it reads the center and the cell left of it at step r of Rule 150 on the whole line from bits 0, 4, 8, ...
    of U at cells 0, 1, 2, ... and bits 2, 6, 10, ... at cells -1, -2, -3, ...; and the spot check
    `held150_orbit_one` is the orbit of 1."""
    width, steps = 12, 40
    for U in range(1 << width):
        parity, V = [], U
        for _ in range(steps):
            parity.append(V & 1)
            V = (V >> 1) ^ V ^ (V << 1)
        assert 0 in parity[4::2] and 0 in parity[5::2], U
        line = {j // 4 if j % 4 == 0 else -(j + 2) // 4 for j in range(width) if U >> j & 1 and j % 2 == 0}
        for r in range(steps // 4):
            assert parity[4 * r] == (0 in line) and parity[4 * r + 2] == (-1 in line), (U, r)
            line = {x + 1 for x in line} ^ line ^ {x - 1 for x in line}
    orbit, V = [], 1
    for _ in range(12):
        orbit.append("true" if V & 1 else "false")
        V = (V >> 1) ^ V ^ (V << 1)
    assert "[" + ", ".join(orbit) + "] := by decide" in module("Analogs/Rule150Descent")
