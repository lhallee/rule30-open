"""The Lean theorems with a computable statement, checked against direct evolution at small sizes, and each module's
spot check against the same computation, so a definition that drifted from Rule 30 would show here too."""

from __future__ import annotations

import re
import sys
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


ETHER = ["0011", "0110", "1101", "0101", "0011", "0001", "0001"]  # B1 B2 B3 B4 B5 c c at phases 0 .. 3, the kit's table


def test_ether_domain() -> None:
    """The kit's ether, evolved by Rule 30 on a ring of 7 r cells, returns after 4 steps; read leftward from its second
    0001 column it is the half with bits 3, 10, 17, ... at phase 0 (-8/127), and that half under the held map stays the
    ether's left half and reads 0001 next to the column (`held_etherLeft`, `ether_fits`); a half sharing exactly its k
    lowest bits with it, k the 2-adic valuation of 127U + 8, follows 0001 for exactly k steps (`ether_countdown`), for
    every U < 2^14, with the spot check `ether_countdown_spot`; and domain B reads 0 at even steps and 1 at odd ones
    (`domainB_repeats`)."""
    reps, steps = 30, 60
    ring = np.array([[int(ETHER[j % 7][ph]) for j in range(7 * reps)] for ph in range(4)], dtype=bool)  # (4, 7 reps)
    for ph in range(4):
        row = ring[ph]  # (7 reps,)
        assert np.array_equal(np.roll(row, 1) ^ (row | np.roll(row, -1)), ring[(ph + 1) % 4]), ph
    left = [[int(ETHER[(5 - j) % 7][ph]) for j in range(7 * reps)] for ph in range(4)]  # cell j + 1 left of column 6
    E = [sum(bit << j for j, bit in enumerate(cells)) for cells in left]  # (4,), as truncated integers
    assert E[0] == sum(1 << j for j in range(3, 7 * reps, 7))
    V = E[0]
    for t in range(steps):
        exact = (1 << (7 * reps - t - 1)) - 1  # bits the truncation has not reached
        assert (V ^ E[t % 4]) & exact == 0 and V & 1 == (t % 4 == 3), t
        V = held(V)
    for U in range(1, 1 << 14):
        k = ((127 * U + 8) & -(127 * U + 8)).bit_length() - 1  # v2(127U + 8)
        assert ((U ^ E[0]) & ((1 << k) - 1)) == 0 and (U ^ E[0]) >> k & 1 == 1, U
        V = U
        for t in range(k):
            assert V & 1 == (t % 4 == 3), (U, t)
            V = held(V)
        assert V & 1 != (k % 4 == 3), U
    orbit = [1032]
    for _ in range(17):
        orbit.append(held(orbit[-1]))
    assert "[" + ", ".join(str(V & 1) for V in orbit) + "] := by decide" in module("Columns/EtherDomain")
    B = sum(1 << j for j in range(1, 80, 2))
    for t in range(40):
        assert B & 1 == t % 2, t
        B = held(B)


def test_no_kicks() -> None:
    """In the orbits of random rows with a leftmost 1, wherever the center does not read 1 at two consecutive steps,
    the cells left of it take one step of the held map (`left_kicked_zero`, `left_kicked_succ`), which is the step
    `period_four_0001_held` uses for 0001."""
    rng = np.random.default_rng(13)
    steps, edge, center = 50, 60, 120
    width = center + steps + 2
    checked = 0
    for _ in range(30):
        row = np.zeros(width, dtype=bool)  # (width,)
        row[edge] = True
        row[edge + 1:] = rng.integers(0, 2, width - edge - 1).astype(bool)
        rows = [row]
        for _ in range(steps):
            r = rows[-1]  # (width,)
            rows.append(np.concatenate([[False], r[:-2] ^ (r[1:-1] | r[2:]), [False]]))
        for t in range(steps - 1):
            if rows[t][center] and rows[t + 1][center]:
                continue
            exact = center - edge + t  # cells -1 .. -exact of the half lie right of the row's left end
            U = sum(1 << j for j in range(exact) if rows[t][center - 1 - j])
            nxt = sum(1 << j for j in range(exact - 1) if rows[t + 1][center - 1 - j])
            assert held(U) & ((1 << (exact - 1)) - 1) == nxt, t
            checked += 1
    assert checked > 1000


def test_small_right() -> None:
    """Each entry certificate of `SmallRight`: every right half of at most six cells, driven by the word from its phase
    and stepped as cells, is in the kit's family at the listed step and depth k, with columns 1 .. k the ether of one of
    the word's alignments, column k a B3 and the next 13 columns a wall state read from the kit's source; each of the
    12 lists covers all 64 halves."""
    source = ROOT / ".lake/packages/rule30prize/lean/Ruliology/CellularAutomata/Rule30Ether.lean"
    text = source.read_text(encoding="utf-8")
    body = text.split("def wallStates : List (Nat × List Bool) := [", 1)[1].split("\n]", 1)[0]
    wall = {(int(phase), tuple(cell == "true" for cell in cells.split(", ")))
            for phase, cells in re.findall(r"\((\d), \[([a-z, ]+)\]\)", body)}
    assert len(wall) == 109
    alignments = {"0001": [(5, 0), (6, 0)], "0011": [(0, 0), (1, 3), (4, 0)], "0111": [(2, 2)]}  # the kit's A0001 ..
    lists = re.findall(r"def entries(\d{4})_(\d) : List \(Nat × Nat\) :=\s*\[([^\]]*)\]", module("Columns/EmptyRight"))
    assert sorted((word, int(phase)) for word, phase, _ in lists) == [(w, ph) for w in alignments for ph in range(4)]
    for word, phase, entries in lists:
        phase, entries = int(phase), [(int(t), int(k)) for t, k in re.findall(r"\((\d+), (\d+)\)", entries)]
        assert len(entries) == 64
        for half, (t1, k) in enumerate(entries):
            row = np.zeros(t1 + k + 20, dtype=bool)  # (n,), columns 1 .. n, white past the light cone
            row[:6] = [(half >> i) & 1 for i in range(6)]
            for t in range(t1):
                left = np.concatenate([[word[(t + phase) % 4] == "1"], row[:-1]])  # (n,)
                right = np.concatenate([row[1:], [False]])  # (n,)
                row = left ^ (row | right)
            strip = tuple(bool(cell) for cell in row[k:k + 13])
            assert any((j0 + k) % 7 == 2 and (psi := (t1 + s + phase) % 4, strip) in wall
                       and all(row[p - 1] == (ETHER[(j0 + p) % 7][psi] == "1") for p in range(1, k + 1))
                       for j0, s in alignments[word]), (word, phase, half)


def test_empty_right_001() -> None:
    """The entries of `emptyRight_001`: the white right half, driven by 001 from phase 0, 1 or 2 and stepped as cells,
    has columns 1 .. 47 equal to state 597 of the kit's trap `t001` at step 1270, 1269 or 1268, whose label has the
    phase of that step; the states and labels are unpacked from the kit's source."""
    kit = ROOT / ".lake/packages/rule30prize/lean/Ruliology/CellularAutomata"
    packed = dict(re.findall(r"def t001_(\w+) : Nat := (\d+)", (kit / "Rule30EtherThreeTrap.lean").read_text("utf-8")))
    digits = sys.get_int_max_str_digits()
    sys.set_int_max_str_digits(0)  # the packed tables have thousands of digits
    try:
        states, labels = int(packed["R"]), int(packed["L"])
    finally:
        sys.set_int_max_str_digits(digits)
    width, label_bits, index = 47, int(packed["lb"]), 597
    state = (states >> (width * index)) % (1 << width)
    label = (labels >> (label_bits * index)) % (1 << label_bits)
    pattern = r"w001 \(t \+ (\d)\)\) 0 (\d+) % 2 \^ 47"
    sources = (kit / "Rule30EtherThreeReach.lean").read_text("utf-8") + module("Columns/EmptyRight")
    entries = re.findall(pattern, sources)
    assert sorted(entries) == [("0", "1270"), ("1", "1269"), ("2", "1268")]
    for phase, steps in ((int(phase), int(steps)) for phase, steps in entries):
        row = np.zeros(steps + width, dtype=bool)  # (n,), columns 1 .. n, white past the light cone
        for t in range(steps):
            left = np.concatenate([["001"[(t + phase) % 3] == "1"], row[:-1]])  # (n,)
            right = np.concatenate([row[1:], [False]])  # (n,)
            row = left ^ (row | right)
        assert [int(cell) for cell in row[:width]] == [(state >> i) & 1 for i in range(width)], phase
        assert (steps + phase) % 3 == label % 3, phase




def centers(rows: np.ndarray, n: int) -> np.ndarray:
    """The center cells at times 1 .. n of each row of `rows`, cells -n .. n at indices 0 .. 2n, white beyond, which
    is exact inside the center's light cone."""
    # rows: (m, 2n + 1)
    out = np.zeros((rows.shape[0], n), dtype=bool)  # (m, n)
    for t in range(n):
        left = np.concatenate([np.zeros((rows.shape[0], 1), dtype=bool), rows[:, :-1]], axis=1)  # (m, 2n + 1)
        right = np.concatenate([rows[:, 1:], np.zeros((rows.shape[0], 1), dtype=bool)], axis=1)  # (m, 2n + 1)
        rows = left ^ (rows | right)
        out[:, t] = rows[:, n]
    return out  # (m, n)


def test_left_window() -> None:
    """Over the 2^n left windows of n <= 10 cells, the center cells at times 1 .. n take every value exactly once, for
    the single cell and 20 random rows (`count_centerWindow`, `centerWindow_unique`). Freeing random sets S of depths,
    exactly 2^(depths of S below T + p) of the rows repeat the center with period p at every depth of S from T + p on
    (`count_adapted`), and no more than that repeat it at every time from T + p to n (`count_periodic`). The single
    cell's window of three cells is the module's spot check."""
    rng = np.random.default_rng(30)
    for n in range(1, 11):
        windows = ((np.arange(1 << n)[:, None] >> np.arange(n)[None, :]) & 1).astype(bool)  # (2^n, n), depth j + 1
        for trial in range(21):
            row = np.zeros(2 * n + 1, dtype=bool) if trial == 0 else rng.integers(0, 2, 2 * n + 1).astype(bool)
            if trial == 0:
                row[n] = True  # the single cell
            rows = np.tile(row, (1 << n, 1))  # (2^n, 2n + 1)
            rows[:, n - 1::-1][:, :n] = windows  # depth j + 1 is index n - 1 - j
            words = centers(rows, n).astype(np.int64) @ (1 << np.arange(n))  # (2^n,)
            assert np.array_equal(np.sort(words), np.arange(1 << n)), (n, trial)
    for _ in range(200):
        n = int(rng.integers(2, 11))
        depths = np.flatnonzero(rng.integers(0, 2, n)) + 1  # (k,), the free depths
        p, T = int(rng.integers(1, 4)), int(rng.integers(0, n))
        row = rng.integers(0, 2, 2 * n + 1).astype(bool)  # (2n + 1,)
        values = ((np.arange(1 << depths.size)[:, None] >> np.arange(depths.size)[None, :]) & 1).astype(bool)
        rows = np.tile(row, (1 << depths.size, 1))  # (2^k, 2n + 1)
        rows[:, n - depths] = values
        column = np.concatenate([rows[:, n:n + 1], centers(rows, n)], axis=1)  # (2^k, n + 1), times 0 .. n
        held = [s for s in depths.tolist() if s >= T + p]
        meets = np.ones(1 << depths.size, dtype=bool)  # (2^k,)
        for s in held:
            meets &= column[:, s] == column[:, s - p]
        assert int(meets.sum()) == 2 ** sum(s < T + p for s in depths.tolist())
        periodic = np.ones(1 << depths.size, dtype=bool)  # (2^k,)
        for t in range(T + p, n + 1):
            periodic &= column[:, t] == column[:, t - p]
        assert int(periodic.sum()) <= int(meets.sum())
    single = np.zeros(7, dtype=bool)  # (7,), cells -3 .. 3
    single[3] = True
    assert centers(single[None, :], 3)[0, ::-1].tolist() == [True, False, True]
    assert "centerWindow single [false, false, false] = [true, false, true]" in module("RandomRows/LeftWindow")


def test_white_gap() -> None:
    """Right halves with random first six cells, white on cells 7 to B and random beyond, driven as cells, enter the
    kit's family no later than the step the entry lists of `EmptyRight` give their first six cells (`gap_0001`,
    `gap_0011`, `gap_0111`), and halves white on cells 1 to 30 with random tails no later than the white half
    (`high_0001`, `high_0011`, `high_0111`). Every listed step plus depth plus 13 is at most B, as `bound0001` and the
    others state, and the white half's is at most 30."""
    from computations import absorption
    wall = absorption.kit_wall()  # (4, 2^13)
    entries = {(word, int(phase)): [(int(t), int(k)) for t, k in re.findall(r"\((\d+), (\d+)\)", body)]
               for word, phase, body in re.findall(r"def entries(\d{4})_(\d) : List \(Nat × Nat\) :=\s*\[([^\]]*)\]",
                                                   module("Columns/EmptyRight"))}
    gaps = {"0001": 316, "0011": 535, "0111": 310}
    for word, gap in gaps.items():
        assert f"p ≤ {gap} → x p = false" in module("Columns/WhiteGap")
    rng = np.random.default_rng(30)
    for (word, phase), pairs in entries.items():
        gap = gaps[word]
        assert len(pairs) == 64 and max(t + k + 13 for t, k in pairs) <= gap and sum(pairs[0]) + 13 <= 30
        prefixes = rng.integers(0, 64, 40)  # (40,)
        cells = np.zeros((40, gap + 200 + 700), dtype=np.uint8)  # (40, n), column j + 1 at index j
        cells[:, :6] = (prefixes[:, None] >> np.arange(6)[None, :]) & 1
        cells[:, gap:gap + 200] = rng.integers(0, 2, (40, 200))
        times = absorption.absorb(word, absorption.packed(cells), phase, 700, wall, gap + 200)  # (40,)
        listed = np.array([pairs[r][0] for r in prefixes.tolist()])  # (40,)
        assert ((times >= 0) & (times <= listed)).all(), (word, phase)
        tails = np.zeros((20, 30 + 200 + 700), dtype=np.uint8)  # (20, n)
        tails[:, 30:230] = rng.integers(0, 2, (20, 200))
        times = absorption.absorb(word, absorption.packed(tails), phase, 700, wall, 230)  # (20,)
        assert ((times >= 0) & (times <= pairs[0][0])).all(), (word, phase)


def test_sparse_right() -> None:
    """The certificates in `SparseRight`, read from its source: for each word and phase, 30 numbers, the first entry of
    each a one-cell half and then one entry per second cell up to its step plus depth plus 13, every step plus depth plus
    13 at most the module's G. Sampled halves with those black cells, white elsewhere up to G and random beyond G,
    driven as cells, enter no later than the listed step (`sparse_0001`, `sparse_0011`, `sparse_0111`)."""
    from computations import absorption, sparse_halves
    wall = absorption.kit_wall()  # (4, 2^13)
    source = module("Columns/SparseRight")
    bounds = {"0001": 778, "0011": 1359, "0111": 623}
    for word, g in bounds.items():
        assert f"theorem sparse_{word} (φ : Nat) (x : Nat → Bool) (hx : AtMostTwo {g} x)" in source
    data = {(word, int(phase)): [int(n, 16) for n in re.findall(r"0x([0-9a-f]+)", body)]
            for word, phase, body in re.findall(r"def cells(\d{4})_(\d) : List Nat := \[([^\]]*)\]", source)}
    assert len(data) == 12
    rng = np.random.default_rng(32)
    for (word, phase), numbers in data.items():
        g = bounds[word]
        assert len(numbers) == 30
        halves, listed = [], []
        for p1, number in enumerate(numbers, start=1):
            (t, k), = sparse_halves.decode(number, 1)
            count = max(0, t + k + 13 - p1)
            pairs = sparse_halves.decode(number >> sparse_halves.BITS, count)
            assert number >> (sparse_halves.BITS * (count + 1)) == 0
            assert max(a + b + 13 for a, b in [(t, k), *pairs]) <= g
            halves.append([p1, t + k + 14 + int(rng.integers(0, 50))])  # the second cell beyond the single's bound
            listed.append(t)
            for j in rng.choice(count, size=min(2, count), replace=False).tolist():
                halves.append([p1, p1 + 1 + j])
                listed.append(pairs[j][0])
        cells = np.zeros((len(halves), g + 300 + 1400), dtype=np.uint8)  # (n, width), column j + 1 at index j
        for i, black in enumerate(halves):
            for q in black:
                if q <= g:
                    cells[i, q - 1] = 1
        cells[:, g:g + 300] = rng.integers(0, 2, (len(halves), 300))
        times = absorption.absorb(word, absorption.packed(cells), phase, 1400, wall, g + 300)  # (n,)
        assert ((times >= 0) & (times <= np.array(listed))).all(), (word, phase)


def test_ether_prefix_data() -> None:
    """The certificates in `EtherPrefix`, read from its source: 16 tail words for each word, alignment and phase, each
    with B + 7 <= 64. Sampled truncations, driven as integer rows one step at a time, are in the family at the listed
    step: a short one at the listed depth through some alignment, one of 100 to 400 cells through its own alignment at
    the base's depth plus the ether columns added in front, checked column by column (`etherPrefix_0001` and the
    others)."""
    from computations import absorption, ether_prefix
    wall = absorption.kit_wall()  # (4, 2^13)
    source = module("Columns/EtherPrefix")
    data = {(word, int(j0), int(phase)): [int(n, 16) for n in re.findall(r"0x([0-9a-f]+)", body)]
            for word, j0, phase, body in re.findall(r"def tails(\d{4})_(\d)_(\d) : List Nat := \[([^\]]*)\]", source)}
    assert len(data) == 24

    def in_family(word: str, alignments: list[tuple[int, int]], row: int, phase: int, k: int) -> bool:
        return any((j0 + k) % 7 == 2 and wall[(phase + shift) % 4][(row >> k) & 0x1FFF]
                   and all((row >> (p - 1)) & 1 == absorption.ether(j0 + p, phase + shift) for p in range(1, k + 1))
                   for j0, shift in alignments)

    rng = np.random.default_rng(34)
    for (word, j0, phase), numbers in data.items():
        shift = dict(absorption.ALIGNMENTS[word])[j0]
        psi = (phase + shift) % 4
        assert len(numbers) == 16
        for tail in rng.choice(16, size=2, replace=False).tolist():
            b, direct, bases = ether_prefix.decode(numbers[tail])
            assert b + 7 <= 64
            samples = [(length, *direct[length], absorption.ALIGNMENTS[word])
                       for length in rng.choice(max(b, 1), size=min(2, b), replace=False).tolist()]
            for length in rng.integers(100, 400, 2).tolist():
                t, k = bases[(length - b) % 7]
                samples.append((length, t, k + length - b - (length - b) % 7, [(j0, shift)]))
            for length, t, k, alignments in samples:
                row = ether_prefix.prefix_half(j0, psi, length, tail)
                for s in range(t):
                    row = ((row << 1) | int(word[(s + phase) % 4])) ^ (row | (row >> 1))
                assert in_family(word, alignments, row, (t + phase) % 4, k), (word, j0, phase, tail, length)


def test_high_three() -> None:
    """`highRight_001`: right halves white on cells 1 to 1,317 with random cells beyond, driven by 001 from phase 0, 1 or
    2 and stepped as cells, have columns 1 .. 47 equal to state 597 of the kit's trap `t001` at step 1270, 1269 or 1268,
    as the white half does; the state is unpacked from the kit's source."""
    kit = ROOT / ".lake/packages/rule30prize/lean/Ruliology/CellularAutomata"
    packed = dict(re.findall(r"def t001_(\w+) : Nat := (\d+)", (kit / "Rule30EtherThreeTrap.lean").read_text("utf-8")))
    digits = sys.get_int_max_str_digits()
    sys.set_int_max_str_digits(0)  # the packed table has thousands of digits
    try:
        states = int(packed["R"])
    finally:
        sys.set_int_max_str_digits(digits)
    width = 47
    state = [(((states >> (width * 597)) % (1 << width)) >> i) & 1 for i in range(width)]
    assert "theorem highRight_001 (φ : Nat) : HighRight3 Rule30EtherThree.w001 1317 φ" in module("Columns/HighThree")
    rng = np.random.default_rng(35)
    for phase, steps in ((0, 1270), (1, 1269), (2, 1268)):
        rows = np.zeros((8, 1317 + 400), dtype=bool)  # (8, n), column j + 1 at index j
        rows[:, 1317:] = rng.integers(0, 2, (8, 400)).astype(bool)
        for t in range(steps):
            left = np.concatenate([np.full((8, 1), "001"[(t + phase) % 3] == "1"), rows[:, :-1]], axis=1)  # (8, n)
            right = np.concatenate([rows[:, 1:], np.zeros((8, 1), dtype=bool)], axis=1)  # (8, n)
            rows = left ^ (rows | right)
        assert (rows[:, :width].astype(int) == np.array(state)[None, :]).all(), phase


def test_long_window() -> None:
    """The literals of `LongWindow`, read from its source: `bigBits` holds the first 65,536 center cells and each
    `rowAt<t>` the row at time t with the seed at bit 65,536, both from rows stepped as integers one at a time; the
    theorem's bound is one more than the time of the factor that `factor_new` checks."""
    source = module("Columns/LongWindow")
    assert ("theorem transient_add_period_ge_65518 (T P : Nat) (hP : 0 < P)\n"
            "    (h : ∀ t, T ≤ t → center (t + P) = center t) : 65518 ≤ T + P") in source
    assert "def lastFactor : Nat := (bigBits >>> 65517) % 2 ^ 19" in source
    rows = {int(t): int(body, 16) << int(shift)
            for t, body, shift in re.findall(r"def rowAt(\d+) : Nat :=\n  0x([0-9a-f]+) <<< (\d+)\n", source)}
    big = int(re.search(r"def bigBits : Nat :=\n  0x([0-9a-f]+)\n", source).group(1), 16)
    assert sorted(rows) == [16384, 32768, 49152]
    n = 65536
    row, bits = 1 << n, 0
    for t in range(n):
        if t in rows:
            assert rows[t] == row, t
        bits |= ((row >> n) & 1) << t
        row = (row << 1) ^ (row | (row >> 1))
    assert big == bits
