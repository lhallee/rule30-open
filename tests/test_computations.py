"""Each computation against an independent implementation, a known sequence, or the numbers its entry quotes."""

from __future__ import annotations

import re
import numpy as np
import pytest

from pathlib import Path

from computations import (absorption, algebra, coin_lock, coupled, deformation, frames, game, held_map,
                          left_diagonals, linear_complexity, lock_certificate, long_window, period_three,
                          periodic_columns, right_half, sensitivity, slow_halves, small_halves, sparse_halves,
                          ether_prefix)
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


def test_held_map_0001() -> None:
    """The search for the condition of 0001 against Python integers for every support to 11, every phase, with and
    without the right half's check; and the latest first failures the ether-domain argument quotes, between M and
    M + 9, with 19 at support 11."""
    for support in range(1, 12):
        for phase in range(4):
            for check in (False, True):
                expected = []
                for U in range(1 << (support - 1), 1 << support):
                    V, t, last = U, 0, 0
                    while t < 63:
                        ph, odd = (t + phase) % 4, V & 1
                        if (ph in (0, 2) and odd) or (ph == 3 and not odd) or (ph == 1 and check and odd and last):
                            break
                        if ph == 1:
                            last = odd
                        V, t = held_map.held(V), t + 1
                    expected.append(t)
                assert held_map.first_failures_0001(support, phase, check).tolist() == expected, (support, phase)
    latest = [max(int(held_map.first_failures_0001(support, phase, False).max()) for phase in range(4))
              for support in range(1, 17)]
    assert all(support <= late <= support + 9 for support, late in zip(range(1, 17), latest))
    assert latest[10] == 19


def c3_brute(word: str, support: int, phase: int) -> int:
    """The latest first failure of the kit's `C3 word` pattern over the left halves of exactly `support` cells, each
    stepped as an integer with the kit's effective boundary as the cell right of bit 0."""
    boundary = {"0001": "0000", "0011": "0010", "0111": "0110"}[word]
    pattern = {"0001": "0*01", "0011": "*001", "0111": "*001"}[word]
    latest = 0
    for U in range(1 << (support - 1), 1 << support):
        t = 0
        while t < 200 and pattern[(t + phase) % 4] in ("*", str(U & 1)):
            U = (U >> 1) ^ (U | (U << 1) | int(boundary[(t + phase) % 4]))
            t += 1
        latest = max(latest, t)
    return latest


def test_c3_ether() -> None:
    """For each word, the ether's left half, read from an ether column aligned with the word, keeps the kit's C3
    pattern under the kit's effective boundary: a 400-cell truncation is exact at cell -1 for 100 steps, and the ether
    repeats every 4, so each C3 has this infinite solution."""
    for word, j0, shift in (("0001", 6, 0), ("0011", 0, 0), ("0011", 1, 3), ("0111", 2, 2)):
        assert absorption.aligned(word, j0, shift)
        boundary = {"0001": "0000", "0011": "0010", "0111": "0110"}[word]
        pattern = {"0001": "0*01", "0011": "*001", "0111": "*001"}[word]
        U = sum(absorption.ether(j0 - 1 - j, shift) << j for j in range(400))
        for t in range(100):
            assert pattern[t % 4] in ("*", str(U & 1)), (word, j0, t)
            U = ((U >> 1) ^ (U | (U << 1) | int(boundary[t % 4]))) & ((1 << 400) - 1)
            assert U & ((1 << 200) - 1) == sum(absorption.ether(j0 - 1 - j, t + 1 + shift) << j for j in range(200))


def test_held_map_tree() -> None:
    """The tree of readings against stepping every half: for 0001 with and without the check against the search over
    every integer to support 15, and for C3 of 0011 and 0111 against integers to support 13, in every phase; the
    Fibonacci count of the branches of 0001 with the check; and the ether-domain argument's step 115 at support 100."""
    for phase in range(4):
        for check in (False, True):
            latest, _ = held_map.tree_failures("0001", 15, phase, check)
            assert latest == [int(held_map.first_failures_0001(support, phase, check).max())
                              for support in range(1, 16)], (phase, check)
        for word in ("0011", "0111"):
            latest, _ = held_map.tree_failures(word, 13, phase, False)
            assert latest == [c3_brute(word, support, phase) for support in range(1, 14)], (word, phase)
    latest, branches = held_map.tree_failures("0001", 100, 0, True)
    fibonacci = [1, 2]
    while len(fibonacci) < 26:
        fibonacci.append(fibonacci[-1] + fibonacci[-2])
    assert [branches[4 * j - 1] for j in range(1, 26)] == fibonacci[1:]
    assert latest[99] == 115


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


def jen_open_brute(pattern: str, width: int) -> list[int]:
    """`game.jen_open` by plain Python: components by mutual reachability, then the same three closures."""
    period, n = len(pattern), 1 << width
    moves = {}
    for ph in range(period):
        for r in range(n):
            cells = [(r >> x) & 1 for x in range(width)]
            for free in (0, 1):
                left = [int(pattern[ph])] + cells[:-1]
                right = cells[1:] + [free]
                nxt = sum((l ^ (c | rr)) << x for x, (l, c, rr) in enumerate(zip(left, cells, right)))
                moves.setdefault((ph, r), []).append((((ph + 1) % period, nxt), free))
    reach = {}
    for node in moves:
        seen, todo = {node}, [node]
        while todo:
            for target, _ in moves[todo.pop()]:
                if target not in seen:
                    seen.add(target)
                    todo.append(target)
        reach[node] = seen
    components = {frozenset(m for m in reach[node] if node in reach[m]) for node in moves}
    sizes = []
    for component in components:
        inside = [(a, b, free) for a in component for b, free in moves[a] if b in component]
        if not inside:
            continue

        def constant(pairs: list[tuple[int, int]]) -> bool:
            return all(len({v for p, v in pairs if p == ph}) <= 1 for ph in range(period))

        left_column = [(ph, int(pattern[(ph + 1) % period]) ^ (int(pattern[ph]) | (r & 1))) for ph, r in component]
        if constant(left_column):
            continue
        if any(constant([(ph, (r >> x) & 1) for ph, r in component]) for x in range(width)):
            continue
        if constant([(a[0], free) for a, _, free in inside]):
            continue
        if any(all(len({(b[0], b[1] & ((1 << j) - 1)) for a, b, _ in inside if (a[0], a[1] & ((1 << j) - 1)) == key})
                   <= 1 for key in {(a[0], a[1] & ((1 << j) - 1)) for a, _, _ in inside}) for j in range(1, width + 1)):
            continue
        sizes.append(len(component))
    return sorted(sizes, reverse=True)


def test_jen_open() -> None:
    """The extended game against plain Python on six blocks at widths 4 and 5, and up to period 8 at width 6 it
    excludes exactly the blocks the game excludes."""
    for pattern in ("0001", "0011", "0111", "01", "001", "00000011"):
        for width in (4, 5):
            assert game.jen_open(pattern, width) == jen_open_brute(pattern, width), (pattern, width)
    blocks = [pattern for period in range(1, 9) for pattern in game.necklaces(period)]
    assert [p for p in blocks if not game.jen_open(p, 6)] == [p for p in blocks if game.bad_pairs(p, 6) == 0]


KIT_SOURCE = ROOT / ".lake/packages/rule30prize/lean/Ruliology/CellularAutomata"


def test_kit_blocks() -> None:
    """`KIT_WORDS` is the kit's strip-certificate table, read from its source, and its three single strip certificates;
    and `kit_blocks` agrees on every primitive block up to period 14 with each family read directly: cyclic runs of 1s
    found position by position, and every rotation of each padded word. That makes 43 blocks, 0^9 1 among them and
    0^7 1 not."""
    table = re.findall(r"\((\d+), (\d+), \d+, \d+\)",
                       (KIT_SOURCE / "Rule30StripCertificateTable.lean").read_text(encoding="utf-8"))
    singles = re.findall(r"theorem not_eventually_([01]+) :",
                         (KIT_SOURCE / "Rule30StripCertificates.lean").read_text(encoding="utf-8"))
    assert len(table) == 30 and len(singles) == 3
    words = {game.least_rotation(format(int(bits), f"0{n}b")) for n, bits in table} | set(singles)
    assert set(game.KIT_WORDS) == words and len(game.KIT_WORDS) == len(words) == 32  # 01111111 is in both
    expected = set(game.KIT_WORDS)
    for period in range(1, 15):
        padded = {("0" * (period - len(tail)) + tail)[i:] + ("0" * (period - len(tail)) + tail)[:i]
                  for tail, white in (("1", 9), ("11", 8), ("10111", 9)) if period - len(tail) >= white
                  for i in range(period)}
        for word in game.necklaces(period):
            runs = []
            for start in range(period):
                if word[start] == "1" and word[start - 1] == "0":
                    length = 0
                    while word[(start + length) % period] == "1":
                        length += 1
                    runs.append(length)
            if all(run >= 9 for run in runs) or word in padded:
                expected.add(word)
    kit = game.kit_blocks(14)
    assert set(kit) == expected and len(kit) == 43
    assert "0000000001" in kit and "00000001" not in kit


def mask_ok(pattern: str, width: int, mask: dict) -> bool:
    """`GameMask.check` in plain Python: cells as lists stepped by the rule, ranks read bit by bit."""
    period, bits = len(pattern), mask["bits"]

    def rank(phase: int, cells: list[bool]) -> int:
        code = sum(1 << i for i, cell in enumerate(cells) if cell)
        return (mask["ranks"][phase] >> (bits * code)) & ((1 << bits) - 1)

    for phase in range(period):
        c, c_next = pattern[phase] == "1", pattern[(phase + 1) % period] == "1"
        for code in range(1 << width):
            cells = [bool(code >> i & 1) for i in range(width)]
            here = rank(phase, cells)
            transient = bool(mask["transient"] >> here & 1)
            for free in (False, True):
                row = [c] + cells + [free]
                after = [row[i] ^ (row[i + 1] | row[i + 2]) for i in range(width)]
                there = rank((phase + 1) % period, after)
                if there < here or (transient and there == here):
                    return False
            if not transient and bool(mask["values"] >> (here * period + phase) & 1) != (c_next ^ (c | cells[0])):
                return False
    return True


def test_game_masks() -> None:
    """The 32 certificates in GameBlocks.lean are `lean_mask` at the least width of blocks the kit does not exclude,
    `gameBlocks` lists the same blocks, and each certificate passes the check in plain Python and fails it with its
    values cleared. The two blocks left out need 114,688 and 229,376 nodes. A certificate at one width gives one at
    every larger width, checked for three blocks up to width 11."""
    lean = (ROOT / "Rule30Open" / "Columns" / "GameBlocks.lean").read_text(encoding="utf-8")
    masks = re.findall(r"def mask([01]+) : GameMask where\n  block := wordOf (\d+) 0b\1\n  width := (\d+)", lean)
    listed = re.findall(r"\((\d+), 0b([01]+)\)", lean.split("def gameBlocks", 1)[1].split("\n\n", 1)[0])
    assert len(masks) == 32 and [(n, p) for p, n, _ in masks] == listed
    kit = game.kit_blocks(14)
    for pattern, n, width in masks:
        width = int(width)
        assert int(n) == len(pattern) and pattern == game.least_rotation(pattern) and pattern not in kit
        assert game.least_width(pattern) == width and len(pattern) << width <= 1 << 15
        assert game.lean_mask(pattern, width) in lean, pattern
        mask = game.game_mask(pattern, width)
        assert mask_ok(pattern, width, mask) and not mask_ok(pattern, width, {**mask, "values": 0}), pattern
    for pattern, width in (("00000001001111", 13), ("00000000010001", 14)):
        assert pattern not in kit and game.least_width(pattern) == width
    assert [len(p) << w for p, w in (("00000001001111", 13), ("00000000010001", 14))] == [114688, 229376]
    for pattern in ("00010111111111", "00000000110011", "0000000001101"):
        least = game.least_width(pattern)
        assert all(game.bad_pairs(pattern, width) == 0 for width in range(least, 12))


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


@pytest.fixture(scope="module")
def coin_certificate() -> np.ndarray:
    """The certificate of 0111 at width 14, the smallest the coin finding uses."""
    return coin_lock.certificate("0111", 14)  # (4, 2^14)


def step_window(word: str, ph: int, window: int, beyond: int, width: int) -> int:
    """One step of a window of columns 1 .. width at phase `ph`, stepped as a whole integer row with `rule30.step`, with
    the center left of it and `beyond` right of it."""
    row = int(word[ph]) | (window << 1) | (beyond << (width + 1))  # center at bit 0, column j at bit j
    return (step(row) >> 1) & ((1 << width) - 1)


def test_coin_entry_paths(coin_certificate: np.ndarray) -> None:
    """Every window of width 14 can enter the certificate of 0111, the farthest in 61 steps; along the recorded first
    values from 300 random windows, stepped as integer rows, the distance drops by one per step and is the smaller of
    the two successors' distances, which makes it the least number of steps."""
    # coin_certificate: (4, 2^14)
    dist, first = coin_lock.entry_paths("0111", coin_certificate)  # (4, 2^14) each
    assert (dist < coin_lock.UNREACHED).all() and int(dist.max()) == 61
    assert (dist[coin_certificate] == 0).all() and (dist[~coin_certificate] > 0).all()
    rng = np.random.default_rng(30)
    for _ in range(300):
        ph, window = int(rng.integers(0, 4)), int(rng.integers(0, 1 << 14))
        for remaining in range(int(dist[ph, window]), 0, -1):
            successors = [step_window("0111", ph, window, beyond, 14) for beyond in (0, 1)]
            assert min(dist[(ph + 1) % 4, s] for s in successors) == remaining - 1
            window, ph = successors[int(first[ph, window])], (ph + 1) % 4
            assert dist[ph, window] == remaining - 1
        assert coin_certificate[ph, window]


def test_universal_word(coin_certificate: np.ndarray) -> None:
    """The universal word of 0111 at width 14 has 209 values and brings every one of the 2^14 windows into the
    certificate, stepped as bool arrays; at width 16 the words of 0001, 0011 and 0111 have 425, 697 and 297 values."""
    # coin_certificate: (4, 2^14)
    values = coin_lock.universal_word("0111", coin_certificate)
    assert len(values) == 209
    rows = ((np.arange(1 << 14)[:, None] >> np.arange(14)[None, :]) & 1).astype(bool)  # (2^14, 14), column j + 1
    for t, value in enumerate(values):
        left = np.concatenate([np.full((rows.shape[0], 1), "0111"[t % 4] == "1"), rows[:, :-1]], axis=1)  # (2^14, 14)
        right = np.concatenate([rows[:, 1:], np.full((rows.shape[0], 1), value == 1)], axis=1)  # (2^14, 14)
        rows = left ^ (rows | right)
    codes = rows.astype(np.int64) @ (1 << np.arange(14))  # (2^14,)
    assert coin_certificate[len(values) % 4][codes].all()
    for word, length in (("0001", 425), ("0011", 697), ("0111", 297)):
        member = coin_lock.certificate(word, 16)  # (4, 2^16)
        values = coin_lock.universal_word(word, member)
        assert len(values) == length and member[length % 4][coin_lock.run_word(word, member, values)].all()


def test_coin_chain(coin_certificate: np.ndarray) -> None:
    """With a fair coin beyond width 14 under 0111, the expected entry time solves its equation with integer-row
    successors and matches 400 simulated runs from the slowest window within four standard errors, and the chance of
    staying out falls by the decay factor per step; at width 16, the finding's expected times and decay factor."""
    # coin_certificate: (4, 2^14)
    expected = coin_lock.expected_entry("0111", coin_certificate)  # (4, 2^14)
    assert (expected[coin_certificate] == 0).all()
    rng = np.random.default_rng(30)
    for _ in range(300):
        ph, window = int(rng.integers(0, 4)), int(rng.integers(0, 1 << 14))
        if not coin_certificate[ph, window]:
            later = sum(expected[(ph + 1) % 4, step_window("0111", ph, window, beyond, 14)] for beyond in (0, 1))
            assert abs(expected[ph, window] - 1 - later / 2) < 1e-4
    slowest = int(np.argmax(expected[0]))
    times = np.zeros(400)  # (400,)
    for run in range(400):
        ph, window = 0, slowest
        while not coin_certificate[ph, window]:
            window, ph = step_window("0111", ph, window, int(rng.integers(0, 2)), 14), (ph + 1) % 4
            times[run] += 1
    assert abs(times.mean() - expected[0, slowest]) < 4 * times.std() / np.sqrt(times.size)
    rate = coin_lock.decay_rate("0111", coin_certificate)
    before, after = coin_lock.stay_out("0111", coin_certificate, 400), coin_lock.stay_out("0111", coin_certificate, 404)
    assert abs(after.max() / before.max() - rate ** 4) < 1e-3
    member = coin_lock.certificate("0111", 16)  # (4, 2^16)
    expected = coin_lock.expected_entry("0111", member)  # (4, 2^16)
    assert (round(float(expected.max()), 1), round(float(expected[0].mean()), 1)) == (139.9, 49.8)
    assert round(coin_lock.decay_rate("0111", member), 5) == 0.98251


def test_coin_sample() -> None:
    """In Rule 30 itself, of the 31 starts of the locking finding, exactly those the certificate finding names stay out
    of the width-16 certificate for 2,000 steps (start 4 under 0001, 24 under 0011, 8 and 18 under 0111), and each of
    them enters the kit's ether-and-wall family."""
    for word, missing in (("0001", [4]), ("0011", [24]), ("0111", [8, 18])):
        times, family = coin_lock.sample(word, coin_lock.certificate(word, 16), 31, 2000)  # (31,), (m,)
        assert np.flatnonzero(times < 0).tolist() == missing, word
        assert (family >= 0).all(), word


def test_slow_halves() -> None:
    """With a beam as wide as the number of halves, the beam search is exhaustive and matches the census of up to 10
    cells under 0001; with the finding's beam it matches the census at its starting length, 12 cells, for all three
    words, as the slow-half finding quotes (544, 980 and 416)."""
    wall = absorption.kit_wall()  # (4, 2^13)
    census = absorption.census("0001", 10, 0, 4000, wall)  # (2^10,)
    best = slow_halves.beam_search("0001", 1 << 10, 6, 10, 4000, wall)
    assert best[10][0] == int(census.max())
    half = best[10][1]  # (10,)
    assert slow_halves.entry_times("0001", half[None, :], 4000, wall)[0] == best[10][0]
    for word, latest in (("0001", 544), ("0011", 980), ("0111", 416)):
        assert slow_halves.beam_search(word, 512, 12, 12, 4000, wall)[12][0] == latest


def test_periodic_columns() -> None:
    """The bit-sliced search against direct evolution: under Rule 150 the single cell's center column survives with
    period 1 and under Rule 90 the row 101 keeps column 1 white; under Rule 30 no triple survives for 12 cells, and the
    nearest miss at 8 cells, simulated as a bool array, repeats exactly 15 times with its period and then fails."""
    found, _, _ = periodic_columns.search(8, 32, 256, 150)
    assert (1, 0, 1) in found
    found, _, _ = periodic_columns.search(8, 32, 256, 90)
    assert (0b101, 1, 1) in found
    found, longest, witness = periodic_columns.search(12, 32, 256, 30)
    assert found == [] and longest == 17
    found, longest, (row, column, period) = periodic_columns.search(8, 32, 256, 30)
    assert found == [] and longest == 15
    cells = np.zeros(8 + 2 * 300, dtype=bool)  # (608,), cell j of the row at index 300 + j
    cells[300:308] = [(row >> j) & 1 for j in range(8)]
    col = spacetime(cells, 299)[:, 300 + column]  # (300,)
    repeats = 0
    while col[period + repeats] == col[repeats]:
        repeats += 1
    assert repeats == longest


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


def test_ether_and_walls(certificate: np.ndarray) -> None:
    """The ether table is a Rule 30 orbit on a ring and every listed alignment holds; the greatest wall is the last 13
    columns of the core certificate of 0001 at width 16, which the core fixes to the ether's B1 B2 B3; the computed wall
    has the kit's 26, 29, 27 and 27 states, steps into itself for both cells beyond, and is the closure of any one of
    its states."""
    # certificate: (4, 2^16)
    ring = np.array([[absorption.ether(j, ph) for j in range(70)] for ph in range(4)], dtype=bool)  # (4, 70)
    for ph in range(4):
        assert np.array_equal(np.roll(ring[ph], 1) ^ (ring[ph] | np.roll(ring[ph], -1)), ring[(ph + 1) % 4])
    assert all(absorption.aligned(word, j0, shift) for word in absorption.WORDS
               for j0, shift in absorption.ALIGNMENTS[word])
    greatest, wall = absorption.greatest_wall(), absorption.kit_wall()  # (4, 2^13) each
    for ph in range(4):
        assert set((np.flatnonzero(certificate[ph]) >> 3).tolist()) == set(np.flatnonzero(greatest[ph]).tolist())
    assert wall.sum(axis=1).tolist() == [26, 29, 27, 27] and not (wall & ~greatest).any()
    states = [(ph, s) for ph in range(4) for s in np.flatnonzero(wall[ph]).tolist()]
    for ph, s in states:
        for beyond in (0, 1):
            row = absorption.ether(2, ph) | (s << 1) | (beyond << 14)  # B3 at bit 0, the wall at bits 1 .. 13
            assert wall[(ph + 1) % 4][(step(row) >> 1) & 0x1FFF]
    seen, todo = {states[0]}, [states[0]]
    while todo:
        ph, s = todo.pop()
        for beyond in (0, 1):
            nxt = ((ph + 1) % 4, (step(absorption.ether(2, ph) | (s << 1) | (beyond << 14)) >> 1) & 0x1FFF)
            if nxt not in seen:
                seen.add(nxt)
                todo.append(nxt)
    assert seen == set(states)


def in_family_slow(word: str, row: int, phase: int, wall: np.ndarray) -> bool:
    """The kit's `InFamily` for a right half held as an integer (bit j is column j + 1), checked column by column."""
    for j0, shift in absorption.ALIGNMENTS[word]:
        psi = (phase + shift) % 4
        for k in range(52):
            if (j0 + k) % 7 == 2 and all((row >> (p - 1)) & 1 == absorption.ether(j0 + p, psi) for p in range(1, k + 1)) \
                    and wall[psi][(row >> k) & 0x1FFF]:
                return True
    return False


def test_absorption_census() -> None:
    """Every right half of up to 6 cells, in every phase of the three words, enters the family exactly when integer
    rows stepped one at a time first meet the family checked column by column; and at 12 cells the latest entries are
    the absorption finding's 544, 980 and 416 at phase 0."""
    wall = absorption.kit_wall()  # (4, 2^13)
    for word in absorption.WORDS:
        for phase in range(4):
            times = absorption.census(word, 6, phase, 600, wall)  # (64,)
            for start in range(64):
                row, t = start, 0
                while not in_family_slow(word, row, (t + phase) % 4, wall):
                    row = ((row << 1) | int(word[(t + phase) % 4])) ^ (row | (row >> 1))
                    t += 1
                assert times[start] == t, (word, phase, start)
    assert [int(absorption.census(word, 12, 0, 1200, wall).max()) for word in absorption.WORDS] == [544, 980, 416]


def least_depth_slow(word: str, row: int, phase: int, wall: np.ndarray) -> int:
    """The least depth at which an integer right half is in the kit's family, checked column by column, or -1."""
    depths = [k for j0, shift in absorption.ALIGNMENTS[word] for k in range(52)
              if (j0 + k) % 7 == 2 and wall[(phase + shift) % 4][(row >> k) & 0x1FFF]
              and all((row >> (p - 1)) & 1 == absorption.ether(j0 + p, phase + shift) for p in range(1, k + 1))]
    return min(depths, default=-1)


def test_sparse_halves() -> None:
    """The certificates of `SparseRight`: packing round-trips, each first black cell lists one entry per second cell up
    to its step plus depth plus 13, and sampled entries are the first step at which integer rows stepped one at a time
    meet the family, at the least depth there, checked column by column."""
    rng = np.random.default_rng(31)
    entries = [(int(t), int(k)) for t, k in zip(rng.integers(0, 2000, 50), rng.integers(0, 64, 50))]
    assert sparse_halves.decode(sparse_halves.encode(entries[0], entries[1:]), 50) == entries
    wall = absorption.kit_wall()  # (4, 2^13)
    word, phase = "0111", 2
    certs = sparse_halves.certificates(word, phase, wall)
    assert len(certs) == 30
    samples = []
    for p1, ((t, k), pairs) in enumerate(certs, start=1):
        assert len(pairs) == max(0, t + k + 13 - p1)
        samples.append((1 << (p1 - 1), t, k))
        for j in rng.choice(len(pairs), size=min(3, len(pairs)), replace=False).tolist():
            samples.append(((1 << (p1 - 1)) | (1 << (p1 + j)), *pairs[j]))
    for half, t, k in samples:
        row = half
        for s in range(t):
            assert least_depth_slow(word, row, (s + phase) % 4, wall) < 0
            row = ((row << 1) | int(word[(s + phase) % 4])) ^ (row | (row >> 1))
        assert least_depth_slow(word, row, (t + phase) % 4, wall) == k
    assert sparse_halves.bound(certs) == 623


def test_small_halves() -> None:
    """The certificates of `TenCells`: packing round-trips, and for sampled halves of up to seven cells each entry is the
    first step at which integer rows stepped one at a time meet the family, at the least depth there, checked column
    by column."""
    rng = np.random.default_rng(43)
    entries = [(int(t), int(k)) for t, k in zip(rng.integers(0, 2000, 40), rng.integers(0, 64, 40))]
    assert small_halves.decode(small_halves.encode(entries), 40) == entries
    wall = absorption.kit_wall()  # (4, 2^13)
    for word, phase in (("0001", 2), ("0011", 1), ("0111", 3)):
        certs = small_halves.certificates(word, 7, phase)
        assert len(certs) == 128
        for half in rng.choice(128, size=12, replace=False).tolist():
            t, k = certs[half]
            row = half
            for s in range(t):
                assert least_depth_slow(word, row, (s + phase) % 4, wall) < 0
                row = ((row << 1) | int(word[(s + phase) % 4])) ^ (row | (row >> 1))
            assert least_depth_slow(word, row, (t + phase) % 4, wall) == k


def test_ether_prefix() -> None:
    """The truncated-ether certificates: packing round-trips; for sampled alignments, phases and tails, each direct entry
    is the first step at which integer rows stepped one at a time meet the family, at the least depth there, checked
    column by column; each base meets it through its own alignment with column 1 the ether's before; and seven more
    ether columns in front give the same step at seven columns more depth, for two more blocks."""
    rng = np.random.default_rng(33)
    entries = [(int(t), int(k)) for t, k in zip(rng.integers(0, 2000, 20), rng.integers(0, 64, 20))]
    assert ether_prefix.decode(ether_prefix.encode(13, entries[:13], entries[13:])) == (13, entries[:13], entries[13:])
    wall = absorption.kit_wall()  # (4, 2^13)

    def stepped(word: str, phase: int, row: int, t: int) -> int:
        for s in range(t):
            row = ((row << 1) | int(word[(s + phase) % 4])) ^ (row | (row >> 1))
        return row

    def own_depth(word: str, j0: int, shift: int, row: int, phase: int) -> int:
        psi = (phase + shift) % 4
        ks = [k for k in range(200) if (j0 + k) % 7 == 2 and wall[psi][(row >> k) & 0x1FFF]
              and all((row >> (p - 1)) & 1 == absorption.ether(j0 + p, psi) for p in range(1, k + 1))]
        return min(ks, default=-1)

    for word, j0, shift, phase, tail in (("0001", 5, 0, 3, 0), ("0011", 1, 3, 0, 5), ("0111", 2, 2, 1, 11)):
        psi = (phase + shift) % 4
        b, direct, bases = ether_prefix.certificate(word, j0, shift, phase, tail)
        for length, (t, k) in enumerate(direct):
            row = ether_prefix.prefix_half(j0, psi, length, tail)
            assert all(least_depth_slow(word, stepped(word, phase, row, s), (s + phase) % 4, wall) < 0 for s in range(t))
            assert least_depth_slow(word, stepped(word, phase, row, t), (t + phase) % 4, wall) == k
        for i, (t, k) in enumerate(bases):
            for extra in range(3):
                row = ether_prefix.prefix_half(j0, psi, b + i + 7 * extra, tail)
                for s in range(t):
                    assert (stepped(word, phase, row, s) & 1) == absorption.ether(j0 + 1, (s + psi) % 4)
                assert own_depth(word, j0, shift, stepped(word, phase, row, t), (t + phase) % 4) == k + 7 * extra


def test_ether_agreement() -> None:
    """`ether_agreement` against a direct comparison of cell strings with every rotation of the ether, on random halves
    and on halves that are a rotation of the ether on a known prefix."""
    rng = np.random.default_rng(36)
    halves = [int(h) for h in rng.integers(0, 1 << 16, 50)]
    halves += [ether_prefix.ether_bits(j0, psi, k) | (1 - absorption.ether(j0 + k + 1, psi)) << k
               for j0, psi, k in ((2, 1, 9), (6, 3, 12), (0, 0, 5))]
    for half in halves:
        cells = format(half, "016b")[::-1]
        best = max(next((k for k in range(16) if cells[k] != str(absorption.ether(j0 + k + 1, psi))), 16)
                   for j0 in range(7) for psi in range(4))
        assert ether_prefix.ether_agreement(half, 16) == best


def test_long_window() -> None:
    """The window of `LongWindow`: the packed center cells against `center_column`, each checkpoint row against the
    integer rows stepped to its time, and the new factor against the set of every earlier factor, read as strings."""
    bits, checkpoints = long_window.simulate()
    column = center_column(long_window.N)  # (N,)
    assert np.array_equal(np.array([(bits >> t) & 1 for t in range(long_window.N)], dtype=np.uint8), column)
    row = 1 << long_window.N
    for t in range(1, max(checkpoints) + 1):
        row = step(row)
        if t in checkpoints:
            assert checkpoints[t] == row, t
    assert sorted(checkpoints) == [16384, 32768, 49152]
    length = long_window.new_factor(bits)
    cells = "".join(map(str, column.tolist()))
    for size, new in ((length - 1, False), (length, True)):
        start = long_window.N - size
        earlier = {cells[j:j + size] for j in range(start)}
        assert (cells[start:] not in earlier) == new, size
    assert length == 19


def test_period_three() -> None:
    """Column 1 of driven right halves against cell arrays stepped with the center as column 0, for both words and
    every phase; `settled_periods` on sequences with a known transient and period; and the counts the negative result
    quotes, at small sizes: under 011 no right half of up to 6 cells has column 1 at the white times settled after 3,000
    steps, while under 001 the white half has settled with period 14 samples, the 21 steps of the kit's trap."""
    rng = np.random.default_rng(41)
    halves = [0, 1, 5, 0b1011, int(rng.integers(0, 1 << 20))]
    steps = 300
    for word in period_three.WORDS:
        for phase in range(3):
            column = period_three.column_one(word, halves, phase, steps)  # (steps, n)
            for i, half in enumerate(halves):
                cells = np.zeros(21 + steps + 2, dtype=bool)  # (m,), column j + 1 at index j + 1, the center at 0
                cells[1:21] = [(half >> j) & 1 for j in range(20)]
                for t in range(steps):
                    assert column[t, i] == cells[1]
                    cells[0] = word[(t + phase) % 3] == "1"
                    left = np.concatenate([[False], cells[:-1]])  # (m,)
                    right = np.concatenate([cells[1:], [False]])  # (m,)
                    cells = left ^ (cells | right)
    block = np.array([1, 0, 0, 1, 1, 0, 1], dtype=np.uint8)  # (7,), primitive
    seqs = np.stack([np.concatenate([rng.integers(0, 2, 100).astype(np.uint8), np.tile(block, 43)]),
                     rng.integers(0, 2, 401).astype(np.uint8)], axis=1)  # (401, 2)
    assert period_three.settled_periods(seqs, 100).tolist() == [7, 0]
    _, periods = period_three.report("011", list(range(64)), 0, 3000)
    assert (periods == 0).all()
    _, periods = period_three.report("001", [0], 0, 6000)
    assert periods.tolist() == [14]


def test_t001_entries() -> None:
    """Entry into the kit's trap t001, read from its source: the white half enters at step 1,270, 1,269 or 1,268 by
    phase, as the kit's `t001_reached` and `EmptyRight.emptyRight_001` state; integer rows stepped one at a time stay
    in the trap for 300 steps after entry with random cells beyond column 47, as the trap's closure requires; and
    `periodic_extent` agrees with the same rows, covering the trap's 38 periodic columns once the white half is in."""
    keys = set(period_three.trap_keys().tolist())
    assert len(keys) == 815
    assert period_three.trap_entries([0], 0, 2000, period_three.trap_keys()).tolist() == [1270]
    assert period_three.trap_entries([0, 0], 1, 2000, period_three.trap_keys()).tolist() == [1269, 1269]
    assert period_three.trap_entries([0], 2, 2000, period_three.trap_keys()).tolist() == [1268]
    rng = np.random.default_rng(42)
    mask = (1 << period_three.TRAP_WIDTH) - 1
    row = 0
    for t in range(1270):
        row = ((row << 1) | int("001"[t % 3])) ^ (row | (row >> 1))
    for trial in range(3):
        noisy = (row & mask) | (int(rng.integers(0, 1 << 62)) << period_three.TRAP_WIDTH)
        for t in range(1270, 1570):
            assert ((noisy & mask) * 4 + t % 3) in keys, (trial, t)
            noisy = ((noisy << 1) | int("001"[t % 3])) ^ (noisy | (noisy >> 1))
    history = [0]
    for t in range(2000):
        history.append(((history[-1] << 1) | int("001"[t % 3])) ^ (history[-1] | (history[-1] >> 1)))
    for t in (500, 2000):
        repeats = [all((history[t] >> p) & 1 == (history[t - 21 * k] >> p) & 1 for k in range(1, 6)) for p in range(128)]
        extent = repeats.index(False) if False in repeats else 128
        assert period_three.periodic_extent(0, 0, t + 1, [t]) == [extent]
    assert extent >= 38  # the trap's 38 columns of period 21


def lean_states(name: str) -> set[tuple[int, int]]:
    """The (phase, strip) pairs of the list `name` in the kit's `Rule30Ether.lean`, the strip's first cell at bit 0."""
    source = ROOT / ".lake/packages/rule30prize/lean/Ruliology/CellularAutomata/Rule30Ether.lean"
    body = source.read_text(encoding="utf-8").split(f"def {name} : List (Nat × List Bool) := [", 1)[1].split("\n]", 1)[0]
    return {(int(phase), sum(1 << i for i, cell in enumerate(cells.split(", ")) if cell == "true"))
            for phase, cells in re.findall(r"\((\d), \[([a-z, ]+)\]\)", body)}


def test_wall_is_the_kits() -> None:
    """The computed wall is the kit's `wallStates`, read from its source, and the kit's `S0001` is the ether's B1 B2 B3
    followed by a wall state at the same phase."""
    wall = absorption.kit_wall()  # (4, 2^13)
    computed = {(ph, s) for ph in range(4) for s in np.flatnonzero(wall[ph]).tolist()}
    assert len(computed) == 109 and lean_states("wallStates") == computed
    b123 = {ph: sum(absorption.ether(j, ph) << j for j in range(3)) for ph in range(4)}
    assert lean_states("S0001") == {(ph, b123[ph] | (s << 3)) for ph, s in computed}


def test_pure_ether() -> None:
    """Under 0001 the periodic half 0010000 is the aligned ether at phase 0, and 1110110 becomes it two steps after
    phase 1, checked on integer rows; neither enters the family, and the aligned ether is outside the family at every
    phase, checked column by column."""
    wall = absorption.kit_wall()  # (4, 2^13)
    for name, phase, when in (("0010000", 0, 0), ("1110110", 1, 2)):
        row = sum(int(name[j % 7]) << j for j in range(400))
        for t in range(when):
            row = (((row << 1) | int("0001"[(t + phase) % 4])) ^ (row | (row >> 1))) & ((1 << 400) - 1)
        assert any(all((row >> (p - 1)) & 1 == absorption.ether(j0 + p, when + phase + shift) for p in range(1, 200))
                   for j0, shift in absorption.ALIGNMENTS["0001"])
        rows = absorption.packed(np.array([[int(name[j % 7]) for j in range(4070)]], dtype=np.uint8))  # (1, 64)
        assert absorption.pure_ether("0001", rows, phase, 8).tolist() == [when]
        assert absorption.absorb("0001", rows, phase, 400, wall, 4070).tolist() == [-1]
    for j0, shift in absorption.ALIGNMENTS["0001"]:
        for phase in range(4):
            row = sum(absorption.ether(j0 + p, phase + shift) << (p - 1) for p in range(1, 120))
            assert not in_family_slow("0001", row, phase, wall)


def test_deep_depth() -> None:
    """The family at any depth: a row with the aligned ether on columns 1 .. k, a wall state from the kit's source on
    the next 13 and random cells beyond is in the family at depth k (k past the 64-column window included), and stops
    being so when one ether column is flipped; the deepest depth is at least the least one `family_depth` finds."""
    rng = np.random.default_rng(17)
    wall = absorption.kit_wall()  # (4, 2^13)
    states = sorted(lean_states("wallStates"))
    for word in absorption.WORDS:
        for j0, shift in absorption.ALIGNMENTS[word]:
            for _ in range(6):
                phase = int(rng.integers(4))
                psi = (phase + shift) % 4
                k = int(rng.choice([k for k in range(3, 140) if (j0 + k) % 7 == 2]))
                strip = rng.choice([s for ph, s in states if ph == psi])
                row = rng.integers(0, 2, 200).astype(bool)  # (200,), column p + 1 at index p
                row[:k] = [absorption.ether(j0 + p, psi) for p in range(1, k + 1)]
                row[k:k + 13] = [(strip >> q) & 1 for q in range(13)]
                assert absorption.deep_depth(word, row[None, :], phase, wall, 180)[0] >= k, (word, k)
                low = np.uint64(sum(int(row[p]) << p for p in range(64)))
                least = absorption.family_depth(word, np.array([low]), phase, wall)[0]
                assert least <= absorption.deep_depth(word, row[None, :], phase, wall, 180)[0]
                row[int(rng.integers(k))] ^= True
                assert absorption.deep_depth(word, row[None, :], phase, wall, 180)[0] < k


def test_lean_entries() -> None:
    """The entry lists of `SmallRight` in `EmptyRight.lean` are the ones `lean_entries` builds."""
    lean = (ROOT / "Rule30Open" / "Columns" / "EmptyRight.lean").read_text(encoding="utf-8")
    assert absorption.lean_entries(6, absorption.kit_wall()) in lean


def test_coupled_exact_death() -> None:
    """Psi against stepping whole rows: a left half equal to Psi(R) at depths 1 .. W and white beyond keeps the center
    on the word exactly until the first black depth of Psi(R) past W, for random words, phases, right halves and
    widths."""
    rng = np.random.default_rng(11)
    steps = 120
    for _ in range(40):
        word = coupled.WORDS[int(rng.integers(len(coupled.WORDS)))]
        phase, right, width = int(rng.integers(len(word))), int(rng.integers(1 << 10)), int(rng.integers(1, 60))
        row = coupled.psi(word, phase, right, steps)
        death = next(j for j in range(width, steps) if (row >> j) & 1) + 1
        middle = width + steps
        cells = np.zeros(middle + steps + 12, dtype=bool)  # (n,), the center at index `middle`
        cells[middle - width:middle] = [(row >> j) & 1 for j in reversed(range(width))]
        cells[middle] = word[phase] == "1"
        cells[middle + 1:middle + 11] = [(right >> i) & 1 for i in range(10)]
        column = spacetime(cells, death)[:, middle]  # (death + 1,)
        want = [int(word[(t + phase) % len(word)]) for t in range(death + 1)]
        assert column[:death].tolist() == want[:death] and column[death] != want[death]


def test_coupled_rebuilds() -> None:
    """Psi of the empty right half against the antidiagonal rebuild of `held_map` with the center as the boundary, and
    for 0011 at phase 2 against the left half of the kit's ether, which it equals from depth 1."""
    c, column = coupled.center("01", 1, 301), coupled.drive_column("01", 1, 0, 301)
    rebuilt, a1, a2 = 0, 0, 0
    for m in range(300):
        reading = ((c >> (m + 1)) ^ ((c >> m) | (column >> m))) & 1  # column -1 at time m, forced
        d = a1 | a2 | ((((c >> (m - 1)) & 1) << (m - 1)) if m else 0)
        bit = reading ^ ((d & ((1 << m) - 1)).bit_count() & 1)
        a1, a2 = held_map.next_diagonal(bit, d, m), a1
        rebuilt |= bit << m
    assert rebuilt == coupled.psi("01", 1, 0, 300)
    ether_left = sum(int(absorption.ETHER[-k % 7][2]) << (k - 1) for k in range(1, 701))
    assert coupled.psi("0011", 2, 0, 700) == ether_left
    assert coupled.ether_after("10001010111100") == 4 and coupled.ether_after("0010011") == 0

