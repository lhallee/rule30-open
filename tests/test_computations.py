"""Each computation against an independent implementation, a known sequence, or the numbers its entry quotes."""

from __future__ import annotations

import math
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


def test_component_periods() -> None:
    """`game.component_periods` against closed walks: for 001 at width 4 and 0001 at width 6, the cyclic period of each
    component that can hold a play is the gcd of the lengths up to 60 of the closed walks inside it through its first
    node, from powers of its adjacency matrix; its phase test agrees with `bad_pairs`; and 001 at width 4 has a
    component of period 6 where the left column takes both values at one phase but not in one class."""
    for pattern, width in (("001", 4), ("0001", 6)):
        source, target, label, recurrent, _ = game.game_graph(pattern, width)
        found = game.component_periods(pattern, width)
        assert len(found) == int(recurrent.sum())
        for (size, cycle, _, _), component in zip(found, np.flatnonzero(recurrent).tolist()):
            members = np.flatnonzero(label == component)  # (m,)
            index = {node: i for i, node in enumerate(members.tolist())}
            adjacency = np.zeros((members.size, members.size))  # (m, m)
            for a, b in zip(source.tolist(), target.tolist()):
                if a in index and b in index:
                    adjacency[index[a], index[b]] = 1.0
            walk, lengths = np.eye(members.size), []  # (m, m)
            for n in range(1, 61):
                walk = np.minimum(walk @ adjacency, 1.0)
                if walk[0, 0] > 0:
                    lengths.append(n)
            assert size == members.size and cycle == math.gcd(*lengths), (pattern, width, component)
        assert any(found_phase for _, _, found_phase, _ in found) == (game.bad_pairs(pattern, width) > 0)
    assert (6, 6, True, False) in game.component_periods("001", 4)


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


def test_game_masks_long() -> None:
    """The 97 certificates in GameBlocksLong.lean are `lean_mask` at the least width, at most 9, of blocks of period 15
    or 16 that the kit does not exclude, `gameBlocks16` lists the same blocks, and sampled certificates pass the check in
    plain Python and fail it with their values cleared."""
    lean = (ROOT / "Rule30Open" / "Columns" / "GameBlocksLong.lean").read_text(encoding="utf-8")
    masks = re.findall(r"def mask([01]+) : GameMask where\n  block := wordOf (\d+) 0b\1\n  width := (\d+)", lean)
    listed = re.findall(r"\((\d+), 0b([01]+)\)", lean.split("def gameBlocks16", 1)[1].split("\n\n", 1)[0])
    assert len(masks) == 97 and [(n, p) for p, n, _ in masks] == listed
    kit = game.kit_blocks(16)
    rng = np.random.default_rng(45)
    sampled = set(rng.choice(len(masks), size=10, replace=False).tolist())
    for i, (pattern, n, width) in enumerate(masks):
        width = int(width)
        assert int(n) == len(pattern) in (15, 16) and pattern == game.least_rotation(pattern) and pattern not in kit
        assert game.least_width(pattern) == width <= 9
        assert game.lean_mask(pattern, width) in lean, pattern
        if i in sampled:
            mask = game.game_mask(pattern, width)
            assert mask_ok(pattern, width, mask) and not mask_ok(pattern, width, {**mask, "values": 0}), pattern


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


def test_wide_window() -> None:
    """The window of `WideWindow`: the packed center cells against `center_column`, the checkpoint rows against the
    integer rows stepped to their times, and the new factor of length 20 against the sets of earlier factors."""
    bits, checkpoints = long_window.simulate(long_window.WIDE)
    column = center_column(long_window.WIDE)  # (WIDE,)
    assert np.array_equal(np.array([(bits >> t) & 1 for t in range(long_window.WIDE)], dtype=np.uint8), column)
    assert sorted(checkpoints) == [16384 * q for q in range(1, 16)]
    row = 1 << long_window.WIDE
    for t in range(1, max(checkpoints) + 1):
        row = step(row)
        if t in checkpoints:
            assert checkpoints[t] == row, t
    cells = "".join(map(str, column.tolist()))
    for size, new in ((19, False), (20, True)):
        start = long_window.WIDE - size
        earlier = {cells[j:j + size] for j in range(start)}
        assert (cells[start:] not in earlier) == new, size
    assert long_window.new_factor(bits, long_window.WIDE) == 20


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


def test_constant_rate() -> None:
    """`constant_rate` against values computed by hand on three entry steps, and against the exponential law on a
    large sample of exponential entry times."""
    ratio, left = period_three.constant_rate(np.array([1261, 1262, 1266]), start=1260, at=1264)
    assert abs(ratio - 3 / 2) < 1e-12 and abs(left - np.exp(-4 / 3)) < 1e-12
    rng = np.random.default_rng(43)
    done = 1260 + rng.exponential(20000.0, 200000)  # (200000,)
    ratio, left = period_three.constant_rate(done)
    assert abs(ratio - 1 / np.log(2)) < 0.02
    assert abs(left / np.exp(-(100000 - 1260) / 20000.0) - 1) < 0.05


def test_t001_entries() -> None:
    """Entry into the kit's trap t001, read from its source: the white half enters at step 1,270, 1,269 or 1,268 by
    phase, as the kit's `t001_reached` and `EmptyRight.emptyRight_001` state, while the half with column 2 black
    enters only at step 35,536 from phase 0; integer rows stepped one at a time stay in the trap for 300 steps after
    entry with random cells beyond column 47, as the trap's closure requires; and `periodic_extent` agrees with the
    same rows, covering the trap's 38 periodic columns once the white half is in."""
    keys = set(period_three.trap_keys().tolist())
    assert len(keys) == 815
    assert period_three.trap_entries([0], 0, 2000, period_three.trap_keys()).tolist() == [1270]
    assert period_three.trap_entries([0, 0], 1, 2000, period_three.trap_keys()).tolist() == [1269, 1269]
    assert period_three.trap_entries([0], 2, 2000, period_three.trap_keys()).tolist() == [1268]
    assert period_three.trap_entries([0, 1, 2, 3], 0, 40000, period_three.trap_keys()).tolist() == [1270, 1267, 35536,
                                                                                                      1267]
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



def test_wall_segments() -> None:
    """The three-valued run of `wall_segments` against brute force: every segment of up to nine cells that it passes
    keeps the cell right of the column the same at each 0 over every row that starts at the wall. The segments that
    start and end with 0 and pass are exactly the five forms; the family's criterion on blocks does not depend on the
    rotation, and the family's blocks of period up to 13 are among those the finite game excludes."""
    import itertools
    import re
    from computations import wall_segments
    for m in range(1, 10):
        for bits in itertools.product("01", repeat=m):
            u = "".join(bits)
            if wall_segments.segment_good(u):
                assert wall_segments.brute_segment(u), u
    forms = re.compile(r"^(0+|0+10|0100|0110+|0110*10)$")
    for m in range(1, 15):
        for bits in itertools.product("01", repeat=m):
            u = "".join(bits)
            if u[0] == "0" and u[-1] == "0" and "1" * 9 not in u:
                assert wall_segments.segment_good(u) == bool(forms.match(u)), u
    assert wall_segments.in_family("1" * 9 + "010") and wall_segments.in_family("1")
    assert not wall_segments.in_family("1" * 9 + "00100") and not wall_segments.in_family("01")
    assert wall_segments.in_family("1" * 9 + "010" + "1" * 9 + "01100")
    rng = np.random.default_rng(45)
    for _ in range(40):
        block = "".join(rng.choice(["0", "1"], size=int(rng.integers(10, 20)), p=[0.2, 0.8]))
        rotations = {wall_segments.in_family(block[i:] + block[:i]) for i in range(len(block))}
        assert len(rotations) == 1, block
    family = [b for p in range(1, 14) for b in wall_segments.necklaces(p) if wall_segments.in_family(b)]
    assert len(family) == 16
    assert all(game.least_width(b, 10) is not None for b in family if b != "1")


def test_window_sets() -> None:
    """The sets of windows of `wall_segments` against brute force and the three values: every segment of up to nine
    cells that the sets of three-cell windows pass, brute force passes too, and so do the sets for every segment the
    three values pass; the parity families pass for small lengths; and the family's blocks of period up to 13 are
    among those the finite game excludes, the blocks with nine 1s in a row all of them."""
    import itertools
    from computations import wall_segments
    for m in range(1, 10):
        for bits in itertools.product("01", repeat=m):
            u = "".join(bits)
            if wall_segments.set_segment_good(u):
                assert wall_segments.brute_segment(u), u
            if wall_segments.segment_good(u):
                assert wall_segments.set_segment_good(u), u
    for k in range(4):
        assert wall_segments.set_segment_good("0" * (2 * k + 3) + "100")
        assert wall_segments.set_segment_good("0" * (2 * k + 3) + "110")
        assert wall_segments.set_segment_good("0" * (2 * k + 2) + "1010")
        assert not wall_segments.set_segment_good("0" * (2 * k + 4) + "100")
    family = [b for p in range(1, 14) for b in wall_segments.necklaces(p) if wall_segments.in_set_family(b)]
    nine = [b for p in range(2, 14) for b in wall_segments.necklaces(p) if "1" * 9 in b + b]
    excluded = [b for b in nine if game.least_width(b, 12) is not None]
    assert sorted(b for b in family if b != "1") == sorted(excluded)


def test_windows_after_ones() -> None:
    """The windows that runs of 1s leave, against the kit's wall: nine 1s leave exactly the windows 0 1 0 and 0 1 1,
    which `wall_windows` uses, and eight leave a window with first cell 1 besides, as the kit's
    `eight_black_not_enough` says."""
    from computations import wall_segments
    assert wall_segments.windows_after_ones(9) == wall_segments.wall_windows(3)
    assert wall_segments.windows_after_ones(8) == frozenset({(0, 1, 0), (0, 1, 1), (1, 0, 0)})
    assert all(len({w[0] for w in wall_segments.windows_after_ones(ones)}) == 2 for ones in range(1, 9))


def test_bit_phases() -> None:
    """`bit_game.phase_rounds` against the game: up to period 10 at width 6 every phase empties a side exactly when
    `game.bad_pairs` finds no component showing both values at a phase. For two blocks of `WIDE`, `lean_block` is the
    text of their checks in BitPhases.lean, and the lists of the three modules hold exactly the 40 blocks of `WIDE`."""
    from computations import bit_game
    for period in range(2, 11):
        for pattern in game.necklaces(period):
            try:
                bit_game.phase_rounds(pattern, 6)
                decided = True
            except ValueError:
                decided = False
            assert decided == (game.bad_pairs(pattern, 6) == 0), pattern
    lean = {name: (ROOT / "Rule30Open" / "Columns" / f"{name}.lean").read_text(encoding="utf-8")
            for name in ("BitPhases", "BitPhases19", "BitPhases20")}
    for block in ("00000000000101101", "000000000010000101"):
        assert bit_game.lean_block(block, bit_game.WIDE[block]) in lean["BitPhases"]
    listed = {}
    for text in lean.values():
        for n, bits, width in re.findall(r"\(\((\d+), 0b([01]+)\), (\d+)\)", text):
            listed[bits] = int(width)
            assert len(bits) == int(n)
    assert listed == bit_game.WIDE


def test_bit_game() -> None:
    """The check of `BitGame` against the finite game: on every primitive block of period at most 9, at widths 5 and 6,
    it decides exactly the blocks the game excludes; and the bit tables' images and preimages agree with the game
    graph on random sets of nodes."""
    from computations import bit_game
    for period in range(1, 10):
        for block in game.necklaces(period):
            for width in (5, 6):
                assert bit_game.criterion(block, width)[0] == (game.bad_pairs(block, width) == 0)
    rng = np.random.default_rng(3)
    for block, width in (("0001", 5), ("00000001", 6), ("0110", 4)):
        tables = bit_game.BitTables(block, width)
        source, target, _, _, _ = game.game_graph(block, width)
        for _ in range(3):
            nodes = rng.random(len(block) << width) < 0.3  # (p 2^K,)
            image = np.zeros_like(nodes)  # (p 2^K,)
            image[target[nodes[source]]] = True
            preimage = np.zeros_like(nodes)  # (p 2^K,)
            preimage[source[nodes[target]]] = True
            table = tables.table(nodes)
            assert (tables.nodes(tables.post(table)) == image).all()
            assert (tables.nodes(tables.pre(table)) == preimage).all()


def test_forcing() -> None:
    """Forcing words: the search over sets of configurations against brute force over every start, for every word of up
    to nine values; the shortest forcing words have seven values; and the blocks of period up to 12 whose 0s all follow
    a forcing word of length 12, against the same test with each lookback checked by brute force."""
    import itertools
    from computations import forcing, wall_segments
    for n in range(1, 10):
        words = forcing.forcing_words(n)
        for bits in itertools.product("01", repeat=n):
            word = "".join(bits)
            assert words.get(word) == forcing.forced_value(word)
    assert forcing.forcing_words(7) == {"0110000": 1, "0110001": 0}
    assert forcing.forced_value("1" * 9) == 0 and forcing.forced_value("1" * 8 + "0") == 1
    family = forcing.forcing_family(forcing.forcing_words(12), 12, 12)
    cache: dict[str, int | None] = {}
    for period in range(1, 13):
        brute = [block for block in wall_segments.necklaces(period)
                 if all(cache.setdefault(word, forcing.forced_value(word)) is not None
                        for word in (forcing.lookback(block, i, 12) for i, ch in enumerate(block) if ch == "0"))]
        assert family[period] == brute
    assert family[8] == ["01111111"] and family[11] == ["00111111111", "01111111111"]


def test_tails() -> None:
    """The tails of `WideWall`, against the two conditions checked by brute force over small periods: a black run of r
    rules out the tails with P - r at most 4 floor(r/9), and nine 1s and b 0s those with P - s - b at most
    4 floor((b - 1)/9) + 2; the kit's Theorems B and D ask more (`kit_theoremB_condition`, `kit_theoremD_condition`)."""
    from computations import wall_segments
    assert wall_segments.longest_tail(45) == (20, 1) and wall_segments.longest_tail(90) == (40, 11)
    assert [wall_segments.least_white_run(m) for m in (0, 2, 6, 10)] == [(1, 37), (1, 46), (10, 64), (19, 82)]
    for tail in range(0, 40):
        ours, kit = wall_segments.least_white_run(tail)
        assert min(b for b in range(1, 400) if tail <= 4 * ((b - 1) // 9) + 2) == ours
        assert min(b for b in range(1, 400) if 1 + 9 * ((tail + 9) // 2) <= b) == kit >= ours
    for run in range(9, 200):
        ours, kit = wall_segments.longest_tail(run)
        assert max(m for m in range(0, run) if m <= 4 * (run // 9)) == ours
        assert max([m for m in range(0, run) if 9 * ((m + 10) // 2) <= run], default=-1) == kit <= ours


def test_stripe() -> None:
    """The stripes of `WideWall`: brute force over every column and every cell beyond a stripe of L cells that ends in a
    black cell finds the cell right of the column the same for 2 L steps and not for 2 L + 1, for L up to 4, and the
    three-valued run first loses it at step 2 L for L up to 10. The shield (0 1)^j is the stripe of length 2 j."""
    from computations import wall_segments
    assert wall_segments.stripe(4) == [0, 1, 0, 1] and wall_segments.stripe(3) == [1, 0, 1]
    for length in range(1, 5):
        assert wall_segments.stripe_brute(length, 2 * length)
        assert not wall_segments.stripe_brute(length, 2 * length + 1)
    for length in range(1, 11):
        assert wall_segments.stripe_known_steps(length) == 2 * length


def test_lock_word() -> None:
    """The lock words of `LockWord`: the trap agrees with `absorption.family_depth`, the depth-first family test, on
    every window; each word, run window by window through the successor table from every start phase, ends every window
    in the trap; and the bit slices agree with that run on sampled windows."""
    from computations import lock_word
    wall = absorption.kit_wall()  # (4, 2^13)
    rng = np.random.default_rng(5)
    for word, (width, _, _, _) in lock_word.LEAST.items():
        member = lock_word.trap(word, width, wall)  # (4, 2^W)
        assert int(member.sum()) == 109
        states = np.arange(1 << width, dtype=np.uint64)  # (2^W,)
        for ph in range(4):
            depth = absorption.family_depth(word, states, ph, wall)  # (2^W,)
            assert np.array_equal(member[ph], (depth >= 0) & (depth <= width - 13))
        values = lock_word.universal_word(word, member)
        successors = lock_certificate.successor_table(word, width)  # (4, 2, 2^W)
        slices = lock_word.slice_run(word, width, values)
        size = 1 << width
        for start in range(4):
            windows = np.arange(size, dtype=np.int64)  # (2^W,)
            for t, value in enumerate(values):
                windows = successors[(start + t) % 4, value][windows]  # (2^W,)
            assert member[(start + len(values)) % 4][windows].all()
            for r in rng.integers(0, size, 20).tolist():
                bit = start * size + r
                assert sum(((slices[j] >> bit) & 1) << j for j in range(width)) == int(windows[r])
        assert lock_word.slice_check(word, width, values, member)


def test_ring_orbits() -> None:
    """The periodic orbits on rings, against a step-by-step search of every state on rings of up to 10 cells, and the
    ether's ring of 7 cells: its alternating column has a left neighbor of period 4."""
    from computations import ring_orbits

    def brute(cells: int) -> int:
        full = (1 << cells) - 1

        def nxt(s: int) -> int:
            left = ((s << 1) | (s >> (cells - 1))) & full
            right = ((s >> 1) | (s << (cells - 1))) & full
            return left ^ (s | right)

        cyclic = set()
        for start in range(1 << cells):
            s = start
            for _ in range(1 << cells):
                s = nxt(s)
            cyclic.add(s)  # after 2^M steps the state is on its cycle
        classes = set()
        for s in cyclic:
            orbit, x = [s], nxt(s)
            while x != s:
                orbit.append(x)
                x = nxt(x)
            classes.add(min(((y << r) | (y >> (cells - r))) & full for y in orbit for r in range(cells)))
        return len(classes)

    for cells in range(1, 11):
        assert len(ring_orbits.orbits(cells)) == brute(cells)
    found, counts = ring_orbits.witnessed(14, 16)
    assert found == {"01": 7} and counts[6] == 3


def test_kit_families() -> None:
    """`PADDING_FAMILIES` and `BLACK_RUN_BLOCKS` are the kit's white-padding certificates and its Theorem B' instances,
    read from its source; at periods 17 and 18 they add 0^13 1011, 0^14 1011 and 0^14 1101 to `kit_blocks`, and up to
    period 16 nothing."""
    padding = (KIT_SOURCE / "Rule30UniformWhitePadding.lean").read_text(encoding="utf-8") + \
        (KIT_SOURCE / "Rule30ShortTail.lean").read_text(encoding="utf-8")
    thresholds = dict(re.findall(r"theorem certificate([A-I]) \(r : Nat\) \(hr : (\d+) ≤ r\)", padding))
    tails = dict(re.findall(r"def tail([A-I]) : List Bool := \[([^\]]*)\]",
                            (KIT_SOURCE / "Rule30Certificates/WhitePaddingFamilies.lean").read_text(encoding="utf-8")))
    assert sorted(thresholds) == sorted(tails) == list("ABCDEFGHI")
    read = {("".join("1" if cell.strip() == "true" else "0" for cell in tails[name].split(",")), int(thresholds[name]))
            for name in thresholds}
    assert read == set(game.PADDING_FAMILIES)
    blocks = re.findall(r"theorem det_[01]+ : Determined \[([^\]]*)\] (\d+) = true",
                        (KIT_SOURCE / "Rule30BlackRunBlocks.lean").read_text(encoding="utf-8"))
    read = {("".join("1" if cell.strip() == "true" else "0" for cell in cells.split(",")), max(9, 9 * int(j0)))
            for cells, j0 in blocks}
    assert read == set(game.BLACK_RUN_BLOCKS)
    assert "padding or black-run family" not in game.kit_blocks(16).values() and len(game.kit_blocks(16)) == 62
    added = {word for word, reason in game.kit_blocks(18).items() if reason == "padding or black-run family"}
    assert added == {"0" * 13 + "1011", "0" * 14 + "1011", "0" * 14 + "1101"}


def test_game_survey() -> None:
    """The survey of `excluded_blocks` over worker processes agrees with the survey in one process, and both agree with
    `least_width`, block by block, on every primitive block of period 8 to 10."""
    one, tried = game.excluded_blocks(10, [6, 10], min_period=8)
    two, tried2 = game.excluded_blocks(10, [6, 10], min_period=8, workers=2)
    assert one == two and tried == tried2 == len(game.necklaces(8)) + len(game.necklaces(9)) + len(game.necklaces(10))
    for period in range(8, 11):
        for block in game.necklaces(period):
            width = game.least_width(block, 10)
            assert (block in one) == (width is not None)
            if width is not None:
                assert one[block] == (6 if width <= 6 else 10)


def test_lock_unreachable() -> None:
    """`lock_word.unreachable` against a forward search: beside an alternating center, at width 19, the set reached
    from a window marked unreachable, with both values of column 20 at every step, never meets the trap, and the set
    reached from a window marked reachable does; under 0111 at width 13 no window is unreachable."""
    from computations import lock_word
    wall = absorption.kit_wall()  # (4, 2^13)
    assert not lock_word.unreachable("0111", 13, wall).any()
    width = 19
    out = lock_word.unreachable("0101", width, wall)  # (4, 2^W)
    member = lock_word.trap("0101", width, wall)  # (4, 2^W)
    successors = lock_certificate.successor_table("0101", width)  # (4, 2, 2^W)

    def meets_trap(window: int) -> bool:
        seen = np.zeros((4, 1 << width), dtype=bool)  # (4, 2^W)
        seen[0, window] = True
        frontier = [np.array([window], dtype=np.int64)] + [np.zeros(0, dtype=np.int64)] * 3  # by phase
        while any(f.size for f in frontier):
            if any(member[ph][frontier[ph]].any() for ph in range(4)):
                return True
            nxt = []
            for ph in range(4):
                prev = frontier[(ph - 1) % 4]  # (m,), at phase ph - 1
                step = np.unique(successors[(ph - 1) % 4][:, prev].ravel())  # (k,)
                step = step[~seen[ph][step]]
                seen[ph][step] = True
                nxt.append(step)
            frontier = nxt
        return False

    rng = np.random.default_rng(7)
    bad = np.flatnonzero(out[0])  # (n,)
    good = np.flatnonzero(~out[0])  # (m,)
    for window in rng.choice(bad, 2, replace=False).tolist():
        assert not meets_trap(window)
    for window in rng.choice(good, 2, replace=False).tolist():
        assert meets_trap(window)


def test_lock_avoid_growth() -> None:
    """`lock_word.avoid_growth` against a direct count: under 0111 at width 13, the number of sequences of column 14 that
    keep the worst window out for L steps, counted step by step, grows by the same factor per step between L = 600 and
    L = 800."""
    from computations import lock_word
    wall = absorption.kit_wall()  # (4, 2^13)
    member = lock_word.trap("0111", 13, wall)  # (4, 2^13)
    successors = lock_certificate.successor_table("0111", 13)  # (4, 2, 2^13)
    counts = np.where(member, 0.0, 1.0)  # (4, 2^13), sequences of length 0 that keep each window out
    worst = []
    for length in range(1, 801):
        nxt = np.empty_like(counts)  # (4, 2^13)
        for ph in range(4):
            later = counts[(ph + 1) % 4]  # (2^13,)
            nxt[ph] = (later[successors[ph, 0]] + later[successors[ph, 1]]) * ~member[ph]
        scale = nxt.max()
        counts = nxt / scale
        worst.append(np.log(scale))
    rate = np.exp(np.mean(worst[600:]))
    assert abs(rate - lock_word.avoid_growth("0111", member)) < 1e-3


def test_locks() -> None:
    """`locks.lock_info` against forward searches: for sampled nodes of the games of 0111 at width 13 and 01010101011 at
    width 10, a node is locked exactly when the nodes it reaches show one value of the left column at each phase, and it
    reaches a locked node exactly when `lock_info` says so; 0111 at width 13 is steerable and 0001 is not. `steering`
    against Rule 30 run on all windows at once: its sequence leaves every start at a listed window that is locked."""
    from computations import locks
    assert locks.steerable("0111", 13) and not locks.steerable("0001", 13)
    rng = np.random.default_rng(11)
    for block, width in (("0111", 13), ("01010101011", 10)):
        source, target, _, _, column = game.game_graph(block, width)  # (2 p n,), (2 p n,), _, _, (p n,)
        locked, reach = locks.lock_info(block, width)  # (p n,), (p n,)
        nodes = column.size
        phase = np.arange(nodes) >> width  # (p n,)
        for node in rng.integers(0, nodes, 6).tolist():
            seen = np.zeros(nodes, dtype=bool)  # (p n,)
            seen[node] = True
            frontier = seen.copy()  # (p n,)
            while frontier.any():
                after = np.zeros(nodes, dtype=bool)  # (p n,)
                after[target[frontier[source]]] = True
                frontier = after & ~seen
                seen |= frontier
            both = any(column[seen & (phase == ph)].any() and (~column[seen & (phase == ph)]).any()
                       for ph in range(len(block)))
            assert locked[node] == (not both)
            assert reach[node] == bool((seen & locked).any())
    # the steering sequence of 0111, run on every window by bit operations: each ends at a listed locked window
    width, period = 13, 4
    values, finals = locks.steering("0111", width)
    locked, _ = locks.lock_info("0111", width)  # (p n,)
    mask = (1 << width) - 1
    for start in range(period):
        windows = np.arange(1 << width, dtype=np.int64)  # (2^W,), bit j is cell j + 1 right of the column
        for step, value in enumerate(values):
            left = ((windows << 1) | int("0111"[(start + step) % period])) & mask  # (2^W,)
            right = (windows >> 1) | (value << (width - 1))  # (2^W,)
            windows = left ^ (windows | right)  # (2^W,)
        final = (start + len(values)) % period
        assert set(np.unique(windows).tolist()) <= set(finals[final])
        assert locked[(final << width) + windows].all()
    assert locks.longest_run("0111") == 3 and locks.longest_run("01010101011") == 2 and locks.longest_run("1000001") == 5
    # no locked node for 01 at width 8: from every node a forward search meets both values of the left column at a phase
    source, target, _, _, column = game.game_graph("01", 8)  # (2 p n,), (2 p n,), _, _, (p n,)
    phase = np.arange(column.size) >> 8  # (p n,)
    for node in range(column.size):
        seen = np.zeros(column.size, dtype=bool)  # (p n,)
        seen[node] = True
        frontier = seen.copy()  # (p n,)
        while frontier.any():
            after = np.zeros(column.size, dtype=bool)  # (p n,)
            after[target[frontier[source]]] = True
            frontier = after & ~seen
            seen |= frontier
        assert any(column[seen & (phase == ph)].any() and (~column[seen & (phase == ph)]).any() for ph in range(2))
    assert not locks.has_lock("01", 8) and locks.has_lock("0111", 13)
    assert locks.family("0^k 11101", 3) == "00011101" and locks.family("00 1^k 01", 4) == "00111101"
    assert locks.fewest_mixed("0111", 13) == 0 and locks.fewest_mixed("01", 8) == 1
    assert locks.lock_census([2, 4], [13]) == {(2, 13): [], (4, 13): ["0111"]}
    # white alone: 27 white values in column 8 lock every window of 7 cells beside 000011111111, and 26 do not
    block, width = "000011111111", 7
    assert locks.constant_steering(block, width, 0) == 27 and locks.white_run(block, [6, 7, 8]) == (7, 27)
    locked, _ = locks.lock_info(block, width)  # (p n,)
    mask, period, ends = (1 << width) - 1, len(block), {}
    for start in range(period):
        windows = np.arange(1 << width, dtype=np.int64)  # (2^W,)
        for step in range(27):
            left = ((windows << 1) | int(block[(start + step) % period])) & mask  # (2^W,)
            windows = left ^ (windows | (windows >> 1))  # (2^W,), the free cell white
            ends[(start, step + 1)] = locked[(((start + step + 1) % period) << width) + windows].all()
    assert all(ends[(start, 27)] for start in range(period))
    assert not all(ends[(start, 26)] for start in range(period))


def test_lock_breaks() -> None:
    """`right_half.lock_breaks` against the right half stepped as 64-bit words by `absorption.step_rows`: driven by
    01111, start 2 holds column 1 with period 10 at the white times from step 6,000 until step 13,000."""
    from computations import absorption, right_half
    start = right_half.random_starts(30, 64)[2]
    steps = 14000
    _, count, first = right_half.lock_breaks("01111", start, steps, 10, 6000)
    rows = np.zeros((1, (64 + steps) // 64 + 2), dtype=np.uint64)  # (1, words)
    rows[0, 0] = np.uint64(start)
    column = np.zeros(steps, dtype=np.uint8)  # (steps,)
    for t in range(steps):
        column[t] = int(rows[0, 0]) & 1
        rows = absorption.step_rows(rows, int("01111"[t % 5]))  # (1, words)
    white = np.array(["01111"[t % 5] == "0" for t in range(steps - 10)])  # (steps - 10,)
    breaks = np.flatnonzero((column[:-10] != column[10:]) & white)  # (b,)
    late = breaks[breaks > 6000]  # (c,)
    assert first == 13000 == int(late[0]) and count == late.size


def test_left_halves() -> None:
    """`left_halves.tree_failures` against two searches of `held_map`: for 0111 its condition is the kit's C3 and the
    latest failures equal `held_map.tree_failures`; for 01 it is the period-two condition and they equal
    `held_map.first_failures`, which steps every integer of each support directly."""
    from computations import held_map, left_halves
    assert left_halves.pattern("0111") == held_map.PATTERN["0111"] == "*001"
    assert "".join(map(str, left_halves.effective("0111"))) == held_map.EFFECTIVE["0111"]
    for phase in range(4):
        assert left_halves.tree_failures("0111", 24, phase) == held_map.tree_failures("0111", 24, phase, False)
    assert left_halves.pattern("01") == "*1" and left_halves.effective("01") == [0, 0]
    runs = [left_halves.tree_failures("01", 12, phase)[0] for phase in range(2)]
    for support in range(2, 13):
        assert [run[support - 1] for run in runs] == [int(held_map.first_failures(support, phase).max())
                                                      for phase in (0, 1)]
    assert left_halves.pattern("01111") == "*0001" and left_halves.effective("01111") == [0, 1, 1, 1, 0]


def test_left_halves_latch() -> None:
    """The latch along real orbits: from random rows, at any column, it never rejects the readings of the cell left
    of the column and every value it knows is the cell right of it. Then the tree, with and without the latch,
    against stepping every half of up to 9 cells directly, the half held as an integer and driven by the effective
    boundary. For 01 the latch is `period_two_golden`: a white reading at one 0 forces a black one at the next."""
    from computations import left_halves
    from computations.rule30 import step
    rng = np.random.default_rng(30)
    known = 0
    for _ in range(40):
        row = int(rng.integers(0, 1 << 40)) << 200  # 40 random cells, white beyond; bit i is cell 200 + i
        rows = [row]
        for _ in range(120):
            rows.append(step(rows[-1]))
        k = 220 + int(rng.integers(-15, 15))  # a column inside the light cone
        column = "".join(str((r >> k) & 1) for r in rows)  # (121,) as a string
        state = left_halves.UNKNOWN
        for t in range(120):
            state = left_halves.advance(column, t, state, (rows[t] >> (k - 1)) & 1, True)
            assert state is not None
            if state != left_halves.UNKNOWN:
                assert state == (rows[t + 1] >> (k + 1)) & 1
                known += 1
    assert known > 1000

    def direct(block: str, support: int, phase: int, latch: bool) -> int:
        boundary = left_halves.effective(block)
        worst = 0
        for start in range(1 << (support - 1), 1 << support):
            half, state, t = start, left_halves.UNKNOWN, 0  # bit j of `half` is cell -1 - j
            while (state := left_halves.advance(block, t + phase, state, half & 1, latch)) is not None:
                half = (half >> 1) ^ (half | (half << 1) | boundary[(t + phase) % len(block)])
                t += 1
            worst = max(worst, t)
        return worst

    for block in ["01", "001", "011", "0011", "00111", "01011", "000111", "0110111"]:
        for latch in (False, True):
            for phase in range(len(block)):
                tree = left_halves.tree_failures(block, 9, phase, latch)[0]
                assert tree == [direct(block, support, phase, latch) for support in range(1, 10)]
    golden = [left_halves.advance("01", t, s, r, True) for t, s, r in [(0, left_halves.UNKNOWN, 0), (1, 1, 1)]]
    assert golden == [1, 0] and left_halves.advance("01", 2, 0, 0, True) is None


def test_left_halves_entropy() -> None:
    """The automaton of the condition counts the tree's branches: the readings of length m that it allows from a phase,
    the latch state unknown, are as many as the halves the tree keeps through step m - 1. Its entropy is w / P without
    the latch, and for 01 with it the golden condition's log2 of the golden ratio over 2."""
    from computations import left_halves
    for block in ["01", "001", "0011", "00101", "0001011"]:
        for latch in (False, True):
            matrix = left_halves.transfer(block, latch)  # (3P, 3P)
            for phase in range(len(block)):
                counts = np.zeros(3 * len(block))  # (3P,)
                counts[3 * phase + left_halves.UNKNOWN] = 1
                branches = left_halves.tree_failures(block, 14, phase, latch)[1]
                for m in range(1, 15):
                    counts = counts @ matrix  # (3P,)
                    assert counts.sum() == branches[m - 1]
        assert abs(left_halves.entropy(block) - block.count("0") / len(block)) < 1e-9
    assert abs(left_halves.entropy("01", True) - np.log2((1 + 5 ** 0.5) / 2) / 2) < 1e-9
    for block in ["01", "001", "0001", "00111", "0110111"]:  # the window of one cell is the latch, by other code
        rates = [left_halves.window_entropy(block, width) for width in range(1, 6)]
        assert abs(rates[0] - left_halves.entropy(block, True)) < 1e-9
        assert all(wide <= narrow + 1e-6 for narrow, wide in zip(rates, rates[1:]))  # eigenvalues to about 1e-8


def test_lock_chain() -> None:
    """`lock_chain` against a step of the rule, the game and the kit. `left_column` inverts `step` on random columns;
    the bottom components of the locked nodes of 0000011101, 0011111101 and 0000000101 at width 13 have columns 1 .. 5,
    1 .. 4 and 1 .. 7 fixed by the phase, the last repeating 0 1^9, and `chain` from it, white at its white phase, gives
    the others and the block; the blocks of period 8 with a locked node at width 13 are the chain of 0 1^7 at distances
    0 to 7; that chain is the kit's ether from distance 8, and the bottom components of 01110111 at width 13 are the
    kit's wall states, read from its source; from the wall, the white phase of 0 1^8 finds cell 1 white and then black,
    as an exact run from the wall does, and those of 0 1^7 and 0 1^9 find it white. The kit's trap for 001 is the chain
    of its column 38; `is_lock` agrees with `locks.lock_info` on the wall and fails once one node is dropped, and passes
    the chain locks of 001 modulo 15 and of 001011 modulo 12."""
    from computations import lock_chain, locks
    rng = np.random.default_rng(11)
    for _ in range(50):
        period = int(rng.integers(2, 13))
        column = "".join(map(str, rng.integers(0, 2, period).tolist()))
        right = "".join(map(str, rng.integers(0, 2, period).tolist()))
        left = lock_chain.left_column(column, right)
        for ph in range(period):
            row = int(left[ph]) | int(column[ph]) << 1 | int(right[ph]) << 2  # bit 0 is the left cell
            assert (step(row) >> 1) & 1 == int(column[(ph + 1) % period])
    for block, frozen in (("0000011101", 5), ("0011111101", 4), ("0000000101", 7)):
        components = lock_chain.frozen_columns(block, 13)
        assert components
        for _, columns in components:
            assert len(columns) == frozen and lock_chain.necklace(columns[-1]) == "0111111111"
            assert lock_chain.chain(columns[-1], "0" * 10, frozen) == columns[::-1] + [block]
    seeds, placed = lock_chain.classify(lock_chain.survey([8], 13), 26)
    assert seeds == {"01111111": ["00000000"]}
    chain8 = [lock_chain.necklace(column) for column in lock_chain.chain("01111111", "0" * 8, 7)]
    assert {block: set(entries) for block, entries in placed.items()} == {
        block: {("01111111", distance)} for distance, block in enumerate(chain8)}
    assert lock_chain.ether_from("01111111", "0" * 8, 8, 21)
    wall = lean_states("wallStates")
    components = lock_chain.bottom_components("01110111", 13)
    assert len(components) == 2
    for members in components:
        assert {(((int(x) >> 13) - 2) % 4, int(x) & 8191) for x in members} == wall
    assert lock_chain.wall_returns(9, 11, 3) == ["0", "1", "01"]
    assert lock_chain.wall_returns(8, 11, 12) == ["0"] * 12 == lock_chain.wall_returns(10, 11, 12)
    cells = 200
    for period, returns in ((8, [0, 0, 0]), (9, [0, 1]), (10, [0, 0, 0])):
        row = sum(1 << j for j in range(2, cells, 2))  # bit j is cell j, bit 0 the column: the wall
        seen = []
        for t in range(len(returns) * period + 1):
            row = (row & ~1) | int(t % period != 0)
            if t and t % period == 0:
                seen.append((row >> 1) & 1)
            row = step(row) & ((1 << cells) - 1)
        assert seen == returns
    seed, _, rebuilt, single, least = lock_chain.t001_as_chain()
    assert lock_chain.necklace(seed) == "000001011111111111101" and rebuilt and single and least == 9
    block, nodes = lock_chain.chain_lock("01111111", 5, 8)
    locked, _ = locks.lock_info(block, 13)  # (8 2^13,)
    assert block == "01110111" and all(locked[ph << 13 | window] for ph, window in nodes)
    assert lock_chain.is_lock(block, nodes, 13) and not lock_chain.is_lock(block, nodes[1:], 13)
    for seed, distance, word in (("000010111111111", 47, "001"), ("000111111111", 24, "001011")):
        block, nodes = lock_chain.chain_lock(seed, 5, distance)
        assert lock_chain.necklace(block[:len(word)]) == word and lock_chain.is_lock(block, nodes, distance + 5)


def test_word_traps() -> None:
    """The traps of `WordTraps.lean` and `NineTraps.lean` are the entries that `lock_chain.lean_trap` and
    `lock_chain.lean_nine` print, and their packed tables, read back from the Lean sources, pass the modules' check by
    `step`: each listed successor is the window one step of the rule later, beside the block at the label's phase, with
    the label one more, and at a white phase the first cell is the label's bit of `u`."""
    import sys
    from computations import lock_chain
    word_traps = (ROOT / "Rule30Open" / "Columns" / "WordTraps.lean").read_text(encoding="utf-8")
    nine_traps = (ROOT / "Rule30Open" / "Columns" / "NineTraps.lean").read_text(encoding="utf-8")
    digits = sys.get_int_max_str_digits()
    sys.set_int_max_str_digits(0)  # the packed tables have thousands of digits
    try:
        names = [entry[0] for entry in lock_chain.TRAPS + lock_chain.NATURAL[:1]]
        for name in names:
            assert lock_chain.lean_trap(name) in word_traps
        assert lock_chain.lean_nine() in nine_traps and lock_chain.lean_trap("trap001010011") in nine_traps
        sources = [(name, word_traps) for name in names]
        sources += [(f"nine{d}", nine_traps) for d in lock_chain.nine_distances() if d]
        sources += [("trap001010011", nine_traps)]
        for name, lean in sources:
            body = lean.split(f"def {name} : WTrap :=", 1)[1].split("}", 1)[0]
            fields = dict(re.findall(r"(\w+) := (\[[^\]]*\]|\d+)", body))
            block = [cell.strip() == "true" for cell in fields["b"].strip("[]").split(",")]
            cells, modulus, n, lb, ib, u, windows, labels, nexts = (
                int(fields[key]) for key in ("K", "m", "n", "lb", "ib", "u", "R", "L", "S"))
            period, mask = len(block), (1 << cells) - 1
            assert modulus % period == 0
            for i in range(n):
                window, label = (windows >> (cells * i)) & mask, (labels >> (lb * i)) % (1 << lb)
                here = int(block[label % period])
                assert label < modulus and (here or (window & 1) == (u >> label) & 1)
                for free in (0, 1):
                    j = (nexts >> (ib * (2 * i + free))) % (1 << ib)
                    row = here | window << 1 | free << (cells + 1)  # bit 0 the block's column, bit x cell x
                    assert j < n and (windows >> (cells * j)) & mask == (step(row) >> 1) & mask
                    assert (labels >> (lb * j)) % (1 << lb) == (label + 1) % modulus
    finally:
        sys.set_int_max_str_digits(digits)


def test_trap_entry() -> None:
    """`lock_chain.entry_steps`, which steps packed rows, against a direct run of each half with `step` on one integer,
    checked against the trap's states at every step, for the traps of 01, 001011 and 01111 (whose 107 cells span two
    words) and the halves of up to four cells, from every phase."""
    from computations import lock_chain
    for name in ("trap01", "trap001011", "trap01111"):
        word, cells, states = lock_chain.trap_states(name)
        period, mask = len(word), (1 << cells) - 1
        halves = list(range(16))
        for phase in range(period):
            got = lock_chain.entry_steps(name, halves, phase, 400)  # (16,)
            for half, first in zip(halves, got.tolist()):
                row, found = half << 1, -1  # bit 0 is the driven column, bit x cell x
                for t in range(400):
                    row = (row & ~1) | int(word[(t + phase) % period])
                    if ((t + phase) % period, (row >> 1) & mask) in states:
                        found = t
                        break
                    row = step(row)
                assert first == found


def test_natural_trap() -> None:
    """`lock_chain.natural_trap` rebuilds the kit's trap for 001: from the empty right half, the closure of the true
    window of 47 cells with the phase counted modulo 21 is, at step 1,500, exactly the states of `t001`, read from the
    kit's source, as pairs of the phase modulo 21 and the window; and two values of column 1 at one white phase are
    rejected, while at a black phase they are not."""
    from computations import lock_chain
    found = lock_chain.natural_trap("001", 0, [1500], [47], [21])
    assert found is not None and found[1:] == (47, 21, 815)
    row = 0
    for t in range(1500):
        row = ((row << 1) | int("001"[t % 3])) ^ (row | (row >> 1))
    nodes = lock_chain.closure("001", 21, 47, 1500, row & ((1 << 47) - 1), 20000)
    kit = {(label % 21, strip) for strip, label in lock_chain.t001_states()}
    shifts = [d for d in range(0, 21, 3) if {((ph + d) % 21, w) for ph, w in nodes} == kit]
    assert len(shifts) == 1
    assert not lock_chain.fixes_left("001", {(3, 0), (3, 1)}) and lock_chain.fixes_left("001", {(2, 0), (2, 1)})


def test_period_nine_wall() -> None:
    """The wall of period 9: from the random start that `NATURAL` names, a run of 001011111 is inside a closed set of
    233 windows of 43 cells, with the phase modulo 9, that fixes column 1 at the white phases, and enters it at step
    6,084 by a direct run with `step`; its chain holds 21 blocks of period 9 at the distances `nine_distances` gives and
    repeats from distance 10 with spatial period 135 in the background that the chain of 0 1^8 enters, columns of the
    two cycles agreeing as sets, each column there being the one 15 places right of it shifted by 8 steps; and the trap
    carried to distance 16 is a lock by `is_lock`."""
    from computations import lock_chain, right_half
    name, word, start, time, cells, modulus = lock_chain.NATURAL[0]
    assert start == right_half.random_starts(30, 64)[13]
    assert lock_chain.natural_trap(word, start, [time], [cells], [modulus]) == (time, cells, modulus, 233)
    _, _, states = lock_chain.trap_states(name)
    row, entered = start << 1, -1
    for t in range(time):
        row = (row & ~1) | int(word[t % 9])
        if (t % 9, (row >> 1) & ((1 << cells) - 1)) in states:
            entered = t
            break
        row = step(row)
    assert entered == 6084
    assert lock_chain.nine_distances() == list(range(19)) + [20, 21]
    values = "".join(str((lock_chain.tables(name)["first"] >> ph) & 1) if word[ph] == "0" else "0" for ph in range(9))
    assert values == "010000000"
    begin, cycle = lock_chain.chain_cycle(word, values)
    begin8, cycle8 = lock_chain.chain_cycle("011111111", "0" * 9)
    assert (begin, len(cycle), begin8, len(cycle8)) == (10, 135, 8, 135) and set(cycle) == set(cycle8)
    columns = lock_chain.chain(word, values, 160)
    assert all(columns[d + 15] == columns[d][8:] + columns[d][:8] for d in range(10, 145))
    t16 = lock_chain.carried(name, 16)
    assert t16["word"] == "000101011" and lock_chain.is_lock(t16["word"], t16["states"], t16["cells"])


def test_white_lock() -> None:
    """`lock_chain.white_lock`: the white right half driven by 001 locks column 1 with period 21 from every phase and is
    then inside a trap of 815 windows of 47 cells modulo 21, the size of the kit's `t001`; driven by 0001 from phase 0 it
    locks with period 4 inside 109 windows of 16 cells; driven by 01 it does not lock within 20,000 steps; and for 001
    from phase 1 column 1 computed by `step` repeats with period 21 at the white times over the second half."""
    from computations import lock_chain
    for phase in range(3):
        lock, last, trap = lock_chain.white_lock("001", phase, 20000)
        assert lock == 21 and last < 1000 and trap is not None and trap[1:] == (47, 21, 815)
    lock, _, trap = lock_chain.white_lock("0001", 0, 20000)
    assert lock == 4 and trap is not None and trap[1:] == (16, 4, 109)
    assert lock_chain.white_lock("01", 0, 20000) == (0, None, None)
    turned, row, column = "010", 0, []
    for t in range(20000):
        row = (row & ~1) | int(turned[t % 3])
        column.append((row >> 1) & 1)
        row = step(row)
    assert all(column[t] == column[t + 21] for t in range(10000, 20000 - 21) if turned[t % 3] == "0")


def test_period_two_fourteen() -> None:
    """A second trap for 01: the random start that `NATURAL` names, driven by 01, is at step 12,000 inside the closure
    of its window of 31 cells with the phase modulo 14, 225 states that fix column 1 at the white phases, and none of
    29 or 30 cells is a trap; the same states, up to the labels, are the 6-cell lock of 0^4 1 0 1^8, of period 14,
    carried 25 columns by `chain_lock`, a lock by `is_lock`; and its column 1 at the white phases has black values
    two white phases apart."""
    from computations import lock_chain, right_half
    name, word, start, time, cells, modulus = lock_chain.NATURAL[2]
    assert start == right_half.random_starts(300, 64)[79]
    assert lock_chain.natural_trap(word, start, [time], list(range(29, 32)), [modulus]) == (time, 31, 14, 225)
    block, nodes = lock_chain.chain_lock("00001011111111", 6, 25)
    assert lock_chain.necklace(block[:2]) == "01" and len(nodes) == 225 and lock_chain.is_lock(block, nodes, 31)
    t = lock_chain.tables(name)
    windows = {window for _, window in t["states"]}
    assert windows == {window for _, window in nodes}
    gate = [(t["first"] >> label) & 1 for label in range(0, 14, 2)]  # column 1 at the white labels
    blacks = [i for i, bit in enumerate(gate) if bit]
    assert any((b - a) % 7 == 2 for a in blacks for b in blacks)


def test_coin_entry() -> None:
    """`lock_chain.coin_entry`: the halves and phases with support in cells 1 to 8 whose windows are already inside
    `trap001011` when the coin takes over at step 200 are exactly those that `entry_steps`, with the rule throughout,
    finds inside by step 200, and with the coin no other enters within 2,000 steps."""
    from computations import lock_chain
    coin = lock_chain.coin_entry("trap001011", 8, 200, 2000)  # (1536,)
    real = np.concatenate([lock_chain.entry_steps("trap001011", list(range(256)), phase, 201)
                           for phase in range(6)])  # (1536,)
    assert set(np.flatnonzero(coin == 0).tolist()) == set(np.flatnonzero(real >= 0).tolist())
    assert (coin == 0).sum() == 10 and (coin > 0).sum() == 0


def test_white_runs() -> None:
    """`lock_chain.white_runs`: under 001011111 the white half's runs from the 9 phases are, at step 100, the six that a
    white letter joins to the next phase, and by step 2,100 the runs from phases 3 to 7 agree on columns 1 to 2,000,
    as a direct run with `step` of the runs from phases 3 and 5 shows."""
    from computations import lock_chain
    word = "001011111"
    assert lock_chain.white_runs(word, 100, 2000) == [[0, 1, 2], [3, 4], [5], [6], [7], [8]]
    assert lock_chain.white_runs(word, 2100, 2000) == [[0, 1, 2], [3, 4, 5, 6, 7], [8]]
    windows = []
    for phase in (3, 5):
        row = 0
        for t in range(2100 - phase):
            row = (row & ~1) | int(word[(phase + t) % 9])
            row = step(row)
        windows.append((row >> 1) & ((1 << 2000) - 1))
    assert windows[0] == windows[1]


def test_nine_white() -> None:
    """`NineWhite.lean`: for each run of `lock_chain.WHITE_RUNS`, the row its first part ends on, cut to the cells that
    can reach the window, is what a direct run of 16,384 steps with `step` gives; and the shortest run, the white half
    under 001010011 from phase 7, enters its wall at step 91,086 by `entry_steps`, and at no earlier step."""
    import sys
    from computations import lock_chain
    lean = (ROOT / "Rule30Open" / "Columns" / "NineWhite.lean").read_text(encoding="utf-8")
    digits = sys.get_int_max_str_digits()
    sys.set_int_max_str_digits(0)  # the rows have tens of thousands of digits
    try:
        for prefix, name, phase, total in lock_chain.WHITE_RUNS:
            word, cells, _ = lock_chain.trap_states(name)
            literal = int(re.search(rf"def {prefix}1 : Nat := (\d+)", lean).group(1))
            row = 0
            for t in range(lock_chain.PART):
                row = (row & ~1) | int(word[(t + phase) % 9])
                row = step(row)
            assert (row >> 1) % (1 << (total - lock_chain.PART + cells)) == literal
    finally:
        sys.set_int_max_str_digits(digits)
    assert lock_chain.entry_steps("trap001010011", [0], 7, 91087).tolist() == [91086]


def test_edge_periods() -> None:
    """`lock_chain.edge_periods`: next to the kit's ether, white to the right, the edge column repeats; next to the
    background of period 9 no column near the edge does; for both, the column at the edge, run directly with `step`,
    agrees on whether it repeats with a period up to 64 over the second half of 512 steps."""
    from computations import lock_chain
    t = lock_chain.tables("trap001011111")
    values = "".join(str((t["first"] >> ph) & 1) if t["word"][ph] == "0" else "0" for ph in range(9))
    cases = [(lock_chain.chain("01111111", "0" * 8, 800), 8, True), (lock_chain.chain(t["word"], values, 900), 10, False)]
    for columns, distance, repeats in cases:
        periods = lock_chain.edge_periods(columns, distance, 0, 512)
        assert any(p is not None for p in periods) == repeats
        reach = 512 + 64
        row = sum(int(columns[distance + reach - i][0]) << i for i in range(reach + 1))
        edge = []
        for _ in range(512):
            edge.append((row >> reach) & 1)
            row = step(row)
        tail = edge[256:]
        found = next((p for p in range(1, 65) if tail[p:] == tail[:-p]), None)
        assert found == periods[6]


def test_period_four_certificate_traps() -> None:
    """`lock_certificate.certificate_tables`: the certificates of 0001 at width 16 and of 0011 and 0111 at width 14 have
    2,611, 1,915 and 4,898 windows, each is a lock by `lock_chain.is_lock`, a direct check with the rule, and
    `lean_certificates` is the text of `PeriodFourCertificate.lean`."""
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
    try:
        assert lock_certificate.lean_certificates() in lean
    finally:
        sys.set_int_max_str_digits(digits)


def test_second_nine_wall() -> None:
    """The second wall of period 9: from the random start that `NATURAL` names, a run of 001010011 is inside a closed
    set of 5,710 windows of 41 cells, with the phase modulo 27, that fixes column 1 at the white phases, by `is_lock`;
    no width from 16 to 40 gives a trap at that step; and the run enters the set at step 7,622 by a direct run with
    `step`."""
    from computations import lock_chain, right_half
    name, word, start, time, cells, modulus = lock_chain.NATURAL[1]
    assert start == right_half.random_starts(30, 64)[2]
    assert lock_chain.natural_trap(word, start, [time], list(range(16, cells + 1)), [modulus]) == (time, cells, 27, 5710)
    t = lock_chain.tables(name)
    assert t["word"] == word and lock_chain.is_lock(word * 3, t["states"], cells)
    _, _, states = lock_chain.trap_states(name)
    row, entered = start << 1, -1
    for t in range(time):
        row = (row & ~1) | int(word[t % 9])
        if (t % 9, (row >> 1) & ((1 << cells) - 1)) in states:
            entered = t
            break
        row = step(row)
    assert entered == 7622
