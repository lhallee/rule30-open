"""settled_words against plain string computations on the space-time diagram, a scalar run of the pair map, an
enumeration of the longest-run law, and a direct check of the run lemmas on the rows."""

from __future__ import annotations

import itertools

import numpy as np

from computations.diagonal_cones import diagonal_table
from computations.settled_slope import Diagonals
from computations.settled_words import (SettledTable, check_pair_map, class_chi_square, least_rotation, max_run_quantiles, pair_next,
                                        pair_prev, regime_rows, run_law, run_transfer, settled_table, window_fit,
                                        words_from_tail)

STEPS, DEPTH, WINDOW = 480, 121, 256


def cyclic_run_str(s: str, c: str) -> int:
    """The longest cyclic run of the character c in s."""
    if set(s) == {c}:
        return len(s)
    return max(len(r) for r in (s + s).split("1" if c == "0" else "0"))


def test_table_against_strings() -> None:
    D = diagonal_table(STEPS, DEPTH)  # (DEPTH, STEPS)
    tail = D[:, STEPS - WINDOW:].T  # (WINDOW, DEPTH)
    t = settled_table(tail)
    for j in range(DEPTH):
        s = "".join(str(int(x)) for x in tail[:, j])
        P = next(p for p in (1, 2, 4, 8, 16, 32) if s[p:] == s[:-p])
        w = s[:P]
        assert int(t.period[j]) == P
        assert int(t.word[j]) == int(w[::-1], 2)
        rots = [w[k:] + w[:k] for k in range(P)]
        assert int(t.canon[j]) == min(int(r[::-1], 2) for r in rots)
        assert int(t.weight[j]) == w.count("1")
        assert int(t.white[j]) == cyclic_run_str(w, "0") and int(t.black[j]) == cyclic_run_str(w, "1")
        half = "".join("1" if c == "0" else "0" for c in w[:P // 2])
        assert bool(t.anti[j]) == (P % 2 == 0 and w[P // 2:] == half)


def scalar_next(a: list[int], b: list[int], P: int) -> list[int]:
    """The P-periodic solution of c(t+1) = a(t) xor (b(t) or c(t)), by running 4P steps from c = 0 and reading the last
    period (b has a black cell, so the run resets within a period)."""
    c, out = 0, []
    for t in range(4 * P):
        if t >= 3 * P:
            out.append(c)
        c = a[t % P] ^ (b[t % P] | c)
    return out


def test_pair_map_against_scalar_run() -> None:
    rng = np.random.default_rng(1)
    for P in (4, 8, 16, 32):
        A = rng.integers(0, 2, size=(40, P))  # (40, P)
        B = rng.integers(0, 2, size=(40, P))  # (40, P)
        B[:, 0] |= rng.integers(0, 2, size=40) | (B.sum(axis=1) == 0)  # not white
        pack = (A * (1 << np.arange(P))).sum(axis=1).astype(np.uint64)  # (40,)
        packb = (B * (1 << np.arange(P))).sum(axis=1).astype(np.uint64)  # (40,)
        c, ok = pair_next(pack, packb, P)
        assert ok.all()
        for r in range(40):
            want = scalar_next(A[r].tolist(), B[r].tolist(), P)
            assert [(int(c[r]) >> k) & 1 for k in range(P)] == want
        assert np.array_equal(pair_prev(packb, c, P), pack)


def test_pair_map_and_regimes(deep_diagonals: Diagonals) -> None:
    pc = check_pair_map(deep_diagonals.tail, 16)
    assert pc.failures == 0 and pc.white_steps == 4 and pc.forward == 10001 - 2 - 4 and pc.backward == 10001 - 2
    t = settled_table(deep_diagonals.tail)
    rows = regime_rows(deep_diagonals.tail, t)
    assert [(r.first, r.last, r.period) for r in rows] == [(0, 2, 1), (3, 7, 2), (8, 28, 4), (29, 399, 8),
                                                           (400, 10000, 16)]
    assert all(r.repeated_pairs == 0 for r in rows)
    assert [r.max_white for r in rows] == [0, 1, 3, 7, 15]
    # the words up to rotation of the period-16 regime, by a set of strings
    w = words_from_tail(deep_diagonals.tail[:, 400:], 16)  # (9601,)
    strings = {min(format(int(x), "016b")[k:] + format(int(x), "016b")[:k] for k in range(16)) for x in w}
    assert rows[-1].words == len(strings) == len(np.unique(least_rotation(w, 16)))
    # anti-periodic at half the regime's period, by strings
    flip = str.maketrans("01", "10")
    anti = sum(1 for x in w if format(int(x), "016b")[8:] == format(int(x), "016b")[:8].translate(flip))
    assert rows[-1].anti == anti


def test_run_law_against_enumeration() -> None:
    for P in (1, 5, 8, 12):
        count = [0] * (P + 1)
        for bits in itertools.product("01", repeat=P):
            count[cyclic_run_str("".join(bits), "0")] += 1
        assert run_law(P) == count


def test_quantiles_against_enumeration() -> None:
    t = SettledTable(np.array([1, 4, 4]), np.zeros(3, dtype=np.uint64), np.zeros(3, dtype=np.uint64),
                     np.array([1, 1, 1]), np.zeros(3, dtype=np.int64), np.zeros(3, dtype=np.int64),
                     np.zeros(3, dtype=bool))
    words = ["".join(b) for b in itertools.product("01", repeat=4) if "1" in b]  # 15 words with a black cell
    m = sorted(max(cyclic_run_str(x, "0"), cyclic_run_str(y, "0")) for x in words for y in words)  # (225,)
    q = max_run_quantiles(t, [2], (0.1, 0.5, 0.9))
    assert q[0].tolist() == [m[int(np.ceil(f * len(m))) - 1] for f in (0.1, 0.5, 0.9)]


def test_run_lemmas_on_rows(deep_diagonals: Diagonals) -> None:
    rt = run_transfer(deep_diagonals.tail, 16)
    assert rt.white_ok == rt.black_ok == rt.depths == 10001 - 2
    tail = deep_diagonals.tail.astype(bool)  # (256, 10001)
    a, b, c = tail[:-1, :-2], tail[:-1, 1:-1], tail[:-1, 2:]  # (255, 9999) each, at times t
    c1 = tail[1:, 2:]  # (255, 9999), at times t + 1
    assert ((~c & ~c1) == (~c & (a == b))).all()  # two white cells exactly when the two before agree
    assert ((c & c1) == (c & ~a)).all()  # two black cells exactly when two before is white


def test_window_fit_against_direct() -> None:
    rng = np.random.default_rng(2)
    V = rng.integers(0, 50, size=30) + 2 * np.arange(30)  # (30,)
    W = np.maximum.accumulate(rng.integers(0, 6, size=30))  # (30,)
    slopes, C = window_fit(V, V, W, [(0, 29)], [1.5, 2.0], [0, 3])
    assert abs(slopes[0] - np.polyfit(np.arange(30), V, 1)[0]) < 1e-9
    for gi, g in enumerate([1.5, 2.0]):
        for ki, k in enumerate([0, 3]):
            c = int(C[gi, ki])
            assert all(V[j] <= g * j + c + k * W[j] for j in range(30))
            assert any(V[j] > g * j + c - 1 + k * W[j] for j in range(30))


def test_chi_square_against_strings(deep_diagonals: Diagonals) -> None:
    w = words_from_tail(deep_diagonals.tail[:, 29:400], 8)  # (371,)
    strings = [format(int(x), "08b") for x in w]
    count: dict[str, int] = {}
    size: dict[str, int] = {}
    for bits in itertools.product("01", repeat=8):
        s = "".join(bits)
        c = min(s[k:] + s[:k] for k in range(8))
        size[c] = size.get(c, 0) + 1
    for s in strings:
        c = min(s[k:] + s[:k] for k in range(8))
        count[c] = count.get(c, 0) + 1
    chi = sum((count.get(c, 0) - len(w) * n / 256) ** 2 / (len(w) * n / 256) for c, n in size.items())
    got, dof = class_chi_square(w, 8)
    assert dof == len(size) - 1 == 35 and abs(got - chi) < 1e-9
