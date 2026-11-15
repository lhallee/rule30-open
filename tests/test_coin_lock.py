"""Tests of computations.coin_lock: entry paths, universal words, stay-out chances and rates against direct runs with
integer rows, full sweeps, simulation and spectral radii built cell by cell."""

from __future__ import annotations

import numpy as np
import pytest

from computations import coin_lock
from computations.rule30 import distinct, step


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


def test_entry_paths_against_full_sweeps() -> None:
    """`coin_lock.entry_paths`, which after a phase's first sweep relaxes only the windows whose successors changed,
    gives the distances and first values of relaxing every window in every sweep, on random sets of windows (some that
    no window reaches, some empty) for blocks of periods 2 to 5 at 3 to 9 cells; and `rule30.distinct` is `np.unique`.
    """
    from computations.lock_certificate import successor_table

    def full_sweeps(word: str, member: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
        # member: (period, 2^W), the windows of the certificate at each phase
        period, size = member.shape
        successors = successor_table(word, size.bit_length() - 1)  # (period, 2, 2^W)
        dist = np.where(member, 0, coin_lock.UNREACHED).astype(np.int64)  # (period, 2^W)
        first = np.zeros((period, size), dtype=np.int8)  # (period, 2^W)
        changed = True
        while changed:
            changed = False
            for ph in range(period):
                after = dist[(ph + 1) % period][successors[ph]] + 1  # (2, 2^W)
                best = np.minimum(after[0], after[1])  # (2^W,)
                better = (best < dist[ph]) & ~member[ph]  # (2^W,)
                if better.any():
                    dist[ph][better] = best[better]
                    first[ph][better] = (after[1] < after[0])[better]
                    changed = True
        return dist, first  # (period, 2^W), (period, 2^W)

    rng = np.random.default_rng(30)
    for word in ("01", "001", "0111", "00101"):
        for width in (3, 6, 9):
            for density in (0.0, 0.002, 0.02, 0.3):
                member = rng.random((len(word), 1 << width)) < density  # (p, 2^W)
                got, want = coin_lock.entry_paths(word, member), full_sweeps(word, member)
                assert np.array_equal(got[0], want[0]) and np.array_equal(got[1], want[1]), (word, width, density)
    for dtype in (np.uint8, np.int64, np.uint64):
        for size in (0, 1, 2, 500):
            values = rng.integers(0, 40, size).astype(dtype)  # (size,)
            assert np.array_equal(distinct(values), np.unique(values)) and distinct(values).dtype == dtype


def test_universal_word(coin_certificate: np.ndarray) -> None:
    """The universal word of 0111 at width 14 has 209 values and brings every one of the 2^14 windows into the
    certificate, stepped as bool arrays; at width 16 the word of 0111 has 297 values (those of 0001 and 0011, 425 and
    697, are the reproduce command of the coin finding)."""
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
    for word, length in (("0111", 297),):
        member = coin_lock.certificate(word, 16)  # (4, 2^16)
        values = coin_lock.universal_word(word, member)
        assert len(values) == length and member[length % 4][coin_lock.run_word(word, member, values)].all()


def test_coin_chain(coin_certificate: np.ndarray) -> None:
    """With a fair coin beyond width 14 under 0111, the expected entry time solves its equation with integer-row
    successors and matches 400 simulated runs from the slowest window within four standard errors (the decay of the
    chance of staying out is checked in `test_period_rate`). The finding's numbers at width 16 (expected times 139.9 and
    49.8, decay factor 0.98251) are the reproduce command of the coin finding."""
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


def test_coin_sample() -> None:
    """In Rule 30 itself, of the 31 starts of the locking finding, exactly those the certificate finding names stay out
    of the width-16 certificate for 2,000 steps (start 4 under 0001, 24 under 0011, 8 and 18 under 0111), and each of
    them enters the kit's ether-and-wall family."""
    for word, missing in (("0001", [4]), ("0011", [24]), ("0111", [8, 18])):
        times, family = coin_lock.sample(word, coin_lock.certificate(word, 16), 31, 2000)  # (31,), (m,)
        assert np.flatnonzero(times < 0).tolist() == missing, word
        assert (family >= 0).all(), word


def test_period_rate() -> None:
    """`coin_lock.period_rate` where the power iteration of `decay_rate` oscillates: for the kit's block 0000000001 at
    width 13, two eigenvalues of one period of the coin step share the largest modulus (ARPACK's `eigs`), and
    `locks.growth`, which iterates to the tolerance 1e-10, gives twice its tenth root, 1.903817, and the locked share
    28.1% that the steerable-locks finding quotes; the locked nodes of 0111 at width 13 are its certificate at width 13,
    whose rate `test_lock_avoid_growth` checks; and for a trap that some window cannot reach the factor is 1, not the 0
    that a vector gone to 0 on some windows would give: the natural trap of 0010101111111 passes the test of reach in
    the game of 6 cells, with factor below 1, and fails it in that of 8, with factor 1. In the game of 6 cells the power
    iteration of `coin_lock.decay_rate` settles to the same factor, and the chance of staying out with a fair coin
    beyond (`coin_lock.stay_out`) falls by it per step."""
    from computations import coin_lock, locks
    from scipy.sparse.linalg import LinearOperator, eigs
    block = "0000000001"
    locked, _ = locks.lock_info(block, 13)  # (p n,)
    member = locked.reshape(len(block), 1 << 13)  # (10, 2^13)
    successors = coin_lock.successor_table(block, 13)  # (10, 2, 2^13)

    def one_period(v: np.ndarray) -> np.ndarray:
        # v: (2^13,) or (2^13, 1), as `eigs` passes it
        v = np.asarray(v, dtype=float).reshape(-1)  # (2^13,)
        for ph in range(len(block) - 1, -1, -1):
            v = 0.5 * (v[successors[ph, 0]] + v[successors[ph, 1]]) * ~member[ph]  # (2^13,)
        return v  # (2^13,)

    share, twice = locks.growth(block, 13)  # 2 `period_rate` of the locked nodes, to the tolerance 1e-10
    assert round(twice, 6) == 1.903817 and round(100 * share, 1) == 28.1
    top = np.sort(np.abs(eigs(LinearOperator((1 << 13, 1 << 13), matvec=one_period, dtype=float), k=4, which="LM",
                              return_eigenvectors=False)))[::-1]  # (4,)
    assert abs(top[0] - top[1]) < 1e-9 and top[2] < 0.9 * top[0]
    assert abs(top[0] ** (1 / len(block)) - twice / 2) < 1e-6
    # the locked nodes of 0111 at 13 cells are its certificate there, the trap of `test_lock_avoid_growth`
    certificate13 = coin_lock.certificate("0111", 13)  # (4, 2^13)
    assert (locks.lock_info("0111", 13)[0].reshape(4, -1) == certificate13).all() and int(certificate13.sum()) == 1915
    # the factor is below 1 exactly when every window can reach the trap: the natural trap of 0010101111111 passes the
    # test of reach in the game of 6 cells and fails in that of 8, where windows that never enter leave the iteration
    # 0 elsewhere and the bound is the step's own, 1
    from computations import lock_chain
    t = lock_chain.extra_tables("0010101111111")
    rates = [coin_lock.period_rate("0010101111111", lock_chain.trap_nodes((t,), w).reshape(13, 1 << w),
                                   tolerance=1e-10, limit=3000) for w in (6, 8)]
    assert rates[0] < 1 == rates[1] and lock_chain.trap_reach(t, width=6) == 1 > lock_chain.trap_reach(t, width=8)
    member6 = lock_chain.trap_nodes((t,), 6).reshape(13, 1 << 6)  # (13, 2^6)
    decay = coin_lock.decay_rate("0010101111111", member6)
    assert abs(decay - rates[0]) < 1e-9
    before, after = (coin_lock.stay_out("0010101111111", member6, steps) for steps in (400, 413))  # (13, 2^6) each
    assert abs(after.max() / before.max() - decay ** 13) < 1e-9


def test_ten_coin() -> None:
    """The period-10 wall with a fair coin in column 17: `coin_lock.stay_out` over 12 steps, for sampled windows at
    phase 0, is the share of the 4,096 values of column 17 over those steps that keep the window outside, counted
    directly with `successor_table`; and the word of `universal_word` brings every window at phase 0 inside by
    `run_word`."""
    from computations import coin_lock, lock_chain
    from computations.lock_certificate import successor_table
    word, member = "0000010001", lock_chain.ten_member()  # (10, 2^16)
    successors = successor_table(word, 16)  # (10, 2, 2^16)
    out = coin_lock.stay_out(word, member, 12)  # (10, 2^16)
    outside = np.flatnonzero(~member[0])  # (m,)
    values = np.arange(1 << 12)  # (4096,), every sequence of column 17 over 12 steps, bit t at step t
    for window in outside[::7919][:3].tolist():
        w, inside = np.full(values.size, window), np.zeros(values.size, dtype=bool)  # (4096,) each
        for t in range(12):
            w = successors[t % 10, (values >> t) & 1, w]
            inside |= member[(t + 1) % 10, w]
        assert abs(out[0, window] - int((~inside).sum()) / 4096) < 1e-12, window
    values = coin_lock.universal_word(word, member)
    end = coin_lock.run_word(word, member, values, 0)  # (2^16,)
    assert member[len(values) % 10][end].all()


def test_natural_coin() -> None:
    """Natural traps with a fair coin in column 17, for a trap of period 11 with labels modulo 11 and one with labels
    modulo 22: `trap_member` holds each state at its phase; `coin_lock.stay_out` over 11 steps, for sampled windows at
    phase 0, is the share of the 2,048 values of column 17 over those steps that keep the window outside, counted
    directly with `successor_table`."""
    from computations import coin_lock, lock_chain
    from computations.lock_certificate import successor_table
    for word in ("00000010001", "00000110101"):
        t = lock_chain.extra_tables(word)
        member = lock_chain.trap_member(t)  # (11, 2^16)
        assert member.sum() == len({(label % 11, window) for label, window in t["states"]})
        successors = successor_table(word, 16)  # (11, 2, 2^16)
        out = coin_lock.stay_out(word, member, 11)  # (11, 2^16)
        values = np.arange(1 << 11)  # (2048,), every sequence of column 17 over 11 steps, bit t at step t
        for window in np.flatnonzero(~member[0])[::9973][:2].tolist():
            w, inside = np.full(values.size, window), np.zeros(values.size, dtype=bool)  # (2048,) each
            for step_ in range(11):
                w = successors[step_ % 11, (values >> step_) & 1, w]
                inside |= member[(step_ + 1) % 11, w]
            assert abs(out[0, window] - int((~inside).sum()) / 2048) < 1e-12, (word, window)


def test_biased_rate() -> None:
    """`coin_lock.biased_rate` with an even coin is `period_rate`, and with a random bias per window it is the spectral
    radius of the biased coin's step outside `t001` cut to 8 cells, built cell by cell with the rule."""
    from computations import coin_lock, lock_chain

    width, states = 8, lock_chain.t001_states()
    member = np.zeros((3, 1 << width), dtype=bool)  # (3, 2^8)
    for strip, label in states:
        member[label % 3, strip & ((1 << width) - 1)] = True
    even = np.full(member.shape, 0.5)  # (3, 2^8)
    assert coin_lock.biased_rate("001", member, even) == pytest.approx(coin_lock.period_rate("001", member), abs=1e-9)
    prob = np.random.default_rng(3).uniform(0.1, 0.9, size=member.shape)  # (3, 2^8)
    outside = [(ph, w) for ph in range(3) for w in range(1 << width) if not member[ph, w]]
    index = {node: i for i, node in enumerate(outside)}
    step = np.zeros((len(outside), len(outside)))  # (m, m)
    for (ph, w), i in index.items():
        cells = [int("001"[ph])] + [(w >> k) & 1 for k in range(width)]
        for coin, weight in ((0, 1 - prob[ph, w]), (1, prob[ph, w])):
            row = cells + [coin]
            new = sum((row[k - 1] ^ (row[k] | row[k + 1])) << (k - 1) for k in range(1, width + 1))
            j = index.get(((ph + 1) % 3, new))
            if j is not None:
                step[i, j] += weight
    radius = float(np.abs(np.linalg.eigvals(step)).max())
    assert coin_lock.biased_rate("001", member, prob) == pytest.approx(radius, abs=1e-6)
