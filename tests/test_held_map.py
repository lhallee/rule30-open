"""Tests of computations.held_map: the vectorized searches and the tree of readings against Python integers stepped
one at a time."""

from __future__ import annotations

from computations import held_map
from computations.held_shift import held


def test_held_map() -> None:
    """The vectorized search against Python integers for every support to 12 in both phases, and at support 20 the
    latest first failures the period-two finding quotes, 37 at odd checks and 30 at even."""
    for support in range(1, 13):
        for phase in (0, 1):
            expected = []
            for U in range(1 << (support - 1), 1 << support):
                V, t = U, 0
                while not ((t + phase) % 2 == 1 and V & 1 == 0) and t < 63:
                    V, t = held(V), t + 1
                expected.append(t)
            assert held_map.first_failures(support, phase).tolist() == expected, (support, phase)
    assert [int(held_map.first_failures(20, phase).max()) for phase in (0, 1)] == [37, 30]


def test_held_map_survivors() -> None:
    """Survivor counts against stepping Python integers, and the exact count 2^((M - 1)/2) at step M - 1 for odd M."""
    for support in range(1, 12):
        brute = [0] * 30  # brute[T]: integers with `support` bits that keep the odd checks through step T
        for U in range(1 << (support - 1), 1 << support):
            V, failed = U, 30
            for t in range(1, 30):
                V = held(V)
                if t % 2 == 1 and V % 2 == 0:
                    failed = t
                    break
            for T in range(min(failed, 30)):
                brute[T] += 1
        assert held_map.survivor_counts(support, 30).tolist() == brute, support
        if support % 2 == 1:
            assert brute[support - 1] == 2 ** ((support - 1) // 2) == held_map.counting_prediction(support, support - 1)


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
                        V, t = held(V), t + 1
                    expected.append(t)
                assert held_map.first_failures_0001(support, phase, check).tolist() == expected, (support, phase)
    latest = [max(int(held_map.first_failures_0001(support, phase, False).max()) for phase in range(4))
              for support in range(1, 17)]
    assert all(support <= late <= support + 9 for support, late in zip(range(1, 17), latest, strict=True))
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


def test_held_map_tree() -> None:
    """The tree of readings against stepping every half: for 0001 with and without the check against the search over
    every integer to support 11, and for C3 of 0011 and 0111 against integers to support 10, in every phase; and the
    Fibonacci count of the branches of 0001 with the check, to support 68 (the tree to support 80 has about four times
    as many branches)."""
    for phase in range(4):
        for check in (False, True):
            latest, _ = held_map.tree_failures("0001", 11, phase, check)
            assert latest == [int(held_map.first_failures_0001(support, phase, check).max())
                              for support in range(1, 12)], (phase, check)
        for word in ("0011", "0111"):
            latest, _ = held_map.tree_failures(word, 10, phase, False)
            assert latest == [c3_brute(word, support, phase) for support in range(1, 11)], (word, phase)
    _, branches = held_map.tree_failures("0001", 68, 0, True)
    fibonacci = [1, 2]
    while len(fibonacci) < 18:
        fibonacci.append(fibonacci[-1] + fibonacci[-2])
    assert [branches[4 * j - 1] for j in range(1, 18)] == fibonacci[1:]
