"""depth_register against brute-force enumeration of word tuples, the weight identity on small periods, and the
transplanted windows at larger periods."""

from __future__ import annotations

import itertools

from computations.depth_register import is_step, is_window, next_words, transplant, weight_identity, window_min


def test_next_words_against_enumeration() -> None:
    for P in (3, 4, 5):
        for a in range(1 << P):
            for b in range(1 << P):
                brute = sorted(c for c in range(1 << P) if is_step(a, b, c, P))
                assert sorted(next_words(a, b, P)) == brute
                assert (len(brute) == 1) if b else (len(brute) in (0, 2))


def test_identity() -> None:
    for P in (2, 3, 4, 5, 6):
        assert weight_identity(P) >= 1 << P


def test_window_min_against_brute_force() -> None:
    # every K-tuple of words of period P, K = 3 and 4, P = 4
    P = 4
    for K in (3, 4):
        best = min(sum(bin(w).count("1") for w in ws)
                   for ws in itertools.product(range(1 << P), repeat=K) if is_window(list(ws), P))
        assert window_min(P, K)[0] == best


def test_transplanted_windows() -> None:
    families = {3: [1, 1, 0], 4: [3, 2, 2, 0], 6: [5, 4, 6, 4, 4, 0], 8: [11, 14, 10, 8, 12, 8, 8, 0]}
    weights = {3: 2, 4: 4, 6: 7, 8: 13}
    for K, ws in families.items():
        assert sum(bin(w).count("1") for w in ws) == weights[K]
        for P in range(5, 41):
            assert is_window(transplant(ws, P), P)
    assert window_min(6, 6)[0] == 7 and window_min(8, 3)[0] == 2
