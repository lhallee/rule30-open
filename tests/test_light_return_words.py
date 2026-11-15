"""Checks of computations/light_return_words.py: walk counts against applying Phi directly, the reduction to the
branch state, the parity of the two children, the embedding of period L/2 in period L, and the tree depths."""

from __future__ import annotations

from computations import light_return_words as w


def test_walk_counts_match_phi() -> None:
    for L in (2, 4, 8):
        assert w.walk_counts(L, 11) == w.brute_counts(L, 11)


def test_every_walk_is_rain_until_the_branch_state() -> None:
    for L in (4, 8, 16, 32):
        full = (1 << L) - 1
        P = w.alternating(L)
        alternating = {P, P ^ full}
        level = w.children((0, full), L)
        assert {s[1] for s in level} == alternating
        rain = w.rain_states(L)
        branch = {(P, P), (P ^ full, P ^ full)}
        for _ in range(6):
            level = [c for s in level for c in w.children(s, L)]
            assert {s for s in level if s not in rain} <= branch | {c for b in branch for c in _descendants(b, L, 6)}
        assert len(rain) == 4
        # one step from a rain state: one rain child and one branch child
        for s in rain:
            kids = set(w.children(s, L))
            assert len(kids & rain) == 1 and len(kids & branch) == 1


def _descendants(state: w.State, L: int, depth: int) -> set[w.State]:
    out: set[w.State] = set()
    level = [state]
    for _ in range(depth):
        level = [c for s in level for c in w.children(s, L)]
        out.update(level)
    return out


def test_children_parity_identity_exhaustive() -> None:
    # |v or w| + |v or not w| = |v| + L for every pair of words of length L <= 8 (independent of the tree)
    for L in range(1, 9):
        full = (1 << L) - 1
        for v in range(1 << L):
            for x in range(1 << L):
                assert bin(v | x).count("1") + bin(v | (x ^ full)).count("1") == bin(v).count("1") + L


def test_children_fertility_parity() -> None:
    # the whole trees; the case |v| odd first occurs at L = 32 (208 of 527 inner nodes)
    assert w.fertility_counts(8) == (7, 0, 0)
    assert w.fertility_counts(16) == (15, 0, 0)
    assert w.fertility_counts(32) == (527, 208, 0)
    for L in (8, 16, 32):  # direct check, written out
        level = [(w.alternating(L), w.alternating(L))]
        while level:
            for s in level:
                kids = w.children(s, L)
                if kids:
                    fertile = [bool(w.children(c, L)) for c in kids]
                    if bin(s[1]).count("1") % 2:
                        assert sum(fertile) == 1
                    else:
                        assert fertile[0] == fertile[1]
            level = [c for s in level for c in w.children(s, L)]


def test_half_period_embedding() -> None:
    for N in (2, 4, 8, 16):
        L = 2 * N
        mask = (1 << N) - 1
        level = [(w.alternating(N), w.alternating(N))]
        while level:  # the whole tree T_N
            for u, v in level:
                big = ((u << N) | u, (v << N) | v)
                kids = w.children(big, L)
                small = w.children((u, v), N)
                assert len(kids) == 2
                if small:
                    assert sorted(kids) == sorted(((a << N) | a, (b << N) | b) for a, b in small)
                else:
                    for _, x in kids:
                        assert (x >> N) == (x & mask) ^ mask
            level = [c for s in level for c in w.children(s, N)]


def test_tree_depths() -> None:
    assert [w.branch_tree(1 << k) for k in range(1, 6)] == [(1, 0), (3, 1), (15, 3), (31, 4), (1055, 14)]
