"""The letter language of the left cut: counts, constraints, the rank ceiling, and the C program against Python."""

from __future__ import annotations

import math
import random
import shutil

import pytest

from computations import letter_words as lw


def list_step(row: list[int]) -> list[int]:
    """One step of the completion on a list, the frame moving right: new[i] = row[i] ^ (row[i+1] | row[i+2])."""
    n = len(row)
    return [row[i] ^ ((row[i + 1] if i + 1 < n else 0) | (row[i + 2] if i + 2 < n else 0)) for i in range(n)]


def words_by_lists(T: int) -> set[tuple[int, ...]]:
    """W_T by stepping lists of 2T cells, letters as e0 + 2 e1: an implementation without numbers."""
    out = set()
    for r in range(1 << (2 * T)):
        row, word = [(r >> k) & 1 for k in range(2 * T)], []
        for _ in range(T):
            word.append(row[0] + 2 * row[1])
            row = list_step(row)
        out.add(tuple(word))
    return out


def test_word_counts_against_list_runs() -> None:
    """|W_T| = 4, 10, 22, 50, 104, 208 for T <= 6, and the coded words are the words of the list runs."""
    for T, count in zip(range(1, 7), (4, 10, 22, 50, 104, 208)):
        coded = lw.word_set(T)
        assert len(coded) == count
        assert {tuple(lw.letters_of(w, T)) for w in coded} == words_by_lists(T)


def test_two_letter_constraints_and_bound() -> None:
    """Every word obeys the two-letter constraints, which are all the constraints of length 2; the number of allowed
    words is 2 P(T + 1) (counted by brute force for T <= 6), and it bounds |W_T|, with equality only for T <= 2."""
    assert lw.word_set(2) == {e | (f << 2) for e in range(4) for f in lw.ALLOWED[e]}
    for T in range(1, 8):
        words = lw.word_set(T)
        assert all(lw.allowed_word(w, T) for w in words)
        assert len(words) <= lw.word_bound(T)
        assert (len(words) == lw.word_bound(T)) == (T <= 2)
    pell = [0, 1]
    for _ in range(12):
        pell.append(2 * pell[-1] + pell[-2])
    for T in range(1, 7):
        assert lw.word_bound(T) == 2 * pell[T + 1] == sum(lw.allowed_word(w, T) for w in range(1 << (2 * T)))


def test_forbidden_words_and_radius() -> None:
    """The minimal forbidden words of length 2 to 6 number 6, 2, 0, 8, 10; the radius of the two-letter shift is
    1 + sqrt 2, and the shift of 7-blocks already grows slower than 2^T."""
    assert lw.minimal_forbidden(6) == {2: 6, 3: 2, 4: 0, 5: 8, 6: 10}
    assert abs(lw.sft_radius(2) - (1 + math.sqrt(2))) < 1e-9
    assert lw.sft_radius(7) < 1.99


def test_rank_and_nl_against_full_runs() -> None:
    """The rank and N_L from the words agree with every completion run on the cone, for small t and a."""
    for t in range(2, 6):
        for a in range(1, t + 1):
            assert lw.rank_and_nl(t, a) == lw.rank_and_nl_full(t, a), (t, a)
    for a in (3, 4):
        assert lw.rank_and_nl(6, a) == lw.rank_and_nl_full(6, a)


def test_known_values() -> None:
    """rank(t, a) = rho(a) and N_L = 2^a where the left-cut rank finding and LeftCut have them."""
    assert lw.rank_and_nl(8, 5) == (lw.rho(5), 32)
    assert lw.rank_and_nl(10, 7) == (lw.rho(7), 128)


def test_lean_threshold() -> None:
    """The arithmetic of `cut_rank_lt_rhoCut`: the word bound at T = t - (ceil((t-3)/2) - 1) is below rho(t - 3) for
    t = 22 and every t >= 24 (checked to 200), and not for t = 23 or t <= 21."""
    def below(t: int) -> bool:
        T, _ = lw.horizon(t, t - 3)
        return lw.word_bound(T) < lw.rho(t - 3)
    assert [t for t in range(4, 201) if below(t)] == [22] + list(range(24, 201))


def test_ideal_small() -> None:
    """With every letter allowed, words of 3 letters separate 4 cells and of 4 letters 6 cells (the C program gives
    5, 7 and 8 letters for 8, 10 and 12 cells)."""
    assert lw.ideal_classes(4, 10)[-1] == 16 and len(lw.ideal_classes(4, 10)) == 3
    assert lw.ideal_classes(6, 10)[-1] == 64 and len(lw.ideal_classes(6, 10)) == 4


def test_edge_shifts() -> None:
    """The eventual left edge of a row white left of a black cell is the single cell's, shifted in time (depth 16)."""
    rng = random.Random(7)
    for _ in range(40):
        assert lw.edge_shift(rng.getrandbits(rng.randint(1, 40)), 16, 70) is not None


@pytest.mark.skipif(shutil.which("cc") is None and shutil.which("gcc") is None, reason="no C compiler")
def test_c_matches_python() -> None:
    """The C program agrees with the Python functions on counts, forbidden words, ranks, N_L and ideal classes."""
    assert int(lw.run_c("count", 7)["count"]) == len(lw.word_set(7))
    assert lw.run_c("forbid", 6) == [f"forbidden {k} {c}" for k, c in lw.minimal_forbidden(6).items()]
    for t, a in ((8, 5), (9, 6), (7, 6)):
        d = lw.run_c("wordmat", t, a)
        assert (int(d["rank"]), int(d["NL"])) == lw.rank_and_nl(t, a)
    assert int(lw.run_c("refine", 9, 6)["NL"]) == lw.rank_and_nl(9, 6)[1]
    assert lw.run_c("ideal", 6, 10)[-1] == f"classes 4 {lw.ideal_classes(6, 10)[-1]}"
