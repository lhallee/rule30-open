"""kit_main's recognizers of the kit's new families against words generated from each family's definition, and the
quarter theorems against a search over every start, run and gap that their Lean hypotheses allow."""

from __future__ import annotations

import itertools
from collections.abc import Callable

from computations import game
from computations.kit_main import (NEW_PADDED, PARAM_BLACK, grammar, lean_literals, new_blocks, padded, param_black,
                                   quarter, reset_mixture, run_pairs, white17)

MAX = 16  # periods checked against generated words


def primitive(word: str) -> bool:
    """No rotation by 1 to len - 1 returns the word."""
    return all(word[i:] + word[:i] != word for i in range(1, len(word)))


def generated(pair_ok: Callable[[int, int], bool], max_period: int,
              whole_ok: Callable[[list[tuple[int, int]]], bool] = lambda pairs: True) -> set[str]:
    """Least rotations of the primitive words 1^r1 0^q1 ... 1^rk 0^qk of length at most `max_period` whose every pair
    passes `pair_ok` and whose list of pairs passes `whole_ok`, from all lists of pairs."""
    found = set()

    def extend(prefix: list[tuple[int, int]], length: int) -> None:
        for r in range(1, max_period - length):
            for q in range(1, max_period - length - r + 1):
                if not pair_ok(r, q):
                    continue
                pairs = prefix + [(r, q)]
                word = "".join("1" * a + "0" * b for a, b in pairs)
                if whole_ok(pairs) and primitive(word):
                    found.add(game.least_rotation(word))
                extend(pairs, length + r + q)
    extend([], 0)
    return found


def recognized(test: Callable[[str], bool], max_period: int) -> set[str]:
    """The primitive necklaces of period up to `max_period` that `test` accepts."""
    return {word for period in range(1, max_period + 1) for word in game.necklaces(period) if test(word)}


def test_run_pairs() -> None:
    assert run_pairs("0001") == [(1, 3)]
    assert run_pairs("1101000") == [(2, 1), (1, 3)]
    assert run_pairs("111") == [] and run_pairs("000") == []


def test_grammar_against_generated() -> None:
    def ok(r: int, q: int) -> bool:
        return (r == 1 and q >= 10) or (r == 2 and q >= 8) or (r == 4 and q >= 7) or (r >= 9 and q >= 9)
    assert recognized(grammar, MAX) == generated(ok, MAX)


def test_long_white_families_against_generated() -> None:
    # Both families need 17 white cells, so up to period 21 a word has at most four 1s: every such word, by the
    # positions of its 1s, and every necklace up to MAX, where neither family has a word.
    sparse = {game.least_rotation("".join("1" if i in ones else "0" for i in range(period)))
              for period in range(MAX + 1, 22) for k in range(1, period - 16)
              for ones in itertools.combinations(range(period), k)}
    sparse = {word for word in sparse if primitive(word)}
    dense = {word for period in range(1, MAX + 1) for word in game.necklaces(period)}
    for test, expected in ((white17, generated(lambda r, q: q >= 17, 21)),
                           (reset_mixture, generated(lambda r, q: r == 1 and q >= 9, 21,
                                                     lambda pairs: any(q >= 17 for _, q in pairs)))):
        assert {word for word in sparse | dense if test(word)} == expected and expected


def test_padded_and_param_against_generated() -> None:
    words = set()
    for tail, bound in NEW_PADDED:
        words |= {"0" * q + tail for q in range(bound, MAX - len(tail) + 1)}
    assert recognized(padded, MAX) == {game.least_rotation(w) for w in words if primitive(w)}
    assert padded("0" * 17 + "111") and not padded("0" * 16 + "111") and padded("0" * 17 + "11111")
    assert padded("0" * 7 + "1111") and not padded("0" * 6 + "1111") and not padded("0" * 18 + "11")
    words = {"1" * r + format(bits, f"0{length}b") for length, bits, r0 in PARAM_BLACK
             for r in range(r0, MAX - length + 1)}
    assert recognized(param_black, MAX) == {game.least_rotation(w) for w in words if primitive(w)}


def brute_quarter(word: str) -> bool:
    """`no_long_black_run_quarter` or `no_black_white_run_quarter` for the center c(t) = word[t mod P], periodic with
    period P = len(word) from time 0, by trying every start t1 < P and every run length the hypotheses allow."""
    P = len(word)
    def c(t: int) -> bool:
        return word[t % P] == "1"
    for t1 in range(P):
        for r in range(P):  # theorem B: r < P black cells from t1, then a white cell
            if all(c(t1 + s) for s in range(r)) and not c(t1 + r) and 9 * ((P - r + 3) // 4) <= r:
                return True
        for s in range(9, P):  # theorem D: s black cells from t1, then r white cells, then a black cell
            if not all(c(t1 + i) for i in range(s)):
                continue  # whatever r is
            for r in range(P):
                if (s + r < P and not any(c(t1 + s + i) for i in range(r)) and c(t1 + s + r)
                        and 1 + 9 * ((P - s - r + 1) // 4) <= r):
                    return True
    return False


def test_quarter_against_brute() -> None:
    words = [w for period in range(1, 14) for w in game.necklaces(period)]
    words += ["000101111111111", "0000000010111111111", "001111111111111111101", "000000000010111111111"]
    assert [quarter(w) for w in words] == [brute_quarter(w) for w in words]
    assert any(quarter(w) for w in words) and not all(quarter(w) for w in words)


def test_lean_literals() -> None:
    text = 'def b := wordOf 5 0b101\n((6, 0b11), x) ⟨4, 0b0111, y⟩ 0b0011 "1001"'
    assert lean_literals(text) == {"00101", "000011", "0111", "0011"}


def test_new_blocks_small() -> None:
    fresh = new_blocks(13, progress=False)
    assert set(fresh) == {"00000001111", "000000001111", "0000000001111"}
    assert all("Rule30GrammarRuns" in reasons for reasons in fresh.values())
    pinned = game.kit_blocks(13)
    assert not set(fresh) & set(pinned)
