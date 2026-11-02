"""The left cut of the cone: streamed subfunction counts, family values, merges and the Lean certificates."""

from __future__ import annotations

from computations import cone_screening as cs
from computations import left_cut as lc


def plain_center(cells: list[int]) -> int:
    """c_t from the 2t + 1 cone cells x_{-t} .. x_t by running the rule on a list, one cell at a time."""
    row = list(cells)  # (2t + 1,)
    while len(row) > 1:
        row = [row[i - 1] ^ (row[i] | row[i + 1]) for i in range(1, len(row) - 1)]  # (len - 2,)
    return row[0]


def test_counts_against_full_tables() -> None:
    """N_L(t, k) from the stream equals the count of distinct rows of the full truth table, for t <= 6 and every k."""
    for t in range(2, 7):
        assert [lc.scan(t, k).count for k in range(1, 2 * t + 1)] == cs.left_counts(t)


def test_streaming_in_small_blocks() -> None:
    """At t = 5, blocks of 2^3 rows (most prefix cells constants, many blocks) give the counts of the full table."""
    table = cs.cone_table(5)  # (2^11,)
    for k in range(1, 11):
        assert lc.scan(5, k, block_bits=3).count == cs.left_count(table, 11, k)


def test_family_values_against_plain_run() -> None:
    """The bit-sliced values on a family equal plain runs of the rule, for every prefix and completion at t = 5."""
    t, k = 5, 3
    family = lc.completion_family(t, k, 2)  # (m,)
    assert family.shape[0] == 4 * (1 + 6 + 15)
    values = lc.family_values(t, k, family)  # (2^k, m)
    for prefix in range(1 << k):
        for col, completion in enumerate(family.tolist()):
            cells = [(prefix >> i) & 1 for i in range(k)] + [(completion >> i) & 1 for i in range(2 * t + 1 - k)]
            assert values[prefix, col] == plain_center(cells)


def test_merges_and_misses() -> None:
    """At t = 9 the 2^9 left halves give 506 functions (`cone_screening`), and every merge is confirmed exactly; the
    family with at most one black cell separates the 2^7 prefixes of 7 cells, and the white right half alone does not."""
    result = lc.scan(9, 9)
    merged = lc.merged_classes(result)
    assert result.count == 506
    assert sum(len(c) - 1 for c in merged) == 512 - 506
    families = {"white": lc.completion_family(9, 7, 0), "one": lc.completion_family(9, 7, 1)}
    result = lc.scan(9, 7, families)
    assert result.count == 128
    assert lc.misses(result, "one") == []
    assert len(result.signatures["white"]) < 128 and lc.misses(result, "white")


def test_certificate_separates() -> None:
    """The completions written into the Lean module split the prefixes at t = 8 into single prefixes, by plain runs."""
    t = 8
    black, order = lc.certificate(t)
    assert black == 1
    signatures = set()
    for prefix in range(1 << (t - 2)):
        cells = [(prefix >> i) & 1 for i in range(t - 2)]
        signatures.add(tuple(plain_center(cells + [(r >> i) & 1 for i in range(t + 3)]) for r in order))
    assert len(signatures) == 1 << (t - 2)


def test_black_run() -> None:
    """The alternating run that ends with a black cell, read from the bits of a prefix."""
    word = [0, 0, 1, 0, 1, 0, 1]  # bits 0 .. 6: the run 0 1 0 1 0 1 on bits 1 .. 6 ends black at bit 6
    prefix = sum(v << i for i, v in enumerate(word))
    assert lc.black_run(prefix, 6) == 6
    assert lc.black_run(prefix, 5) == 0  # bit 5 is white
    assert lc.black_run(int("10101010", 2), 7) == 8
    assert all(lc.black_run(0, end) == 0 for end in range(5))


def test_family_count_against_full_table() -> None:
    """The count through a family, with every group of equal values compared in full, equals the full table's count:
    with the white right half only (many groups to compare) and with one black cell, at t = 7."""
    table = cs.cone_table(7)  # (2^15,)
    for k in (4, 5):
        for black in (0, 1):
            count, merged = lc.family_count(7, k, black)
            assert count == cs.left_count(table, 15, k) == 1 << k and merged == []


def test_stripes_fix_the_center() -> None:
    """The stripe to -1 fixes c_t exactly when `cone_screening`'s odd pattern does (t <= 11); the stripe to -3 does not
    fix it for t <= 11, by the prefix's full subfunction."""
    for t in range(3, 12):
        assert lc.stripe_fixes(t, -1) == cs.constant_value(cs.pattern_values(t, True))
        k = t - 2
        assert lc.stripe_fixes(t, -3) == lc.constant_of(t, k, lc.stripe_prefix(t, k, -3)) is None
