"""Tests of computations.forcing: the search for forcing words against brute force over every start."""

from __future__ import annotations


def test_forcing() -> None:
    """Forcing words: the search over sets of configurations against brute force over every start, for every word of up
    to seven values; the shortest forcing words have seven values; and the blocks of period up to 11 whose 0s all follow
    a forcing word of length 12, against the same test with each lookback checked by brute force."""
    import itertools
    from computations import forcing, wall_segments
    for n in range(1, 8):
        words = forcing.forcing_words(n)
        for bits in itertools.product("01", repeat=n):
            word = "".join(bits)
            assert words.get(word) == forcing.forced_value(word)
    assert forcing.forcing_words(7) == {"0110000": 1, "0110001": 0}
    assert forcing.forced_value("1" * 9) == 0 and forcing.forced_value("1" * 8 + "0") == 1
    family = forcing.forcing_family(forcing.forcing_words(12), 12, 11)
    cache: dict[str, int | None] = {}
    for period in range(1, 12):
        brute = [block for block in wall_segments.necklaces(period)
                 if all(cache.setdefault(word, forcing.forced_value(word)) is not None
                        for word in (forcing.lookback(block, i, 12) for i, ch in enumerate(block) if ch == "0"))]
        assert family[period] == brute
    assert family[8] == ["01111111"] and family[11] == ["00111111111", "01111111111"]
