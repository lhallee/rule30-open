"""The traps on words of column 1 against naive fixed points and direct runs."""

from __future__ import annotations

import numpy as np

from computations.gap_traps import (escape_readings, forbidden_words, forced_entry, greatest_trap, necklace_blocks,
                                    readings, step_windows, word_entropy)


def naive_step(w: int, width: int, center: int, beyond: int) -> int:
    """One step of a window of columns 1..width, cell by cell."""
    cells = [center] + [(w >> i) & 1 for i in range(width)] + [beyond]
    new = [cells[i - 1] ^ (cells[i] | cells[i + 1]) for i in range(1, width + 1)]
    return sum(b << i for i, b in enumerate(new))


def naive_trap(block: str, width: int, words: tuple[str, ...]) -> set[tuple[int, int, int]]:
    """The greatest closed set of states (phase, window, last readings as a string), by removing bad states."""
    keep = max(len(w) for w in words) - 1
    states = {(p, w, s) for p in range(len(block)) for w in range(1 << width) for s in range(1 << keep)}

    def successors(p: int, w: int, s: int) -> list[tuple[bool, tuple[int, int, int]]]:
        out = []
        for x in (0, 1):
            v = naive_step(w, width, int(block[p]), x)
            if block[p] == "0":
                text = format(s, f"0{keep}b") + str(w & 1)
                ok = not any(text.endswith(word) for word in words)
                out.append((ok, ((p + 1) % len(block), v, int(text[1:], 2) if keep else 0)))
            else:
                out.append((True, ((p + 1) % len(block), v, s)))
        return out

    moves = {st: successors(*st) for st in states}  # each state's moves, stepped cell by cell once
    while True:
        bad = {st for st in states if any(not ok or nxt not in states for ok, nxt in moves[st])}
        if not bad:
            return states
        states -= bad


def test_step_windows() -> None:
    windows = np.arange(1 << 7, dtype=np.int64)
    for center in (0, 1):
        for beyond in (0, 1):
            fast = step_windows(windows, 7, center, beyond)
            assert fast.tolist() == [naive_step(w, 7, center, beyond) for w in range(1 << 7)]


def test_greatest_trap_matches_naive() -> None:
    sizes = []
    for block, words in (("011", ("000",)), ("001", ("111",)), ("0011", ("000",)), ("011", ("00", "010"))):
        good = greatest_trap(block, 6, words)  # (period, 2^6, sufs)
        naive = naive_trap(block, 6, words)
        fast = {(p, w, s) for p, w, s in zip(*np.nonzero(good))}
        assert fast == naive
        sizes.append(len(fast))
    assert sizes == [552, 640, 736, 0]


def test_forced_entry_matches_naive() -> None:
    block, width, words = "011", 6, ("000",)
    good = greatest_trap(block, width, words)
    forced = forced_entry(good, block, width)
    keep = max(len(w) for w in words) - 1
    mask = (1 << keep) - 1
    attractor = {(p, w, s) for p, w, s in zip(*np.nonzero(good))}
    while True:
        new = set(attractor)
        for p in range(len(block)):
            for w in range(1 << width):
                for s in range(1 << keep):
                    nexts = []
                    for x in (0, 1):
                        v = naive_step(w, width, int(block[p]), x)
                        s2 = ((s << 1) | (w & 1)) & mask if block[p] == "0" else s
                        nexts.append(((p + 1) % len(block), v, s2))
                    if all(n in attractor for n in nexts):
                        new.add((p, w, s))
        if new == attractor:
            break
        attractor = new
    assert {(p, w, s) for p, w, s in zip(*np.nonzero(forced))} == attractor and len(attractor) == 744


def test_readings_and_learned_words_of_011() -> None:
    """The words that 011 never shows, learned from a small sample, include the four of the trap, and a direct run
    of a random long half avoids them after a short transient."""
    words = forbidden_words("011", 6, 4, 1500)
    assert {"00", "010", "01110", "011110"} <= set(words)
    rng = np.random.default_rng(5)
    half = int(rng.integers(0, 1 << 62)) | (int(rng.integers(0, 1 << 62)) << 62)
    r = "".join(map(str, readings("011", 1, half, 1200)))[60:]
    assert not any(w in r for w in ("00", "010", "01110", "011110"))


def test_necklace_blocks() -> None:
    assert necklace_blocks(3) == ["001", "011"]
    assert len(necklace_blocks(7)) == 18 and len(necklace_blocks(6)) == 9


def test_word_entropy() -> None:
    """No 11 is the golden-mean shift; the count of words of length 14 avoiding the words of 011 agrees in growth."""
    assert abs(word_entropy(("11",)) - np.log2((1 + 5 ** 0.5) / 2)) < 1e-12
    words = ("00", "010", "01110", "011110")
    counts = [sum(1 for x in range(1 << n) if not any(w in format(x, f"0{n}b") for w in words)) for n in (12, 16)]
    assert abs(np.log2(counts[1] / counts[0]) / 4 - word_entropy(words)) < 0.02


def test_escape_readings_matches_naive() -> None:
    block, width, words = "011", 6, ("000",)
    good = greatest_trap(block, width, words)
    forced = forced_entry(good, block, width)
    keep = 2
    out = {(p, w, s) for p, w, s in zip(*np.nonzero(~forced))}

    def nexts(p: int, w: int, s: int) -> list[tuple[int, int, int]]:
        s2 = ((s << 1) | (w & 1)) & ((1 << keep) - 1) if block[p] == "0" else s
        return [((p + 1) % 3, naive_step(w, width, int(block[p]), x), s2) for x in (0, 1)]

    while True:
        new = {st for st in out if any(n in out for n in nexts(*st))}
        if new == out:
            break
        out = new
    expected = {w & 1 for p, w, s in out if block[p] == "0"}
    assert escape_readings(good, forced, block, width) == expected and len(out) > 0
