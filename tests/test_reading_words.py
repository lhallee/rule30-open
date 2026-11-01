"""The module ReadingWords: its sections are the generator's text, its small certificates match a naive fixed point,
and direct runs of random halves avoid each block's words from the reading the module states."""

from __future__ import annotations

import numpy as np

from computations.reading_certificates import Spec, certificate, phase_readings
from computations.reading_modules import (COLLECTIONS, COLUMNS, READING_WORDS, module_parts, reading_module,
                                          statement)

PATH = COLUMNS / "ReadingWords.lean"


def naive_ranks(spec: Spec) -> dict[tuple[int, int, str], int]:
    """The rank of every state (phase, window, stored readings as a string), from a cell-by-cell step: remove the states
    with a bad step or a removed successor until none is left to remove, then add backward layers; -1 where none."""
    width, block, keep = spec.width, spec.block, spec.keep

    def succ(p: int, w: int, s: str) -> list[tuple[bool, tuple[int, int, str]]]:
        out = []
        for x in (0, 1):
            cells = [int(block[p])] + [(w >> i) & 1 for i in range(width)] + [x]
            v = sum((cells[i - 1] ^ (cells[i] | cells[i + 1])) << (i - 1) for i in range(1, width + 1))
            if p in spec.phases:
                text = s + str(w & 1)
                out.append((not any(text.endswith(u) for u in spec.words),
                            ((p + 1) % len(block), v, text[len(text) - keep:])))
            else:
                out.append((True, ((p + 1) % len(block), v, s)))
        return out

    texts = [format(s, f"0{keep}b") for s in range(1 << keep)]
    states = {(p, w, s) for p in range(len(block)) for w in range(1 << width) for s in texts}
    good = set(states)
    while True:
        drop = {st for st in good if any(not ok or nx not in good for ok, nx in succ(*st))}
        if not drop:
            break
        good -= drop
    layer, k = {st: 0 for st in good}, 0
    while True:
        add = {st for st in states - layer.keys() if all(nx in layer for _, nx in succ(*st))}
        if not add:
            return {st: layer.get(st, -1) for st in states}
        k += 1
        layer.update({st: k for st in add})


def test_rows() -> None:
    """Fifteen blocks, one section each, at white phases, with distinct headline names."""
    text = PATH.read_text(encoding="utf-8")
    blocks = [row[0] for row in READING_WORDS]
    assert len(blocks) == len(set(blocks)) == 15
    for block, q, _, _ in READING_WORDS:
        assert block[q] == "0"
        assert f"\nsection B{block}\n" in text and f"\nend B{block}\n" in text
        assert f"theorem readings_{block} (R : Nat → Bool) (ph : Nat)" in text
        assert f"theorem readings_{block}_evolve (init : Int → Bool) (T : Nat)" in text
    assert len(COLLECTIONS["ReadingWords"].modules) == 15


def test_sections_are_generated() -> None:
    """The sections of two blocks are the text the generator writes from their ranks."""
    text = PATH.read_text(encoding="utf-8")
    for row in READING_WORDS:
        if row[0] in ("01011", "0000101"):
            _, body = module_parts(reading_module(*row))
            assert f"section B{row[0]}\n\n{body}\nend B{row[0]}\n" in text


def test_matches_naive() -> None:
    """For the two smallest certificates the ranks equal the naive ranks, and the statement is read off them."""
    for row in READING_WORDS:
        block, q, width, words = row
        if block not in ("01011", "0000101"):
            continue
        spec = Spec(block, (q,), width, words)
        good, rank = certificate(spec)  # (P, 2^W, 2^keep)
        naive = naive_ranks(spec)
        for (p, w, s), r in naive.items():
            assert rank[p, w, int(s, 2)] == r
        assert min(naive.values()) == 0
        st = statement(reading_module(*row))
        assert st.max_rank == max(naive.values()) and st.good == sum(r == 0 for r in naive.values())


def test_direct_runs() -> None:
    """Random halves of 120 cells driven by each block from every phase: the readings avoid the words once the last
    reading of a word is at the largest rank, and from the first reading the module states."""
    rng = np.random.default_rng(11)
    for row in READING_WORDS:
        block, q, _, words = row
        st = statement(reading_module(*row))
        period = len(block)
        steps = st.max_rank + 12 * period
        for ph in range(period):
            half = int(rng.integers(0, 1 << 60)) | (int(rng.integers(0, 1 << 60)) << 60)
            reads = [b for p, b in phase_readings(block, ph, half, steps) if p == q]
            times = [t for t in range(steps) if (t + ph) % period == q]
            assert len(reads) == len(times) and times[0] == (q - ph) % period
            text = "".join(map(str, reads))
            for u in words:
                for i in range(len(text) - len(u) + 1):
                    if times[i + len(u) - 1] >= st.max_rank or i >= st.first:
                        assert text[i:i + len(u)] != u, (block, ph, u, i)
