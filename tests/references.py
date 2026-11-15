"""Plain reference code that several test files read: the repository root, the core of 0001, packed Lean fields, the
kit's ether lists and the family's least depth checked column by column."""

from __future__ import annotations

import re
import numpy as np

from pathlib import Path

from computations import absorption


ROOT = Path(__file__).resolve().parents[1]


def packed_fields(value: int, bits: int, count: int) -> list[int]:
    """Fields 0 .. count - 1 of `bits` bits each of a packed Lean literal, field i at bits i * bits and up, read from
    its bytes at once rather than by one shift of the whole number per field."""
    raw = value.to_bytes(max((value.bit_length() + 7) // 8, (bits * count + 7) // 8), "little")
    cells = np.unpackbits(np.frombuffer(raw, dtype=np.uint8), bitorder="little")[:bits * count]  # (bits count,)
    if bits < 63:  # each field fits an int64: the cells times their weights, every field at once
        return (cells.reshape(count, bits).astype(np.int64) @ (1 << np.arange(bits, dtype=np.int64))).tolist()
    weights = [1 << k for k in range(bits)]
    return [sum(w for w, cell in zip(weights, row, strict=True) if cell) for row in cells.reshape(count, bits).tolist()]


CORE_0001 = [{1: 0, 2: 0, 3: 1}, {1: 0, 2: 1, 3: 1}, {1: 1, 2: 1, 3: 0}, {1: 1, 2: 0, 3: 1}]  # 001, 011, 110, 101


def least_depth_slow(word: str, row: int, phase: int, wall: np.ndarray) -> int:
    """The least depth at which an integer right half is in the kit's family, checked column by column, or -1."""
    # wall: (4, 2^13), the wall states at each ether phase
    depths = [k for j0, shift in absorption.ALIGNMENTS[word] for k in range(52)
              if (j0 + k) % 7 == 2 and wall[(phase + shift) % 4][(row >> k) & 0x1FFF]
              and all((row >> (p - 1)) & 1 == absorption.ether(j0 + p, phase + shift) for p in range(1, k + 1))]
    return min(depths, default=-1)


def lean_states(name: str) -> set[tuple[int, int]]:
    """The (phase, strip) pairs of the list `name` in the kit's `Rule30Ether.lean`, the strip's first cell at bit 0."""
    source = ROOT / ".lake/packages/rule30prize/lean/Ruliology/CellularAutomata/Rule30Ether.lean"
    body = source.read_text(encoding="utf-8").split(f"def {name} : List (Nat × List Bool) := [", 1)[1].split("\n]", 1)[0]
    return {(int(phase), sum(1 << i for i, cell in enumerate(cells.split(", ")) if cell == "true"))
            for phase, cells in re.findall(r"\((\d), \[([a-z, ]+)\]\)", body)}
