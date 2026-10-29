"""Truncated ether: the certificates of `EtherPrefix.lean`.

The right half that is the ether aligned with the center's word never enters the kit's ether-and-wall family. Its
truncations do: the half that is the aligned ether on cells 1 .. K, then a word u, then white, enters for every K. A
half that enters at step T, with column 1 equal to the ether's at every step before T, still enters at step T, seven
columns deeper, behind seven more columns of ether (`EtherPrefix.shift7_family`). So for each word, alignment, phase and
tail word u, one base per residue of K modulo 7 and a direct check of every smaller K settle every K.

This module finds them: B, the least length from which every residue class has a base, the entry of every K < B
through any alignment, and the entry of each K in B .. B + 6 through the half's own alignment with a clean column 1.
It packs them as the Lean module reads them: one number per tail word, B in the low 6 bits, then 17 bits an entry, the
entry (t, k) as t * 64 + k, the direct entries for K = 0 .. B - 1 and then the bases for K = B .. B + 6.

    python -m computations.ether_prefix --tail 4            # B and the latest entries for tails of up to 4 cells
    python -m computations.ether_prefix --tail 4 --lean     # the certificate section of EtherPrefix.lean
"""

from __future__ import annotations

import argparse
import sys
import time
import numpy as np

from tqdm.auto import tqdm

from computations import absorption


BITS = 17  # bits of one packed entry t * 64 + k
DEPTHS = 64  # every depth is below this
LONGEST = 64  # the packed truncation needs K <= 64
STEPS = 2000

WALLS = [set(np.flatnonzero(row).tolist()) for row in absorption.kit_wall()]  # per phase, the 13-bit wall states


def ether_bits(j0: int, psi: int, n: int) -> int:
    """The ether columns j0 + 1 .. j0 + n at phase psi, bit p - 1 for column p."""
    return sum(absorption.ether(j0 + p, psi) << (p - 1) for p in range(1, n + 1))


def prefix_half(j0: int, psi: int, length: int, tail: int) -> int:
    """The aligned ether on cells 1 .. length at phase psi, then the tail word, white beyond."""
    return ether_bits(j0, psi, length) | (tail << length)


def depths(word: str, row: int, phase: int, alignments: list[tuple[int, int]], deepest: int) -> list[int]:
    """The depths k <= deepest at which the integer half is in the family at drive phase `phase` (the center reads
    word[phase] now) through one of the alignments."""
    found = []
    for j0, shift in alignments:
        psi = (phase + shift) % 4
        differ = row ^ ether_bits(j0, psi, deepest)
        clean = (differ & -differ).bit_length() - 1 if differ else deepest  # columns 1 .. clean carry the ether
        found += [k for k in range(min(clean, deepest) + 1) if (j0 + k) % 7 == 2 and ((row >> k) & 0x1FFF) in WALLS[psi]]
    return found


def entry(word: str, phase: int, row: int, alignments: list[tuple[int, int]], column: tuple[int, int] | None = None,
          steps: int = STEPS) -> tuple[int, int, bool] | None:
    """The first step at which the half is in the family through one of the alignments, the least depth then, and,
    when `column` = (j0, shift) is given, whether column 1 was that alignment's ether at every step before."""
    clean = True
    for t in range(steps):
        found = [k for k in depths(word, row, (t + phase) % 4, alignments, DEPTHS - 1) if k < DEPTHS]
        if found:
            return t, min(found), clean
        if column is not None and (row & 1) != absorption.ether(column[0] + 1, (t + phase + column[1]) % 4):
            clean = False
        row = ((row << 1) | int(word[(t + phase) % 4])) ^ (row | (row >> 1))
    return None


def certificate(word: str, j0: int, shift: int, phase: int, tail: int) -> tuple[int, list[tuple[int, int]],
                                                                                list[tuple[int, int]]]:
    """B, the direct entries for K = 0 .. B - 1 and the bases for K = B .. B + 6, for one alignment, phase and tail."""
    psi = (phase + shift) % 4
    alignment = [(j0, shift)]
    base = {}
    for r in range(7):
        for length in range(r, LONGEST - 6, 7):
            found = entry(word, phase, prefix_half(j0, psi, length, tail), alignment, (j0, shift))
            if found is not None and found[2]:
                base[r] = length
                break
        assert r in base, f"no base for {word} {(j0, shift)} phase {phase} tail {tail} residue {r}"
    b = max(base.values())
    assert b + 7 <= LONGEST
    direct = []
    for length in range(b):
        found = entry(word, phase, prefix_half(j0, psi, length, tail), absorption.ALIGNMENTS[word])
        assert found is not None, f"{word} {(j0, shift)} phase {phase} tail {tail}: K = {length} does not enter"
        direct.append(found[:2])
    bases = []
    for length in range(b, b + 7):
        found = entry(word, phase, prefix_half(j0, psi, length, tail), alignment, (j0, shift))
        assert found is not None and found[2], f"{word} {(j0, shift)} phase {phase} tail {tail}: base {length} fails"
        bases.append(found[:2])
    return b, direct, bases


def encode(b: int, direct: list[tuple[int, int]], bases: list[tuple[int, int]]) -> int:
    """One tail as the Lean module reads it: B in bits 0 .. 5, then entry j in bits 6 + 17 j .. 6 + 17 j + 16."""
    assert b < 64 and len(direct) == b and len(bases) == 7
    number = b
    for j, (t, k) in enumerate(direct + bases):
        assert 0 <= k < DEPTHS and t * DEPTHS + k < 1 << BITS
        number |= (t * DEPTHS + k) << (6 + BITS * j)
    return number


def decode(number: int) -> tuple[int, list[tuple[int, int]], list[tuple[int, int]]]:
    """The inverse of `encode`."""
    b = number & 63
    entries = [((number >> (6 + BITS * j)) & ((1 << BITS) - 1)) for j in range(b + 7)]
    pairs = [(e // DEPTHS, e % DEPTHS) for e in entries]
    return b, pairs[:b], pairs[b:]


def combos() -> list[tuple[str, int, int, int]]:
    """Every word, alignment and phase."""
    return [(word, j0, shift, phase) for word in absorption.WORDS for j0, shift in absorption.ALIGNMENTS[word]
            for phase in range(4)]


def lean_data(tail_cells: int) -> str:
    """The certificate section of `EtherPrefix.lean`: one list per word, alignment and phase, one number per tail
    word, and the kernel check of each list."""
    blocks = []
    for word, j0, shift, phase in tqdm(combos(), desc="alignments and phases", file=sys.stderr, leave=False):
        name = f"tails{word}_{j0}_{phase}"
        numbers = ",\n".join(f"  0x{encode(*certificate(word, j0, shift, phase, tail)):x}"
                             for tail in range(1 << tail_cells))
        blocks.append(f"def {name} : List Nat := [\n{numbers}]\n\n"
                      f"theorem {name}_ok : tailsOK w{word} A{word} {phase} {j0} {(phase + shift) % 4} 0 {name} = true "
                      f":= by\n  decide +kernel\n")
    return "\n".join(blocks)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--tail", type=int, default=4, help="tail words of at most this many cells")
    parser.add_argument("--lean", action="store_true", help="print the Lean certificate section")
    args = parser.parse_args()

    started = time.perf_counter()
    if args.lean:
        print(lean_data(args.tail))
        return
    worst_b, worst_direct, worst_base = 0, 0, 0
    for word, j0, shift, phase in tqdm(combos(), desc="alignments and phases", file=sys.stderr, leave=False):
        bs = []
        for tail in range(1 << args.tail):
            b, direct, bases = certificate(word, j0, shift, phase, tail)
            bs.append(b)
            worst_direct = max([worst_direct] + [t for t, _ in direct])
            worst_base = max([worst_base] + [t for t, _ in bases])
        worst_b = max(worst_b, max(bs))
        print(f"{word} alignment ({j0}, {shift}) phase {phase}: B from {min(bs)} to {max(bs)} over "
              f"{1 << args.tail} tails")
    print(f"largest B {worst_b}; latest direct entry at step {worst_direct}, latest base entry at step {worst_base}")
    print(f"({time.perf_counter() - started:.0f} s)")


if __name__ == "__main__":
    main()
