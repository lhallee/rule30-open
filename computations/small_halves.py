"""Every right half of a few cells: the entry certificates of `TenCells.lean`.

Every right half of at most `cells` cells (the integers below 2^cells, bit j being column j + 1), driven by a word of
period four from each phase, enters the kit's ether-and-wall family (`absorption.entry_certificate`). Entry at step t
and depth k reads only the initial cells 1 .. t + k + 13 (`SparseRight.inFamily_of_fast`), so every right half whose
cells cells + 1 .. G are white enters with the half of its first cells, where G bounds every t + k + 13. This module
packs the entries as the Lean module reads them: 17 bits a half, the entry (t, k) as t * 64 + k, half r at bits
17 r .. 17 r + 16 of its chunk, and `CHUNK` halves a chunk.

    python -m computations.small_halves --cells 10          # the latest entry and the bound G for each word
    python -m computations.small_halves --cells 10 --lean   # the certificate section of TenCells.lean
"""

from __future__ import annotations

import argparse
import sys
import time

from tqdm.auto import tqdm

from computations import absorption


BITS = 17  # bits of one packed entry t * 64 + k
DEPTHS = 64  # every depth is below this
CHUNK = 128  # halves per kernel check


def certificates(word: str, cells: int, phase: int) -> list[tuple[int, int]]:
    """The entry step and least depth of every right half below 2^cells."""
    return absorption.entry_certificate(word, cells, phase, absorption.kit_wall())


def bound(entries: list[tuple[int, int]]) -> int:
    """The largest t + k + 13 over the entries: the cells the theorem constrains."""
    return max(t + k + 13 for t, k in entries)


def encode(entries: list[tuple[int, int]]) -> int:
    """Entries packed 17 bits each, the first at bit 0."""
    number = 0
    for j, (t, k) in enumerate(entries):
        assert 0 <= k < DEPTHS and t * DEPTHS + k < 1 << BITS
        number |= (t * DEPTHS + k) << (BITS * j)
    return number


def decode(number: int, count: int) -> list[tuple[int, int]]:
    """The first `count` entries of a packed number."""
    packed = [(number >> (BITS * j)) & ((1 << BITS) - 1) for j in range(count)]
    return [(e // DEPTHS, e % DEPTHS) for e in packed]


def lean_data(cells: int) -> str:
    """The certificate section of `TenCells.lean`: for each word and phase, the packed chunks `halves<word>_<phase>`,
    one kernel check per chunk, and the bound G per word."""
    blocks = []
    chunks = (1 << cells) // CHUNK
    for word in tqdm(absorption.WORDS, desc="words", file=sys.stderr, leave=False):
        certs = [certificates(word, cells, phase) for phase in range(4)]
        g = max(bound(c) for c in certs)
        blocks.append(f"/-! #### `{word}`, every `t + k + 13` at most {g} -/\n")
        for phase, entries in enumerate(certs):
            name = f"halves{word}_{phase}"
            numbers = ",\n".join(f"  0x{encode(entries[i * CHUNK:(i + 1) * CHUNK]):x}" for i in range(chunks))
            checks = "\n".join(f"theorem {name}_{i} : halvesOK w{word} A{word} {phase} {g} {CHUNK} {i * CHUNK} "
                               f"({name}.getD {i} 0) = true := by decide +kernel" for i in range(chunks))
            blocks.append(f"def {name} : List Nat := [\n{numbers}]\n\n{checks}\n")
    return "\n".join(blocks)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--cells", type=int, default=10)
    parser.add_argument("--lean", action="store_true", help="print the Lean certificate section")
    args = parser.parse_args()

    started = time.perf_counter()
    if args.lean:
        print(lean_data(args.cells))
        return
    for word in absorption.WORDS:
        certs = [certificates(word, args.cells, phase) for phase in range(4)]
        print(f"{word}: every right half of at most {args.cells} cells enters, the latest at step "
              f"{max(t for c in certs for t, _ in c)}, the deepest at depth {max(k for c in certs for _, k in c)}; "
              f"G = {max(bound(c) for c in certs)}")
    print(f"({time.perf_counter() - started:.0f} s)")


if __name__ == "__main__":
    main()
