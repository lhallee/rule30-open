"""Right halves with at most two black cells among their first G cells: the certificates of `SparseRight.lean`.

A right half driven by a word of period four that is white on cells 1 .. 30 enters the kit's ether-and-wall family
(`WhiteGap.high_*`). Otherwise let p1 <= 30 be its first black cell. The half {p1}, one black cell, enters at some step t
and depth k, and entry reads only the initial cells 1 .. t + k + 13 (`WhiteGap.inFamily_of_check_cone`), so every half
whose next black cell lies beyond t + k + 13 enters with it. Otherwise let p2 be the second black cell: the half
{p1, p2} enters at its own step t' and depth k', and so does every half that agrees with it on cells 1 .. t' + k' + 13.
So every half with at most two black cells among cells 1 .. G enters, where G bounds every t + k + 13 used.

For each word and phase this module computes, for p1 = 1 .. 30, the entry of {p1} and of every {p1, p2} with
p1 < p2 <= t + k + 13, and packs them as the Lean module reads them: one number per p1, 17 bits an entry, the entry
(t, k) as t * 64 + k, the half {p1} first and then p2 = p1 + 1, p1 + 2, ...

    python -m computations.sparse_halves            # the counts and the bound G for each word
    python -m computations.sparse_halves --lean     # the certificate section of SparseRight.lean
"""

from __future__ import annotations

import argparse
import sys
import textwrap
import time
import numpy as np

from tqdm.auto import tqdm

from computations import absorption


FIRST = 30  # a half white on cells 1 .. FIRST enters by `WhiteGap.high_*`
BITS = 17  # bits of one packed entry t * 64 + k
DEPTHS = 64  # every depth is below this
STEPS = 4000


def entries(word: str, phase: int, halves: list[int], wall: np.ndarray) -> list[tuple[int, int]]:
    """The first step at which each half (bit j is column j + 1) is in the family, and the least depth at that step."""
    width = max(half.bit_length() for half in halves)
    rows = np.zeros((len(halves), (width + STEPS + 2) // 64 + 1), dtype=np.uint64)  # (n, words)
    for i, half in enumerate(halves):
        for j in range(0, width, 64):
            rows[i, j // 64] = np.uint64((half >> j) & ((1 << 64) - 1))
    times = absorption.absorb(word, rows, phase, STEPS, wall, width)  # (n,)
    assert (times >= 0).all(), "a half did not enter"
    depths = np.full(len(halves), -1, dtype=np.int64)  # (n,)
    t = 0
    for i in np.argsort(times, kind="stable").tolist():  # step every half together, reading each at its entry
        while t < times[i]:
            rows = absorption.step_rows(rows, int(word[(t + phase) % 4]))
            t += 1
        depths[i] = absorption.family_depth(word, rows[i:i + 1, 0], (t + phase) % 4, wall)[0]
    assert (depths >= 0).all() and (depths < DEPTHS).all()
    return list(zip(times.tolist(), depths.tolist()))


def certificates(word: str, phase: int, wall: np.ndarray) -> list[tuple[tuple[int, int], list[tuple[int, int]]]]:
    """For p1 = 1 .. FIRST: the entry (t, k) of the half {p1} and the entries of {p1, p2}, p2 = p1 + 1 .. t + k + 13."""
    singles = entries(word, phase, [1 << (p1 - 1) for p1 in range(1, FIRST + 1)], wall)
    pairs, owner = [], []
    for p1, (t, k) in enumerate(singles, start=1):
        for p2 in range(p1 + 1, t + k + 14):
            pairs.append((1 << (p1 - 1)) | (1 << (p2 - 1)))
            owner.append(p1)
    found = entries(word, phase, pairs, wall)
    certs = [(single, []) for single in singles]
    for p1, entry in zip(owner, found):
        certs[p1 - 1][1].append(entry)
    return certs


def bound(certs: list[tuple[tuple[int, int], list[tuple[int, int]]]]) -> int:
    """The largest t + k + 13 over every entry: the cells 1 .. G that the theorem constrains."""
    return max(t + k + 13 for single, pairs in certs for t, k in [single, *pairs])


def encode(single: tuple[int, int], pairs: list[tuple[int, int]]) -> int:
    """One p1 as the Lean module reads it: entry j in bits 17 j .. 17 j + 16, the half {p1} first."""
    number = 0
    for j, (t, k) in enumerate([single, *pairs]):
        assert 0 <= k < DEPTHS and t * DEPTHS + k < 1 << BITS
        number |= (t * DEPTHS + k) << (BITS * j)
    return number


def decode(number: int, count: int) -> list[tuple[int, int]]:
    """The first `count` entries of a packed number."""
    packed = [(number >> (BITS * j)) & ((1 << BITS) - 1) for j in range(count)]
    return [(e // DEPTHS, e % DEPTHS) for e in packed]


def lean_data(wall: np.ndarray) -> str:
    """The certificate section of `SparseRight.lean`: per word and phase, the numbers `cells<word>_<phase>`, one
    theorem per first black cell that the kernel checks, and their assembly `cells<word>_<phase>_ok`."""
    blocks = []
    for word in tqdm(absorption.WORDS, desc="words", file=sys.stderr, leave=False):
        certs = [certificates(word, phase, wall) for phase in range(4)]
        g = max(bound(c) for c in certs)
        for phase, cert in enumerate(certs):
            name = f"cells{word}_{phase}"
            numbers = ",\n".join(f"  0x{encode(single, pairs):x}" for single, pairs in cert)
            checks = "\n".join(f"theorem cell{word}_{phase}_{p1} : cellOK w{word} A{word} {phase} {g} {p1} "
                               f"({name}.getD {p1 - 1} 0) = true := by decide +kernel" for p1 in range(1, FIRST + 1))
            names = " ".join(f"cell{word}_{phase}_{p1}" for p1 in range(1, FIRST + 1))
            assembly = "\n    ".join(textwrap.wrap(names, width=114))
            blocks.append(f"def {name} : List Nat := [\n{numbers}]\n\n{checks}\n\n"
                          f"theorem {name}_ok : ∀ p1, 1 ≤ p1 → p1 ≤ 30 → cellOK w{word} A{word} {phase} {g} p1\n"
                          f"    ({name}.getD (p1 - 1) 0) = true :=\n  all30\n    {assembly}\n")
    return "\n".join(blocks)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--lean", action="store_true", help="print the Lean definitions instead of the counts")
    args = parser.parse_args()

    started = time.perf_counter()
    wall = absorption.kit_wall()  # (4, 2^13)
    if args.lean:
        print(lean_data(wall))
        return
    for word in absorption.WORDS:
        rows = []
        for phase in range(4):
            certs = certificates(word, phase, wall)
            pairs = [entry for _, more in certs for entry in more]
            rows.append((phase, len(pairs), max(t for (t, _), _ in certs), max(t for t, _ in pairs), bound(certs)))
        g = max(row[4] for row in rows)
        print(f"{word}: G = {g}")
        for phase, count, single, latest, b in rows:
            print(f"  phase {phase}: {count} halves of two cells; latest entry of one cell at step {single}, of two "
                  f"cells at step {latest}; largest step + depth + 13 is {b}")
    print(f"({time.perf_counter() - started:.0f} s)")


if __name__ == "__main__":
    main()
