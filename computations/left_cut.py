"""The center cell after t steps, read from the left: how many functions of the rest of the row the k leftmost cells
leave, counted without the full truth table.

c_t is a Boolean function of the 2t + 1 cells x_{-t} .. x_t of row 0 (new x_j = x_{j-1} xor (x_j or x_{j+1})). Fix the
k leftmost cells (the *prefix*, bit i of its index is x_{-t+i}, as in `cone_screening`) and call the function of the
other 2t + 1 - k cells that remains the prefix's subfunction; N_L(t, k) is the number of distinct subfunctions, the width
at level k of every ordered decision diagram that reads the row from left to right. N_L(t, t - 2) = 2^(t-2) for
3 <= t <= 17 and not for t = 18, 19, 20.

* `scan` streams the prefixes in blocks: the free cells and the b prefix cells next to the cut are bit-sliced (64 rows
  to a machine word), the other prefix cells are constants, and only a 128-bit digest of each subfunction is kept. The
  table of 2^(2t+1) entries is never stored. Since c_t = x_{-t} xor g with g free of x_{-t} (`cone_screening`), only the
  prefixes with x_{-t} = 0 are evolved; the other half are the complements. Two prefixes with different digests have
  different subfunctions; prefixes with equal digests are compared exactly by `merged_classes`, which recomputes each
  subfunction cell by cell as an array of bools.
* `completion_family` lists the completions (settings of the free cells) with the cells between the cut and column 0
  free and at most `black` black cells in the right half x_0 .. x_t; `scan` records each prefix's values on them, and
  `misses` lists the pairs of prefixes with different subfunctions that the family does not tell apart.
* `family_count` gives N_L(t, k) exactly and faster: the prefixes, bit-sliced, are grouped by their values on a family
  (`family_values`), and only within a group are subfunctions compared in full.
* `stripe_fixes` tells whether an alternating stretch from x_{-t} to a black cell at `wall` fixes c_t for every setting
  of the cells right of it; the stretches to -3 and -4 do from t = 18 on (to t = 22).
* `certificate` and `lean_certificates` give the lists of completions that the Lean module `LeftCut` checks.

    python -m computations.left_cut --t 17 --k 15 --black 2      # N_L(17, 15), streamed, and both families (200 s)
    python -m computations.left_cut --t 15 --k 14 --merges       # the merged prefixes at k = t - 1
    python -m computations.left_cut --t 20 --k 18 --family-count 2   # N_L(20, 18) = 2^18 - 26 (5 min)
    python -m computations.left_cut --t 22 --stripes             # which stripes fix the center (1 min)
    python -m computations.left_cut --t 17 --lean                # the certificates of LeftCut
"""


from __future__ import annotations

import argparse
import hashlib
import itertools
import sys
from dataclasses import dataclass, field

import numpy as np

from tqdm.auto import tqdm

from computations import cone_screening as cs

ONES = np.uint64(0xFFFF_FFFF_FFFF_FFFF)
ZERO = np.uint64(0)
LOW_PATTERNS = [
    np.uint64(0xAAAA_AAAA_AAAA_AAAA),
    np.uint64(0xCCCC_CCCC_CCCC_CCCC),
    np.uint64(0xF0F0_F0F0_F0F0_F0F0),
    np.uint64(0xFF00_FF00_FF00_FF00),
    np.uint64(0xFFFF_0000_FFFF_0000),
    np.uint64(0xFFFF_FFFF_0000_0000),
]


def packed_variables(count: int) -> list[np.ndarray]:
    """The `count` variables as packed bit arrays over all 2^count assignments: bit j of the array (bit j % 64 of word
    j // 64) is bit i of j for variable i. With fewer than 6 variables the 64 bits of the single word repeat the table."""
    words = 1 << max(count - 6, 0)
    index = np.arange(words, dtype=np.int64)  # (words,)
    out = []
    for i in range(count):
        if i < 6:
            out.append(np.full(words, LOW_PATTERNS[i], dtype=np.uint64))  # (words,)
        else:
            out.append(np.where((index >> (i - 6)) & 1 == 1, ONES, ZERO).astype(np.uint64))  # (words,)
    return out  # count x (words,)


def completion_family(t: int, k: int, black: int) -> np.ndarray:
    """Completions of a prefix of k cells, as indices of the free cells (bit i is x_{-t+k+i}): every setting of the cells
    x_{-t+k} .. x_{-1} between the cut and column 0, with a right half x_0 .. x_t of at most `black` black cells."""
    gap = t - k  # free cells left of column 0
    rights = [0]
    for size in range(1, black + 1):
        rights += [sum(1 << m for m in cells) for cells in itertools.combinations(range(t + 1), size)]
    return np.array([low + (right << gap) for right in rights for low in range(1 << gap)], dtype=np.int64)  # (m,)


@dataclass
class Scan:
    """The result of one streaming pass at (t, k): the prefixes grouped by the digest of their subfunction, and for
    each family of completions the prefixes grouped by their values on it."""

    t: int
    k: int
    classes: dict[bytes, list[int]] = field(default_factory=dict)
    signatures: dict[str, dict[bytes, list[int]]] = field(default_factory=dict)

    @property
    def count(self) -> int:
        """N_L(t, k), once the merges are confirmed by `merged_classes`."""
        return len(self.classes)


def _digest(data: bytes) -> bytes:
    return hashlib.blake2b(data, digest_size=16).digest()


def scan(t: int, k: int, families: dict[str, np.ndarray] | None = None, block_bits: int = 18,
         progress: bool = False) -> Scan:
    """Stream the 2^k prefixes of c_t in blocks of 2^b, b the number of prefix cells next to the cut that are
    bit-sliced (so that a block has about 2^block_bits rows), and group them by subfunction and by signature."""
    if not 1 <= k <= 2 * t:
        raise ValueError("need 1 <= k <= 2t")
    families = families or {}
    free = 2 * t + 1 - k
    b = max(0, min(k - 1, block_bits - free))
    width = 1 << free  # entries of one subfunction
    variables = packed_variables(free + b)  # (free + b) x (words,)
    sliced_prefix = variables[free:]  # b x (words,), prefix cells x_{-t+k-b} .. x_{-t+k-1}
    free_cells = variables[:free]  # free x (words,), cells x_{-t+k} .. x_t
    result = Scan(t, k, {}, {name: {} for name in families})
    blocks = 1 << (k - b - 1)
    words = variables[0].shape[0]
    for high in tqdm(range(blocks), desc=f"t={t} k={k} blocks", file=sys.stderr, disable=not progress):
        scalar_prefix = high << 1  # bits 1 .. k - b - 1 of the prefix; bit 0 (x_{-t}) is 0
        row: list[np.ndarray | np.uint64] = [ONES if (scalar_prefix >> i) & 1 else ZERO for i in range(k - b)]
        row += list(sliced_prefix) + list(free_cells)  # 2t + 1 entries
        center = cs.step_slices(row, t)[0]  # (words,) or a scalar
        center = np.broadcast_to(center, (words,)).astype(np.uint64)  # (words,)
        bits = np.unpackbits(center.view(np.uint8), bitorder="little")[: width << b]  # (2^(free+b),)
        bits = bits.reshape(1 << b, width)  # (2^b, 2^free), row j: sliced prefix cells = bits of j
        if free >= 6:
            rows = center.reshape(1 << b, width // 64)  # (2^b, 2^free / 64)
            keys = [(_digest(r.tobytes()), _digest((~r).tobytes())) for r in rows]
        else:
            keys = [(_digest(r.tobytes()), _digest((1 - r).tobytes())) for r in bits]
        sigs = {name: np.packbits(bits[:, fam], axis=1) for name, fam in families.items()}  # each (2^b, ceil(m/8))
        for j in range(1 << b):
            prefix = scalar_prefix | (j << (k - b))
            for flip in (0, 1):
                result.classes.setdefault(keys[j][flip], []).append(prefix | flip)
            for name, sig in sigs.items():
                row_sig = sig[j]  # (ceil(m/8),)
                m = families[name].shape[0]
                comp = np.packbits(1 - np.unpackbits(row_sig, count=m))  # (ceil(m/8),)
                result.signatures[name].setdefault(row_sig.tobytes(), []).append(prefix)
                result.signatures[name].setdefault(comp.tobytes(), []).append(prefix | 1)
    return result


def subfunction(t: int, k: int, prefix: int) -> np.ndarray:
    """The subfunction of one prefix as an array of bools over the 2^(2t+1-k) completions, cell by cell (no packing)."""
    free = 2 * t + 1 - k
    row: list[np.ndarray | np.bool_] = [np.bool_((prefix >> i) & 1) for i in range(k)]
    row += cs.variable_slices(free)  # 2t + 1 entries
    center = cs.step_slices(row, t)[0]  # (2^free,) or a scalar
    return np.broadcast_to(center, (1 << free,)).astype(bool)  # (2^free,)


def merged_classes(result: Scan) -> list[list[int]]:
    """The classes of more than one prefix, each confirmed by comparing the subfunctions exactly."""
    out = []
    for members in result.classes.values():
        if len(members) > 1:
            first = subfunction(result.t, result.k, members[0])  # (2^free,)
            for other in members[1:]:
                if not np.array_equal(first, subfunction(result.t, result.k, other)):
                    raise AssertionError("digest collision")
            out.append(sorted(members))
    return sorted(out)


def misses(result: Scan, name: str) -> list[tuple[int, int]]:
    """Pairs of prefixes with different subfunctions and the same values on the family `name`."""
    cls = {p: key for key, members in result.classes.items() for p in members}
    out = []
    for members in result.signatures[name].values():
        for p, q in itertools.combinations(sorted(members), 2):
            if cls[p] != cls[q]:
                out.append((p, q))
    return sorted(out)


def family_values(t: int, k: int, family: np.ndarray, progress: bool = False) -> np.ndarray:
    """c_t at every prefix and every completion of `family`, with the prefix cells bit-sliced and each completion a row
    of constants."""
    # family: (m,)
    free = 2 * t + 1 - k
    variables = packed_variables(k)  # k x (words,)
    words = variables[0].shape[0]
    out = np.zeros((1 << k, family.shape[0]), dtype=bool)  # (2^k, m)
    for col, completion in enumerate(tqdm(family.tolist(), desc=f"t={t} k={k} completions", file=sys.stderr,
                                          disable=not progress)):
        row: list[np.ndarray | np.uint64] = list(variables)
        row += [ONES if (completion >> i) & 1 else ZERO for i in range(free)]  # 2t + 1 entries
        center = np.broadcast_to(cs.step_slices(row, t)[0], (words,)).astype(np.uint64)  # (words,)
        out[:, col] = np.unpackbits(center.view(np.uint8), bitorder="little")[: 1 << k].astype(bool)
    return out  # (2^k, m)


def greedy_order(values: np.ndarray) -> list[int]:
    """Columns of `values` in an order that refines the partition of its rows fast: each next column is the first of
    those that leave the fewest pairs of rows unseparated. Stops when every class is a single row, or no column helps."""
    # values: (n, m)
    n = values.shape[0]
    label = np.zeros(n, dtype=np.int64)  # (n,), the class of each row
    order: list[int] = []
    live = np.arange(n)  # (L,), the rows in classes of two or more
    while live.size:
        lab = label[live]  # (L,)
        sort = np.argsort(lab, kind="stable")  # (L,)
        live, lab = live[sort], lab[sort]
        starts = np.flatnonzero(np.r_[True, lab[1:] != lab[:-1]])  # (c,)
        sizes = np.diff(np.r_[starts, lab.size])  # (c,)
        ones = np.add.reduceat(values[live].astype(np.int64), starts, axis=0)  # (c, m)
        zeros = sizes[:, None] - ones  # (c, m)
        pairs = (ones * (ones - 1) // 2 + zeros * (zeros - 1) // 2).sum(axis=0)  # (m,)
        best = int(np.argmin(pairs))
        if pairs[best] == int((sizes * (sizes - 1) // 2).sum()):
            return order
        order.append(best)
        _, label = np.unique(label * 2 + values[:, best], return_inverse=True)
        counts = np.bincount(label)  # (classes,)
        live = np.flatnonzero(counts[label] >= 2)
    return order


def family_count(t: int, k: int, black: int, progress: bool = False) -> tuple[int, list[list[int]]]:
    """N_L(t, k) exactly, through a family: prefixes with different values on `completion_family(t, k, black)` have
    different subfunctions, and within each group of equal values the subfunctions are compared in full by
    `subfunction`. Returns the count and the classes of more than one prefix."""
    values = family_values(t, k, completion_family(t, k, black), progress)  # (2^k, m)
    keys = np.packbits(values, axis=1)  # (2^k, ceil(m / 8))
    _, inverse, counts = np.unique(keys, axis=0, return_inverse=True, return_counts=True)
    inverse = inverse.ravel()  # (2^k,)
    count = int(counts.shape[0])
    merged: list[list[int]] = []
    for group in tqdm(np.flatnonzero(counts > 1).tolist(), desc=f"t={t} k={k} groups", file=sys.stderr,
                      disable=not progress):
        members = np.flatnonzero(inverse == group).tolist()
        classes: dict[bytes, list[int]] = {}
        for p in members:
            classes.setdefault(np.packbits(subfunction(t, k, p)).tobytes(), []).append(p)
        count += len(classes) - 1
        merged += [sorted(c) for c in classes.values() if len(c) > 1]
    return count, sorted(merged)


def stripe_prefix(t: int, k: int, wall: int, tail: int = 0) -> int:
    """The prefix of k cells x_{-t} .. x_{-t+k-1} that alternates from x_{-t} to a black cell at `wall` (x_wall = 1,
    x_{wall-1} = 0, ...) and carries the bits of `tail` on the cells right of the wall (bit 0 is x_{wall+1})."""
    out = 0
    for i in range(k):
        cell = -t + i
        bit = (wall - cell) % 2 == 0 if cell <= wall else (tail >> (cell - wall - 1)) & 1 == 1
        out |= int(bit) << i
    return out


def constant_of(t: int, k: int, prefix: int) -> int | None:
    """0 or 1 when the prefix fixes c_t for every completion, else None."""
    return cs.constant_value(subfunction(t, k, prefix).astype(np.uint8))


def black_run(prefix: int, end: int) -> int:
    """The length of the alternating run of the prefix that ends with a black cell at bit `end` (bit i is x_{-t+i}),
    0 when that cell is white."""
    length = 0
    while end - length >= 0 and (prefix >> (end - length)) & 1 == (1 if length % 2 == 0 else 0):
        length += 1
    return length


def stripe_fixes(t: int, wall: int) -> int | None:
    """The value of c_t when x_{-t} .. x_wall alternate and x_wall = 1, if it is the same for every setting of the cells
    x_{wall+1} .. x_t (bit-sliced, packed), else None."""
    free = t - wall
    variables = packed_variables(free)  # free x (words,)
    row: list[np.ndarray | np.uint64] = [ONES if (wall - cell) % 2 == 0 else ZERO for cell in range(-t, wall + 1)]
    row += variables  # 2t + 1 entries
    center = np.broadcast_to(cs.step_slices(row, t)[0], variables[0].shape)  # (words,)
    if np.all(center == ONES):
        return 1
    if np.all(center == ZERO):
        return 0
    return None


def certificate(t: int) -> tuple[int, list[int]]:
    """The completions, in the order `greedy_order` gives, that the Lean module `LeftCut` splits the prefixes of
    k = t - 2 cells by, as indices of the free cells (bit i is x_{-2+i}); taken from the family with at most one black
    cell in the right half when it separates every prefix, else from the family with at most two (or three). Returns
    the number of black cells allowed and the completions; raises ValueError when no family separates, as for t = 18."""
    k = t - 2
    for black in (1, 2, 3):
        family = completion_family(t, k, black)  # (m,)
        values = family_values(t, k, family)  # (2^k, m)
        order = greedy_order(values)
        labels = np.unique(np.packbits(values[:, order], axis=1), axis=0)  # (distinct signatures, ceil(len / 8))
        if labels.shape[0] == 1 << k:
            return black, [int(family[i]) for i in order]
    raise ValueError("no family of at most three black cells separates the prefixes")


def lean_certificates(t_max: int) -> str:
    """The Lean lines of `LeftCut` that hold the certificates for t = 3 .. t_max and their kernel checks."""
    lines = []
    for t in range(3, t_max + 1):
        black, order = certificate(t)
        cells = "cell" if black == 1 else "cells"
        lines.append(f"/-- The {len(order)} completions for `t = {t}`, from the family with at most {black} black {cells} "
                     "in the right half. -/")
        lines.append(f"def cutCert{t} : List Nat := {order}")
        lines.append("")
        lines.append(f"theorem cutCert{t}_check : cutCheck {t} cutCert{t} = true := by")
        lines.append("  decide +kernel")
        lines.append("")
    lines.append("/-- The certificate for `t`, empty outside the range checked. -/")
    lines.append("def cutCertList : Nat → List Nat")
    lines += [f"  | {t} => cutCert{t}" for t in range(3, t_max + 1)]
    lines.append("  | _ => []")
    lines.append("")
    return "\n".join(lines)


def word(prefix: int, k: int) -> str:
    """The prefix as the string x_{-t} .. x_{-t+k-1}."""
    return "".join(str((prefix >> i) & 1) for i in range(k))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--t", type=int, required=True)
    parser.add_argument("--k", type=int, default=0)
    parser.add_argument("--black", type=int, default=-1, help="also test completion families with up to this many "
                        "black cells in the right half (needs k <= t)")
    parser.add_argument("--merges", action="store_true", help="print the merged prefixes")
    parser.add_argument("--lean", action="store_true", help="print the certificates of LeftCut for t = 3 .. --t")
    parser.add_argument("--stripes", action="store_true", help="for the walls -1 .. -6 and t <= --t, whether the "
                        "stripe to the wall fixes c_t (at most 28 free cells)")
    parser.add_argument("--family-count", type=int, default=-1, help="count N_L(t, k) exactly through the family with "
                        "at most this many black cells, instead of streaming every prefix")
    args = parser.parse_args()
    if args.lean:
        print(lean_certificates(args.t))
        return
    t, k = args.t, args.k
    if args.stripes:
        for wall in tqdm(range(-1, -7, -1), desc="walls", file=sys.stderr):
            values = {s: stripe_fixes(s, wall) for s in range(max(3, -wall), t + 1) if s - wall <= 28}
            fixed = [s for s, v in values.items() if v is not None]
            print(f"wall {wall}: c_t fixed for t in {fixed} (value {set(values[s] for s in fixed)}), "
                  f"checked t = {min(values)} .. {max(values)}")
        return
    if args.family_count >= 0:
        count, merged = family_count(t, k, args.family_count, progress=True)
        print(f"N_L({t}, {k}) = {count} of 2^{k} = {1 << k}; classes of more than one prefix: {len(merged)}")
        for members in merged:
            value = constant_of(t, k, members[0])
            runs = " ".join(f"{word(p, k)} ({black_run(p, k - 1)}, {black_run(p, k - 2)})" for p in members)
            print(f"    fixes {value}: {runs}")
        return
    fams = {f"black<={w}": completion_family(t, k, w) for w in range(args.black + 1)}
    result = scan(t, k, fams, progress=True)
    merged = merged_classes(result)
    print(f"N_L({t}, {k}) = {result.count} of 2^{k} = {1 << k}; classes of more than one prefix: {len(merged)}")
    if args.merges:
        for members in merged:
            print("   ", " ".join(word(p, k) for p in members))
    for name, fam in fams.items():
        found = misses(result, name)
        print(f"family {name} ({fam.shape[0]} completions): {len(result.signatures[name])} signatures, "
              f"{len(found)} pairs not separated")
        for p, q in found[:40]:
            print("   ", word(p, k), word(q, k))


if __name__ == "__main__":
    main()
