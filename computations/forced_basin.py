"""The forced-entry basin of the kit's ether-and-wall family in the game of a word of period four.

Drive a right half with the center repeating 0001, 0011 or 0111, as in `absorption.py`. A node of the game of width K
is a phase and a window: columns 1 .. K, column j + 1 at bit j, with the center reading word[phase] now. One step needs
column K + 1, which the game leaves free. A window certifies entry into the family (`family_target`) when for an
alignment (j0, s) of the word and a depth k with column j0 + k a B3 column and k + 13 <= K, columns 1 .. k carry the
ether aligned with the drive and columns k + 1 .. k + 13 form one of the kit's 109 wall states at the ether phase. The
forced basin (`basin_ranks`) is the least set of nodes that holds these and every node whose successors for both
values of column K + 1 lie in it; the rank of a node is the round in which it joins, so a half whose window lies in the
basin at rank r is in the family by step r, whatever its cells beyond column K.

`absorption.family_cut`, which [the kit's absorption reach](../findings/columns/kit-absorption-reach.md) uses, keeps a
member of the family whose wall is cut off by the window; that cut does not certify entry, and the target here does.
The forced entry into the certificate of `lock_certificate.py` (`forced_entry`), a different target, gives the same
set for every word at widths 13 to 20 (`certificate_basin`). `entry_times` compares, for every right half of a few
cells, the step at which it enters the family with the step at which its window first lies in the basin.
`lean_module` writes `Rule30Open.Columns.ForcedBasin18`: the sets of nodes of rank at most n at which the kernel's
rounds are cut, which the kernel recomputes.

    python -m computations.forced_basin shares --widths 12,13,14,15,16,17,18,19,20,21,22   # about 2 minutes
    python -m computations.forced_basin shares --widths 23,24   # about 8 minutes
    python -m computations.forced_basin times --cells 16 --width 20 --steps 2000   # under a minute
    python -m computations.forced_basin compare --widths 13,14,15,16,17,18,19,20   # under a minute
    python -m computations.forced_basin lean --width 18 --size 16 > Rule30Open/Columns/ForcedBasin18.lean
"""

from __future__ import annotations

import argparse
import sys
import time
import numpy as np

from tqdm.auto import tqdm

from computations import absorption as ab
from computations import lock_certificate
from computations.lock_certificate import step_windows

WORDS = ab.WORDS
WALL_CELLS = ab.WALL_CELLS


def family_target(word: str, width: int, wall: np.ndarray) -> np.ndarray:
    """out[phase, v] says that window v at that phase is in the family for some alignment and depth whose wall fits in
    the window, so that the cells beyond column `width` do not matter."""
    # wall: (4, 2^13)
    n = 1 << width
    windows = np.arange(n, dtype=np.int64)  # (n,)
    out = np.zeros((4, n), dtype=bool)  # (4, n)
    for phase in range(4):
        for j0, shift in ab.ALIGNMENTS[word]:
            psi = (phase + shift) % 4  # the ether phase of now
            ether = sum(ab.ether(j0 + p, psi) << (p - 1) for p in range(1, width + 1))
            for k in range(width - WALL_CELLS + 1):
                if (j0 + k) % 7 == 2:
                    strip = (windows >> k) & ((1 << WALL_CELLS) - 1)  # (n,)
                    out[phase] |= (((windows ^ ether) & ((1 << k) - 1)) == 0) & wall[psi][strip]
    return out  # (4, n)


def successors(word: str, width: int) -> np.ndarray:
    """out[phase, beyond, v] is the window after v at that phase when column width + 1 reads `beyond`."""
    windows = np.arange(1 << width, dtype=np.int64)  # (n,)
    return np.stack([np.stack([step_windows(windows, int(word[phase]), beyond, width).astype(np.int32)
                               for beyond in (0, 1)]) for phase in range(4)])  # (4, 2, n)


def basin_ranks(word: str, width: int, target: np.ndarray) -> np.ndarray:
    """The rank of every node in the forced basin of `target`, -1 outside it. Rank 0 is the target; a node joins at
    rank r + 1 when both its successors have rank at most r and it has none. All phases join in the same round, so the
    rank is the latest step at which the free column can delay entry."""
    # target: (4, n)
    succ = successors(word, width)  # (4, 2, n)
    rank = np.where(target, 0, -1).astype(np.int16)  # (4, n)
    with tqdm(desc=f"{word} width {width}", file=sys.stderr, leave=False) as bar:
        r = 0
        while True:
            inside = rank >= 0  # (4, n)
            joins = [~inside[ph] & inside[(ph + 1) % 4][succ[ph, 0]] & inside[(ph + 1) % 4][succ[ph, 1]]
                     for ph in range(4)]  # 4 x (n,)
            if not any(j.any() for j in joins):
                return rank  # (4, n)
            r += 1
            for ph in range(4):
                rank[ph, joins[ph]] = r
            bar.update()


def rank_histogram(rank: np.ndarray) -> np.ndarray:
    """out[r] counts the nodes of rank r, all phases together."""
    # rank: (4, n)
    return np.bincount(rank[rank >= 0].astype(np.int64))  # (max rank + 1,)


def forward_rank(word: str, width: int, target: np.ndarray, phase: int, window: int, depth: int) -> int:
    """The rank of one node by a forward search, independent of `basin_ranks`: the least n such that no play stays out
    of the target at steps 0 .. n, by the set of nodes that plays reach at step n while out of it so far; -1 if some
    play stays out for `depth` steps."""
    # target: (4, n)
    front = set() if target[phase, window] else {(phase, window)}
    for n in range(depth + 1):
        if not front:
            return n
        nxt = set()
        for ph, v in front:
            for beyond in (0, 1):
                w = int(step_windows(np.array([v], dtype=np.int64), int(word[ph]), beyond, width)[0])
                if not target[(ph + 1) % 4, w]:
                    nxt.add(((ph + 1) % 4, w))
        front = nxt
    return -1


def entry_times(word: str, cells: int, phase: int, rank: np.ndarray, steps: int,
                wall: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """For every right half of at most `cells` cells, driven from `phase`, the first step at which it is in the family
    (any depth up to 51, `absorption.family_depth`) and the first step at which its window lies in the basin whose
    ranks are `rank`; -1 if not within `steps`. A half in the family at a depth whose wall does not fit in the window
    keeps that depth, so its window may never reach the basin."""
    # rank: (4, 2^width)
    width = rank.shape[1].bit_length() - 1
    rows = np.zeros((1 << cells, (cells + steps + 2) // 64 + 2), dtype=np.uint64)  # (2^cells, words)
    rows[:, 0] = np.arange(1 << cells, dtype=np.uint64)
    family = np.full(1 << cells, -1, dtype=np.int64)  # (2^cells,)
    basin = np.full(1 << cells, -1, dtype=np.int64)  # (2^cells,)
    mask = np.uint64((1 << width) - 1)
    for t in tqdm(range(steps), desc=f"{word} halves of {cells} cells", file=sys.stderr, leave=False):
        ph = (t + phase) % 4
        live = np.flatnonzero((family < 0) | (basin < 0))  # (m,)
        if live.size == 0:
            break
        low = rows[live, 0]  # (m,)
        hit = (basin[live] < 0) & (rank[ph][(low & mask).astype(np.int64)] >= 0)  # (m,)
        basin[live[hit]] = t
        entered = (family[live] < 0) & (ab.family_depth(word, low, ph, wall) >= 0)  # (m,)
        family[live[entered]] = t
        active = min(rows.shape[1], (cells + t + 2) // 64 + 1)
        rows[live, :active] = ab.step_rows(rows[live, :active], int(word[ph]))
    return family, basin  # (2^cells,), (2^cells,)


def certificate_basin(word: str, width: int) -> np.ndarray:
    """The forced entry into the `jen` certificate of `lock_certificate.py` (the union over the assignments of column 1
    at the white phases), which [the certificate finding](../findings/columns/period-four-certificate.md) measures."""
    union = np.zeros((4, 1 << width), dtype=bool)  # (4, n)
    for seed in lock_certificate.jen_seeds(word):
        member, _ = lock_certificate.greatest_invariant_set(word, seed, width)  # (4, n)
        union |= member
    return lock_certificate.forced_entry(word, union)  # (4, n)


def compact_bits(inside: np.ndarray) -> int:
    """The nodes of `inside` as one integer: phase p, window v at bit p 2^K + v."""
    # inside: (4, n)
    packed = np.packbits(inside.reshape(-1).astype(np.uint8), bitorder="little")  # (4 n / 8,)
    return int.from_bytes(packed.tobytes(), "little")


LEAN_WORDS = {"0001": ("w0001", "A0001", 3), "0011": ("w0011", "A0011", 2), "0111": ("w0111", "A0111", 1)}


def chunks(rounds: int, size: int) -> list[int]:
    """`rounds` cut into nearly equal parts of at most `size`."""
    parts = -(-rounds // size)
    return [rounds // parts + (1 if i < rounds % parts else 0) for i in range(parts)]


def lean_wide(word: str, width: int, size: int, wall: np.ndarray) -> str:
    """The checkpoints, their kernel checks and the theorem `forcedBasin_<word>_<width>` of
    `Rule30Open.Columns.ForcedBasin18`: the basin's rounds cut into parts of at most `size`, each part checked from the
    stored set of the last."""
    rank = basin_ranks(word, width, family_target(word, width, wall))  # (4, n)
    inside = rank >= 0  # (4, n)
    rounds, counts = int(rank.max()), inside.sum(axis=1).tolist()
    w, a, psi = LEAN_WORDS[word]
    parts = chunks(rounds, size)
    ends = np.cumsum(parts).tolist()
    target = f"(target {a} {width})"
    lines, start = [], target
    for i, end in enumerate(ends[:-1]):
        name = f"ck{word}_{width}_{i + 1}"
        lines.append(f"/-- The nodes of rank at most {end}. -/\ndef {name} : Nat :=\n  "
                     f"{hex(compact_bits(inside & (rank <= end)))}\n")
        lines.append(f"theorem {name}_ok :\n    basinFrom {w} {width} {target} {start} {parts[i]} = "
                     f"spread {width} {name} := by\n  decide +kernel\n")
        start = f"(spread {width} {name})"
    last = f"basinFrom {w} {width} {target} {start} {parts[-1]}"
    lines.append(f"theorem counts{word}_{width} :\n    (List.range 4).map (countPhase {width} ({last})) =\n"
                 f"      {counts} := by\n  decide +kernel\n")
    split = " + ".join(str(x) for x in parts)
    adds = ", ".join(["basinFrom_add"] * (len(parts) - 1))
    oks = ", ".join(f"ck{word}_{width}_{i + 1}_ok" for i in range(len(parts) - 1))
    lines.append(f"theorem forcedBasin_{word}_{width} :\n    Covers {w} {a} {width} {rounds} (basin {w} {a} {width} "
                 f"{rounds}) {counts} :=\n"
                 f"  covers_of_counts rfl {a}_ok \u27e8{psi}, rfl\u27e9 (by decide) {rounds} _ (by\n"
                 f"    rw [show basin {w} {a} {width} {rounds} = {last} by\n"
                 f"      unfold basin\n      rw [show {rounds} = {split} from rfl, {adds}]\n      rw [{oks}]]\n"
                 f"    exact counts{word}_{width})\n")
    return "\n".join(lines)


WIDE_HEADER = """module

public import Rule30Open.Columns.ForcedBasin

/-!
# The forced basin of the period-four family at width {width}

`ForcedBasin` at width {width}, for the three words. The kernel computes the basin's rounds as there, cut into parts
of at most {size} rounds: each part starts from the stored set where the last one ended and is checked to end at the
next stored set (`ck<word>_{width}_<i>_ok`), and the last part ends with the counts. `ForcedBasin.basinFrom_add` joins
the parts, so the theorems are about the same set as at widths 14 and 16, the basin after all its rounds. Written by
`python -m computations.forced_basin lean --width {width} --size {size}`.

The natural-language argument is `ForcedBasin{width}.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata Rule30Ether ForcedBasin

set_option Elab.async false

"""


def lean_module(width: int, size: int, wall: np.ndarray) -> str:
    """The module `Rule30Open.Columns.ForcedBasin<width>` for the three words."""
    body = "\n".join(lean_wide(word, width, size, wall) for word in WORDS)
    return WIDE_HEADER.format(width=width, size=size) + body + "\nend Rule30Open\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("mode", choices=["shares", "times", "compare", "lean"])
    parser.add_argument("--widths", default="12,13,14,15,16,17,18,19,20,21,22")
    parser.add_argument("--words", nargs="+", default=list(WORDS), choices=list(WORDS))
    parser.add_argument("--cells", type=int, default=16, help="times: every right half of up to this many cells")
    parser.add_argument("--width", type=int, default=20, help="times, lean: the window width of the basin")
    parser.add_argument("--steps", type=int, default=2000, help="times: steps searched")
    parser.add_argument("--phase", type=int, default=0, help="times: the phase of the drive at step 0")
    parser.add_argument("--size", type=int, default=16, help="lean: the most rounds of one kernel check")
    args = parser.parse_args()

    started = time.perf_counter()
    wall = ab.kit_wall()  # (4, 2^13)
    if args.mode == "shares":
        for word in args.words:
            for width in [int(x) for x in args.widths.split(",")]:
                target = family_target(word, width, wall)  # (4, n)
                rank = basin_ranks(word, width, target)  # (4, n)
                inside = rank >= 0  # (4, n)
                hist = rank_histogram(rank)  # (r + 1,)
                quart = np.searchsorted(np.cumsum(hist), [0.5 * hist.sum(), 0.9 * hist.sum()]) if hist.size else []
                print(f"{word} K={width}: target {target.sum(axis=1).tolist()}, basin {inside.sum(axis=1).tolist()} "
                      f"of {1 << width} per phase, share {', '.join(f'{x:.4f}' for x in inside.mean(axis=1))}; "
                      f"largest rank {rank.max(axis=1).tolist()}; rank median and 90% {list(map(int, quart))}",
                      flush=True)
    elif args.mode == "times":
        for word in args.words:
            rank = basin_ranks(word, args.width, family_target(word, args.width, wall))  # (4, n)
            family, basin = entry_times(word, args.cells, args.phase, rank, args.steps, wall)  # (2^cells,) each
            both = basin >= 0  # (2^cells,)
            gap = family[both] - basin[both]  # (m,)
            print(f"{word}, every right half of up to {args.cells} cells from phase {args.phase}, basin of width "
                  f"{args.width} (largest rank {int(rank.max())}): {int((family < 0).sum())} not in the family by "
                  f"step {args.steps}; {int(both.sum())} reach the basin, all of them in the family by "
                  f"{int(gap.max())} steps later (median {int(np.median(gap))}); "
                  f"{int(((family >= 0) & ~both).sum())} enter the family at a depth whose wall does not fit in the "
                  f"window and are not in the basin by step {args.steps}")
            for q in (0.5, 0.9, 0.99, 0.999, 1.0):
                f, b = int(np.quantile(family[family >= 0], q)), int(np.quantile(basin[both], q))
                print(f"  quantile {q}: family entry {f}, basin entry {b}, difference {f - b}")
    elif args.mode == "compare":
        for word in args.words:
            for width in [int(x) for x in args.widths.split(",")]:
                basin = basin_ranks(word, width, family_target(word, width, wall)) >= 0  # (4, n)
                other = certificate_basin(word, width)  # (4, n)
                print(f"{word} K={width}: basin {basin.sum(axis=1).tolist()}, forced entry into the certificate "
                      f"{other.sum(axis=1).tolist()}, the same set: {bool(np.array_equal(basin, other))}", flush=True)
    else:
        sys.stdout.write(lean_module(args.width, args.size, wall))
    print(f"({time.perf_counter() - started:.0f} s)", file=sys.stderr if args.mode == "lean" else sys.stdout)


if __name__ == "__main__":
    main()
