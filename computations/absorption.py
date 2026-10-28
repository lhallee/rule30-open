"""Absorption of the right half into the kit's ether-and-wall family, for every small right half and for infinite ones.

Drive a right half with the center repeating 0001, 0011 or 0111 in some phase, as in `right_half.py`. The kit's family
(`Rule30Ether.InFamily`) is a set of states that the driven rule never leaves and on which column 1 is periodic: columns
1 .. k carry the ether, aligned with the center, column k is a B3 column, and columns k + 1 .. k + 13 form a wall state.
The kit's open `Absorption` says every finitely supported right half enters it, in every phase; masked Jen then excludes
the word as the center's eventual period (`Rule30Ether.least_period_four_of_absorption`).

The kit lists its 109 wall states. Here they are computed: the greatest set of 13-cell strips right of a B3 column that
the rule maps into itself for both values of the cell beyond, with the first cell equal to B4 wherever B3 is white,
has exactly one terminal strongly connected component, and that component is the kit's wall. The greatest set itself
is the wall of the certificate in `lock_certificate.py` (its core seed for 0001 is the ether's B1 B2 B3).

Each run also reports how entry times are spread (`tail`), and names each periodic half that never enters with the
step at which it is the pure ether aligned with the drive (`pure_ether`), or -1.

`--words 0101` drives with the alternating center, whose alignments with the ether are (3, 0) and (3, 2). `shield` puts
the ether on columns 1 to 120 and random cells beyond, and reports when and at what depth each half enters and how far
its disturbance moves in. `lean_entries` writes the entry step and depth of every right half of a few cells, the lists
that `Rule30Open.Columns.EmptyRight` checks in the kernel.

    python -m computations.absorption census --cells 16 --steps 4000   # every right half of up to 16 cells
    python -m computations.absorption infinite --count 2000 --steps 4000 --max-period 11   # random and periodic halves
    python -m computations.absorption starts --steps 12000   # the 31 starts of the locking finding
    python -m computations.absorption census --cells 14 --words 0101   # the alternating center: few halves enter
    python -m computations.absorption shield --count 300 --steps 3000   # the ether on columns 1 to 120, random beyond
"""

from __future__ import annotations

import argparse
import sys
import textwrap
import time
import numpy as np

from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components
from tqdm.auto import tqdm

from computations.game import necklaces
from computations.lock_certificate import step_windows
from computations.right_half import random_starts


ETHER = ["0011", "0110", "1101", "0101", "0011", "0001", "0001"]  # B1 B2 B3 B4 B5 c c at phases 0 .. 3, the kit's table
ALIGNMENTS = {"0001": [(5, 0), (6, 0)], "0011": [(0, 0), (1, 3), (4, 0)], "0111": [(2, 2)],  # the kit's A0001 .. A0111
              "0101": [(3, 0), (3, 2)]}  # the kit's aligned_0101_3, and its shift by two steps
WORDS = ("0001", "0011", "0111")
WALL_CELLS = 13
ONE = np.uint64(1)


def ether(j: int, phase: int) -> int:
    """Ether column j mod 7 at phase `phase` mod 4."""
    return int(ETHER[j % 7][phase % 4])


def aligned(word: str, j0: int, shift: int) -> bool:
    """Whether the word is the ether column j0 shifted by `shift` in time, as the kit's `aligned` asks."""
    return all(ether(j0, psi + shift) == int(word[psi]) for psi in range(4))


def wall_graph() -> tuple[np.ndarray, np.ndarray]:
    """The successors of every 13-cell strip right of a B3 column, for both cells beyond, and the seed that asks the
    first cell to be B4 where B3 is white."""
    states = np.arange(1 << WALL_CELLS, dtype=np.int64)  # (2^13,)
    successors = np.stack([np.stack([step_windows(states, ether(2, ph), beyond, WALL_CELLS) for beyond in (0, 1)])
                           for ph in range(4)])  # (4, 2, 2^13)
    seed = np.stack([np.ones(states.size, dtype=bool) if ether(2, ph) else (states & 1) == ether(3, ph)
                     for ph in range(4)])  # (4, 2^13)
    return successors, seed  # (4, 2, 2^13), (4, 2^13)


def greatest_wall() -> np.ndarray:
    """The greatest set of wall states, one set per phase inside the seed, that the rule maps into the next phase's
    set for both cells beyond."""
    successors, member = wall_graph()  # (4, 2, 2^13), (4, 2^13)
    changed = True
    while changed:
        changed = False
        for ph in range(4):
            keep = member[ph] & member[(ph + 1) % 4][successors[ph]].all(axis=0)  # (2^13,)
            if not np.array_equal(keep, member[ph]):
                member[ph], changed = keep, True
    return member  # (4, 2^13)


def kit_wall() -> np.ndarray:
    """The unique terminal strongly connected component of the greatest wall: the kit's 109 wall states."""
    successors, _ = wall_graph()  # (4, 2, 2^13)
    member = greatest_wall().reshape(-1)  # (4 2^13,)
    size = 1 << WALL_CELLS
    source = np.concatenate([ph * size + np.arange(size) for ph in range(4) for _ in (0, 1)])  # (8 2^13,)
    target = np.concatenate([((ph + 1) % 4) * size + successors[ph, beyond] for ph in range(4) for beyond in (0, 1)])
    inside = member[source] & member[target]  # (8 2^13,)
    graph = csr_matrix((np.ones(int(inside.sum()), dtype=np.int8), (source[inside], target[inside])),
                       shape=(4 * size, 4 * size))
    _, label = connected_components(graph, directed=True, connection="strong")  # (4 2^13,)
    leaving = label[source] != label[target]  # (8 2^13,), a move out of its component
    exits = np.zeros(label.max() + 1, dtype=bool)  # (components,)
    exits[label[source][member[source] & leaving]] = True
    sinks = [c for c in np.unique(label[member]).tolist() if not exits[c]]
    assert len(sinks) == 1, f"the greatest wall has {len(sinks)} terminal components"
    return (label == sinks[0]).reshape(4, size)  # (4, 2^13)


def family_depth(word: str, low: np.ndarray, phase: int, wall: np.ndarray) -> np.ndarray:
    """For each right half whose columns 1 .. 64 are the bits of `low`, at drive phase `phase` (the center reads
    word[phase] now), the least depth k at which it is in the family with that wall, or -1."""
    # low: (n,), bit j is column j + 1
    depth = np.full(low.size, -1, dtype=np.int64)  # (n,)
    for j0, shift in ALIGNMENTS[word]:
        psi = (phase + shift) % 4  # the ether phase of now
        pattern = np.uint64(sum(ether(j0 + p, psi) << (p - 1) for p in range(1, 65)))
        differ = low ^ pattern  # (n,)
        for k in range(64 - WALL_CELLS + 1):
            if (j0 + k) % 7 != 2:
                continue
            ether_ok = (differ & np.uint64((1 << k) - 1)) == 0  # (n,), columns 1 .. k carry the ether
            strip = ((low >> np.uint64(k)) & np.uint64((1 << WALL_CELLS) - 1)).astype(np.int64)  # (n,)
            found = ether_ok & wall[psi][strip] & ((depth < 0) | (depth > k))  # (n,)
            depth[found] = k
    return depth  # (n,)


def step_rows(rows: np.ndarray, center: int) -> np.ndarray:
    """One step of every right half in `rows`, bit i across its 64-bit words being column i + 1, with `center` left of
    column 1."""
    # rows: (n, words)
    left = rows << ONE  # (n, words)
    left[:, 1:] |= rows[:, :-1] >> np.uint64(63)
    left[:, 0] |= np.uint64(center)
    right = rows >> ONE  # (n, words)
    right[:, :-1] |= rows[:, 1:] << np.uint64(63)
    return left ^ (rows | right)  # (n, words)


def absorb(word: str, rows: np.ndarray, phase: int, steps: int, wall: np.ndarray, reach: int) -> np.ndarray:
    """The first time before `steps` at which each right half of `rows` is in the family, or -1. `reach` bounds the
    columns that are not white at time 0, so only the words they can have reached by time t are stepped."""
    # rows: (n, words)
    times = np.full(rows.shape[0], -1, dtype=np.int64)  # (n,)
    index = np.arange(rows.shape[0])  # (n,)
    rows = rows.copy()  # (n, words)
    for t in range(steps):
        inside = family_depth(word, rows[:, 0], (t + phase) % 4, wall) >= 0  # (n,)
        times[index[inside]] = t
        rows, index = rows[~inside], index[~inside]
        if index.size == 0:
            break
        active = min(rows.shape[1], (reach + t + 2) // 64 + 1)
        rows[:, :active] = step_rows(rows[:, :active], int(word[(t + phase) % 4]))
    return times  # (n,)


def pure_ether(word: str, rows: np.ndarray, phase: int, steps: int) -> np.ndarray:
    """The first time before `steps` at which columns 1 .. 64 of each right half in `rows` are the ether aligned with
    the drive, or -1. A half that is periodic with period 7 beyond the columns the center has reached is then the
    aligned ether everywhere, which the rule keeps with period 4 in time, so it never enters the family."""
    # rows: (n, words)
    times = np.full(rows.shape[0], -1, dtype=np.int64)  # (n,)
    rows = rows.copy()  # (n, words)
    for t in range(steps):
        psi = (t + phase) % 4
        for j0, shift in ALIGNMENTS[word]:
            pattern = np.uint64(sum(ether(j0 + p, psi + shift) << (p - 1) for p in range(1, 65)))
            times[(times < 0) & (rows[:, 0] == pattern)] = t
        rows = step_rows(rows, int(word[psi]))
    return times  # (n,)


def tail(times: np.ndarray) -> str:
    """The mean entry time and the fraction of halves still outside the family after 100, 200, 300 and 400 steps."""
    # times: (n,), -1 for a half that never entered
    outside = [float(((times > t) | (times < 0)).mean()) for t in (100, 200, 300, 400)]
    entered = times[times >= 0]  # (m,)
    mean = f"mean entry {entered.mean():.1f}" if entered.size else "no entry"
    return f"{mean}, outside after 100/200/300/400 steps: " + ", ".join(f"{x:.2g}" for x in outside)


def leading_ether(word: str, rows: np.ndarray, phase: int, span: int) -> np.ndarray:
    """For rows of cells (column j + 1 at index j) at drive phase `phase`, how many columns from column 1 carry the
    ether of the word's first alignment, up to `span`."""
    # rows: (n, cells), bool
    j0, shift = ALIGNMENTS[word][0]
    row = np.array([ether(j0 + p, phase + shift) for p in range(1, span + 1)], dtype=bool)  # (span,)
    differ = rows[:, :span] != row  # (n, span)
    return np.where(differ.any(axis=1), differ.argmax(axis=1), span)  # (n,)


def deep_depth(word: str, rows: np.ndarray, phase: int, wall: np.ndarray, span: int) -> np.ndarray:
    """`family_depth` for rows of cells at any depth k below `span`, not only within the first 64 columns: the deepest
    k at which each row is in the family, or -1."""
    # rows: (n, cells), bool
    weights = 1 << np.arange(WALL_CELLS)  # (13,)
    depth = np.full(rows.shape[0], -1, dtype=np.int64)  # (n,)
    for j0, shift in ALIGNMENTS[word]:
        psi = (phase + shift) % 4
        row = np.array([ether(j0 + p, psi) for p in range(1, span + 1)], dtype=bool)  # (span,)
        differ = rows[:, :span] != row  # (n, span)
        leading = np.where(differ.any(axis=1), differ.argmax(axis=1), span)  # (n,)
        for k in range(span - WALL_CELLS):
            if (j0 + k) % 7 == 2:
                strip = rows[:, k:k + WALL_CELLS].astype(np.int64) @ weights  # (n,)
                depth[(leading >= k) & wall[psi][strip]] = np.maximum(depth[(leading >= k) & wall[psi][strip]], k)
    return depth  # (n,)


def shield(word: str, ether_cells: int, count: int, phase: int, steps: int, wall: np.ndarray,
           rng: np.random.Generator) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Right halves that carry the aligned ether on columns 1 .. ether_cells and random cells beyond: the first step at
    which each is in the family at any depth (or -1), the deepest depth it has then, and how far its first column off
    the ether moved toward the center over the run."""
    j0, shift = ALIGNMENTS[word][0]
    cells = ether_cells + steps + 50
    rows = np.zeros((count, cells), dtype=bool)  # (count, cells)
    rows[:, :ether_cells] = [ether(j0 + p, phase + shift) for p in range(1, ether_cells + 1)]
    rows[:, ether_cells:] = rng.integers(0, 2, (count, cells - ether_cells)).astype(bool)
    entry = np.full(count, -1, dtype=np.int64)  # (count,)
    depth = np.full(count, -1, dtype=np.int64)  # (count,)
    front = np.full(count, ether_cells, dtype=np.int64)  # (count,), the fewest leading ether columns so far
    span = ether_cells + 40
    for t in range(steps):
        front = np.minimum(front, leading_ether(word, rows, (t + phase) % 4, ether_cells))
        deep = deep_depth(word, rows, (t + phase) % 4, wall, span)  # (count,)
        new = (entry < 0) & (deep >= 0)  # (count,)
        entry[new], depth[new] = t, deep[new]
        center = np.full((count, 1), word[(t + phase) % 4] == "1")  # (count, 1)
        left = np.concatenate([center, rows[:, :-1]], axis=1)  # (count, cells)
        right = np.concatenate([rows[:, 1:], np.zeros((count, 1), dtype=bool)], axis=1)  # (count, cells)
        rows = left ^ (rows | right)
    return entry, depth, ether_cells - front  # (count,) each


def entry_certificate(word: str, cells: int, phase: int, wall: np.ndarray, steps: int = 4000) -> list[tuple[int, int]]:
    """For each right half below 2^cells, its first step in the family and the least depth k at that step: the Lean
    lists `entries<word>_<phase>` of `SmallRight` in `EmptyRight.lean`."""
    rows = np.zeros((1 << cells, (cells + steps + 2) // 64 + 1), dtype=np.uint64)  # (2^cells, words)
    rows[:, 0] = np.arange(1 << cells, dtype=np.uint64)
    times = absorb(word, rows, phase, steps, wall, cells)  # (2^cells,)
    assert (times >= 0).all(), "a right half did not enter"
    entries = []
    for half, entry in enumerate(times.tolist()):
        row = rows[half:half + 1].copy()  # (1, words)
        for t in range(entry):
            row = step_rows(row, int(word[(t + phase) % 4]))
        entries.append((entry, int(family_depth(word, row[:, 0], (entry + phase) % 4, wall)[0])))
    return entries


def lean_entries(cells: int, wall: np.ndarray) -> str:
    """The Lean definitions `entries<word>_<phase>` of `entry_certificate`, as `EmptyRight.lean` has them."""
    lines = []
    for word in WORDS:
        for phase in range(4):
            pairs = [f"({t},\u00a0{k})" for t, k in entry_certificate(word, cells, phase, wall)]  # no break in a pair
            body = textwrap.wrap("[" + ", ".join(pairs) + "]", width=118, initial_indent="  ", subsequent_indent="   ")
            header = f"def entries{word}_{phase} : List (Nat \u00d7 Nat) :=\n"
            lines.append(header + "\n".join(body).replace("\u00a0", " "))
    return "\n".join(lines)


def census(word: str, cells: int, phase: int, steps: int, wall: np.ndarray) -> np.ndarray:
    """The first time each right half of at most `cells` cells, the integers below 2^cells, enters the family."""
    rows = np.zeros((1 << cells, (cells + steps + 2) // 64 + 1), dtype=np.uint64)  # (2^cells, words)
    rows[:, 0] = np.arange(1 << cells, dtype=np.uint64)
    return absorb(word, rows, phase, steps, wall, cells)  # (2^cells,)


def packed(bits: np.ndarray) -> np.ndarray:
    """Rows of cells, cell j + 1 at index j, packed into 64-bit words with column 1 at bit 0."""
    # bits: (n, cells)
    words = -(-bits.shape[1] // 64)
    padded = np.zeros((bits.shape[0], 64 * words), dtype=np.uint8)  # (n, 64 words)
    padded[:, :bits.shape[1]] = bits
    return np.packbits(padded, axis=1, bitorder="little").view(np.uint64)  # (n, words)


def periodic_halves(max_period: int, cells: int) -> tuple[list[str], np.ndarray]:
    """Every spatially periodic right half whose period word is a rotation of a primitive word of at most
    `max_period` cells, out to `cells` cells; cell j + 1 reads the word's letter j mod its length."""
    words = [u[r:] + u[:r] for p in range(1, max_period + 1) for u in necklaces(p) for r in range(p)]
    bits = np.array([[int(u[j % len(u)]) for j in range(cells)] for u in words], dtype=np.uint8)  # (n, cells)
    return words, packed(bits)  # (n, words)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("mode", choices=["census", "infinite", "starts", "shield"])
    parser.add_argument("--cells", type=int, default=12, help="census: every right half of up to this many cells")
    parser.add_argument("--steps", type=int, default=4000)
    parser.add_argument("--count", type=int, default=40, help="infinite: random halves per word and phase")
    parser.add_argument("--max-period", type=int, default=8, help="infinite: periods of the periodic halves")
    parser.add_argument("--words", nargs="+", default=list(WORDS), choices=sorted(ALIGNMENTS))
    args = parser.parse_args()

    started = time.perf_counter()
    wall = kit_wall()  # (4, 2^13)
    print(f"the kit's wall, computed: {wall.sum(axis=1).tolist()} states at phases 0 to 3, of "
          f"{greatest_wall().sum(axis=1).tolist()} in the greatest wall")
    rng = np.random.default_rng(30)
    for word in args.words:
        assert all(aligned(word, j0, shift) for j0, shift in ALIGNMENTS[word])
        for phase in tqdm(range(4), desc=word, file=sys.stderr, leave=False):
            if args.mode == "census":
                times = census(word, args.cells, phase, args.steps, wall)  # (2^cells,)
                latest = [int(times[:1 << n].max()) if (times[:1 << n] >= 0).all() else None
                          for n in range(1, args.cells + 1)]
                print(f"{word} phase {phase}: {int((times >= 0).sum())} of {times.size} right halves of up to "
                      f"{args.cells} cells enter within {args.steps} steps, the latest at {int(times.max())}; latest "
                      f"entry by cells: {latest}; {tail(times)}")
            elif args.mode == "shield":
                entry, depth, moved = shield(word, 120, args.count, phase, args.steps, wall, rng)  # (count,) each
                print(f"{word} phase {phase}: of {args.count} halves with the ether on columns 1 to 120 and random "
                      f"cells beyond, {int((entry >= 0).sum())} enter the family within {args.steps} steps, the latest "
                      f"at {int(entry.max())}, at depths {int(depth.min())} to {int(depth.max())} (median "
                      f"{int(np.median(depth))}); the first column off the ether moved in by at most "
                      f"{int(moved.max())} (mean {moved.mean():.1f})")
            elif args.mode == "starts":
                starts = random_starts(30, 64)
                bits = np.zeros((len(starts), args.steps + 70), dtype=np.uint8)  # (31, cells)
                bits[:, :64] = [[(start >> i) & 1 for i in range(64)] for start in starts]
                times = absorb(word, packed(bits), phase, args.steps, wall, 64)  # (31,)
                print(f"{word} phase {phase}: {int((times >= 0).sum())} of {len(starts)} starts of the locking "
                      f"finding enter, the latest at {int(times.max())}; starts 4, 8, 18 and 24 at "
                      f"{times[[4, 8, 18, 24]].tolist()}")
            else:
                cells = args.steps + 70
                random = packed(rng.integers(0, 2, (args.count, cells), dtype=np.uint8))  # (count, words)
                times = absorb(word, random, phase, args.steps, wall, cells)  # (count,)
                names, rows = periodic_halves(args.max_period, cells)  # (n, words)
                periodic = absorb(word, rows, phase, args.steps, wall, cells)  # (n,)
                missed = np.flatnonzero(periodic < 0)  # (m,)
                pure = pure_ether(word, rows[missed], phase, 8)  # (m,)
                print(f"{word} phase {phase}: {int((times >= 0).sum())} of {args.count} random infinite halves enter, "
                      f"the latest at {int(times.max())}, {tail(times)}; {int((periodic >= 0).sum())} of "
                      f"{periodic.size} periodic halves enter, the latest at {int(periodic.max())}; not entering, "
                      "with the step at which each is the aligned ether: "
                      + ", ".join(f"{names[i]} ({t})" for i, t in zip(missed.tolist(), pure.tolist())))
    print(f"({time.perf_counter() - started:.0f} s)")


if __name__ == "__main__":
    main()
