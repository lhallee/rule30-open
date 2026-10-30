"""A finite certificate for the period-four lock: a set of right-half windows that the driven rule cannot leave.

Drive a finite right half with the center repeating `word`, as in `right_half.py`. A state of width W holds columns
1 .. W, bit j being column j + 1; the phase of time t is t mod p, and the center applied from t to t + 1 is
word[t mod p]. This module computes

- the phase table of a run: the value of each column at each phase when it is constant over the run's second part,
- the forced lattice, the cells constant at a phase and equal across several starts, and which of its cells the rule
  derives from the forced cells one phase earlier in three-valued logic,
- the GF(2) affine hull of the windows a run visits at each phase, its constraints and how often the rule leaves it,
- the greatest family of windows, one set per phase, inside a seed condition, that the rule maps into the next
  phase's set for both values of column W + 1, the time at which a run first enters it, and the windows from which
  entry is forced whatever column W + 1 does.

The seed `core` asks columns 1 .. k to read the empty start's phase table. The seed `jen` asks only that column 1 take
some fixed value at each white phase (where the word reads 0), which is what masked Jen (the kit's
`Rule30MaskedJen.masked_jen`) needs; its set is the union of the sets of every such assignment.

    python -m computations.lock_certificate 0001 --widths 14 16 --steps 20000
    python -m computations.lock_certificate 0011 --seed jen --widths 12 14 16 18 20 --hull-widths --entry-steps 12000
"""

from __future__ import annotations

import argparse
import sys
import numpy as np

from tqdm.auto import tqdm

from computations.right_half import random_starts


def spacetime(word: str, start: int, steps: int, width: int) -> np.ndarray:
    """Columns 1 .. width of the right half `start` driven by `word`, at times 0 .. steps - 1; out[t, j] is column
    j + 1 at time t."""
    centers = [int(bit) for bit in word]
    mask, size = (1 << width) - 1, (width + 7) // 8
    windows = bytearray()
    row = start
    for t in range(steps):
        windows += (row & mask).to_bytes(size, "little")
        row = ((row << 1) | centers[t % len(centers)]) ^ (row | (row >> 1))
    packed = np.frombuffer(bytes(windows), dtype=np.uint8).reshape(steps, size)  # (steps, size)
    return np.unpackbits(packed, axis=1, bitorder="little")[:, :width]  # (steps, width)


def window_codes(rows: np.ndarray) -> np.ndarray:
    """Each row of cells as the integer whose bit j is column j + 1; at most 62 columns."""
    # rows: (n, width)
    weights = np.int64(1) << np.arange(rows.shape[1], dtype=np.int64)  # (width,)
    return rows.astype(np.int64) @ weights  # (n,)


def phase_table(word: str, start: int, steps: int, burn: int, width: int) -> np.ndarray:
    """table[j, ph] is column j + 1 at phase ph when it is constant over times burn .. steps - 1, and -1 otherwise."""
    period = len(word)
    rows = spacetime(word, start, steps, width)[burn:]  # (steps - burn, width)
    phases = np.arange(burn, steps) % period  # (steps - burn,)
    table = np.full((width, period), -1, dtype=np.int8)  # (width, period)
    for ph in range(period):
        cells = rows[phases == ph]  # (n, width)
        constant = (cells == cells[0]).all(axis=0)  # (width,)
        table[constant, ph] = cells[0, constant]
    return table  # (width, period)


def column_text(table: np.ndarray, column: int) -> str:
    """Column `column` (from 1) of a phase table as text, `*` where it varies."""
    # table: (width, period)
    return "".join("*" if value < 0 else str(value) for value in table[column - 1])


def forced_lattice(word: str, starts: list[int], steps: int, burn: int, width: int) -> tuple[np.ndarray, bool]:
    """The cells constant at a phase in every start's table with the same value, and whether the tables agree."""
    tables = np.stack([phase_table(word, start, steps, burn, width) for start in starts])  # (starts, width, period)
    agree = (tables == tables[0]).all(axis=0)  # (width, period)
    forced = np.where(agree, tables[0], -1).astype(np.int8)  # (width, period)
    return forced, bool(agree.all())  # (width, period)


def underived_cells(word: str, table: np.ndarray) -> list[list[int]]:
    """Per phase ph, the columns whose forced value at phase ph + 1 the rule does not derive from the forced cells at
    phase ph, reading unforced cells (and the cell beyond the table) as unknown, with OR(1, unknown) = 1 and
    XOR(unknown, x) = unknown."""
    # table: (width, period)
    width, period = table.shape
    failures = []
    for ph in range(period):
        before, after = table[:, ph].astype(np.int64), table[:, (ph + 1) % period]  # (width,) each
        left = np.concatenate([[int(word[ph])], before[:-1]])  # (width,), the center left of column 1
        right = np.concatenate([before[1:], [-1]])  # (width,)
        either = np.where((before == 1) | (right == 1), 1, np.where((before == 0) & (right == 0), 0, -1))  # (width,)
        derived = np.where((left < 0) | (either < 0), -1, left ^ either)  # (width,)
        failures.append([j + 1 for j in range(width) if after[j] >= 0 and derived[j] != after[j]])
    return failures


def echelon(vectors: np.ndarray) -> list[int]:
    """A basis of the GF(2) span of the integers `vectors`, with distinct leading bits, largest first."""
    # vectors: (n,)
    basis: dict[int, int] = {}
    for vector in np.unique(vectors).tolist():
        while vector:
            lead = vector.bit_length() - 1
            if lead not in basis:
                basis[lead] = vector
                break
            vector ^= basis[lead]
    return [basis[lead] for lead in sorted(basis, reverse=True)]


def reduce(points: np.ndarray, basis: list[int]) -> np.ndarray:
    """Each point with the span of `basis` (as `echelon` returns it) reduced away; zero exactly on the span."""
    # points: (n,)
    out = points.copy()  # (n,)
    for vector in basis:
        lead = vector.bit_length() - 1
        out ^= ((out >> lead) & 1) * vector
    return out  # (n,)


def affine_hull(codes: np.ndarray) -> tuple[int, list[int]]:
    """The affine span of the windows `codes` over GF(2), as a base point and a basis of its directions."""
    # codes: (n,)
    base = int(codes[0])
    return base, echelon(codes ^ base)


def constraint_columns(basis: list[int], width: int) -> list[int]:
    """The columns that occur in some affine constraint of a hull with directions `basis`: the support of the space
    orthogonal to the directions."""
    rows = np.array([[(vector >> j) & 1 for j in range(width)] for vector in basis], dtype=np.uint8).reshape(-1, width)
    pivots: list[int] = []
    for column in range(width):
        r = len(pivots)
        below = np.flatnonzero(rows[r:, column]) + r  # (m,)
        if below.size == 0:
            continue
        rows[[r, below[0]]] = rows[[below[0], r]]
        others = np.flatnonzero(rows[:, column])  # (m,)
        rows[others[others != r]] ^= rows[r]
        pivots.append(column)
    support = set()
    for free in sorted(set(range(width)) - set(pivots)):
        support.add(free)  # the orthogonal vector of a free column has it and the pivots whose row has it
        support.update(pivot for r, pivot in enumerate(pivots) if rows[r, free])
    return sorted(column + 1 for column in support)


def step_windows(states: np.ndarray, center: int, beyond: int, width: int) -> np.ndarray:
    """One step of every window in `states`, with `center` left of column 1 and `beyond` right of column `width`."""
    # states: (n,)
    left = (states << 1) | center  # (n,), bit j holds column j
    right = (states >> 1) | (beyond << (width - 1))  # (n,), bit j holds column j + 2
    return (left ^ (states | right)) & ((1 << width) - 1)  # (n,)


def hull_exit_fraction(word: str, hulls: list[tuple[int, list[int]]], width: int) -> list[float]:
    """Per phase, the fraction of (hull point, value of column width + 1) pairs whose successor leaves the next
    phase's hull."""
    period = len(word)
    fractions = []
    for ph in range(period):
        base, basis = hulls[ph]
        points = np.array([base], dtype=np.int64)  # (1,)
        for vector in basis:
            points = np.concatenate([points, points ^ vector])  # (2^k,)
        next_base, next_basis = hulls[(ph + 1) % period]
        successors = np.concatenate(
            [step_windows(points, int(word[ph]), beyond, width) for beyond in (0, 1)])  # (2^(k + 1),)
        fractions.append(float((reduce(successors ^ next_base, next_basis) != 0).mean()))
    return fractions


def core_seed(table: np.ndarray, columns: int) -> list[dict[int, int]]:
    """Per phase, columns 1 .. `columns` set to the values of the phase table, which must be constant there."""
    # table: (width, period)
    if (table[:columns] < 0).any():
        raise ValueError(f"columns 1 .. {columns} of the table are not all constant at every phase")
    return [{j + 1: int(table[j, ph]) for j in range(columns)} for ph in range(table.shape[1])]


def jen_seeds(word: str) -> list[list[dict[int, int]]]:
    """Every assignment of column 1 at the white phases (where the word reads 0), each a seed that fixes nothing at the
    black phases. The union of their greatest invariant sets is invariant, and on it column 1 is periodic at the white
    times whatever value it locks to."""
    white = [ph for ph, bit in enumerate(word) if bit == "0"]
    seeds = []
    for values in range(1 << len(white)):
        fixed = {ph: (values >> i) & 1 for i, ph in enumerate(white)}
        seeds.append([{1: fixed[ph]} if ph in fixed else {} for ph in range(len(word))])
    return seeds


def seed_mask(states: np.ndarray, condition: dict[int, int]) -> np.ndarray:
    """Which windows meet `condition`, a map from columns to values."""
    # states: (n,)
    mask = np.ones(states.shape, dtype=bool)  # (n,)
    for column, value in condition.items():
        mask &= ((states >> (column - 1)) & 1) == value
    return mask  # (n,)


def successor_table(word: str, width: int) -> np.ndarray:
    """out[ph, beyond, s] is the successor of window s at phase ph when column width + 1 is `beyond`."""
    states = np.arange(1 << width, dtype=np.int64)  # (2^W,)
    return np.stack([np.stack([step_windows(states, int(word[ph]), beyond, width) for beyond in (0, 1)])
                     for ph in range(len(word))])  # (period, 2, 2^W)


def greatest_invariant_set(word: str, seed: list[dict[int, int]], width: int) -> tuple[np.ndarray, int]:
    """The largest family of windows, one set per phase inside the seed, that the rule maps into the next phase's set
    for both values of column width + 1, as membership masks; and the number of passes that found it. Each pass
    removes, phase by phase, the windows with a successor outside the current next set."""
    period = len(word)
    states = np.arange(1 << width, dtype=np.int64)  # (2^W,)
    successors = successor_table(word, width)  # (period, 2, 2^W)
    member = np.stack([seed_mask(states, seed[ph]) for ph in range(period)])  # (period, 2^W)
    passes = 0
    with tqdm(desc=f"passes at width {width}", file=sys.stderr, leave=False) as bar:
        changed = True
        while changed:
            changed, passes = False, passes + 1
            for ph in range(period):
                keep = member[ph] & member[(ph + 1) % period][successors[ph]].all(axis=0)  # (2^W,)
                if not np.array_equal(keep, member[ph]):
                    member[ph], changed = keep, True
            bar.update()
    return member, passes  # (period, 2^W)


def is_invariant(word: str, member: np.ndarray, width: int) -> bool:
    """Whether every window of each phase's set steps into the next phase's set for both values of column width + 1."""
    # member: (period, 2^W)
    period = len(word)
    for ph in range(period):
        inside = np.flatnonzero(member[ph]).astype(np.int64)  # (n,)
        for beyond in (0, 1):
            if not member[(ph + 1) % period][step_windows(inside, int(word[ph]), beyond, width)].all():
                return False
    return True


def forced_entry(word: str, member: np.ndarray) -> np.ndarray:
    """The windows from which the run enters `member` whatever the values of column width + 1: the least family
    containing `member` that holds every window whose successors for both values lie in it."""
    # member: (period, 2^W)
    period, size = member.shape
    successors = successor_table(word, size.bit_length() - 1)  # (period, 2, 2^W)
    forced = member.copy()  # (period, 2^W)
    changed = True
    while changed:
        changed = False
        for ph in range(period):
            grown = forced[ph] | forced[(ph + 1) % period][successors[ph]].all(axis=0)  # (2^W,)
            if not np.array_equal(grown, forced[ph]):
                forced[ph], changed = grown, True
    return forced  # (period, 2^W)


# The certificates that `Rule30Open.Columns.PeriodFourCertificate` checks: the word and the width.
CERTIFICATES = [("0001", 16), ("0011", 14), ("0111", 14)]


def certificate_tables(word: str, width: int) -> dict:
    """The `jen` certificate of the word at this width as a labelled trap of `lock_chain.relabeled_tables`: the
    nonempty greatest invariant sets of the assignments of column 1 at the white phases, which must be exactly one."""
    from computations import lock_chain
    found = []
    for seed in jen_seeds(word):
        member, _ = greatest_invariant_set(word, seed, width)  # (period, 2^W)
        if member.any():
            found.append({(ph, int(w)) for ph in range(len(word)) for w in np.flatnonzero(member[ph])})
    assert len(found) == 1, "one assignment of the white phases carries the certificate"
    return lock_chain.relabeled_tables(word, width, found[0])


def lean_certificates() -> str:
    """The trap entries of `Rule30Open.Columns.PeriodFourCertificate`, with their kernel checks."""
    from computations import lock_chain
    out = []
    for word, width in CERTIFICATES:
        name = f"cert{word}"
        out.append(lock_chain.lean_entry(certificate_tables(word, width), name)
                   + f"\ntheorem {name}_check : {name}.check = true := by decide +kernel\n")
    return "\n".join(out)


def entry_time(word: str, member: np.ndarray, start: int, steps: int) -> int | None:
    """The first time before `steps` at which the window of the right half `start` lies in the set of its phase."""
    # member: (period, 2^W)
    period, size = member.shape
    width = size.bit_length() - 1
    codes = window_codes(spacetime(word, start, steps, width))  # (steps,)
    inside = np.flatnonzero(member[np.arange(steps) % period, codes])  # (n,)
    return int(inside[0]) if inside.size else None


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("word", nargs="?", default="")
    parser.add_argument("--lean", action="store_true", help="print the traps of PeriodFourCertificate.lean")
    parser.add_argument("--widths", type=int, nargs="+", default=[14, 16], help="widths of the invariant set")
    parser.add_argument("--steps", type=int, default=20000)
    parser.add_argument("--burn", type=int, default=1000, help="tables and hulls read times burn .. steps - 1")
    parser.add_argument("--seed", choices=["core", "jen"], default="core")
    parser.add_argument("--core-columns", type=int, default=3)
    parser.add_argument("--hull-widths", type=int, nargs="*", default=[12, 14, 16, 18])
    parser.add_argument("--lattice-width", type=int, default=120)
    parser.add_argument("--entry-steps", type=int, default=6000)
    args = parser.parse_args()
    if args.lean:
        print(lean_certificates())
        return

    word, period = args.word, len(args.word)
    starts = random_starts(30, 64)

    table = phase_table(word, 0, args.steps, args.burn, args.lattice_width)  # (lattice_width, period)
    print(f"phase table of {word} from the empty start, times {args.burn} .. {args.steps - 1}:")
    for column in range(1, 13):
        print(f"  column {column:>2}: {column_text(table, column)}")

    forced, agree = forced_lattice(word, starts[:3], args.steps, args.burn, args.lattice_width)  # (lattice_width, period)
    counts = (forced >= 0).sum(axis=1)  # (lattice_width,)
    last = int(np.flatnonzero(counts)[-1]) + 1
    print(f"forced lattice over 3 starts (tables {'agree' if agree else 'differ'}): cells per column 1 .. {last}: "
          f"{counts[:last].tolist()}, total {int(counts.sum())}; none in columns {last + 1} .. {args.lattice_width}")
    for ph, columns in enumerate(underived_cells(word, forced[:last + 1])):
        print(f"  phase {ph} to {(ph + 1) % period}: forced cells not derived at columns {columns}")

    phases = np.arange(args.burn, args.steps) % period  # (steps - burn,)
    for width in args.hull_widths:
        codes = np.concatenate([window_codes(spacetime(word, start, args.steps, width)[args.burn:])
                                for start in starts[:7]])  # (7 (steps - burn),)
        hulls = [affine_hull(codes[np.tile(phases, 7) == ph]) for ph in range(period)]
        dims = [len(basis) for _, basis in hulls]
        columns = sorted({c for _, basis in hulls for c in constraint_columns(basis, width)})
        exits = hull_exit_fraction(word, hulls, width)
        print(f"affine hull at width {width}, 7 starts: dimension {dims}, constraints {[width - d for d in dims]} in "
              f"columns {columns[0]} .. {columns[-1]}; exit fractions {[round(f, 3) for f in exits]}")

    seeds = [core_seed(table, args.core_columns)] if args.seed == "core" else jen_seeds(word)
    for width in tqdm(args.widths, desc="widths", file=sys.stderr):
        members = []
        for seed in seeds:
            member, passes = greatest_invariant_set(word, seed, width)  # (period, 2^W)
            members.append(member)
            if member.any() or args.seed == "core":
                print(f"width {width}, seed {seed}: greatest invariant set sizes {member.sum(axis=1).tolist()} after "
                      f"{passes} passes")
        union = np.logical_or.reduce(members)  # (period, 2^W)
        sizes = union.sum(axis=1).tolist()
        print(f"width {width}: union sizes {sizes}, invariant by enumeration: {is_invariant(word, union, width)}")
        if not any(sizes):
            continue
        print(f"  entry forced whatever column {width + 1} does from {forced_entry(word, union).sum(axis=1).tolist()} "
              f"of {1 << width} windows per phase")
        times = [entry_time(word, union, start, args.entry_steps) for start in starts]
        entered = [t for t in times if t is not None]
        missing = [i for i, t in enumerate(times) if t is None]
        print(f"  {len(entered)} of {len(starts)} starts enter within {args.entry_steps} steps, the latest at "
              f"{max(entered) if entered else None}; starts that do not: {missing}")
        for i in missing[:3]:
            outlier = phase_table(word * 2, starts[i], args.steps, args.burn, width)  # (width, 2 period)
            print(f"  start {i}, columns 1 .. {width} at {2 * period} phases: "
                  + " ".join(column_text(outlier, column) for column in range(1, width + 1)))


if __name__ == "__main__":
    main()
