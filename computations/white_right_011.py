"""The certificate behind `Rule30Open.Columns.WhiteRightHalf011`: against a white right half, no left half within
depth W < 32,752 keeps the center on 011 through time W + 16, in any phase.

Fix the center column c(t) = word[(t + phase) mod len(word)] and a white right half at time 0. The right half evolves
as the half driven by c, so its column 1 is known at every time; the center's update forces column -1, and Rule 30 is
permutive in its left input, so columns 1 and 0 rebuild every column to the left by one recurrence,
x(t, -k - 1) = x(t + 1, -k) xor (x(t, -k) or x(t, -k + 1)), started at k = 0 with column 1 as x(t, 1). The row at time
0 that results is Psi, the kit's `Rule30Realization.lc` at time 0 (`coupled.psi` computes the same row). A finite
row whose center follows c through time T has the cells of Psi at the depths 1 .. T (the kit's `unique` and
`lc_congr`), so a left half within depth W loses c by the first black depth of Psi beyond W.

The Lean module computes Psi as numbers, one bit per time, in the same steps as `psi_bits` here:
- `column_one(word, phase, steps)`: column 1 of the driven white right half at times 0 .. steps - 1 (the Lean
  `colOneN`, through the kit's `stepN`);
- `centers(word, phase, steps)`: the center column at times 0 .. steps - 1 (`centerN`);
- `psi_bits(word, phase, depth)`: Psi at depths 0 .. depth, bit d the depth d (`psiBitsC`, through the reconstruction
  `colC` and `WhiteRightHalf.psiLoop`);
- `gaps_check(row, depth, gap, starts)`: the kit-free check `WhiteRightHalf.gapsCheck`, that every window of `gap`
  depths starting at a depth in 1 .. starts holds a black cell.

    python -m computations.white_right_011              # Psi of 011 to depth 32,768, its runs and the check, seconds
    python -m computations.white_right_011 --lean       # the census section of the Lean module
"""

from __future__ import annotations

import argparse

WORD = "011"
DEPTH = 32768  # depths of Psi the kernel computes
GAP = 16  # every window of GAP depths holds a black cell
STARTS = DEPTH - GAP  # the windows start at depths 1 .. STARTS, so the theorem holds for W < STARTS


def letter(word: str, phase: int, t: int) -> int:
    """The center at time t."""
    return int(word[(t + phase) % len(word)])


def step_right(c: int, r: int) -> int:
    """The kit's `stepN c r`: one step of the right half r (bit i the column i + 1) beside the center cell c."""
    full = c | (r << 1)
    return full ^ ((full >> 1) | (full >> 2))


def column_one(word: str, phase: int, steps: int) -> int:
    """Column 1 of the white right half driven by the center, at times 0 .. steps - 1, bit t the time t."""
    out, r = 0, 0
    for t in range(steps):
        out |= (r & 1) << t
        r = step_right(letter(word, phase, t), r)
    return out


def centers(word: str, phase: int, steps: int) -> int:
    """The center column at times 0 .. steps - 1, bit t the time t."""
    return sum(letter(word, phase, t) << t for t in range(steps))


def psi_bits(word: str, phase: int, depth: int) -> int:
    """Psi of the white right half at depths 0 .. depth, bit d the depth d (depth 0 is the center at time 0): the
    columns rebuilt leftward from column 1 (times below `depth`) and column 0 (times up to `depth`), keeping bit 0 of
    each, as the Lean `psiBitsC`."""
    prev, cur = column_one(word, phase, depth), centers(word, phase, depth + 1)
    acc = 0
    for k in range(1, depth + 2):  # cur is column 1 - k
        acc |= (cur & 1) << k
        prev, cur = cur, (cur >> 1) ^ (cur | prev)
    return acc >> 1


def runs_and(z: int, g: int) -> int:
    """Bit j set when bits j .. j + g of z all are (the Lean `runsAnd`)."""
    out = z
    for i in range(1, g + 1):
        out &= z >> i
    return out


def gaps_check(row: int, depth: int, gap: int, starts: int) -> bool:
    """The Lean `gapsCheck`: no `gap` depths in a row, starting at a depth in 1 .. starts, without a black cell of
    `row` among the depths 1 .. depth."""
    return runs_and(((1 << (depth + 1)) - 1) ^ row, gap - 1) & (((1 << (starts + 1)) - 1) ^ 1) == 0


def longest_white_run(row: int, depth: int) -> int:
    """The longest run of white depths among 1 .. depth that ends in a black cell at a depth up to `depth`."""
    best, run = 0, 0
    for d in range(1, depth + 1):
        if (row >> d) & 1:
            best, run = max(best, run), 0
        else:
            run += 1
    return best


def lean_section(depth: int = DEPTH, gap: int = GAP, starts: int = STARTS) -> str:
    """The census section of the Lean module: one kernel check of the gaps per phase."""
    out = []
    for phase in range(len(WORD)):
        out.append(f"theorem gaps011_{phase} : gapsCheck (psiBitsC (col011 {phase}) {depth}) {depth} {gap} {starts} = "
                   f"true := by\n  decide +kernel")
    return "\n\n".join(out)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--depth", type=int, default=DEPTH)
    parser.add_argument("--gap", type=int, default=GAP)
    parser.add_argument("--lean", action="store_true", help="print the census section of the Lean module")
    args = parser.parse_args()
    starts = args.depth - args.gap
    if args.lean:
        print(lean_section(args.depth, args.gap, starts))
        return
    for phase in range(len(WORD)):
        row = psi_bits(WORD, phase, args.depth)
        black = (row >> 1).bit_count()
        print(f"{WORD} phase {phase}: {black} black cells at depths 1 to {args.depth}, the last at "
              f"{row.bit_length() - 1}; longest white run {longest_white_run(row, args.depth)}; every {args.gap} "
              f"depths from 1 to {starts + args.gap - 1} hold a black cell: {gaps_check(row, args.depth, args.gap, starts)}")


if __name__ == "__main__":
    main()
