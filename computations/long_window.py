"""The center column's first 65,536 or 262,144 cells, the checkpoints and the new factor of `LongWindow.lean` and
`WideWindow.lean`.

If the center column had period P from time T, every factor starting at a time t >= T would occur again at t + P.
So if the factor of length L at time M occurs nowhere before M, no eventual period has T + P <= M. This module computes
the first n center cells, n = N = 65,536 or n = WIDE = 262,144, the least L for which the factor at n - L is new, and
the packed rows at the checkpoints, every 16,384 steps, that let the kernel check the simulation in parts of 16,384
steps. It prints them as the Lean module reads them: rows with the seed at bit n, stored shifted down by n - t.

    python -m computations.long_window                  # the bound and the factor
    python -m computations.long_window --lean           # the literals of LongWindow.lean
    python -m computations.long_window --wide           # the same for 262,144 cells, about 1 min
    python -m computations.long_window --wide --lean    # the literals of WideWindow.lean
"""

from __future__ import annotations

import argparse
import sys
import time

from tqdm.auto import tqdm


N = 65536  # center cells, and the bit of the seed in a packed row
WIDE = 262144  # the same for `WideWindow.lean`
CHUNK = 16384


def simulate(n: int = N) -> tuple[int, dict[int, int]]:
    """The center cells c(0) .. c(n - 1) as bits of one number, and the packed rows at the checkpoints, the seed at bit
    n."""
    row, bits, checkpoints = 1 << n, 0, {}
    for t in range(n):
        if t and t % CHUNK == 0:
            checkpoints[t] = row
        bits |= ((row >> n) & 1) << t
        row = (row << 1) ^ (row | (row >> 1))
    return bits, checkpoints


def new_factor(bits: int, n: int = N) -> int:
    """The least L such that the factor of length L at n - L occurs at no earlier position."""
    for length in range(1, n):
        last = (bits >> (n - length)) & ((1 << length) - 1)
        if all(((bits >> j) & ((1 << length) - 1)) != last for j in range(n - length)):
            return length
    raise ValueError("no new factor")


def lean_literals(n: int = N) -> str:
    """The definitions `bigBits` and `rowAt16384` .. `rowAt49152` of `LongWindow.lean`, or for n = WIDE, `wideBits`
    and `wideAt16384` .. `wideAt245760` of `WideWindow.lean`."""
    bits, checkpoints = simulate(n)
    row_name, bits_name = ("rowAt", "bigBits") if n == N else ("wideAt", "wideBits")
    lines = []
    for t, row in tqdm(checkpoints.items(), desc="checkpoints", file=sys.stderr, leave=False):
        lines.append(f"/-- The packed row at time {t}, the seed at bit {n}. -/\n"
                     f"def {row_name}{t} : Nat :=\n  0x{row >> (n - t):x} <<< {n - t}\n")
    lines.append(f"/-- The center cells c(0) .. c({n - 1}), bit t being c(t). -/\ndef {bits_name} : Nat :=\n"
                 f"  0x{bits:x}\n")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--lean", action="store_true", help="print the Lean literals")
    parser.add_argument("--wide", action="store_true", help="262,144 cells instead of 65,536")
    args = parser.parse_args()
    started = time.perf_counter()
    n = WIDE if args.wide else N
    if args.lean:
        print(lean_literals(n))
        return
    bits, _ = simulate(n)
    length = new_factor(bits, n)
    print(f"the factor of length {length} at time {n - length} is new among the first {n} center cells, so an "
          f"eventual period from time T with period P has T + P >= {n - length + 1}")
    print(f"({time.perf_counter() - started:.0f} s)")


if __name__ == "__main__":
    main()
