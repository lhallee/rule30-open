"""The center column's first 65,536 cells, the checkpoints and the new factor of `LongWindow.lean`.

If the center column had period P from time T, every factor starting at a time t >= T would occur again at t + P.
So if the factor of length L at time M occurs nowhere before M, no eventual period has T + P <= M. This module computes
the first N = 65,536 center cells, the least L for which the factor at N - L is new, and the packed rows at the
checkpoints 16,384, 32,768 and 49,152 that let the kernel check the simulation in four parts. It prints them as the
Lean module reads them: rows with the seed at bit N, stored shifted down by N - t.

    python -m computations.long_window          # the bound and the factor
    python -m computations.long_window --lean   # the literals of LongWindow.lean
"""

from __future__ import annotations

import argparse
import time


N = 65536  # center cells, and the bit of the seed in a packed row
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


def lean_literals() -> str:
    """The definitions `bigBits` and `rowAt16384` .. `rowAt49152` of `LongWindow.lean`."""
    bits, checkpoints = simulate()
    lines = []
    for t, row in checkpoints.items():
        lines.append(f"/-- The packed row at time {t}, the seed at bit {N}. -/\n"
                     f"def rowAt{t} : Nat :=\n  0x{row >> (N - t):x} <<< {N - t}\n")
    lines.append(f"/-- The center cells c(0) .. c({N - 1}), bit t being c(t). -/\ndef bigBits : Nat :=\n  0x{bits:x}\n")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--lean", action="store_true", help="print the Lean literals")
    args = parser.parse_args()
    started = time.perf_counter()
    if args.lean:
        print(lean_literals())
        return
    bits, _ = simulate()
    length = new_factor(bits)
    print(f"the factor of length {length} at time {N - length} is new among the first {N} center cells, so an "
          f"eventual period from time T with period P has T + P >= {N - length + 1}")
    print(f"({time.perf_counter() - started:.0f} s)")


if __name__ == "__main__":
    main()
