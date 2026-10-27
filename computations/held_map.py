"""The period-two integer map H(U) = (U >> 1) xor (U or (U << 1)), and how long a finite half keeps its condition.

If the center column alternated from some time on, some positive integer U would have H^t(U) odd at every odd t
(Lean: `period_two_integer` in `Rule30Open.PeriodTwo.HeldColumn`). For each support M, the integers with exactly M bits,
this search finds every U's first failure and reports the latest. Bit 0 of H^t(U) depends only on bits 0 .. t of U,
so the search tracks H^t(U) modulo 2^(limit + 1 - t) in 64-bit words.

    python -m computations.held_map 24   # the latest first failure for every support up to 24, both phases
"""

from __future__ import annotations

import argparse
import sys
import numpy as np

from tqdm.auto import tqdm


ONE = np.uint64(1)


def held(U: int) -> int:
    """One step of the held map on a Python integer: Rule 30 left of a column held at 0, bit j the cell j + 1 away."""
    return (U >> 1) ^ (U | (U << 1))


def first_failures(support: int, phase: int, limit: int = 63) -> np.ndarray:
    """For every U with exactly `support` bits, the first t with t + phase odd at which H^t(U) is even, or `limit` when
    there is none before it. Phase 0 checks the odd steps, phase 1 the even ones."""
    assert limit <= 63, "the parity at step t needs bits 0 .. t, and the words hold 64"
    U = np.arange(1 << (support - 1), 1 << support, dtype=np.uint64)  # (n,)
    V = U & np.uint64((1 << (limit + 1)) - 1)  # (n,), H^t(U) modulo 2^(limit + 1 - t)
    failure = np.full(U.size, limit, dtype=np.int64)  # (n,)
    alive = np.ones(U.size, dtype=bool)  # (n,)
    for t in range(limit):
        if (t + phase) % 2 == 1:
            dead = alive & ((V & ONE) == 0)  # (n,)
            failure[dead] = t
            alive &= ~dead
        V = ((V >> ONE) ^ (V | (V << ONE))) & np.uint64((1 << (limit - t)) - 1)  # (n,)
    return failure  # (n,)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("max_support", type=int)
    max_support = parser.parse_args().max_support

    for support in tqdm(range(1, max_support + 1), desc="supports", file=sys.stderr):
        latest = [int(first_failures(support, phase).max()) for phase in (0, 1)]
        print(f"support {support}: latest first failure at step {latest[0]} (odd checks), {latest[1]} (even checks); "
              f"2M = {2 * support}")


if __name__ == "__main__":
    main()
