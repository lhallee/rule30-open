"""The period-two integer map H(U) = (U >> 1) xor (U or (U << 1)), and how long a finite half keeps its condition.

If the center column alternated from some time on, some positive integer U would have H^t(U) odd at every odd t
(Lean: `period_two_integer` in `Rule30Open.PeriodTwo.HeldColumn`). For each support M, the integers with exactly M bits,
this search finds every U's first failure and reports the latest. Bit 0 of H^t(U) depends only on bits 0 .. t of U,
so the search tracks H^t(U) modulo 2^(limit + 1 - t) in 64-bit words.

An eventual 0001 in the center column gives the same map a denser condition (Lean: `center_period_four_0001_integer`
in `Rule30Open.Columns.EtherDomain`): H^t(U) even where t is 0 or 2 modulo 4, odd where it is 3, and, with the right
half's check, never odd at two steps 4 apart where it is 1. `--word 0001` searches that condition, with and without the
check, over the four phases.

`--tree` searches along the tree of readings the condition allows (`tree_failures`): bit 0 at step t is bit t of U
XOR a function of the lower bits, so each allowed reading fixes one more bit of U, and the search visits a Fibonacci
number of branches instead of every integer. `--tree check` is the condition of 0001 with the check at phase 0, Lean's
statement; `--tree c3` is the kit's open `Rule30PeriodFourSkeleton.C3` for each of 0001, 0011 and 0111 in all four
phases: the left half, with the center replaced by the kit's effective boundary, keeping cell -1 on the kit's pattern.

    python -m computations.held_map 24   # the latest first failure for every support up to 24, both phases
    python -m computations.held_map 22 --word 0001   # the same for the condition of 0001
    python -m computations.held_map 100 --tree check   # the condition of 0001 below 2^100, in seconds
    python -m computations.held_map 56 --tree c3   # C3 for the three words, every left half of up to 56 cells
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


def first_failures_0001(support: int, phase: int, check: bool, limit: int = 63) -> np.ndarray:
    """For every U with exactly `support` bits, the first t at which H^t(U) leaves the condition of 0001 at phase
    (t + phase) mod 4: even at phases 0 and 2, odd at phase 3, and with `check` not odd at phase 1 when it was odd 4
    steps before; `limit` when there is none before it."""
    assert limit <= 63, "the parity at step t needs bits 0 .. t, and the words hold 64"
    U = np.arange(1 << (support - 1), 1 << support, dtype=np.uint64)  # (n,)
    V = U & np.uint64((1 << (limit + 1)) - 1)  # (n,), H^t(U) modulo 2^(limit + 1 - t)
    failure = np.full(U.size, limit, dtype=np.int64)  # (n,)
    alive = np.ones(U.size, dtype=bool)  # (n,)
    free = np.zeros(U.size, dtype=bool)  # (n,), whether the last phase-1 step was odd
    for t in range(limit):
        odd = (V & ONE) == ONE  # (n,)
        ph = (t + phase) % 4
        if ph == 1:
            dead = alive & odd & free if check else np.zeros(U.size, dtype=bool)  # (n,)
            free = odd
        else:
            dead = alive & (~odd if ph == 3 else odd)  # (n,)
        failure[dead] = t
        alive &= ~dead
        V = ((V >> ONE) ^ (V | (V << ONE))) & np.uint64((1 << (limit - t)) - 1)  # (n,)
    return failure  # (n,)


EFFECTIVE = {"0001": "0000", "0011": "0010", "0111": "0110"}  # the kit's effWord: the column at t and t + 1 both 1
PATTERN = {"0001": "0*01", "0011": "*001", "0111": "*001"}  # the kit's colPattern: cell -1 at phases 0 .. 3, * free


def next_diagonal(u: int, d: int, m: int) -> int:
    """Antidiagonal m of the left half's spacetime, whose bit t is bit m - t of the half at step t, from bit m of the
    half at step 0, `u`, and `d`, the OR of antidiagonals m - 1 and m - 2 with the boundary at step m - 1 as its bit
    m - 1: bit 0 is `u`, and bit t + 1 is bit t XOR bit t of `d`."""
    x, shift = d, 1
    while shift < m:
        x ^= x << shift  # prefix XOR, doubling
        shift <<= 1
    return (((1 << (m + 1)) - 1) if u else 0) ^ ((x & ((1 << m) - 1)) << 1)


def allowed(word: str, t: int, odd: bool, last_odd: bool, check: bool) -> bool:
    """Whether bit 0 being `odd` at a step of phase t mod 4 fits the pattern of `word`; with `check`, the free phase is
    never odd twice in a row (`last_odd` is the last free step)."""
    want = PATTERN[word][t % 4]
    return not (check and last_odd and odd) if want == "*" else odd == (want == "1")


def tree_failures(word: str, max_support: int, phase: int, check: bool,
                  limit: int = 4096) -> tuple[list[int], list[int]]:
    """For each M up to `max_support`, the latest first failure of the kit's condition `C3 word` over the left halves
    of exactly M cells, run from phase `phase` (the half follows Rule 30 with the column replaced by `EFFECTIVE` and
    cell -1 must fit `PATTERN`), and the number of halves of at most M cells that keep it through step M - 1. For
    0001 with `check` and phase 0 this is the condition of `center_period_four_0001_integer`, and the latest failures
    equal those of `first_failures_0001`.

    Bit 0 at step m is bit m of the half at step 0 XOR the parity of the `d` of `next_diagonal`, so each value the
    condition allows at step m fixes bit m of the half. The halves that keep the condition through step M - 1 are the
    branches of a tree, one per allowed reading, and each is then followed with zeros beyond cell M until it fails.
    Raises AssertionError if one keeps the condition through step `limit`, which would be a candidate for the
    conjecture's failure."""
    boundary = [int(bit) for bit in EFFECTIVE[word]]
    latest, branches = [0] * (max_support + 1), [0] * (max_support + 1)
    early = [False] * (max_support + 1)  # whether some half of more than m + 1 cells first fails at step m
    stack = [(0, 0, 0, False, 0)]  # (m, antidiagonal m - 1, antidiagonal m - 2, last free step odd, bit m - 1)
    while stack:
        m, a1, a2, last_odd, top = stack.pop()
        if m:
            branches[m] += 1
        if top:  # follow the half, of exactly m cells, until it fails
            t, b1, b2, last = m, a1, a2, last_odd
            while True:
                d = b1 | b2 | (boundary[(t - 1 + phase) % 4] << (t - 1))
                odd = d.bit_count() % 2 == 1
                if not allowed(word, t + phase, odd, last, check):
                    break
                assert t < limit, f"a half of {m} cells keeps the condition through step {limit}"
                last = odd if PATTERN[word][(t + phase) % 4] == "*" else last
                b1, b2, t = next_diagonal(0, d, t), b1, t + 1
            latest[m] = max(latest[m], t)
        if m == max_support:
            continue
        d = a1 | a2 | ((boundary[(m - 1 + phase) % 4] << (m - 1)) if m else 0)
        parity = d.bit_count() % 2
        for odd in (False, True):
            u = int(odd) ^ parity
            if allowed(word, m + phase, odd, last_odd, check):
                free = PATTERN[word][(m + phase) % 4] == "*"
                stack.append((m + 1, next_diagonal(u, d, m), a1, odd if free else last_odd, u))
            else:  # every half with these cells and cell m + 1 equal to u fails at step m
                latest[m + 1] = max(latest[m + 1], m) if u else latest[m + 1]
                early[m] = True
    for support in range(2, max_support + 1):
        latest[support] = max([latest[support]] + [m for m in range(support - 1) if early[m]])
    return latest[1:], branches[1:]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("max_support", type=int)
    parser.add_argument("--word", choices=["01", "0001"], default="01")
    parser.add_argument("--tree", choices=["check", "c3"],
                        help="along the tree of readings: 0001 with the check at phase 0, or C3 for the three words")
    args = parser.parse_args()

    if args.tree == "check":
        latest, branches = tree_failures("0001", args.max_support, 0, True)
        for support in range(4, args.max_support + 1, 4):
            print(f"support {support}: latest first failure at step {latest[support - 1]} "
                  f"(M + {latest[support - 1] - support}); {branches[support - 1]} integers below 2^{support} keep the "
                  f"condition through step {support - 1}")
        return
    if args.tree == "c3":
        for word in PATTERN:
            runs = [tree_failures(word, args.max_support, phase, False)
                    for phase in tqdm(range(4), desc=word, file=sys.stderr, leave=False)]
            margin = [max(run[0][m - 1] for run in runs) - m for m in range(1, args.max_support + 1)]  # (supports,)
            widest = max(range(args.max_support), key=lambda m: margin[m])
            print(f"C3 {word}: every left half of at most {args.max_support} cells fails in all four phases; the "
                  f"latest first failure is M + {margin[widest]} at most, at M = {widest + 1}; margins at M = 10, 20, "
                  f"...: {margin[9::10]}; {[run[1][-1] for run in runs]} halves keep it through step "
                  f"{args.max_support - 1}, by phase")
        return
    for support in tqdm(range(1, args.max_support + 1), desc="supports", file=sys.stderr):
        if args.word == "01":
            latest = [int(first_failures(support, phase).max()) for phase in (0, 1)]
            print(f"support {support}: latest first failure at step {latest[0]} (odd checks), {latest[1]} (even "
                  f"checks); 2M = {2 * support}")
        else:
            plain, checked = (max(int(first_failures_0001(support, phase, check).max()) for phase in range(4))
                              for check in (False, True))
            print(f"support {support}: latest first failure at step {plain} (three phases), {checked} (with the "
                  f"right half's check); 4M/3 = {4 * support / 3:.1f}")


if __name__ == "__main__":
    main()
