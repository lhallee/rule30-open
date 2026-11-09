"""The diagonal-freedom construction for invertible T-functions, and its center-override form for Rule 30.

An invertible T-function F is given by its level functions: bit i of F(y) is y_i xor f_i(y mod 2^i). A map G is stored
as F with a set of flipped residues per level: bit i of G(y) is y_i xor f_i(r) xor [r in flips[i]], r = y mod 2^i.
For Rule 30's right-edge map Phi(y) = y xor (2y or 4y), f_i(r) = r_(i-1) or r_(i-2).

* `build`: the construction of [diagonal freedom](../negative-results/frames/diagonal-freedom.md), level by level: at
  each level i >= t0 with i = q L_i + r, a flip at the first point of the cycle (when r >= 1) sets bit i of G^i(x) to
  d(i) against the final parity, and a flip at the last point restores the parity pi_i of F, in every case.
* `check_random`: the construction on random invertible T-functions: the cycle lengths of the seed are kept at every
  level, bit t of G^t(x) is d(t) where L_t does not divide t and the forced value where it does, and at most two
  residues change per level.
* `check_override`: the center-override form for Phi and x = 1 (flips at the orbit times i - 1 and L_i - 1), run to N
  levels for a prescribed word: the cycle lengths, the readout, the light cone and both edges (G^s(1) has exactly
  2s + 1 binary digits), and the cells where G differs from the Rule 30 law, by kind.

    python -m computations.diagonal_freedom --override 40 8     # the four words to 40 levels with t0 = 8 (about 15 s)
    python -m computations.diagonal_freedom --random 10 300     # 300 random T-functions, 10 levels (seconds)
"""

from __future__ import annotations

import argparse
import random
from typing import Callable

from tqdm.auto import tqdm

Level = Callable[[int, int], int]  # f(i, r): the level function at level i on the residue r = y mod 2^i


def phi_level(i: int, r: int) -> int:
    """Phi's level function: bit i - 1 or bit i - 2 of r (zero below bit 0)."""
    return (((r >> (i - 1)) & 1) if i >= 1 else 0) | (((r >> (i - 2)) & 1) if i >= 2 else 0)


def apply(y: int, n: int, f: Level, flips: dict[int, set[int]]) -> int:
    """G(y) mod 2^n, bit by bit."""
    out = 0
    for i in range(n):
        low = y & ((1 << i) - 1)
        out |= (((y >> i) & 1) ^ f(i, low) ^ (1 if low in flips.get(i, ()) else 0)) << i
    return out


def cycle(x: int, n: int, f: Level, flips: dict[int, set[int]]) -> list[int]:
    """The cycle of x modulo 2^n under G, as residues in orbit order."""
    start = x & ((1 << n) - 1)
    out, y = [start], apply(start, n, f, flips)
    while y != start:
        out.append(y)
        y = apply(y, n, f, flips)
    return out


def cycle_lengths(x: int, n: int, f: Level, flips: dict[int, set[int]] | None = None) -> list[int]:
    """L_0, ..., L_n: the cycle lengths of x modulo 2^0, ..., 2^n under G (F when flips is empty)."""
    return [len(cycle(x, k, f, flips or {})) for k in range(n + 1)]


def build(x: int, n: int, t0: int, d: list[int], f: Level, override: bool = False) -> dict[int, set[int]]:
    """The flips of the construction at the levels t0 <= i < n. With override, the first flip is at the orbit time
    i - 1 instead of the first point of the cycle (the center-override form)."""
    L = cycle_lengths(x, n + 1, f)  # F's cycle lengths, which G keeps
    pi = [int(L[i + 1] == 2 * L[i]) for i in range(n)]  # doubling parities
    flips: dict[int, set[int]] = {}
    for i in range(t0, n):
        o = cycle(x, i, f, flips)  # the G-cycle modulo 2^i, of length L[i] by the levels below
        u = [f(i, r) for r in o]
        q, r = divmod(i, len(o))
        changed: set[int] = set()
        if r >= 1:
            a = (i - 1) % len(o) if override else 0
            if ((x >> i) & 1) ^ (q * pi[i] % 2) ^ (sum(u[:r]) % 2) != d[i]:
                u[a] ^= 1
                changed ^= {o[a]}
        if sum(u) % 2 != pi[i]:
            u[-1] ^= 1
            changed ^= {o[-1]}
        flips[i] = changed
    return flips


def readout(x: int, n: int, f: Level, flips: dict[int, set[int]]) -> list[int]:
    """Bit t of G^t(x) for t < n, computed modulo 2^n."""
    out, y = [], x & ((1 << n) - 1)
    for t in range(n):
        out.append((y >> t) & 1)
        y = apply(y, n, f, flips)
    return out


def check_random(n: int, trials: int, seed: int = 3) -> dict[str, int]:
    """The construction on random invertible T-functions (random level tables), seeds, t0 and words: counts of the
    cases where the cycle lengths change, the readout differs from d or from the forced value, or a level changes more
    than two residues."""
    rng = random.Random(seed)
    bad = {"lengths": 0, "readout": 0, "residues": 0, "cases": 0}
    for _ in tqdm(range(trials), desc="random T-functions", leave=False):
        tables = [[rng.randint(0, 1) for _ in range(1 << i)] for i in range(n + 1)]  # (n + 1,) lists of 2^i bits
        f: Level = lambda i, r, T=tables: T[i][r]  # noqa: E731
        x, t0 = rng.getrandbits(n + 1), rng.randint(1, 3)
        d = [rng.randint(0, 1) for _ in range(n + 1)]
        L = cycle_lengths(x, n + 1, f)
        flips = build(x, n, t0, d, f)
        rd = readout(x, n, f, flips)
        bad["cases"] += 1
        bad["lengths"] += cycle_lengths(x, n, f, flips) != L[:n + 1]
        forced = lambda t: ((x >> t) & 1) ^ ((t // L[t]) * int(L[t + 1] == 2 * L[t]) % 2)  # noqa: E731
        bad["readout"] += any(rd[t] != (d[t] if t % L[t] else forced(t)) for t in range(t0, n))
        bad["residues"] += any(len(v) > 2 for v in flips.values())
    return bad


WORDS: dict[str, Callable[[int], int]] = {
    "white": lambda t: 0,
    "black": lambda t: 1,
    "(10)": lambda t: 1 - t % 2,
    "(110)": lambda t: int(t % 3 != 2),
}


def check_override(n: int, t0: int, word: Callable[[int], int]) -> dict[str, int | bool]:
    """The center-override form for Phi and x = 1, run on the orbit modulo 2^n for 2 L_n + 1 steps: whether the cycle
    lengths, the readout from t0 on and the light cone with both edges hold, and the numbers of cells where G differs
    from the Rule 30 law at the center, before time L_i on diagonal i, and at L_i <= t < L_(i+1)."""
    d = [word(t) for t in range(n + 1)]
    flips = build(1, n, t0, d, phi_level, override=True)
    L = cycle_lengths(1, n + 1, phi_level)
    out: dict[str, int | bool] = {"lengths": cycle_lengths(1, n, phi_level, flips) == L[:n + 1],
                                  "readout": True, "cone": True, "center": 0, "before": 0, "in_period": 0}
    y = 1
    for s in range(2 * L[n] + 1):
        z = apply(y, n, phi_level, flips)
        t = s + 1
        for i in range(n):
            if ((z >> i) & 1) != ((y >> i) & 1) ^ phi_level(i, y & ((1 << i) - 1)):
                key = "center" if t == i else ("before" if t < L[i] else ("in_period" if t < L[i + 1] else None))
                if key:
                    out[key] += 1
        y = z
        if t0 <= t < n and ((y >> t) & 1) != d[t]:
            out["readout"] = False
        if 2 * t + 1 <= n and y >> (2 * t) != 1:
            out["cone"] = False
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--override", nargs=2, type=int, metavar=("N", "T0"))
    parser.add_argument("--random", nargs=2, type=int, metavar=("N", "TRIALS"))
    args = parser.parse_args()
    if args.override:
        n, t0 = args.override
        print("L_n:", cycle_lengths(1, n, phi_level))
        for name, word in tqdm(WORDS.items(), desc="words", leave=False):
            r = check_override(n, t0, word)
            print(f"{name}: lengths kept {r['lengths']}, readout {r['readout']}, light cone and edges {r['cone']}; "
                  f"the law differs at {r['center']} center cells, {r['before']} cells before L_i on diagonal i, "
                  f"{r['in_period']} cells with L_i <= t < L_(i+1)")
    if args.random:
        n, trials = args.random
        print(check_random(n, trials))


if __name__ == "__main__":
    main()
