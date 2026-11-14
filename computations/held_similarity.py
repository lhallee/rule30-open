"""The held map as a 2-adic expanding map: exact similarities on residue classes, never affine on any of them.

Write H(U) = (U >> 1) xor (U or (U << 1)), the held map of `held_shift`, on 2-adic integers (cell j is bit j). The
3x+1 map T is affine on each class modulo 2^n after n steps; this module checks the replacement for H:

- `similarity_holds`: on each class modulo 2^n, H^n multiplies 2-adic distances by exactly 2^n, that is
  v(H^n U - H^n V) = v(U - V) - n whenever U = V modulo 2^n.
- `affinity_defect`: H^n agrees with no affine map on any class a + 2^k Z_2. For m large the class holds a + 2^m and
  a + 3 * 2^m, whose images differ from H^n(a) by 2^(m - n) E^n(1) and 2^(m - n) E^n(3), where
  E(x) = x xor ((x << 1) or (x << 2)) is the held map without its boundary; an affine map would need
  E^n(3) = 3 E^n(1).
- `inverse_branch` and `ifs_point`: the two inverse branches of H (fix u_0) are similarities of ratio 1/2, and the
  point of K with itinerary beta is the limit of G_(beta_0) o ... o G_(beta_(n-1))(0) with
  G_b(W) = H_b^(-1)(H_1^(-1)(W)), correct modulo 4^n: the analog of Bernstein's series, with nonaffine maps.
- `survivors_below` and `survivors_with_bits`: how many integers below 2^N, or with exactly M bits, have H^t odd at
  every odd t <= T. Below 2^N the count is 2^(N - ceil(T / 2)) for T < N; with exactly M bits it is
  2^(M - 1 - ceil(T / 2)) for T <= M - 2, and at T = M - 1 it is 2^((M - 1) / 2) only for odd M.

    python -m computations.held_similarity --max-n 12      # the table of E^n(3) against 3 E^n(1), and the checks
"""

from __future__ import annotations

import argparse
import random

from tqdm.auto import tqdm

from computations.held_shift import held


def boundaryless(x: int) -> int:
    """The held map on a nonnegative integer seen far from cell 0: bit j is x_j xor (x_(j-1) or x_(j-2)). For m >= 1,
    H(x 2^m) = 2^(m - 1) E(x)."""
    return x ^ ((x << 1) | (x << 2))


def held_power(U: int, n: int, bits: int) -> int:
    """H^n(U) modulo 2^bits. Bit j of H^n(U) reads bits j - n .. j + n of U, so U is needed modulo 2^(bits + n)."""
    mask = (1 << (bits + n)) - 1
    V = U & mask
    for _ in range(n):
        V = held(V) & mask
    return V & ((1 << bits) - 1)


def valuation(x: int, cap: int) -> int:
    """The 2-adic valuation of x, or cap when x is 0 modulo 2^cap."""
    x &= (1 << cap) - 1
    if x == 0:
        return cap
    return (x & -x).bit_length() - 1


def similarity_holds(n: int, bits: int, samples: int, seed: int = 0) -> bool:
    """Draw pairs U = V modulo 2^n that differ below bit `bits` and check v(H^n U - H^n V) = v(U - V) - n."""
    rng = random.Random(seed)
    for _ in range(samples):
        U = rng.getrandbits(bits + n + 8)
        k = rng.randrange(n, bits)
        V = U ^ (1 << k) ^ (rng.getrandbits(bits + n + 8) << (k + 1))  # differs first at bit k
        d = held_power(U, n, bits) - held_power(V, n, bits)
        if valuation(d, bits) != k - n:
            return False
    return True


def affinity_defect(n: int, k: int, a: int) -> tuple[int, int, int]:
    """For the class a + 2^k Z_2 (0 <= a < 2^k) and m = k + 2n + 3, return (m, d1, d3) with
    d1 = H^n(a + 2^m) - H^n(a) and d3 = H^n(a + 3 2^m) - H^n(a), exact on integers. An affine map on the class has
    d3 = 3 d1."""
    assert 0 <= a < 1 << k
    m = k + 2 * n + 3
    base = a
    one = a + (1 << m)
    three = a + 3 * (1 << m)
    for _ in range(n):
        base, one, three = held(base), held(one), held(three)
    return m, one - base, three - base


def boundaryless_power(x: int, n: int) -> int:
    """E^n(x)."""
    for _ in range(n):
        x = boundaryless(x)
    return x


def inverse_branch(V: int, first: int, bits: int) -> int:
    """The U with H(U) = V and u_0 = first, modulo 2^bits, from V modulo 2^(bits - 1): u_(j+1) = v_j xor (u_j or
    u_(j-1)) with u_(-1) = 0."""
    u = [first]  # bits of U, low first
    prev = 0
    for j in range(bits - 1):
        nxt = ((V >> j) & 1) ^ (u[j] | prev)
        prev = u[j]
        u.append(nxt)
    return sum(b << i for i, b in enumerate(u))


def ifs_point(beta: list[int]) -> int:
    """The point of K with itinerary beginning beta, modulo 4^len(beta): G_(beta_0) o ... o G_(beta_(n-1)) applied to
    0, where G_b(W) = inverse_branch(inverse_branch(W, 1), b). Each branch adds one exact bit."""
    W, bits = 0, 0
    for b in reversed(beta):
        bits += 1
        W = inverse_branch(W, 1, bits)
        bits += 1
        W = inverse_branch(W, b, bits)
    return W


def survivors_below(N: int, T: int) -> int:
    """How many integers 0 <= U < 2^N have H^t(U) odd at every odd t <= T, by stepping each one."""
    count = 0
    for U in range(1 << N):
        V, alive = U, True
        for t in range(1, T + 1):
            V = held(V)
            if t % 2 == 1 and V & 1 == 0:
                alive = False
                break
        count += alive
    return count


def survivors_with_bits(M: int, T: int) -> int:
    """How many integers with exactly M bits (2^(M-1) <= U < 2^M) have H^t(U) odd at every odd t <= T."""
    return survivors_below(M, T) - survivors_below(M - 1, T)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--max-n", type=int, default=12)
    args = parser.parse_args()
    print("n  E^n(1)  E^n(3)  3 E^n(1)")
    for n in range(1, args.max_n + 1):
        e1, e3 = boundaryless_power(1, n), boundaryless_power(3, n)
        print(n, e1, e3, 3 * e1)
    bad = 0
    for n in tqdm(range(1, args.max_n + 1), desc="classes"):
        assert similarity_holds(n, 48, 200, seed=n)
        for k in range(0, 7):
            for a in range(1 << k):
                m, d1, d3 = affinity_defect(n, k, a)
                assert d1 == boundaryless_power(1, n) << (m - n)
                assert d3 == boundaryless_power(3, n) << (m - n)
                bad += d3 == 3 * d1
    print("classes modulo 2^k, k <= 6, n <=", args.max_n, "on which d3 = 3 d1:", bad)
    for T in range(1, 12):
        print("integers below 2^12 passing the odd steps up to", T, ":", survivors_below(12, T),
              "against 2^(12 - ceil(T / 2)) =", 1 << (12 - (T + 1) // 2))
    for M in tqdm(range(2, 13), desc="bit lengths"):
        print("integers with", M, "bits passing every odd step up to M - 2 :", survivors_with_bits(M, M - 2),
              "; up to M - 1 :", survivors_with_bits(M, M - 1))


if __name__ == "__main__":
    main()
