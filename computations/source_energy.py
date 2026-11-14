"""The source energy of the kit's main-branch module `Rule30SourceEnergy`, and what its hypothesis forces.

For N = 2^n the kit uses the n shifts S = {0, 1, 2, 4, ..., 2^(n-2)}, the signs z(t) = (-1)^c(t) extended by 0
outside [0, N), Z(u) = sum over s in S of z(u + s), and Esrc(n) = sum over 0 <= u < N of Z(u)^2. Its theorem
`problem2_of_source_energy` gives Problem 2 from Esrc(n) = o(N n^2). The entry
`findings/structure/source-energy-dyadic.md` proves that the same hypothesis gives density 1/2 on every residue class
mod 2^k (hence Problem 1 as well), so it fails for sequences with density 1/2 and a bias on one class, such as
c(t) = t mod 2.

* `source_energy`: Esrc(n) of a 0/1 array of length at least 2^n, in the kit's definition.
* `iid_mean`: the mean of Esrc(n) over independent fair signs, sum over u of #{s in S : u + s < N}.
* `normalized`: Esrc(n) / (N n^2), the quantity the kit's hypothesis sends to 0.
* `progression_sum`: F = sum over t < M of z(t) f(t) for f the indicator of t = r mod 2^k.
* `progression_bound`: the entry's bound (n - k) |F| <= sqrt(M Esrc(n)) + k M + 2^n for 2^(n-1) < M <= 2^n,
  for every f of period 2^k with |f| <= 1.
* `class_bias`: max over r of |sum over t < N, t = r mod 2^k, of z(t)| / (N / 2^k).
* `lacunary_polynomial`: P_n(theta) = sum over s in S of e(s theta), e(x) = exp(2 pi i x).
* `fourier_coefficient`: zhat_M(theta) = sum over t < M of z(t) e(-t theta).
* `fourier_bound`: the entry's inequality |P_n(theta)| |zhat_M(theta)| <= sqrt(M Esrc(n)) + 2^n, as the bound on
  |zhat_M(theta)| / M it gives.
* `cycle_average`: the limit of P_n(theta) / n for theta = a / q, the mean of e(2^j theta) over the eventual cycle
  of the doubling map; it is 1 for q a power of two, a nonzero Gauss period mean for q = 2^k p with p an odd prime, and
  0 for q = 9.
* `planted_nine`: independent cells with P(black at t) = (1 - delta cos(2 pi t / 9)) / 2, a sequence that satisfies the
  kit's hypothesis almost surely and is biased on the classes mod 9.

    python -m computations.source_energy               # the entry's tables, n = 8 .. 18 (about 10 seconds)
    python -m computations.source_energy --bits 14     # a smaller run (a second)
"""

from __future__ import annotations

import argparse
import math
import sys
from fractions import Fraction

import numpy as np
from tqdm.auto import tqdm

from computations.rule30 import center_column


def shifts(n: int) -> list[int]:
    """The kit's shift set S = {0} and 2^j for 0 <= j <= n - 2; it has n elements for n >= 1."""
    return [0] + [1 << j for j in range(n - 1)]


def signs(cells: np.ndarray) -> np.ndarray:
    """z(t) = (-1)^c(t) as int64."""
    # cells: (m,)
    return 1 - 2 * cells.astype(np.int64)  # (m,)


def shifted_sums(cells: np.ndarray, n: int) -> np.ndarray:
    """Z(u) for 0 <= u < 2^n, with z extended by 0 at and beyond 2^n."""
    # cells: (m,) with m >= 2^n
    size = 1 << n
    z = signs(cells[:size])  # (N,)
    total = np.zeros(size, dtype=np.int64)  # (N,)
    for s in shifts(n):
        total[: size - s] += z[s:]
    return total  # (N,)


def source_energy(cells: np.ndarray, n: int) -> int:
    """Esrc(n) of the kit: sum over 0 <= u < 2^n of Z(u)^2."""
    # cells: (m,) with m >= 2^n
    values = shifted_sums(cells, n)  # (N,)
    return int(np.dot(values, values))


def iid_mean(n: int) -> int:
    """The mean of Esrc(n) over independent fair signs: the cross terms vanish, so it is the number of pairs (u, s)
    with s in S and u + s < 2^n."""
    size = 1 << n
    return sum(size - s for s in shifts(n))


def normalized(energy: int, n: int) -> float:
    """Esrc(n) / (2^n n^2)."""
    return energy / ((1 << n) * n * n)


def progression_sum(cells: np.ndarray, length: int, k: int, r: int) -> int:
    """F = sum over t < length with t = r mod 2^k of z(t)."""
    # cells: (m,) with m >= length
    z = signs(cells[:length])  # (length,)
    return int(z[r % (1 << k) :: 1 << k].sum())


def progression_bound(energy: int, n: int, length: int, k: int) -> float:
    """The entry's bound on |F| / length for any f of period 2^k with |f| <= 1, valid for
    2^(n-1) < length <= 2^n and k < n: (sqrt(length Esrc) + k length + 2^n) / ((n - k) length)."""
    return (math.sqrt(length * energy) + k * length + (1 << n)) / ((n - k) * length)


def class_bias(cells: np.ndarray, n: int, k: int) -> float:
    """max over r of |sum over t < 2^n, t = r mod 2^k, of z(t)| divided by the class size 2^(n - k)."""
    # cells: (m,) with m >= 2^n
    z = signs(cells[: 1 << n]).reshape(-1, 1 << k)  # (2^(n-k), 2^k)
    return float(np.abs(z.sum(axis=0)).max()) / (1 << (n - k))


def expo(x: Fraction) -> complex:
    """e(x) = exp(2 pi i x) for a rational x, reduced mod 1 first so large shifts lose no precision."""
    frac = x - math.floor(x)
    return complex(math.cos(2 * math.pi * frac), math.sin(2 * math.pi * frac))


def lacunary_polynomial(n: int, theta: Fraction) -> complex:
    """P_n(theta) = sum over s in S of e(s theta); at theta = 1/2 it is n - 2."""
    return sum((expo(s * theta) for s in shifts(n)), complex(0.0))


def fourier_coefficient(cells: np.ndarray, length: int, theta: Fraction) -> complex:
    """zhat_M(theta) = sum over t < length of z(t) e(-t theta), with the phases t theta reduced mod 1 exactly."""
    # cells: (m,) with m >= length
    q = theta.denominator
    phases = (np.arange(length, dtype=np.int64) * theta.numerator) % q  # (length,)
    angles = -2 * np.pi * phases / q  # (length,)
    z = signs(cells[:length]).astype(np.float64)  # (length,)
    return complex(np.dot(z, np.cos(angles)), np.dot(z, np.sin(angles)))


def fourier_bound(energy: int, n: int, length: int, theta: Fraction) -> float:
    """The entry's bound on |zhat_M(theta)| / M: (sqrt(M Esrc) + 2^n) / (|P_n(theta)| M), for 2^(n-1) < M <= 2^n."""
    return (math.sqrt(length * energy) + (1 << n)) / (
        abs(lacunary_polynomial(n, theta)) * length
    )


def cycle_average(theta: Fraction) -> complex:
    """The mean of e(2^j theta) over the cycle that the doubling map x -> 2x mod 1 enters from theta."""
    x = theta - math.floor(theta)
    seen: dict[Fraction, int] = {}
    orbit: list[Fraction] = []
    while x not in seen:
        seen[x] = len(orbit)
        orbit.append(x)
        x = (2 * x) % 1
    cycle = orbit[seen[x] :]
    return sum((expo(y) for y in cycle), complex(0.0)) / len(cycle)


def planted_nine(length: int, delta: float, seed: int) -> np.ndarray:
    """Independent 0/1 cells, black at t with probability (1 - delta cos(2 pi t / 9)) / 2, so E z(t) = delta cos(2 pi t / 9)."""
    rng = np.random.default_rng(seed)
    mean = delta * np.cos(2 * np.pi * (np.arange(length) % 9) / 9)  # (length,)
    return (rng.random(length) < (1 - mean) / 2).astype(np.uint8)  # (length,)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument(
        "--bits", type=int, default=18, help="largest n, so 2^n center cells"
    )
    args = parser.parse_args(argv)
    top = args.bits
    cells = center_column(1 << top)  # (2^top,)
    alternating = (np.arange(1 << top) & 1).astype(np.uint8)  # (2^top,), c(t) = t mod 2
    print("n  Esrc/(N n^2)  iid mean/(N n^2)  ratio to iid  alternating Esrc/(N n^2)")
    for n in tqdm(range(8, top + 1), desc="n", file=sys.stderr):
        energy = source_energy(cells, n)
        mean = iid_mean(n)
        print(
            f"{n:2d}  {normalized(energy, n):.5f}  {normalized(mean, n):.5f}  {energy / mean:.4f}"
            f"  {normalized(source_energy(alternating, n), n):.5f}"
        )
    print(
        "\nclass bias of the center column on t < 2^n, max over r of |mean of z on t = r mod 2^k|"
    )
    print("k  bias  bias * sqrt(class size)  bound from Esrc at M = 2^n")
    energy = source_energy(cells, top)
    for k in range(7):
        bias = class_bias(cells, top, k)
        print(
            f"{k}  {bias:.5f}  {bias * math.sqrt(1 << (top - k)):.3f}"
            f"  {progression_bound(energy, top, 1 << top, k):.3f}"
        )
    print(
        "\ntheta  cycle average  |P_n|/n  |zhat_N|/N  |zhat_N|/sqrt(N)  bound from Esrc"
    )
    size = 1 << top
    for theta in (
        Fraction(1, 2),
        Fraction(1, 4),
        Fraction(1, 8),
        Fraction(1, 3),
        Fraction(1, 5),
        Fraction(1, 7),
        Fraction(1, 6),
        Fraction(1, 9),
    ):
        coefficient = abs(fourier_coefficient(cells, size, theta))
        print(
            f"{theta!s:5s}  {abs(cycle_average(theta)):.4f}  {abs(lacunary_polynomial(top, theta)) / top:.4f}"
            f"  {coefficient / size:.5f}  {coefficient / math.sqrt(size):.3f}  {fourier_bound(energy, top, size, theta):.3f}"
        )
    planted = planted_nine(size, 0.5, 0)  # (2^top,)
    planted_energy = source_energy(planted, top)
    print("\nplanted mod-9 sequence, delta = 0.5, seed 0, t < 2^n")
    print(
        f"Esrc / iid mean {planted_energy / iid_mean(top):.4f}  Esrc/(N n^2) {normalized(planted_energy, top):.5f}"
        f"  black fraction {planted.mean():.4f}  on t = 0 mod 9 {planted[::9].mean():.4f}"
        f"  max |P_n(1/9)| for n <= 200 {max(abs(lacunary_polynomial(m, Fraction(1, 9))) for m in range(2, 201)):.3f}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
