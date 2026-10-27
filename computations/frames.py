"""The right-edge frame: Rule 30 as a bijection of the 2-adic integers, and the single cell's exact past.

Read a row leftward from a frame that moves one cell right per step: bit k of y at time t is cell t - k. Then one step
of the rule is Phi(y) = y xor (2y or 4y), since bit k of the new row is cell t + 1 - k, which reads cells t - k,
t + 1 - k and t + 2 - k, bits k, k - 1 and k - 2 of y. Phi is a bijection of the 2-adic integers (bit k of Phi(y) is
y_k plus a function of lower bits), and the single cell is y = 1, so its center column is bit t of Phi^t(1).

A rational 2-adic integer is an eventually periodic bit sequence, held here as (prefix, period) lists of bits, bit 0
first. Every rho_k = Phi^-k(1) is rational: inverting Phi bit by bit is a finite-state transducer, so it maps an
eventually periodic sequence to one.

    python -m computations.frames 3000   # periods and preperiods of rho_k, with the checks for every k
"""

from __future__ import annotations

import argparse
import sys

from collections.abc import Iterator
from tqdm.auto import tqdm


Bits = list[int]


def phi(y: int, bits: int) -> int:
    """Phi(y) = y xor (2y or 4y), modulo 2^bits."""
    return (y ^ ((y << 1) | (y << 2))) & ((1 << bits) - 1)


def psi(y: int, bits: int) -> int:
    """The first `bits` bits of Psi(y), whose bit t is bit t of Phi^t(y): the column of the row y at the frame's
    position at time 0. Psi(1) is the single cell's center column."""
    out = 0
    for t in range(bits):
        out |= ((y >> t) & 1) << t
        y = phi(y, bits)
    return out


def minimal(prefix: Bits, period: Bits) -> tuple[Bits, Bits]:
    """The same 2-adic number with the shortest period word and the shortest prefix."""
    n = len(period)
    for d in range(1, n + 1):
        if n % d == 0 and period == period[:d] * (n // d):
            period = period[:d]
            break
    prefix = list(prefix)
    while prefix and prefix[-1] == period[-1]:
        prefix.pop()
        period = [period[-1], *period[:-1]]
    return prefix, period


def phi_inverse(prefix: Bits, period: Bits) -> tuple[Bits, Bits]:
    """Phi^-1 of an eventually periodic number: z_j = y_j xor (z_(j-1) or z_(j-2)) with z_(-1) = z_(-2) = 0. After the
    prefix the transducer state (z_(j-1), z_(j-2)) at the start of each period repeats within four periods."""
    out, a, b = [], 0, 0
    for y in prefix:
        z = y ^ (a | b)
        out.append(z)
        a, b = z, a
    seen: dict[tuple[int, int], int] = {}
    blocks: list[Bits] = []
    while (a, b) not in seen:
        seen[(a, b)] = len(blocks)
        block = []
        for y in period:
            z = y ^ (a | b)
            block.append(z)
            a, b = z, a
        blocks.append(block)
    start = seen[(a, b)]
    transient = [z for block in blocks[:start] for z in block]
    return minimal(out + transient, [z for block in blocks[start:] for z in block])


def phi_rational(prefix: Bits, period: Bits) -> tuple[Bits, Bits]:
    """Phi of an eventually periodic number. Output bit j reads input bits j, j - 1 and j - 2, so it repeats with the
    input's period from two bits after the prefix on."""
    start = len(prefix) + 2
    y = list(prefix) + period * (-(-(start + len(period)) // len(period)))
    z = [y[j] ^ ((y[j - 1] if j >= 1 else 0) | (y[j - 2] if j >= 2 else 0)) for j in range(start + len(period))]
    return minimal(z[:start], z[start:])


def seed_past(k_max: int) -> Iterator[tuple[int, Bits, Bits]]:
    """rho_k = Phi^-k(1) as (k, prefix, period word) for k = 1 .. k_max."""
    prefix, period = [1], [0]
    for k in range(1, k_max + 1):
        prefix, period = phi_inverse(prefix, period)
        yield k, prefix, period


def ring_death(period: Bits, limit: int) -> tuple[int, bool] | None:
    """Steps until the word, wrapped on a ring, turns all white under Phi (Rule 30 followed by a rotation), and whether
    the step before is all black; None while it is still alive after `limit` steps."""
    n = len(period)
    mask = (1 << n) - 1
    y = sum(bit << i for i, bit in enumerate(period))
    for steps in range(1, limit + 1):
        once = (y << 1) | (y >> (n - 1))
        twice = (y << 2) | (y >> (n - 2)) if n > 1 else y
        image = (y ^ (once | twice)) & mask
        if image == 0:
            return steps, y == mask
        y = image
    return None


def to_int(prefix: Bits, period: Bits, bits: int) -> int:
    """The first `bits` bits of an eventually periodic number, as an integer."""
    sequence = list(prefix)
    while len(sequence) < bits:
        sequence += period
    return sum(bit << i for i, bit in enumerate(sequence[:bits]))


def check_past(k: int, prefix: Bits, period: Bits) -> None:
    """Phi^k(rho_k) = 1 exactly: it holds modulo 2^bits with bits past the prefix's light cone and two periods, and the
    periodic tail's image is the ring's, which `ring_death` shows dies in exactly k steps."""
    bits = len(prefix) + 2 * k + 4 * len(period)
    y = to_int(prefix, period, bits)
    for _ in range(k):
        y = phi(y, bits)
    assert y == 1, k
    assert ring_death(period, k) == (k, True), k


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("k_max", type=int)
    k_max = parser.parse_args().k_max

    last_period = 0
    for k, prefix, period in tqdm(seed_past(k_max), total=k_max, desc="seed past", unit="step", file=sys.stderr):
        check_past(k, prefix, period)
        if len(period) != last_period or k in (28, 30, 66, 300, 1000, k_max):
            word = "".join(map(str, period)) if len(period) <= 48 else "..."
            print(f"k = {k}: preperiod {len(prefix)}, period {len(period)}, word {word}")
        last_period = len(period)
    print(f"checked k = 1 .. {k_max}: Phi^k(rho_k) = 1, and the period word dies on a ring in exactly k steps")


if __name__ == "__main__":
    main()
