"""Tests of computations.ether_prefix: the truncated-ether certificates and `ether_agreement` against integer rows
stepped one at a time and direct comparison with the ether."""

from __future__ import annotations

import numpy as np

from computations import absorption, ether_prefix
from references import least_depth_slow


def test_ether_prefix() -> None:
    """The truncated-ether certificates: packing round-trips; for sampled alignments, phases and tails, each direct entry
    is the first step at which integer rows stepped one at a time meet the family, at the least depth there, checked
    column by column; each base meets it through its own alignment with column 1 the ether's before; and seven more
    ether columns in front give the same step at seven columns more depth, for two more blocks."""
    rng = np.random.default_rng(33)
    entries = [(int(t), int(k)) for t, k in zip(rng.integers(0, 2000, 20), rng.integers(0, 64, 20), strict=True)]
    assert ether_prefix.decode(ether_prefix.encode(13, entries[:13], entries[13:])) == (13, entries[:13], entries[13:])
    wall = absorption.kit_wall()  # (4, 2^13)

    def stepped(word: str, phase: int, row: int, t: int) -> list[int]:
        rows = [row]  # the rows at steps 0 .. t
        for s in range(t):
            row = ((row << 1) | int(word[(s + phase) % 4])) ^ (row | (row >> 1))
            rows.append(row)
        return rows

    def own_depth(word: str, j0: int, shift: int, row: int, phase: int) -> int:
        psi = (phase + shift) % 4
        ks = [k for k in range(200) if (j0 + k) % 7 == 2 and wall[psi][(row >> k) & 0x1FFF]
              and all((row >> (p - 1)) & 1 == absorption.ether(j0 + p, psi) for p in range(1, k + 1))]
        return min(ks, default=-1)

    for word, j0, shift, phase, tail in (("0001", 5, 0, 3, 0), ("0011", 1, 3, 0, 5), ("0111", 2, 2, 1, 11)):
        psi = (phase + shift) % 4
        b, direct, bases = ether_prefix.certificate(word, j0, shift, phase, tail)
        for length, (t, k) in enumerate(direct):
            rows = stepped(word, phase, ether_prefix.prefix_half(j0, psi, length, tail), t)
            assert all(least_depth_slow(word, rows[s], (s + phase) % 4, wall) < 0 for s in range(t))
            assert least_depth_slow(word, rows[t], (t + phase) % 4, wall) == k
        for i, (t, k) in enumerate(bases):
            for extra in range(3):
                rows = stepped(word, phase, ether_prefix.prefix_half(j0, psi, b + i + 7 * extra, tail), t)
                for s in range(t):
                    assert (rows[s] & 1) == absorption.ether(j0 + 1, (s + psi) % 4)
                assert own_depth(word, j0, shift, rows[t], (t + phase) % 4) == k + 7 * extra


def test_ether_agreement() -> None:
    """`ether_agreement` against a direct comparison of cell strings with every rotation of the ether, on random halves
    and on halves that are a rotation of the ether on a known prefix."""
    rng = np.random.default_rng(36)
    halves = [int(h) for h in rng.integers(0, 1 << 16, 50)]
    halves += [ether_prefix.ether_bits(j0, psi, k) | (1 - absorption.ether(j0 + k + 1, psi)) << k
               for j0, psi, k in ((2, 1, 9), (6, 3, 12), (0, 0, 5))]
    for half in halves:
        cells = format(half, "016b")[::-1]
        best = max(next((k for k in range(16) if cells[k] != str(absorption.ether(j0 + k + 1, psi))), 16)
                   for j0 in range(7) for psi in range(4))
        assert ether_prefix.ether_agreement(half, 16) == best
