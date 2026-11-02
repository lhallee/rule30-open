"""Tests for computations.seed_past_lean: the certificates of the single cell's past and their window checks."""

from __future__ import annotations

from pathlib import Path

from computations import seed_past_lean as spl


LEAN = Path(__file__).resolve().parents[1] / "Rule30Open" / "Frames" / "SeedPastTable.lean"


def brute_rho(k: int, bits: int) -> int:
    """rho_k modulo 2^bits, inverting Phi k times on integers bit by bit, from the single cell."""
    y = 1
    for _ in range(k):
        z = 0
        for j in range(bits):
            prev = ((z >> (j - 1)) & 1 if j >= 1 else 0) | ((z >> (j - 2)) & 1 if j >= 2 else 0)
            z |= (((y >> j) & 1) ^ prev) << j
        y = z
    return y


def brute_period(y: int, start: int, length: int) -> int:
    """The least q with bit j + q = bit j for start <= j < start + length."""
    q = 1
    while any(((y >> (j + q)) & 1) != ((y >> j) & 1) for j in range(start, start + length)):
        q += 1
    return q


def test_certificates_against_brute_force() -> None:
    certs = spl.certificates(tuple(range(0, 13)))
    assert [c[0] for c in certs] == list(range(13))
    for cert in certs:
        k, n, p, _, _ = cert
        bits = n + 4 * p + 8
        y = brute_rho(k, bits)
        assert spl.expand(cert, bits) == y, k
        assert brute_period(y, n, 2 * p) == p, k
        assert n == 0 or ((y >> (n - 1)) & 1) != ((y >> (n - 1 + p)) & 1), k


def test_checks_accept_and_reject() -> None:
    certs = spl.certificates(tuple(range(0, 13)))
    for high, low in zip(certs[1:], certs[:-1]):
        assert spl.link_ok(high, low)
    for cert in certs:
        assert spl.min_period_ok(cert) and spl.preperiod_ok(cert)
    k, n, p, a, w = certs[10]
    assert not spl.link_ok((k, n, p, a, w ^ 1), certs[9])
    assert not spl.min_period_ok((k, n, 2 * p, a, w | (w << p)))
    assert not spl.preperiod_ok((k, n + 1, p, a | ((w & 1) << n), (w >> 1) | ((w & 1) << (p - 1))))
    assert (k, n, p, a, w) == (10, 0, 12, 0, 0b010010001001)


def test_lean_data_matches_module() -> None:
    text = LEAN.read_text(encoding="utf-8")
    rows = spl.lean_data(spl.certificates(tuple(range(0, 13)))).splitlines()[1:]
    for row in rows:
        assert row.rstrip(",]") + "," in text
