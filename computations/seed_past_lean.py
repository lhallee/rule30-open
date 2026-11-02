"""Certificates of the single cell's past for the Lean kernel, and the window checks it runs on them.

`frames.seed_past` carries rho_k = Phi^-k(1) exactly as a prefix and a period word. Here each is packed as a
certificate (k, N, P, a, w): bit j of rho_k is bit j of a for j < N and bit (j - N) mod P of w from N on. The Lean module
`Rule30Open.Frames.SeedPastTable` stores the certificates for k = 0 .. 66, 300, 1000 and 3000 and checks, in the
kernel, the same three things that `link_ok`, `min_period_ok` and `preperiod_ok` check here on integers:

* a link from the certificate of k to that of k + d: d steps of Phi on the first B bits of rho_(k + d), with
  B = max(N + 2d, N') + P past both preperiods by a full period, give the first B bits of rho_k, and P' divides P;
* the period P is minimal: no q < P is a period of the window of P bits at N;
* the preperiod N is minimal for that period: bit N - 1 differs from bit N - 1 + P.

    python -m computations.seed_past_lean   # the data of SeedPastTable.lean, with the checks
"""

from __future__ import annotations

import sys

from tqdm.auto import tqdm

from computations.frames import phi, seed_past


Certificate = tuple[int, int, int, int, int]  # (k, N, P, a, w)

LEAN_KS: tuple[int, ...] = (*range(0, 67), 300, 1000, 3000)


def certificates(ks: tuple[int, ...] = LEAN_KS) -> list[Certificate]:
    """The certificates of rho_k for the k in `ks`, in increasing order; rho_0 = 1 is (0, 1, 1, 1, 0)."""
    wanted = sorted(set(ks))
    out: list[Certificate] = [(0, 1, 1, 1, 0)] if wanted and wanted[0] == 0 else []
    top = wanted[-1]
    picks = set(wanted)
    for k, prefix, period in tqdm(seed_past(top), total=top, desc="seed past", unit="step", file=sys.stderr,
                                  disable=top < 500):
        if k in picks:
            a = sum(bit << i for i, bit in enumerate(prefix))
            w = sum(bit << i for i, bit in enumerate(period))
            out.append((k, len(prefix), len(period), a, w))
    return out


def expand(cert: Certificate, bits: int) -> int:
    """The first `bits` bits of the certificate's sequence, as an integer."""
    _, n, p, a, w = cert
    word = w % (1 << p)
    copies = bits // p + 1
    rep = 0
    for i in range(copies):
        rep |= word << (i * p)
    return ((a % (1 << n)) | (rep << n)) % (1 << bits)


def link_ok(high: Certificate, low: Certificate) -> bool:
    """d = k - k' steps of Phi take the certificate `high` of k to the certificate `low` of k' < k, on a window past
    both preperiods by a full period of `high`, whose period is a multiple of that of `low`."""
    k1, n1, p1, _, _ = high
    k0, n0, p0, _, _ = low
    d = k1 - k0
    if d <= 0 or p1 == 0 or p0 == 0 or p1 % p0 != 0:
        return False
    bits = max(n1 + 2 * d, n0) + p1
    y = expand(high, bits)
    for _ in range(d):
        y = phi(y, bits)
    return y == expand(low, bits)


def min_period_ok(cert: Certificate) -> bool:
    """No q with 0 < q < P is a period of the window of P bits at N, so no q < P is an eventual period."""
    _, n, p, _, _ = cert
    window = expand(cert, n + 2 * p) >> n
    mask = (1 << p) - 1
    return all(((window >> q) ^ window) & mask != 0 for q in range(1, p))


def preperiod_ok(cert: Certificate) -> bool:
    """N = 0, or bit N - 1 differs from bit N - 1 + P, so the period P does not start before N."""
    _, n, p, _, _ = cert
    if n == 0:
        return True
    y = expand(cert, n + p)
    return (y >> (n - 1)) & 1 != (y >> (n - 1 + p)) & 1


def lean_data(certs: list[Certificate]) -> str:
    """The certificate list of SeedPastTable.lean, base case excluded."""
    rows = [f"  ({k}, {n}, {p}, 0x{a:x}, 0x{w:x})" for k, n, p, a, w in certs if k > 0]
    return "def seedCerts : List (Nat × Nat × Nat × Nat × Nat) := [\n" + ",\n".join(rows) + "]\n"


def main() -> None:
    certs = certificates()
    for high, low in zip(certs[1:], certs[:-1]):
        assert link_ok(high, low), (high[0], low[0])
    for cert in certs:
        assert min_period_ok(cert) and preperiod_ok(cert), cert[0]
    for k, n, p, _, _ in certs:
        if k in (1, 2, 4, 10, 18, 28, 30, 66, 300, 1000, 3000):
            print(f"k = {k}: preperiod {n}, period {p}", file=sys.stderr)
    print(lean_data(certs), end="")


if __name__ == "__main__":
    main()
