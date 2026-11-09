"""The left cut of the cone for every t: white and late-seed completions separate the a leftmost cells.

c_t is a Boolean function of the 2t + 1 cells x_{-t} .. x_t of row 0 (new x_j = x_{j-1} xor (x_j or x_{j+1})). A row of
the cone is a number N with bit k equal to x_{-t+k}; one step is `nstep` (bit k becomes bit k xor (bit k+1 or bit k+2)),
the frame moving one cell right, and c_t is bit 0 after t steps. The a leftmost cells are the low bits P < 2^a, the
completion (cells from -t + a on) the number r, and N = 2^a r + P.

* The probes at t are the white completion r = 0 and the late seeds r = 2^mu, mu = 2(T1 - R) - d, T1 = t - ceil(a/2),
  0 <= R <= Rmax, d in {0, 1}, inside the cone (T1 >= R + d): the single black cell at t - (a % 2) - 2R - d.
* `separates` tells whether the probes give the 2^a settings pairwise different centers, from plain runs of the rule,
  bit-sliced over the settings (`centers_plain`); `separates_all_single` the same for the white completion and every
  completion with one black cell. `least_R` gives the least Rmax that does, `scan` the last t at which
  no Rmax does (t_f) and the largest least Rmax above it (R_a).
* `edge_frame` is the single black cell read from its left edge (bit j is the cell j places right of it):
  Z_0 = 1, Z_{s+1} = 4 Z_s xor (2 Z_s or Z_s). `edge_period` gives the period and the onset of its low J bits.
* `late_check` mirrors the kernel check of the Lean module `LateSeedCut` exactly: the a cells of every setting packed in
  one number (`pack_init`, `pack_step`), run the last m = min(t, ceil(a/2) + Rmax + 1) steps from every value v of the
  left cells after the white stretch, split by the columns as `LeftCut.refineMasks` does.
* `lean_params` gives the parameters of the module for each a: (lateStart, Rmax, J, p, s0), and `--lean` prints them.

    python -m computations.late_seed_cut --scan 2 10 --tmax 80       # t_f(a) and R_a for a = 2 .. 10 (a few seconds)
    python -m computations.late_seed_cut --check 2 10                # the module's checks, mirrored (a few seconds)
    python -m computations.late_seed_cut --edge 64                   # periods and onsets of the left edge, J <= 64
    python -m computations.late_seed_cut --lean 2 10                 # the parameters written into LateSeedCut
    python -m computations.late_seed_cut --below 2 13 --tmax 100     # below the threshold, every single black cell
"""

from __future__ import annotations

import argparse

from tqdm.auto import tqdm


def nstep(r: int) -> int:
    """One step of Rule 30 on a row read as a number, the frame moving one cell right."""
    return r ^ ((r >> 1) | (r >> 2))


def nevo(r: int, s: int) -> int:
    """`nstep` applied s times."""
    for _ in range(s):
        r = nstep(r)
    return r


def late_cen(a: int, t: int, r: int, P: int) -> int:
    """c_t of the row with the bits of P on the cells -t .. -t + a - 1 and the bits of r from -t + a on."""
    return nevo((r << a) + P, t) & 1


def seed_pos(a: int, t: int, R: int, d: int) -> int:
    """The position mu of the late seed (R, d) counted from the cut (bit mu of the completion)."""
    return 2 * (t - (a + 1) // 2 - R) - d


def probe_list(a: int, t: int, Rmax: int) -> list[int]:
    """The completions of the probes at t, as numbers: white, then the seeds (R, d) inside the cone (`lateProbes`)."""
    T1 = t - (a + 1) // 2
    out = [0]
    for R in range(Rmax + 1):
        for d in (0, 1):
            if T1 >= R + d:
                out.append(1 << seed_pos(a, t, R, d))
    return out


def cell_pattern(i: int, n: int) -> int:
    """`LeftCut.cellPattern i n`: bit P is bit i of P, for P < 2^n, built by doubling the number of settings."""
    v = 0
    for m in range(n):
        half = 1 << (1 << m)  # 2^(2^m)
        v = v + half * ((half - 1) if i == m else v)
    return v


def slices(a: int) -> list[int]:
    """The a cells of every setting: entry k has bit P equal to bit k of P, for P < 2^a. List of a ints of 2^a bits."""
    return [cell_pattern(k, a) for k in range(a)]


def centers_plain(a: int, t: int, r: int) -> int:
    """c_t for all 2^a settings at once (bit P), by a plain run of the 2t + 1 cone cells, bit-sliced over P."""
    ones = (1 << (1 << a)) - 1
    row = slices(a) + [ones if (r >> k) & 1 else 0 for k in range(2 * t + 1 - a)]  # (2t + 1,) ints of 2^a bits
    for _ in range(t):
        row = [row[i] ^ ((row[i + 1] if i + 1 < len(row) else 0) | (row[i + 2] if i + 2 < len(row) else 0))
               for i in range(len(row) - 2)]  # (len - 2,)
    return row[0]


def refine_masks(cols: list[int], a: int) -> bool:
    """`LeftCut.refineMasks` on the mask of all 2^a settings: true when the columns split it into single settings."""
    masks = [(1 << (1 << a)) - 1]
    for col in cols:
        new = []
        for m in masks:
            for u in (m & col, m ^ (m & col)):
                if u & (u - 1):
                    new.append(u)
        masks = new
    return not masks


def separates(a: int, t: int, Rmax: int) -> bool:
    """Do the white and late-seed probes with R <= Rmax separate the 2^a settings at t (plain runs)?"""
    return refine_masks([centers_plain(a, t, r) for r in probe_list(a, t, Rmax)], a)


def separates_all_single(a: int, t: int) -> bool:
    """Do the white completion and every completion with one black cell (any cell -t + a .. t) separate at t?"""
    cols = [centers_plain(a, t, 0)] + [centers_plain(a, t, 1 << mu) for mu in range(2 * t + 1 - a)]
    return refine_masks(cols, a)


def least_R(a: int, t: int, Rcap: int) -> int | None:
    """The least Rmax <= Rcap whose probes separate at t, or None."""
    T1 = t - (a + 1) // 2
    cols = [centers_plain(a, t, 0)]
    for R in range(Rcap + 1):
        for d in (0, 1):
            if T1 >= R + d:
                cols.append(centers_plain(a, t, 1 << seed_pos(a, t, R, d)))
        if refine_masks(cols, a):
            return R
    return None


def scan(a: int, tmax: int) -> tuple[int, int, list[int | None]]:
    """For t = a + 1 .. tmax: the least R at each t (cap 2a + 6), t_f (the last t with none, a if none fails) and R_a
    (the largest least R above t_f)."""
    res = [least_R(a, t, 2 * a + 6) for t in tqdm(range(a + 1, tmax + 1), desc=f"a={a}", leave=False)]
    fails = [a + 1 + i for i, R in enumerate(res) if R is None]
    tf = max(fails) if fails else a
    Ra = max(R for i, R in enumerate(res) if a + 1 + i > tf and R is not None)
    return tf, Ra, res


def edge_frame(s: int) -> int:
    """The single black cell after s steps read from its left edge: bit j is the cell j places right of the edge."""
    Z = 1
    for _ in range(s):
        Z = (Z << 2) ^ ((Z << 1) | Z)
    return Z


def edge_period(J: int, horizon: int | None = None) -> tuple[int, int]:
    """The period p and the onset s0 of the low J bits of the edge frame: the least p with Z_{s+p} = Z_s mod 2^J for
    all large s, and the least s0 from which it holds. The low bits follow a map of their own, so the first value that
    repeats is Z_{s0} mod 2^J, and it repeats after p steps."""
    mask = (1 << J) - 1
    horizon = horizon or 8 * J + 200
    hist = []  # (horizon,) low J bits of Z_s
    Z = 1
    for _ in range(horizon):
        hist.append(Z & mask)
        Z = ((Z << 2) ^ ((Z << 1) | Z)) & mask
    seen: dict[int, int] = {}
    for s, h in enumerate(hist):
        if h in seen:
            s0, p = seen[h], s - seen[h]
            return p, s0
        seen[h] = s
    raise ValueError("no repetition within the horizon")


_PACK_INIT: dict[int, int] = {}


def pack_init(a: int) -> int:
    """`packInit a a`: block k (bits k 2^a .. (k+1) 2^a - 1), bit P is bit k of P. Kept per a."""
    if a not in _PACK_INIT:
        n = 1 << a
        _PACK_INIT[a] = sum(c << (k * n) for k, c in enumerate(slices(a)))
    return _PACK_INIT[a]


def bob_pack(a: int, r: int) -> int:
    """`bobPack`: two blocks of all ones or all zeros by bits 0 and 1 of r."""
    n = 1 << a
    ones = (1 << n) - 1
    return ((ones if (r >> 1) & 1 else 0) << n) + (ones if r & 1 else 0)


def pack_step(a: int, X: int, r: int) -> int:
    """`packStep`: one step of the a cells of every setting, the completion r."""
    n = 1 << a
    Y = (bob_pack(a, r) << (a * n)) + X
    return (Y ^ ((Y >> n) | (Y >> (2 * n)))) % (1 << (a * n))


def late_col(a: int, t: int, r: int) -> int:
    """`lateCol`: bit P is c_t of the row 2^a r + P, run packed."""
    X = pack_init(a)
    for _ in range(t):
        X = pack_step(a, X, r)
        r = nstep(r)
    return X % (1 << (1 << a))


def late_check(a: int, t: int, Rmax: int) -> bool:
    """`lateCheck`: the columns of the last m steps, from every value of the left cells after the white stretch."""
    m = min(t, (a + 1) // 2 + Rmax + 1)
    return refine_masks([late_col(a, m, nevo(r, t - m)) for r in probe_list(a, t, Rmax)], a)


def lean_params(a: int, tmax: int) -> tuple[int, int, int, int, int]:
    """(lateStart, Rmax, J, p, s0) for the module: lateStart = t_f + 1, Rmax = R_a, J = 2 Rmax + 3 and the period data
    of the low J bits of the left edge."""
    tf, Ra, _ = scan(a, tmax)
    J = 2 * Ra + 3
    p, s0 = edge_period(J)
    return tf + 1, Ra, J, p, s0


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--scan", nargs=2, type=int, metavar=("A0", "A1"))
    parser.add_argument("--tmax", type=int, default=80)
    parser.add_argument("--check", nargs=2, type=int, metavar=("A0", "A1"))
    parser.add_argument("--edge", type=int, metavar="JMAX")
    parser.add_argument("--lean", nargs=2, type=int, metavar=("A0", "A1"))
    parser.add_argument("--below", nargs=2, type=int, metavar=("A0", "A1"))
    args = parser.parse_args()
    if args.below:
        for a in range(args.below[0], args.below[1] + 1):
            tf, _, _ = scan(a, args.tmax)
            ok = [t for t in range(a + 1, tf + 1) if separates_all_single(a, t)]
            print(f"a={a}: t_f = {tf}; t in [{a + 1}, {tf}] where white and every single black cell separate: {ok}")
    if args.scan:
        for a in range(args.scan[0], args.scan[1] + 1):
            tf, Ra, res = scan(a, args.tmax)
            fails = [a + 1 + i for i, R in enumerate(res) if R is None]
            print(f"a={a}: fails at t={fails}, t_f={tf}, R_a={Ra} (t <= {args.tmax}); least R by t = {res}")
    if args.edge:
        for J in range(1, args.edge + 1):
            p, s0 = edge_period(J)
            print(f"J={J}: period {p}, onset {s0}")
    if args.check or args.lean:
        a0, a1 = args.check or args.lean
        for a in range(a0, a1 + 1):
            tA, R, J, p, s0 = lean_params(a, args.tmax)
            t0 = s0 + R + 1 + (a + 1) // 2
            if args.lean:
                print(f"a={a}: lateStart {tA}, Rmax {R}, J {J}, period {p}, onset {s0}; checks t in [{tA}, {t0 + p})")
            if args.check:
                ok = all(late_check(a, t, R) for t in tqdm(range(tA, t0 + p), desc=f"a={a}", leave=False))
                print(f"a={a}: the checks at t = {tA} .. {t0 + p - 1} pass: {ok}")


if __name__ == "__main__":
    main()
