"""Onsets of the left diagonals over every seed row, and the lemmas a seed-uniform induction on them would use.

A seed row is white left of a black cell lo, with cells x_1, x_2, ... right of it. Its left diagonals
D_i(t) = cell(t, lo - t + i) obey the single cell's recurrence D_{i+2}(t+1) = D_i(t) xor (D_{i+1}(t) or D_{i+2}(t))
with D_{-1} = D_{-2} = 0, from D_0(0) = 1 and D_i(0) = x_i, so D_i depends on x_1 .. x_i only, and the row at any
later time t is again a seed row, with x_i = D_i(t). The vector v_t = (D_0(t), D_1(t), ...) evolves by itself: bit k
of v_{t+1} is bit k - 2 of v_t xor (bit k - 1 or bit k). The onset T_i of a seed is the least T from which D_i repeats
with period P (a multiple of every period met; the onset does not depend on which multiple), read on the times
0 .. H - 1: the least T with D_i(t + P) = D_i(t) for T <= t <= H - 1 - P. If every onset of every diagonal <= i read
this way is at most H - 1 - P, then v_t restricted to the diagonals <= i repeats from the largest of them on, so the
window onsets are the true ones. M_i is the largest onset of diagonal i over all 2^i seeds, and M'_i = max(M_{i-1}, M_i)
is the largest pair onset S_i = max(T_{i-1}, T_i).

- `scalar_onsets`: one seed, the vector as a Python integer (the independent check).
- `onset_table`: every seed of x_1 .. x_J at once, bit-packed across seeds, and the onset of every depth for every seed.
- `exhaustive_max`, `pruned_max`: the C searches `seed_onsets_search.c` (every seed, with the number of seeds that reach
  the largest onset) and `seed_onsets_prune.c` (branch and bound), compiled on first use.
- `driven_max`: the relaxation the branch and bound uses. From S_i on, the diagonals past i are those of a row driven by
  the periodic pair (D_{i-1}, D_i) from some vector; G_m(pair) is the largest onset of driven diagonal m over all 2^m
  vectors, so T_{i+m} <= S_i + G_m(pair) for every seed.
- `skeleton`: the periodic parts of the single cell's diagonals. Up to depth 53,206 every seed's periodic parts are those
  of the single cell shifted in time (the only memory is at the white diagonals 2, 7, 28 and 399, each after a diagonal
  of odd weight, where the two choices differ by a shift), which the table checks on the depths it reads
  (`same_skeleton`).

    python -m computations.seed_onsets --exhaustive 38              # about 8 min on two cores
    python -m computations.seed_onsets --prune 76 --K 0             # branch and bound to depth 76, about 47 min
    python -m computations.seed_onsets --lemmas 20                  # every seed of 20 cells, a few seconds
    python -m computations.seed_onsets --relax 80 --m 16            # the driven relaxation, about 15 s
    python -m computations.seed_onsets --sample 1000 --samples 200  # random seeds, about 20 s
"""

from __future__ import annotations

import argparse
import functools
import os
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

import numpy as np
from tqdm.auto import tqdm

from computations.settled_slope import stream

HERE = Path(__file__).resolve().parent
U64 = np.uint64
ALL = U64(0xFFFFFFFFFFFFFFFF)


def ceil_three_halves(j: np.ndarray | int) -> np.ndarray | int:
    """ceil(3j/2)."""
    return -(-3 * j // 2)


def scalar_onsets(v0: int, depth: int, H: int, P: int) -> np.ndarray:
    """Onsets of diagonals 0 .. depth from the vector v0 (bit i = D_i(0)), one Python integer per time."""
    n = depth + 1
    mask = (1 << n) - 1
    v = v0 & mask
    ring = [0] * P
    last = np.full(n, -1, dtype=np.int64)  # (n,): the last t - P with D_i(t) != D_i(t - P)
    for t in range(H):
        if t >= P:
            d = v ^ ring[t % P]
            while d:
                low = d & -d
                last[low.bit_length() - 1] = t - P
                d ^= low
        ring[t % P] = v
        v = ((v << 2) ^ ((v << 1) | v)) & mask
    return last + 1  # (n,)


def seed_vector(x: str) -> int:
    """The vector (1, x_1, x_2, ...) of the seed with cells x_1 x_2 ... as an integer, bit i = D_i(0)."""
    return 1 | sum(1 << (k + 1) for k, c in enumerate(x) if c == "1")


def seed_rows(J: int) -> np.ndarray:
    """D_i(0) for i = 0 .. J over the 2^J seeds s (x_i = bit i - 1 of s), bit-packed: row i, bit s of the row."""
    s = np.arange(1 << J, dtype=np.uint64)  # (2^J,)
    rows = np.empty((J + 1, max(1, (1 << J) // 64)), dtype=U64)  # (J + 1, W)
    for i in range(J + 1):
        bits = np.ones(1 << J, dtype=np.uint8) if i == 0 else ((s >> U64(i - 1)) & U64(1)).astype(np.uint8)  # (2^J,)
        if J >= 6:
            rows[i] = np.packbits(bits, bitorder="little").view(U64)
        else:
            rows[i] = U64(int(sum(int(b) << k for k, b in enumerate(bits))))
    return rows


def step_rows(D: np.ndarray, left: np.ndarray | None = None) -> np.ndarray:
    """One time step of bit-packed diagonals: row i of the result is D_{i-2} xor (D_{i-1} or D_i), rows -2 and -1 being
    `left` (two rows, white if None)."""
    # D: (n, W); left: (2, W)
    pad = np.concatenate([np.zeros((2, D.shape[1]), dtype=U64) if left is None else left, D])  # (n + 2, W)
    return pad[:-2] ^ (pad[1:-1] | pad[2:])  # (n, W)


def onset_table(J: int, H: int, P: int = 8, progress: bool = False) -> np.ndarray:
    """The onset of every diagonal 0 .. J for every seed x_1 .. x_J (row s: x_i = bit i - 1 of s)."""
    D = seed_rows(J)  # (J + 1, W)
    n = 1 << J
    ring = np.zeros((P,) + D.shape, dtype=U64)  # (P, J + 1, W)
    last = np.full((J + 1, n), -1, dtype=np.int16)  # (J + 1, 2^J)
    for t in tqdm(range(H), desc=f"onset table J={J}", file=sys.stderr, mininterval=5, disable=not progress):
        if t >= P:
            d = D ^ ring[t % P]  # (J + 1, W)
            for i in np.flatnonzero(d.any(axis=1)):
                bits = np.unpackbits(d[i].view(np.uint8), bitorder="little")[:n].astype(bool)  # (2^J,)
                last[i, bits] = t - P
        ring[t % P] = D
        D = step_rows(D)
    onsets = (last + 1).T.copy()  # (2^J, J + 1)
    assert onsets.max() <= H - 1 - P, "horizon too short for the onsets"
    return onsets


def skeleton(depth: int, P: int = 64) -> tuple[np.ndarray, np.ndarray]:
    """The single cell's onsets (depth + 1,) and periodic parts: row r is D_i(base + r) for r < P, with base a multiple
    of P after every onset."""
    steps = 2 * depth + 4 * P
    steps -= steps % P
    d = stream(depth, steps, period=P, window=P, progress=False)
    assert d.onset.max() <= steps - 2 * P
    return d.onset, d.tail  # (depth + 1,), (P, depth + 1)


def driven_max(a: np.ndarray, b: np.ndarray, m: int, H: int, P: int = 8) -> np.ndarray:
    """G_0 .. G_m: the largest onset of driven diagonal k over all 2^k initial vectors, the diagonals -2 and -1 being the
    words a and b repeated from time 0 (a, b of length P)."""
    rows = seed_rows(m)[1:] if m >= 1 else np.zeros((0, 1), dtype=U64)  # (m, W): driven diagonal k at bit k - 1
    W = rows.shape[1]
    lanes = 1 << m
    full = ALL if lanes >= 64 else U64((1 << lanes) - 1)
    ring = np.zeros((P,) + rows.shape, dtype=U64)  # (P, m, W)
    last = np.full(m, -1, dtype=np.int64)  # (m,)
    E = rows
    for t in range(H):
        if t >= P:
            last[(E ^ ring[t % P]).any(axis=1)] = t - P
        ring[t % P] = E
        left = np.array([[full if a[t % P] else 0] * W, [full if b[t % P] else 0] * W], dtype=U64)  # (2, W)
        E = step_rows(E, left)
    G = np.concatenate([[0], last + 1])  # (m + 1,)
    assert G.max() <= H - 1 - P, "horizon too short for the driven onsets"
    return G


def driven_scalar(a: np.ndarray, b: np.ndarray, w: int, m: int, H: int, P: int = 8) -> np.ndarray:
    """Onsets of driven diagonals 1 .. m (index 0 unused, 0) from the vector w (bit k - 1 = diagonal k at time 0), one
    time step at a time: the independent check of `driven_max`."""
    E = [0, 0] + [(w >> (k - 1)) & 1 for k in range(1, m + 1)]  # index k + 1 = driven diagonal k, k = -1 .. m
    hist = np.zeros((H, m + 1), dtype=np.uint8)  # (H, m + 1)
    for t in range(H):
        E[0], E[1] = int(a[t % P]), int(b[t % P])
        hist[t, 1:] = E[2:]
        E = E[:2] + [E[k - 2] ^ (E[k - 1] | E[k]) for k in range(2, m + 2)]
    out = np.zeros(m + 1, dtype=np.int64)  # (m + 1,)
    for k in range(1, m + 1):
        diff = np.flatnonzero(hist[P:, k] != hist[:-P, k])  # (·,)
        out[k] = diff.max() + 1 if diff.size else 0
    return out


def relaxation_table(depth: int, m: int, H: int, P: int = 8, progress: bool = True) -> np.ndarray:
    """R[i, k] = max over phases phi of G_k(pair i at phi), the pair (D_{i-1}, D_i) of the single cell's periodic parts,
    for 1 <= i <= depth (row 0 unused). P must be a multiple of every period to `depth` (8 below depth 400)."""
    _, tail = skeleton(depth)  # tail: (64, depth + 1)
    R = np.zeros((depth + 1, m + 1), dtype=np.int64)  # (depth + 1, m + 1)
    for i in tqdm(range(1, depth + 1), desc="relaxation", file=sys.stderr, mininterval=5, disable=not progress):
        for phi in range(P):
            a, b = tail[phi:phi + P, i - 1], tail[phi:phi + P, i]  # (P,), (P,)
            R[i] = np.maximum(R[i], driven_max(a, b, m, H, P))
    return R


def same_skeleton(onsets: np.ndarray, J: int, H: int, P: int = 8) -> bool:
    """Whether every seed x_1 .. x_J has, at every depth <= J, the single cell's periodic part shifted in time: checked on
    the times H - P .. H - 1, after every onset."""
    _, tail = skeleton(J)  # (64, J + 1)
    D = seed_rows(J)  # (J + 1, W)
    for _ in range(H - P):
        D = step_rows(D)
    window = np.zeros((P, J + 1, D.shape[1]), dtype=U64)  # (P, J + 1, W)
    for r in range(P):
        window[r] = D
        D = step_rows(D)
    assert onsets.max() <= H - P - 1
    n = 1 << J
    ok = np.zeros((J + 1, n), dtype=bool)  # (J + 1, 2^J)
    bits = np.stack([np.unpackbits(window[r].view(np.uint8), axis=-1, bitorder="little")[:, :n] for r in range(P)])
    # bits: (P, J + 1, 2^J)
    for phi in range(P):
        ref = tail[phi:phi + P, :J + 1]  # (P, J + 1)
        ok |= (bits == ref[:, :, None]).all(axis=0)
    return bool(ok.all())


# ---------------------------------------------------------------------------------------------------------------------
# The C searches


@functools.cache
def _binary(name: str) -> Path:
    """Compile computations/<name>.c once per process into a temporary directory."""
    cc = shutil.which("cc") or shutil.which("gcc")
    assert cc, "a C compiler is needed for the searches"
    out = Path(tempfile.mkdtemp(prefix="seed_onsets_")) / name
    flags = ["-O3", "-march=native"] if os.environ.get("SEED_ONSETS_FAST", "1") == "1" else ["-O1"]
    subprocess.run([cc, *flags, "-fopenmp", "-w", str(HERE / f"{name}.c"), "-o", str(out)], check=True)
    return out


@dataclass(frozen=True, slots=True)
class Search:
    best: np.ndarray  # (J + 1,) largest onset of each depth over all seeds
    seeds: list[str]  # a seed x_1 .. x_j that reaches it
    count: np.ndarray | None  # (J + 1,) number of seeds x_1 .. x_j that reach it (exhaustive search only)
    largest: int  # the largest onset the search computed, to compare with H - 9
    nodes: int = 0  # nodes of the branch and bound


def exhaustive_max(J: int, H: int, split: int = 8, threads: int = 1, progress: bool = False) -> Search:
    """Every seed of x_1 .. x_J (`seed_onsets_search.c`, period 8)."""
    run = subprocess.run([str(_binary("seed_onsets_search")), str(J), str(H), "8", str(min(split, J - 9))],
                         stdout=subprocess.PIPE, stderr=None if progress else subprocess.DEVNULL, text=True,
                         check=True, env={**os.environ, "OMP_NUM_THREADS": str(threads)})
    lines = [ln.split() for ln in run.stdout.strip().splitlines()]
    best = np.array([int(ln[1]) for ln in lines], dtype=np.int64)  # (J + 1,)
    count = np.array([int(ln[2]) for ln in lines], dtype=np.int64)  # (J + 1,)
    seeds = [ln[3] if len(ln) > 3 else "" for ln in lines]
    return Search(best, seeds, count, int(best.max()))


def pruned_max(J: int, H: int, K: int, split: int = 10, hints: list[str] | None = None, threads: int = 1,
               progress: bool = False) -> Search:
    """Branch and bound over the seeds of x_1 .. x_J (`seed_onsets_prune.c`, period 8), with driven bounds to K
    diagonals and `hints` (seeds evaluated first). The progress of the tasks goes to stderr if `progress`."""
    run = subprocess.run([str(_binary("seed_onsets_prune")), str(J), str(H), str(K), str(min(split, J))],
                         input="\n".join(hints or []) + "\n", stdout=subprocess.PIPE,
                         stderr=None if progress else subprocess.DEVNULL, text=True, check=True,
                         env={**os.environ, "OMP_NUM_THREADS": str(threads)})
    lines = run.stdout.strip().splitlines()
    rows = [ln.split() for ln in lines[:J + 1]]
    best = np.array([int(r[1]) for r in rows], dtype=np.int64)  # (J + 1,)
    seeds = [r[2] if len(r) > 2 else "" for r in rows]
    largest = int(lines[J + 1].split()[-1])
    return Search(best, seeds, None, largest, int(lines[J + 2].split()[-1]))


# ---------------------------------------------------------------------------------------------------------------------
# The lemmas


def offset_over(M: np.ndarray) -> int:
    """The least c with M_j <= ceil(3j/2) + c for every j in the range (negative if M stays below)."""
    j = np.arange(len(M))  # (n,)
    return int((M - ceil_three_halves(j)).max())


def pair_max(M: np.ndarray) -> np.ndarray:
    """M'_j = max(M_{j-1}, M_j), M'_0 = M_0."""
    out = M.copy()  # (n,)
    out[1:] = np.maximum(M[1:], M[:-1])
    return out


def pair_onsets(onsets: np.ndarray) -> np.ndarray:
    """S_j = max(T_{j-1}, T_j) for every seed (S_0 = T_0)."""
    S = onsets.astype(np.int64)  # (seeds, J + 1)
    S[:, 1:] = np.maximum(onsets[:, 1:], onsets[:, :-1])
    return S


def increments(onsets: np.ndarray) -> np.ndarray:
    """inc[i, k] = max over seeds of S_{i+k} - S_i, for i + k <= J (-10^9 elsewhere)."""
    S = pair_onsets(onsets)  # (seeds, J + 1)
    n = S.shape[1]
    inc = np.full((n, n), -10**9, dtype=np.int64)  # (J + 1, J + 1)
    for i in range(n):
        inc[i, :n - i] = (S[:, i:] - S[:, i:i + 1]).max(axis=0)
    return inc


def subadditive_failures(Mp: np.ndarray) -> list[tuple[int, int, int]]:
    """The (a, b, excess) with a <= b, a + b in the range and M'_{a+b} > M'_a + M'_b."""
    out = []
    for a in range(1, len(Mp)):
        for b in range(a, len(Mp) - a):
            if Mp[a + b] > Mp[a] + Mp[b]:
                out.append((a, b, int(Mp[a + b] - Mp[a] - Mp[b])))
    return out


def random_onsets(depth: int, samples: int, seed: int = 5, progress: bool = True) -> tuple[np.ndarray, list[str]]:
    """Onsets of diagonals 0 .. depth (period 64) for `samples` seeds with x_1 .. x_depth fair coins, and the seeds."""
    H = 2 * depth + 200
    rng = np.random.default_rng(seed)
    out = np.zeros((samples, depth + 1), dtype=np.int64)  # (samples, depth + 1)
    seeds = []
    for k in tqdm(range(samples), desc=f"random seeds to depth {depth}", file=sys.stderr, mininterval=5,
                  disable=not progress):
        x = int.from_bytes(rng.bytes(depth // 8 + 1), "little") & ((1 << depth) - 1)
        seeds.append("".join(str((x >> i) & 1) for i in range(depth)))
        out[k] = scalar_onsets(1 | (x << 1), depth, H, 64)
    assert out.max() <= H - 64 - 1, "horizon too short"
    return out, seeds


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--exhaustive", type=int, default=0, help="depth J of the exhaustive search")
    parser.add_argument("--prune", type=int, default=0, help="depth J of the branch and bound")
    parser.add_argument("--K", type=int, default=24, help="driven bounds to K diagonals")
    parser.add_argument("--H", type=int, default=0, help="horizon, a multiple of 8 (default from J)")
    parser.add_argument("--threads", type=int, default=2)
    parser.add_argument("--hints", help="file of seeds to evaluate first (default the seed x_3 = 1)")
    parser.add_argument("--lemmas", type=int, default=0, help="the lemma checks on every seed of this many cells")
    parser.add_argument("--relax", type=int, default=0, help="the relaxation table to this depth (with --m)")
    parser.add_argument("--m", type=int, default=16)
    parser.add_argument("--sample", type=int, default=0, help="random seeds to this depth (with --samples)")
    parser.add_argument("--samples", type=int, default=200)
    args = parser.parse_args()

    if args.exhaustive:
        J = args.exhaustive
        H = args.H or 8 * ((3 * J // 2 + 40) // 8)
        s = exhaustive_max(J, H, split=10, threads=args.threads, progress=True)
        assert s.largest <= H - 9, "horizon too short"
        print(f"every seed x_1 .. x_{J}, horizon {H}, period 8: the largest onset of each depth")
        print(f"{'j':>3} {'M_j':>4} {'ceil(3j/2)':>10} {'seeds':>12}  a worst seed x_1 ..")
        for j in range(J + 1):
            print(f"{j:>3} {s.best[j]:>4} {ceil_three_halves(j):>10} {s.count[j]:>12}  {s.seeds[j]}")
        print(f"least c with M_j <= ceil(3j/2) + c for j <= {J}: {offset_over(s.best)}")

    if args.prune:
        J = args.prune
        H = args.H or 8 * ((2 * J + 48) // 8)
        hints = Path(args.hints).read_text().split() if args.hints else ["001"]
        s = pruned_max(J, H, args.K, split=12, hints=hints, threads=args.threads, progress=True)
        assert s.largest <= H - 9, "horizon too short"
        print(f"branch and bound over the seeds x_1 .. x_{J}, horizon {H}, driven bounds to {args.K} diagonals, "
              f"{s.nodes} nodes, largest onset computed {s.largest}")
        print(f"{'j':>3} {'M_j':>4} {'ceil(3j/2)':>10} {'M_j - j':>8}  a worst seed x_1 ..")
        for j in range(J + 1):
            print(f"{j:>3} {s.best[j]:>4} {ceil_three_halves(j):>10} {s.best[j] - j:>8}  {s.seeds[j]}")
        print(f"least c with M_j <= ceil(3j/2) + c for j <= {J}: {offset_over(s.best)}")

    if args.lemmas:
        J = args.lemmas
        T = onset_table(J, 3 * J + 40, progress=True)  # (2^J, J + 1)
        M = T.max(axis=0)  # (J + 1,)
        print(f"every seed x_1 .. x_{J}: M_j = {M.tolist()}")
        print(f"same skeleton up to a shift for every seed and depth: {same_skeleton(T, J, 3 * J + 40)}")
        inc = increments(T)  # (J + 1, J + 1)
        print("largest S_{i+k} - S_i over seeds and i, k = 1 ..:", [int(inc[:, k].max()) for k in range(1, J + 1)])
        print("subadditivity failures (a, b, excess):", subadditive_failures(pair_max(M))[:10])

    if args.relax:
        H = 4 * args.m + 48
        R = relaxation_table(args.relax, args.m, H)  # (relax + 1, m + 1)
        k = np.arange(args.m + 1)  # (m + 1,)
        worst = R[1:].max(axis=0)  # (m + 1,)
        print(f"relaxation G_k (max over phases and depths 1 .. {args.relax}) for k = 0 .. {args.m}: {worst.tolist()}")
        print("  minus ceil(3k/2):", (worst - ceil_three_halves(k)).tolist())


    if args.sample:
        depth = args.sample
        R, seeds = random_onsets(depth, args.samples)  # (samples, depth + 1)
        single = scalar_onsets(1, depth, 2 * depth + 200, 64)  # (depth + 1,)
        j = np.arange(depth + 1)  # (depth + 1,)
        over = R - single  # (samples, depth + 1)
        print(f"{args.samples} random seeds, diagonals 0 .. {depth}")
        for lo, hi in [(20, 69), (69, 139), (139, 300), (300, 600), (600, depth + 1)]:
            if lo > depth:
                break
            seg = over[:, lo:hi].max(axis=0)  # (hi - lo,)
            print(f"  j in [{lo}, {hi}): max T_j - T_j(single) = {seg.max()} at j = {lo + int(seg.argmax())}; "
                  f"max T_j - ceil(3j/2) = {int((R[:, lo:hi] - ceil_three_halves(j[lo:hi])).max())}")
        two = scalar_onsets(seed_vector("001"), depth, 2 * depth + 200, 64)  # (depth + 1,): the seed x_3 = 1
        delay = two - single  # (depth + 1,)
        stop = next((jj for jj in range(11, depth + 1) if delay[jj] != 6), depth + 1)
        print(f"the seed x_3 = 1: T_j - T_j(single) = 6 for 11 <= j <= {stop - 1}"
              + (f", {delay[stop]} at j = {stop} (T_j = {two[stop]}, single {single[stop]})" if stop <= depth else ""))
        first = next(((jj, int(np.argmax(over[:, jj]))) for jj in range(20, depth + 1) if over[:, jj].max() > 8), None)
        if first:
            print(f"first j >= 20 with a seed above T_j(single) + 8: j = {first[0]}, T_j = {R[first[1], first[0]]}, "
                  f"single {single[first[0]]}, seed x_1 .. x_{first[0]} = {seeds[first[1]][:first[0]]}")


if __name__ == "__main__":
    main()
