"""Where three routes to a run slope below 3/5 for every driven left half stop.

The left half of any configuration that is white left of column 0 at time 0 is a function of column 0, the driver
c(0) = 1, c(1), c(2), ... (`run_mechanism.driven_rows`). In left-diagonal coordinates D_j(t) = cell(t, j - t) the
driver only sets the first value of each diagonal, D_j(j) = c(j), and for t >= j + 1 the rule reads
D_j(t) = D_{j-2}(t-1) xor (D_{j-1}(t-1) or D_j(t-1)), with D_{-1} = D_{-2} = 0. Three computations.

1. `right_end_first_times`: the first time at which each word of `width` cells is the right end (cells -1 .. -width)
   of some driven left half. Every word of up to 16 cells occurs, so no argument that only looks at the right end can
   exclude the alternating word; an exclusion must use the time.

2. `window_game_distances`: the window game in which a window of `width` cells at the right end of the left half moves
   with a free driver and a free cell entering from the left. The alternating word of `width` cells is reached from
   the white window in fewer than `width` steps, so a rank on such windows does not even give the light-cone bound.

3. `driver_pairs` and `skeleton`: the adjacent pairs (D_{j-1}, D_j) over every driver, deduplicated, with their periods,
   the number of their periodic parts up to a time shift, and the time from which they repeat (their onset); and the
   periodic parts of the single cell's diagonals: period, longest cyclic white run, longest cyclic run of antiphase
   alternation of the pair (D_{j-1}, D_j). `onset_bound` is the onset that the reset lemma gives from the white runs.

4. `white_followers`: at each white diagonal w of the single cell, whether the diagonal after it flips and whether
   its complement is a time shift of it. Only then does the time shift of `DrivenSkeleton` pass the white diagonal.

    python -m computations.run_slope_routes ends --width 16 --steps 100   # about 2 s
    python -m computations.run_slope_routes game --width 22               # about 25 s
    python -m computations.run_slope_routes pairs --depth 90              # about 3 min, 0.8 GB peak
    python -m computations.run_slope_routes skeleton --depth 8001         # about 7 s
    python -m computations.run_slope_routes followers --depth 59000 --steps 110000   # about 3 s
"""

from __future__ import annotations

import argparse
import sys
import time
from collections.abc import Iterator
from dataclasses import dataclass

import numpy as np

from computations.diagonal_cones import diagonal_table
from computations.left_diagonals import diagonals
from computations.run_mechanism import driven_rows

# ---------------------------------------------------------------------------------------------------------------------
# 1. Right ends of the driven left halves
# ---------------------------------------------------------------------------------------------------------------------


def alternating_word(width: int) -> int:
    """The right end that a black run leaves: bit k - 1 (cell -k) is black exactly for even k."""
    return sum(1 << (k - 1) for k in range(2, width + 1, 2))


def right_end_first_times(width: int, steps: int, progress: bool = False) -> np.ndarray:
    """For each word of `width` cells (bit k - 1 is cell -k), the first time t <= steps at which some driver makes it
    the right end of the left half, or -1."""
    assert width <= 63
    first = np.full(1 << width, -1, dtype=np.int64)  # (2^width,)
    mask = np.uint64((1 << width) - 1)
    start = time.time()
    for t, B, _ in driven_rows(steps):
        ends = np.unique((B[:, 0] & mask).astype(np.int64))  # (m,)
        new = ends[first[ends] < 0]  # (m',)
        first[new] = t
        if progress and t % 10 == 0:
            print(f"  t = {t}: {len(B)} rows, {(first >= 0).sum()} words, {time.time() - start:.0f} s", file=sys.stderr,
                  flush=True)
    return first  # (2^width,)


def first_times_by_width(first: np.ndarray, width: int) -> list[tuple[int, int, int, int]]:
    """From `right_end_first_times(width, ...)`: for w = 1 .. width, (w, number of words of w cells never seen, latest
    first time over the words seen, first time of the alternating word or -1)."""
    # first: (2^width,)
    out: list[tuple[int, int, int, int]] = []
    seen = first >= 0  # (2^width,)
    codes = np.arange(1 << width, dtype=np.int64)  # (2^width,)
    for w in range(1, width + 1):
        f = np.full(1 << w, np.iinfo(np.int64).max, dtype=np.int64)  # (2^w,)
        np.minimum.at(f, codes[seen] & ((1 << w) - 1), first[seen])
        ok = f < np.iinfo(np.int64).max  # (2^w,)
        alt = int(f[alternating_word(w)]) if ok[alternating_word(w)] else -1
        out.append((w, int((~ok).sum()), int(f[ok].max()) if ok.any() else -1, alt))
    return out


# ---------------------------------------------------------------------------------------------------------------------
# 2. The window game
# ---------------------------------------------------------------------------------------------------------------------


def window_game_distances(width: int) -> np.ndarray:
    """Breadth-first distance from the white window to every window of `width` cells (bit k - 1 is cell -k) when each
    step chooses the driver and the cell -(width + 1) freely; -1 for windows never reached."""
    n = 1 << width
    mask = np.int64(n - 1)
    dist = np.full(n, -1, dtype=np.int64)  # (2^width,)
    dist[0] = 0
    frontier = np.zeros(1, dtype=np.int64)  # (m,)
    s = 0
    while len(frontier):
        s += 1
        nxt = []
        for e in (0, 1):
            B = frontier | np.int64(e << width)  # (m,), bit width is the entering cell
            for c in (0, 1):
                nxt.append(((B >> 1) ^ (B | ((B << 1) | c))) & mask)  # (m,)
        y = np.unique(np.concatenate(nxt))  # (m',)
        frontier = y[dist[y] < 0]
        dist[frontier] = s
    return dist  # (2^width,)


# ---------------------------------------------------------------------------------------------------------------------
# 3. The left diagonals over every driver, and the single cell's
# ---------------------------------------------------------------------------------------------------------------------

PERIODS = (1, 2, 4, 8, 16, 32, 64)


def detect_periods(X: np.ndarray) -> np.ndarray:
    """For each row x of X (times 0 .. h - 1): the least power of two p <= 64 with x(t + p) = x(t) on the second half
    of the horizon, -1 if none."""
    # X: (n, h)
    n, h = X.shape
    per = np.full(n, -1, dtype=np.int64)  # (n,)
    for p in PERIODS:
        if 2 * p >= h // 2:
            break
        new = (X[:, h // 2 + p:] == X[:, h // 2:h - p]).all(axis=1) & (per < 0)  # (n,)
        per[new] = p
    return per  # (n,)


def onsets(X: np.ndarray, p: int, first: int) -> np.ndarray:
    """For each row x of X: the least T >= first with x(t + p) = x(t) for every T <= t < h - p."""
    # X: (n, h)
    h = X.shape[1]
    eq = X[:, p:] == X[:, :-p]  # (n, h - p)
    last_bad = (h - p) - np.argmax(~eq[:, ::-1], axis=1)  # (n,), one past the last mismatch
    last_bad[eq.all(axis=1)] = 0
    return np.maximum(last_bad, first)  # (n,)


def _rotation_classes(P: np.ndarray, Q: np.ndarray, period: np.ndarray) -> int:
    """Number of distinct periodic parts of the pairs (P, Q) up to a time shift (rows with an undetected period are
    left out)."""
    # P, Q: (n, h); period: (n,)
    h = P.shape[1]
    classes: set[tuple[int, bytes]] = set()
    size = P.itemsize
    for i in np.nonzero(period > 0)[0].tolist():
        p = int(period[i])
        first, second = P[i, h - p:].tobytes(), Q[i, h - p:].tobytes()  # p items each
        # the bytes of the (2, p) array of the two rows turned k places (`np.roll` along the time axis), every k
        classes.add((p, min(first[len(first) - k * size:] + first[:len(first) - k * size]
                            + second[len(second) - k * size:] + second[:len(second) - k * size] for k in range(p))))
    return len(classes)


@dataclass
class DepthPairs:
    depth: int  # j
    pairs: int  # distinct pairs (D_{j-1}, D_j) on times j .. horizon - 1 over every driver
    period: int  # largest pair period
    unsettled: int  # pairs whose period was not detected within the horizon
    classes: int  # distinct periodic parts up to a time shift
    white: bool  # some driver makes D_j white from some time on
    onset: int  # largest pair onset over every driver


def driver_pairs(depth: int, horizon: int, progress: bool = False) -> Iterator[DepthPairs]:
    """For j = 1 .. depth, the pairs (D_{j-1}, D_j) over every driver with c(0) = 1. Two drivers with the same pair on
    times j .. horizon - 1 have the same deeper diagonals, so one is kept."""
    P = np.zeros((1, horizon), dtype=np.uint8)  # (n, horizon), D_{j-1}; D_{-1} = 0
    Q = np.ones((1, horizon), dtype=np.uint8)  # (n, horizon), D_j; D_0 = 1 always
    start = time.time()
    for j in range(1, depth + 1):
        n = len(P)
        PP = np.concatenate([P, P])  # (2n, horizon), D_{j-2}
        QQ = np.concatenate([Q, Q])  # (2n, horizon), D_{j-1}
        R = np.zeros((2 * n, horizon), dtype=np.uint8)  # (2n, horizon), D_j
        R[:, j] = np.repeat(np.array([0, 1], dtype=np.uint8), n)
        for t in range(j, horizon - 1):
            R[:, t + 1] = PP[:, t] ^ (QQ[:, t] | R[:, t])
        key = np.ascontiguousarray(np.concatenate([QQ[:, j:], R[:, j:]], axis=1))  # (2n, 2 (horizon - j))
        _, idx = np.unique(key, axis=0, return_index=True)
        P, Q = QQ[idx], R[idx]  # (n', horizon) each
        m = len(P)
        per_p, per_q = detect_periods(P), detect_periods(Q)  # (n',) each
        pair_per = np.where((per_p > 0) & (per_q > 0), np.maximum(per_p, per_q), -1)  # (n',)
        on = np.zeros(m, dtype=np.int64)  # (n',), the pair repeats with the larger period from the later onset
        for p in set(pair_per[pair_per > 0].tolist()):
            rows = np.nonzero(pair_per == p)[0]
            on[rows] = np.maximum(onsets(P[rows], p, j), onsets(Q[rows], p, j))
        white = bool((Q[:, horizon // 2:].max(axis=1) == 0).any())
        if progress and j % 10 == 0:
            print(f"  depth {j}: {m} pairs, {time.time() - start:.0f} s", file=sys.stderr, flush=True)
        yield DepthPairs(j, m, int(pair_per.max()), int((pair_per < 0).sum()), _rotation_classes(P, Q, pair_per),
                         white, int(on[pair_per > 0].max()))


@dataclass
class Skeleton:
    period: np.ndarray  # (depth,) least power-of-two period of D_j
    white_run: np.ndarray  # (depth,) longest cyclic white run of the periodic part of D_j, -1 if it is white
    alt_run: np.ndarray  # (depth,) for j >= 1, longest cyclic run of times t with D_{j-1}(t) != D_j(t) != D_j(t + 1)


def _longest_cyclic_run(ok: np.ndarray) -> int:
    """Longest run of True in a cyclic word, len(ok) if all True."""
    # ok: (p,)
    if ok.all():
        return len(ok)
    w = np.concatenate([ok, ok]).astype(np.int8)  # (2p,)
    best = run = 0
    for v in w.tolist():
        run = run + 1 if v else 0
        best = max(best, run)
    return best


def skeleton_from_table(D: np.ndarray) -> Skeleton:
    """Periodic parts of the diagonals of a table D[j, t], read from its last quarter."""
    # D: (depth, steps)
    depth, steps = D.shape
    period = np.zeros(depth, dtype=np.int64)  # (depth,)
    white = np.zeros(depth, dtype=np.int64)  # (depth,)
    alt = np.zeros(depth, dtype=np.int64)  # (depth,)
    tail = D[:, 3 * steps // 4:]  # (depth, steps / 4)
    for j in range(depth):
        p = 1
        while not np.array_equal(tail[j, p:], tail[j, :-p]):
            p *= 2
            assert 4 * p <= tail.shape[1], f"diagonal {j} has no period up to {p} in the table"
        period[j] = p
    for j in range(depth):
        x = tail[j, -int(period[j]):]  # (p,)
        white[j] = -1 if x.max() == 0 else _longest_cyclic_run(x == 0)
        if j:
            p = int(max(period[j], period[j - 1]))
            y, z = tail[j - 1, -p - 1:], tail[j, -p - 1:]  # (p + 1,) each
            alt[j] = _longest_cyclic_run((y[:-1] != z[:-1]) & (z[1:] != z[:-1]))
    return Skeleton(period, white, alt)


def skeleton(depth: int, steps: int) -> Skeleton:
    """The single cell's skeleton to `depth`, from `steps` rows (steps must exceed the onsets by four periods)."""
    return skeleton_from_table(diagonal_table(steps, depth))


@dataclass
class WhiteFollower:
    depth: int  # w, an eventually white diagonal of the single cell
    period: int  # least period P of D_{w-1}
    weight: int  # black cells of D_{w-1} per period
    flips: bool  # D_{w+1}(t + P) = not D_{w+1}(t) on the window
    complement_is_shift: bool  # the complement of the periodic part of D_{w+1} is one of its rotations


def white_followers(D: np.ndarray) -> list[WhiteFollower]:
    """For each white diagonal w of a window D[j, t] of settled diagonals (w + 1 < depth): whether the diagonal after
    it flips, and whether its complement is a time shift of it. Where it is not, `skeleton_step` gives two classes."""
    # D: (depth, window), window at least four times every period
    out: list[WhiteFollower] = []
    for w in range(1, D.shape[0] - 1):
        if D[w].max():
            continue
        p = 1
        while not np.array_equal(D[w - 1, p:], D[w - 1, :-p]):
            p *= 2
        x = D[w + 1, -2 * p:]  # (2p,), one period of D_{w+1} (period p or 2p)
        flips = bool(np.array_equal(x[p:], 1 - x[:p]))
        comp = any(np.array_equal(1 - x, np.roll(x, k)) for k in range(2 * p))
        out.append(WhiteFollower(w, p, int(D[w - 1, -p:].sum()), flips, comp))
    return out


def onset_bound(white_run: np.ndarray) -> np.ndarray:
    """The onset that the reset lemma gives over every driver whose diagonals have the periodic parts of the skeleton:
    B_1 = 2 and B_{j+1} = max(B_j, j + 1) + white_run_j + 1 (white_run_j = -1 for a white diagonal)."""
    # white_run: (depth,)
    B = np.zeros(len(white_run), dtype=np.int64)  # (depth,)
    if len(B) > 1:
        B[1] = 2
    for j in range(1, len(B) - 1):
        B[j + 1] = max(int(B[j]), j + 1) + int(white_run[j]) + 1
    return B  # (depth,)


def settled_slope(gamma: float) -> float:
    """The black slope that the window argument gives if every pair settles by time gamma j (settled-runs)."""
    return 3 * (gamma - 1) / (5 * gamma - 1)


# ---------------------------------------------------------------------------------------------------------------------


def run_ends(args: argparse.Namespace) -> None:
    first = right_end_first_times(args.width, args.steps, progress=True)
    print(f"{'w':>3} {'unseen':>7} {'latest':>7} {'alt':>5}")
    for w, unseen, latest, alt in first_times_by_width(first, args.width):
        print(f"{w:>3} {unseen:>7} {latest:>7} {alt:>5}")


def run_game(args: argparse.Namespace) -> None:
    for w in range(2, args.width + 1, 2):
        d = window_game_distances(w)
        print(f"width {w}: alternating word at distance {d[alternating_word(w)]}, reached windows {(d >= 0).sum()}",
              flush=True)


def run_pairs(args: argparse.Namespace) -> None:
    horizon = args.horizon or 4 * args.depth + 128
    print(f"{'j':>4} {'pairs':>8} {'period':>6} {'classes':>7} {'white':>5} {'onset':>6} {'onset/j':>8}")
    for r in driver_pairs(args.depth, horizon, progress=True):
        if r.depth % args.every == 0 or r.white or r.unsettled:
            print(f"{r.depth:>4} {r.pairs:>8} {r.period:>6} {r.classes:>7} {'yes' if r.white else '':>5} {r.onset:>6} "
                  f"{r.onset / r.depth:>8.3f}" + (f"  unsettled {r.unsettled}" if r.unsettled else ""), flush=True)


def run_skeleton(args: argparse.Namespace) -> None:
    sk = skeleton(args.depth, args.steps or 3 * args.depth + 600)
    B = onset_bound(sk.white_run)
    print(f"white diagonals: {np.nonzero(sk.white_run < 0)[0].tolist()}")
    for k in sorted(set(sk.period.tolist())):
        print(f"period {k} first at depth {int(np.argmax(sk.period == k))}")
    print(f"{'j':>5} {'max g':>6} {'mean g':>7} {'max A':>6} {'B_j/j':>7} {'slope':>6}")
    for j in [50, 100, 200, 400, 800, 1200, 1600, 2000, 4000, 8000]:
        if j < args.depth:
            g = sk.white_run[1:j]
            gamma = B[j] / j
            print(f"{j:>5} {g.max():>6} {g[g >= 0].mean():>7.3f} {sk.alt_run[1:j].max():>6} {gamma:>7.3f} "
                  f"{settled_slope(gamma):>6.3f}")


def run_followers(args: argparse.Namespace) -> None:
    print(f"{'w':>7} {'P':>3} {'weight':>6} {'flips':>5} {'complement a shift':>18}")
    for f in white_followers(diagonals(args.steps, args.depth, 128)):
        print(f"{f.depth:>7} {f.period:>3} {f.weight:>6} {'yes' if f.flips else 'no':>5} "
              f"{'yes' if f.complement_is_shift else 'no':>18}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("ends")
    p.add_argument("--width", type=int, default=16)
    p.add_argument("--steps", type=int, default=100)
    p.set_defaults(func=run_ends)
    p = sub.add_parser("game")
    p.add_argument("--width", type=int, default=22)
    p.set_defaults(func=run_game)
    p = sub.add_parser("pairs")
    p.add_argument("--depth", type=int, default=100)
    p.add_argument("--horizon", type=int, default=0)
    p.add_argument("--every", type=int, default=10)
    p.set_defaults(func=run_pairs)
    p = sub.add_parser("skeleton")
    p.add_argument("--depth", type=int, default=2000)
    p.add_argument("--steps", type=int, default=0)
    p.set_defaults(func=run_skeleton)
    p = sub.add_parser("followers")
    p.add_argument("--depth", type=int, default=59000)
    p.add_argument("--steps", type=int, default=110000)
    p.set_defaults(func=run_followers)
    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
