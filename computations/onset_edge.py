"""The onsets of the single cell's left diagonals as the left edge of a difference pattern.

Let X be the single cell's pattern and Y(t, x) = X(t + P, x - P) its translate by P steps and P cells. Both are Rule 30
trajectories, and on the left diagonal D_j(t) = X(t, j - t) the translate reads Y(t, j - t) = D_j(t + P). So X and Y
agree on diagonal j at time t exactly when D_j(t) = D_j(t + P). Let L(t) be the leftmost cell where X(t) and Y(t)
differ and d(t) = L(t) + t its diagonal. The edge moves left by at most one cell per step, so d never decreases, and
max_{i <= j} T_i^P (T_i^P the first time from which D_i repeats with period P) is the least t with d(t) > j.

The edge law (Rule 30 is xor of the left neighbor with an OR, `edge_move`): if the shared cell L - 1 is white the edge
moves to L - 1; if it is black the edge stays at L when the copy that is white at L is white at L + 1, and otherwise
retreats to L + 1, or further when the copy that is black at L is white at L + 1 and L + 2.

- `single_cell_edge`: d(t) for the single cell against its translate, from the vector of diagonals of
  `settled_slope.stream`, with the law checked at every step;
- `running_onsets`: the least t with d(t) > j, against max_{i <= j} T_i^P from `settled_slope.stream`;
- `move_table`, `window_table`: move frequencies, retreat sizes and the depth gain d(t + 1) - d(t) by regime and over
  windows of 1,000 steps;
- `random_edges`: the same edge for two uniform random rows that differ at one cell (`flip`) or on a half line
  (`half`), and the speed of the left edge of the damage;
- `background_edges`: a background all of whose left diagonals repeat with period P, a row equal to it left of cell 1
  and random right of it, and two edges: against the background, and against the row's own translate by P.

    python -m computations.onset_edge single --depth 200000 --period 32   # about 2.5 min, 0.3 GB
    python -m computations.onset_edge single --depth 87866 --period 16    # about 30 s
    python -m computations.onset_edge random --samples 400 --steps 4000   # about 30 s
    python -m computations.onset_edge background --period 32 --samples 200 --steps 3000   # about 40 s
"""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass

import numpy as np
from tqdm.auto import tqdm

from computations.settled_slope import stream

LEFT, STAY, RETREAT_ONE, RETREAT_MORE = -1, 0, 1, 2


def edge_move(shared: int, x: tuple[int, int, int], y: tuple[int, int, int]) -> int:
    """The edge law. `shared` is the common cell L - 1, `x` and `y` the cells L, L + 1, L + 2 of the two copies, which
    differ at L. Returns the move of the edge in the next row: -1, 0, 1, or 2 for a move of at least 2."""
    assert x[0] != y[0]
    if not shared:
        return LEFT
    white, black = (x, y) if x[0] == 0 else (y, x)
    if not white[1]:
        return STAY
    return RETREAT_ONE if black[1] or black[2] else RETREAT_MORE


def law_from_code(code: int) -> int:
    """`edge_move` on a local code: bits 0 .. 4 are X at L - 2 .. L + 2, bits 5 .. 9 are Y at L - 2 .. L + 2."""
    xs = [(code >> k) & 1 for k in range(5)]
    ys = [(code >> (5 + k)) & 1 for k in range(5)]
    return edge_move(xs[1], (xs[2], xs[3], xs[4]), (ys[2], ys[3], ys[4]))


def law_cases() -> list[tuple[int, int, tuple[int, int, int], tuple[int, int, int]]]:
    """The 128 local cases: the shared cells L - 2 and L - 1, the cells L .. L + 2 of X, and L + 1, L + 2 of Y, with
    Y(L) = not X(L)."""
    cases = []
    for c in range(128):
        b = [(c >> k) & 1 for k in range(7)]
        cases.append((b[0], b[1], (b[2], b[3], b[4]), (1 - b[2], b[5], b[6])))
    return cases


def lowest_bit(v: int) -> int:
    """The index of the lowest set bit of v > 0."""
    return (v & -v).bit_length() - 1


def window_bits(v: int, lo: int) -> int:
    """Bits lo .. lo + 4 of v, with bits below 0 read as 0."""
    return ((v >> lo) if lo >= 0 else (v << -lo)) & 31


@dataclass(frozen=True, slots=True)
class EdgeRun:
    period: int  # the translate is by `period` steps and cells
    depth: int  # diagonals 0 .. depth are evolved
    edge: np.ndarray  # (m,) d(s) for s = 0 .. m - 1, depth + 1 once X and Y agree on every diagonal <= depth
    code: np.ndarray  # (m,) the local code of `law_from_code` at time s (0 once d(s) > depth)
    violations: int  # steps at which the edge law fails (0: it is a theorem)


def single_cell_edge(depth: int, steps: int, period: int, progress: bool = True) -> EdgeRun:
    """d(s) for s = 0 .. steps - 1 - period: the least diagonal j <= depth with D_j(s) != D_j(s + period). The vector
    v_t of diagonals 0 .. depth evolves as in `settled_slope.stream`; the law is checked at every step at which the
    local window lies inside the evolved diagonals."""
    n = depth + 1
    mask = (1 << n) - 1
    m = steps - period
    edge = np.full(m, n, dtype=np.int64)  # (m,)
    code = np.zeros(m, dtype=np.int64)  # (m,)
    ring = [0] * period  # ring[t % period] = v_{t - period} when read at time t
    v = 1
    violations = 0
    prev_d, prev_code = -1, 0
    for t in tqdm(range(steps), desc=f"edge, period {period}", unit="step", file=sys.stderr, mininterval=5,
                  disable=not progress):
        if t >= period:
            s = t - period
            old = ring[t % period]  # v_s, the cells of X along the diagonals; v_t gives those of Y
            diff = old ^ v
            if diff:
                d = lowest_bit(diff)
                edge[s] = d
                code[s] = window_bits(old, d - 2) | window_bits(v, d - 2) << 5
            else:
                d = n
            if prev_d >= 0 and prev_d + 3 <= depth:
                move = d - prev_d - 1
                law = law_from_code(prev_code)
                if not (move == law or (law == RETREAT_MORE and move >= 2)):
                    violations += 1
            prev_d, prev_code = (d, int(code[s])) if d < n else (-1, 0)
        ring[t % period] = v
        v = ((v << 2) ^ ((v << 1) | v)) & mask
    return EdgeRun(period, depth, edge, code, violations)


def running_onsets(edge: np.ndarray, depth: int) -> np.ndarray:
    """E_j = the least s with d(s) > j, for j = 0 .. depth (len(edge) if there is none). d must not decrease."""
    # edge: (m,)
    assert (np.diff(edge) >= 0).all(), "the edge's diagonal never decreases"
    return np.searchsorted(edge, np.arange(depth + 1), side="right")  # (depth + 1,)


@dataclass(frozen=True, slots=True)
class MoveRow:
    label: str
    steps: int  # steps counted
    left: float  # frequency of a move to L - 1
    stay: float
    retreat: float  # frequency of a move to L + 1 or further
    sizes: dict[int, float]  # retreat size -> frequency among all steps
    gain: float  # mean of d(s + 1) - d(s)
    gain_se: float  # batch-means standard error over blocks of 1,000 steps


def moves(edge: np.ndarray) -> np.ndarray:
    """The moves d(s + 1) - d(s) - 1 of the edge, for the steps at which both values are below the cut-off."""
    # edge: (m,)
    return np.diff(edge) - 1  # (m - 1,)


def batch_se(gain: np.ndarray, block: int = 1000) -> float:
    """The standard error of the mean of `gain` from the means of consecutive blocks of `block` steps."""
    # gain: (k,)
    nb = len(gain) // block
    if nb < 2:
        return float("nan")
    means = gain[:nb * block].reshape(nb, block).mean(axis=1)  # (nb,)
    return float(means.std(ddof=1) / np.sqrt(nb))


def move_row(label: str, mv: np.ndarray) -> MoveRow:
    """Move frequencies and the depth gain of a sequence of moves."""
    # mv: (k,)
    k = len(mv)
    sizes = {int(r): float((mv == r).sum() / k) for r in np.unique(mv[mv > 0])}
    gain = (mv + 1).astype(np.float64)  # (k,)
    return MoveRow(label, k, float((mv == -1).mean()), float((mv == 0).mean()), float((mv > 0).mean()), sizes,
                   float(gain.mean()), batch_se(gain))


def move_table(edge: np.ndarray, depth: int, bounds: list[int]) -> list[MoveRow]:
    """Move statistics grouped by the depth d(s) of the edge, in the ranges [bounds[i], bounds[i + 1])."""
    # edge: (m,)
    live = np.flatnonzero(edge[1:] <= depth)  # (k,): steps s with d(s + 1) <= depth
    mv = moves(edge)[live]  # (k,)
    at = edge[live]  # (k,)
    rows = []
    for lo, hi in zip(bounds[:-1], bounds[1:]):
        sel = (at >= lo) & (at < hi)
        if sel.sum() > 0:
            rows.append(move_row(f"depths {lo} .. {hi - 1}", mv[sel]))
    return rows


@dataclass(frozen=True, slots=True)
class WindowRow:
    windows: int
    retreat_min: float  # least retreat frequency over the windows
    retreat_max: float
    retreat_sd: float
    gain_min: float  # least mean gain over the windows
    gain_max: float
    gain_sd: float


def window_table(edge: np.ndarray, depth: int, start: int, width: int = 1000) -> WindowRow:
    """Retreat frequency and mean gain over consecutive windows of `width` steps from step `start`."""
    # edge: (m,)
    last = int(np.flatnonzero(edge <= depth)[-1])  # the last step with the edge inside the evolved diagonals
    mv = moves(edge[start:last + 1])  # (k,)
    nb = len(mv) // width
    blocks = mv[:nb * width].reshape(nb, width)  # (nb, width)
    retreat = (blocks > 0).mean(axis=1)  # (nb,)
    gain = (blocks + 1).mean(axis=1)  # (nb,)
    return WindowRow(nb, float(retreat.min()), float(retreat.max()), float(retreat.std()), float(gain.min()),
                     float(gain.max()), float(gain.std()))


def step_row(row: int, width: int) -> int:
    """One step of Rule 30 on a row of `width` cells held as an integer (bit i is cell i), white outside."""
    return ((row << 1) ^ (row | (row >> 1))) & ((1 << width) - 1)


def random_bits(rng: np.random.Generator, n: int) -> int:
    """n fair bits as an integer."""
    raw = np.packbits(rng.integers(0, 2, n, dtype=np.uint8), bitorder="little")  # (ceil(n / 8),)
    return int.from_bytes(raw.tobytes(), "little") & ((1 << n) - 1)


@dataclass(frozen=True, slots=True)
class EdgeSample:
    speed: np.ndarray  # (samples,) (L(0) - L(T)) / T, the left speed of the edge over the whole run
    late_gain: np.ndarray  # (samples,) mean of d(s + 1) - d(s) over the steps after the burn-in
    moves: np.ndarray  # (samples * (T - burn),) the moves after the burn-in
    violations: int


def track(x: int, y: int, steps: int, width: int, burn: int, lag: int = 0) -> tuple[list[int], int]:
    """The leftmost difference of x and y for `steps` steps, both evolved by Rule 30, and the law violations. With
    `lag` > 0, y is replaced by the translate of x: cell i of the second row at time s is x at time s + lag, cell
    i - lag. Differences left of cell s + 2 lag + 3 are ignored: the rows are white outside, and those cells may feel
    the left end; the callers check that the edge stays right of them."""
    edges: list[int] = []
    violations = 0
    hist = [x]
    for _ in range(lag):
        hist.append(step_row(hist[-1], width))
    prev = None
    for s in range(steps):
        a = hist[0] if lag else x
        b = (hist[-1] << lag) if lag else y
        diff = (a ^ b) >> (s + 2 * lag + 3) << (s + 2 * lag + 3)  # cells left of s + 2 lag + 3 may feel the left end
        L = lowest_bit(diff)
        edges.append(L)
        if prev is not None and s > burn:
            pL, pc = prev
            mv = L - pL
            law = law_from_code(pc)
            if not (mv == law or (law == RETREAT_MORE and mv >= 2)):
                violations += 1
        prev = (L, window_bits(a, L - 2) | window_bits(b, L - 2) << 5)
        if lag:
            hist.pop(0)
            hist.append(step_row(hist[-1], width))
        else:
            x, y = step_row(x, width), step_row(y, width)
    return edges, violations


def random_edges(samples: int, steps: int, mode: str, seed: int, burn: int = 200, progress: bool = True) -> EdgeSample:
    """Two uniform random rows that differ at cell c only (`flip`) or are independent from cell c on (`half`). The
    rows have c + steps + 64 cells with c = 3 steps / 2 + 64, white outside; the run asserts that the edge at time s stays
    right of cell s + 2, so no cell it reads feels the left end, and the right end is more than `steps` cells away."""
    rng = np.random.default_rng(seed)
    c = 3 * steps // 2 + 64
    width = c + steps + 64
    speed, late, mv_all, viol = [], [], [], 0
    for _ in tqdm(range(samples), desc=f"random rows ({mode})", unit="sample", file=sys.stderr, mininterval=5,
                  disable=not progress):
        x = random_bits(rng, width)
        if mode == "flip":
            y = x ^ (1 << c)
        else:
            y = (x & ((1 << c) - 1)) | (random_bits(rng, width - c) << c)
            y = (y & ~(1 << c)) | ((~x >> c & 1) << c)  # different at c
        edges, v = track(x, y, steps + 1, width, burn)
        viol += v
        e = np.array(edges)  # (steps + 1,)
        assert (e > np.arange(steps + 1) + 2).all() and e[0] == c  # the edge never reads a cell the ends reach
        speed.append((c - e[-1]) / steps)
        m = np.diff(e[burn:])  # (steps - burn,)
        late.append(float((m + 1).mean()))
        mv_all.append(m)
    return EdgeSample(np.array(speed), np.array(late), np.concatenate(mv_all), viol)


def pair_next(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    """The periodic word c with c(t + 1) = a(t) xor (b(t) or c(t)), for words a, b of length P with b not white: the
    next left diagonal of a background, set by the reset at a black cell of b."""
    # a, b: (P,)
    P = len(a)
    r = int(np.argmax(b))
    c = np.zeros(P, dtype=np.uint8)  # (P,)
    c[(r + 1) % P] = 1 - a[r]
    for k in range(1, P):
        t = (r + k) % P
        c[(t + 1) % P] = a[t] ^ (b[t] | c[t])
    return c  # (P,)


def background_words(P: int, n: int, rng: np.random.Generator) -> np.ndarray:
    """n consecutive left diagonals, all of period P, from two random words (redrawn if a white diagonal appears)."""
    while True:
        D = np.zeros((n, P), dtype=np.uint8)  # (n, P): D[i] is diagonal i, D[i][t % P] its cell at time t
        D[0] = rng.integers(0, 2, P)
        D[1] = rng.integers(0, 2, P)
        ok = bool(D[1].any())
        for i in range(2, n):
            if not ok:
                break
            D[i] = pair_next(D[i - 2], D[i - 1])
            ok = bool(D[i].any())
        if ok:
            return D


def background_row(D: np.ndarray, t: int) -> int:
    """Row t of the background (bit i is cell i, on diagonal i + t), for the cells whose diagonal is in D."""
    # D: (n, P)
    n, P = D.shape
    cells = D[t:, t % P]  # (n - t,): cell i reads diagonal i + t
    raw = np.packbits(cells, bitorder="little")
    return int.from_bytes(raw.tobytes(), "little")


@dataclass(frozen=True, slots=True)
class BackgroundSample:
    gain_bg: np.ndarray  # (samples,) mean gain of the edge against the background after the burn-in
    gain_tr: np.ndarray  # (samples,) mean gain of the edge against the row's own translate by P
    moves_bg: np.ndarray  # (k,) moves after the burn-in, pooled
    moves_tr: np.ndarray  # (k,)
    behind: float  # fraction of times at which the translate edge is at or right of the background edge
    violations: int


def background_edges(P: int, samples: int, steps: int, seed: int, burn: int = 200,
                     progress: bool = True) -> BackgroundSample:
    """A background S whose left diagonals all repeat with period P, a row Y equal to S at cells <= c and random right
    of c (and different at c + 1), and two edges: Y against S, and Y against its translate Y(t + P, x - P). Left of the
    first edge Y equals S, which its translate leaves unchanged, so the second edge is never left of the first."""
    rng = np.random.default_rng(seed)
    c = 3 * steps // 2 + 2 * P + 64
    width = c + steps + 2 * P + 64
    gb, gt, mb, mt, behind, viol = [], [], [], [], [], 0
    for _ in tqdm(range(samples), desc=f"background, period {P}", unit="sample", file=sys.stderr, mininterval=5,
                  disable=not progress):
        D = background_words(P, width, rng)  # (width, P)
        S0 = background_row(D, 0) & ((1 << width) - 1)
        right = random_bits(rng, width - c - 1) << (c + 1)
        Y0 = (S0 & ((1 << (c + 1)) - 1)) | right
        if not (Y0 ^ S0) >> (c + 1) & 1:
            Y0 ^= 1 << (c + 1)
        e_bg, v1 = track(S0, Y0, steps + 1, width, burn)
        e_tr, v2 = track(Y0, 0, steps + 1, width, burn, lag=P)
        viol += v1 + v2
        a, b = np.array(e_bg), np.array(e_tr)  # (steps + 1,)
        s_ = np.arange(steps + 1)  # (steps + 1,)
        assert (a > s_ + 2 * P + 2).all() and (b > s_ + 2 * P + 2).all()  # no cell read feels the ends
        assert (b >= a).all()
        behind.append(float((b[burn:] > a[burn:]).mean()))
        ma, mb_ = np.diff(a[burn:]), np.diff(b[burn:])  # (steps - burn,)
        gb.append(float((ma + 1).mean()))
        gt.append(float((mb_ + 1).mean()))
        mb.append(ma)
        mt.append(mb_)
    return BackgroundSample(np.array(gb), np.array(gt), np.concatenate(mb), np.concatenate(mt), float(np.mean(behind)),
                            viol)


def print_rows(rows: list[MoveRow]) -> None:
    print(f"{'':>26} {'steps':>8} {'left':>7} {'stay':>7} {'retreat':>7} {'r=1':>7} {'r=2':>7} {'r>=3':>7} "
          f"{'gain':>7} {'se':>7} {'slope':>7}")
    for r in rows:
        r1 = r.sizes.get(1, 0.0)
        r2 = r.sizes.get(2, 0.0)
        r3 = sum(v for k, v in r.sizes.items() if k >= 3)
        print(f"{r.label:>26} {r.steps:>8} {r.left:7.4f} {r.stay:7.4f} {r.retreat:7.4f} {r1:7.4f} {r2:7.4f} {r3:7.4f} "
              f"{r.gain:7.4f} {r.gain_se:7.4f} {1 / r.gain:7.4f}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("what", choices=["single", "random", "background"])
    parser.add_argument("--depth", type=int, default=200000)
    parser.add_argument("--period", type=int, default=32)
    parser.add_argument("--steps", type=int, default=0, help="single: default 3 depth / 2 + 600")
    parser.add_argument("--samples", type=int, default=200)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--burn", type=int, default=200)
    args = parser.parse_args()
    if args.what == "single":
        steps = args.steps or 3 * args.depth // 2 + 600
        run = single_cell_edge(args.depth, steps, args.period)
        E = running_onsets(run.edge, args.depth)  # (depth + 1,)
        d = stream(args.depth, steps, period=args.period)
        M = np.maximum.accumulate(d.onset)  # (depth + 1,)
        m = len(run.edge)
        print(f"period {args.period}, diagonals 0 .. {args.depth}, {steps} steps, edge at times 0 .. {m - 1}")
        print(f"edge law violations: {run.violations}")
        print(f"least t with d(t) > j equals max_(i <= j) T_i from settled_slope.stream for every j <= {args.depth}: "
              f"{bool(np.array_equal(E, M))}; largest such time {int(E.max())}, at least four periods before the end: "
              f"{bool(E.max() <= m - 4 * args.period)}")
        inside = np.flatnonzero(run.edge <= args.depth)  # (k,): times with the edge among the evolved diagonals
        excess = 2 * inside - 3 * run.edge[inside]  # (k,): 2 t - 3 d(t)
        c_star = max(0, int(excess.max()))
        t_top = min(m - 1, (3 * (args.depth + 1) + c_star) // 2)
        late = excess[inside >= 1000]
        print(f"EdgeBound with P = {args.period}: 3 d(t) >= 2 t - c for every t <= {t_top} with c = {c_star} (at t = "
              f"{int(inside[np.argmax(excess)])}); over t >= 1000 the largest 2 t - 3 d(t) is {int(late.max())}")
        bounds = [b for b in [0, 400, 53207, 87867] if b <= args.depth] + [args.depth + 1]
        print_rows(move_table(run.edge, args.depth, bounds))
        print_rows(move_table(run.edge, args.depth, [400, args.depth + 1]))
        start = int(np.searchsorted(run.edge, 400))
        w = window_table(run.edge, args.depth, start)
        print(f"windows of 1,000 steps from depth 400 (step {start}): {w.windows}; retreat frequency from "
              f"{w.retreat_min:.4f} to {w.retreat_max:.4f} (sd {w.retreat_sd:.4f}); gain from {w.gain_min:.4f} to "
              f"{w.gain_max:.4f} (sd {w.gain_sd:.4f})")
        live = run.edge[1:] <= args.depth
        gain = (moves(run.edge)[live] + 1).astype(np.float64)
        print(f"batch-means standard error of the gain past depth 400, blocks of 1,000 and 10,000 steps: "
              f"{batch_se(gain[start:], 1000):.5f}, {batch_se(gain[start:], 10000):.5f}")
    elif args.what == "random":
        for mode in ["flip", "half"]:
            r = random_edges(args.samples, args.steps or 4000, mode, args.seed, args.burn)
            lam, se = r.speed.mean(), r.speed.std(ddof=1) / np.sqrt(len(r.speed))
            g, gse = r.late_gain.mean(), r.late_gain.std(ddof=1) / np.sqrt(len(r.late_gain))
            print(f"{mode}: {args.samples} samples of {args.steps or 4000} steps; left speed {lam:.4f} +- {se:.4f}, "
                  f"1 / (1 - speed) = {1 / (1 - lam):.4f} +- {se / (1 - lam) ** 2:.4f}; gain after step {args.burn} "
                  f"{g:.4f} +- {gse:.4f} (slope {1 / g:.4f}); law violations {r.violations}")
            print_rows([move_row(f"random rows, {mode}", r.moves)])
    else:
        r = background_edges(args.period, args.samples, args.steps or 3000, args.seed, args.burn)
        for name, g, mv in [("against background", r.gain_bg, r.moves_bg), ("against translate", r.gain_tr, r.moves_tr)]:
            mean, se = g.mean(), g.std(ddof=1) / np.sqrt(len(g))
            print(f"period {args.period}, {args.samples} samples of {args.steps or 3000} steps, {name}: gain {mean:.4f} "
                  f"+- {se:.4f}, slope {1 / mean:.4f} +- {se / mean ** 2:.4f}")
            print_rows([move_row(f"background {args.period}, {name[8:]}", mv)])
        print(f"translate edge strictly right of the background edge at {r.behind:.4f} of the times; law violations "
              f"{r.violations}")


if __name__ == "__main__":
    main()
