"""How runs of the single cell's center column end, and how long a run the left half alone allows.

Three computations.

1. `mechanism`: the center window (cells -half .. half) of the single black cell for `steps` steps, every maximal run
   of the center column, and for each run the cells that start and end it. A black run of length L from time a is an
   alternating domain of row a (cell -k black exactly for even k, k < L) whose left end moves right one cell per step;
   `domain_profile` follows that domain back in time. A white run is read through the sequence e_i = cell(a + i, -1):
   during the run the center is cell(t, -1) xor cell(t, 1), and column 1 is white until the black front from the right
   arrives and black after it (the kit's `col_one`), so the run lasts while e reads 0^z 1^o.

2. `driven`: the left half (cells -1, -2, ...) at time t is a function of the center column alone, since the left half
   starts white: `driven_rows` lists every left half that some driver c(0) = 1, c(1), ..., c(t - 1) produces, with one
   driver for each. A black run of the center from time a is an alternating right end of the row at time a, and a white
   run from time a is a word 0^z 1^o at the start of column -1 under the white driver (column 1 can only latch from white
   to black during a white run). So the longest run that any driver allows bounds the runs of every configuration whose
   cells left of column 0 are white at time 0, the single cell among them. `class_black_max` computes the longest black
   run over those configurations themselves, by enumeration, for small a.

3. `forced`: the cells of row a - s that every s-step preimage of a word shares, by enumeration. An alternating word
   forces a trapezoid (right end 4 cells further left per step); a black or a white block forces nothing.

    python -m computations.run_mechanism mechanism --steps 1048576      # about 2 min
    python -m computations.run_mechanism driven --steps 175 --every 5   # about 20 min, 3 GB of memory
    python -m computations.run_mechanism class --steps 26               # about 1 min
    python -m computations.run_mechanism forced                         # about 1 s
"""

from __future__ import annotations

import argparse
import sys
import time
from collections.abc import Iterator
from dataclasses import dataclass

import numpy as np

# ---------------------------------------------------------------------------------------------------------------------
# 1. The single cell's center window and its runs
# ---------------------------------------------------------------------------------------------------------------------


def center_window(steps: int, half: int, progress: bool = False) -> np.ndarray:
    """Cells -half .. half of rows 0 .. steps - 1 of the single black cell, as bits packed little-endian per row.

    The row is a Python integer whose bit i is cell lo + i; cells that cannot reach the window before `steps` are
    dropped, so the work is about steps^2 / 2 cell updates."""
    width = 2 * half + 1
    nbytes = (width + 7) // 8
    out = np.zeros((steps, nbytes), dtype=np.uint8)  # (steps, nbytes)
    mask = (1 << width) - 1
    row, lo = 1, 0
    start = time.time()
    for t in range(steps):
        shift = -half - lo
        window = (row >> shift) & mask if shift >= 0 else (row << -shift) & mask
        out[t] = np.frombuffer(window.to_bytes(nbytes, "little"), dtype=np.uint8)
        # one step with the origin moved one cell left: new bit j is cell lo - 1 + j
        row = (row << 2) ^ ((row << 1) | row)
        lo -= 1
        keep_lo = -(steps - t) - half - 2
        if keep_lo > lo + 64:
            row >>= keep_lo - lo
            lo = keep_lo
        keep_hi = (steps - t) + half + 2
        if t % 64 == 0 and row.bit_length() + lo > keep_hi + 128:
            row &= (1 << (keep_hi - lo)) - 1
        if progress and t % (1 << 16) == 0 and t:
            print(f"  step {t}/{steps}, {time.time() - start:.0f} s", file=sys.stderr, flush=True)
    return out  # (steps, nbytes)


def window_cells(packed: np.ndarray, half: int) -> np.ndarray:
    """Unpack `center_window` output: column half + x is cell x."""
    # packed: (steps, nbytes)
    return np.unpackbits(packed, axis=1, bitorder="little")[:, : 2 * half + 1]  # (steps, 2 * half + 1)


def maximal_runs(column: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Starts, lengths and colors of the maximal runs of a 0/1 sequence; the last run is dropped (it may continue)."""
    # column: (n,)
    change = np.nonzero(np.diff(column.astype(np.int8)))[0] + 1  # (r,)
    starts = np.concatenate([[0], change])  # (r + 1,)
    ends = np.concatenate([change, [len(column)]])  # (r + 1,)
    return starts[:-1], (ends - starts)[:-1], column[starts[:-1]].astype(np.uint8)  # each (r,)


def alt(x: int) -> int:
    """The alternating pattern that a black center run leaves to its left: cell x is black exactly for even x."""
    return 1 if x % 2 == 0 else 0


def alternating_left(cells: np.ndarray, half: int, t: int) -> int:
    """Length of the alternating stretch of row t that ends at the center (cells 0, -1, ... with cell x = alt(x))."""
    # cells: (steps, 2 * half + 1)
    n = 0
    while n <= half and cells[t, half - n] == alt(-n):
        n += 1
    return n


def domain_profile(cells: np.ndarray, half: int, a: int, length: int) -> list[tuple[int, int]]:
    """For a black run of `length` from time a: at row a - s, the alternating domain starts at p = -(length - 1) - s.
    Returns (s, right end q) for s = 0, 1, ... while cell p is in phase and the domain has at least 2 cells."""
    out: list[tuple[int, int]] = []
    s = 0
    while a - s >= 0:
        p = -(length - 1) - s
        if p < -half or cells[a - s, half + p] != alt(p):
            break
        q = p
        while q + 1 <= half and cells[a - s, half + q + 1] == alt(q + 1):
            q += 1
        if q - p + 1 < 2:
            break
        out.append((s, q))
        s += 1
    return out


def white_reading(cells: np.ndarray, half: int, a: int, length: int) -> tuple[int, int, int]:
    """(ell, z, o) for a white run of `length` from time a: ell is the number of white cells right of the center in row
    a (capped at half), and column -1 from time a reads 0^z 1^o then breaks."""
    ell = 0
    while ell < half and cells[a, half + 1 + ell] == 0:
        ell += 1
    z = 0
    while a + z < cells.shape[0] and cells[a + z, half - 1] == 0:
        z += 1
    o = 0
    while a + z + o < cells.shape[0] and cells[a + z + o, half - 1] == 1:
        o += 1
    return ell, z, o


@dataclass
class Mechanism:
    steps: int
    black_runs: int
    white_runs: int
    longest_black: tuple[int, int]  # (length, start)
    longest_white: tuple[int, int]
    black_identity_failures: int  # runs whose length is not the alternating length of row a
    white_identity_failures: int  # runs whose length is not the one read off column -1 and ell
    white_end_counts: dict[str, int]  # 'before front', 'at front', 'after front', over white runs of length >= min_len
    long_black: list[tuple[int, int, int, int]]  # (a, L, domain lifetime, longest domain length seen)
    long_black_offset: list[int]  # for each long black run, max over s of |right end + 4s| (0: exactly the trapezoid)
    long_white: list[tuple[int, int]]  # (ell, L) for white runs of length >= min_len


def mechanism(steps: int, half: int = 64, min_len: int = 12, progress: bool = True) -> Mechanism:
    """Runs of the center column to `steps` and the cells that end them."""
    cells = window_cells(center_window(steps, half, progress), half)  # (steps, 2 * half + 1)
    column = cells[:, half]  # (steps,)
    starts, lengths, colors = maximal_runs(column)
    black_fail = white_fail = 0
    ends = {"before front": 0, "at front": 0, "after front": 0}
    long_black: list[tuple[int, int, int, int]] = []
    long_black_offset: list[int] = []
    long_white: list[tuple[int, int]] = []
    tail = 2 * half
    for k, (a, L, c) in enumerate(zip(starts.tolist(), lengths.tolist(), colors.tolist())):
        if a == 0 or a + L + 1 >= steps:
            continue
        if progress and k % 200_000 == 0 and k:
            print(f"  run {k}/{len(starts)}", file=sys.stderr, flush=True)
        if c == 1:
            if alternating_left(cells, half, a) != L:
                black_fail += 1
            if L >= min_len and a > tail:
                prof = domain_profile(cells, half, a, L)
                long_black.append((a, L, len(prof), max(q + L + s for s, q in prof)))
                long_black_offset.append(max(abs(q + 4 * s) for s, q in prof))
        else:
            ell, z, o = white_reading(cells, half, a, L)
            # the run lasts while column -1 reads 0^z 1^o with the switch at the front's arrival a + ell
            if ell >= half:
                continue
            predicted = 1 + (ell if ell < z else (z + o if ell == z else z))
            if predicted != L:
                white_fail += 1
            if L >= min_len:
                key = "before front" if L <= ell else ("at front" if L == ell + 1 else "after front")
                ends[key] += 1
                long_white.append((ell, L))
    bl = lengths[colors == 1]
    wl = lengths[colors == 0]
    ib, iw = int(np.argmax(bl)), int(np.argmax(wl))
    return Mechanism(steps, len(bl), len(wl), (int(bl[ib]), int(starts[colors == 1][ib])),
                     (int(wl[iw]), int(starts[colors == 0][iw])), black_fail, white_fail, ends, long_black,
                     long_black_offset, long_white)


# ---------------------------------------------------------------------------------------------------------------------
# 2. The left half driven by an arbitrary center column
# ---------------------------------------------------------------------------------------------------------------------
# A left half at time t is a multiword integer: bit k - 1 is cell -k. One step with center value d:
# new cell -k = cell -(k + 1) xor (cell -k or cell -(k - 1)), with cell 0 = d, that is B' = (B >> 1) ^ (B | (B << 1) | d).


def _shr1(B: np.ndarray) -> np.ndarray:
    # B: (n, W) uint64, word 0 holds bits 0..63
    out = B >> np.uint64(1)  # (n, W)
    out[:, :-1] |= B[:, 1:] << np.uint64(63)
    return out


def _shl1(B: np.ndarray) -> np.ndarray:
    # B: (n, W)
    out = B << np.uint64(1)  # (n, W)
    out[:, 1:] |= B[:, :-1] >> np.uint64(63)
    return out


def driven_step(B: np.ndarray, d: int) -> np.ndarray:
    """One step of the driven left half for every row of B with center value d."""
    # B: (n, W)
    left = _shl1(B)  # (n, W)
    left[:, 0] |= np.uint64(d)
    return _shr1(B) ^ (B | left)  # (n, W)


def _unique_rows(B: np.ndarray, D: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    # B, D: (n, W)
    view = np.ascontiguousarray(B).view(np.dtype((np.void, B.dtype.itemsize * B.shape[1])))[:, 0]  # (n,)
    _, idx = np.unique(view, return_index=True)
    return B[idx], D[idx]  # (m, W) each


def driven_rows(steps: int, progress: bool = False) -> Iterator[tuple[int, np.ndarray, np.ndarray]]:
    """Yield (t, rows, drivers) for t = 1 .. steps: every left half at time t from a white start under some driver with
    c(0) = 1, each with one driver that produces it (bit u of the driver is c(u))."""
    words = steps // 64 + 1
    B = np.zeros((1, words), dtype=np.uint64)  # (1, words)
    D = np.zeros((1, words), dtype=np.uint64)  # (1, words)
    D[0, 0] = 1
    B = driven_step(B, 1)
    yield 1, B, D
    start = time.time()
    for t in range(1, steps):
        D1 = D.copy()  # (n, words)
        D1[:, t // 64] |= np.uint64(1) << np.uint64(t % 64)
        B, D = _unique_rows(np.concatenate([driven_step(B, 0), driven_step(B, 1)]), np.concatenate([D, D1]))
        if progress and (t + 1) % 25 == 0:
            print(f"  t = {t + 1}: {len(B)} rows, {time.time() - start:.0f} s", file=sys.stderr, flush=True)
        yield t + 1, B, D


def _trailing_matches(B: np.ndarray, pattern: np.ndarray, t: int) -> np.ndarray:
    """Number of low bits (cells -1, -2, ...) in which each row agrees with `pattern`, at most t."""
    # B: (n, W); pattern: (W,)
    diff = B ^ pattern  # (n, W)
    n, W = B.shape
    out = np.full(n, 64 * W, dtype=np.int64)  # (n,)
    done = np.zeros(n, dtype=bool)  # (n,)
    for w in range(W):
        x = diff[:, w]  # (n,)
        nz = (x != 0) & ~done
        low = x[nz] & (~x[nz] + np.uint64(1))
        out[nz] = 64 * w + np.round(np.log2(low.astype(np.float64))).astype(np.int64)
        done |= nz
    return np.minimum(out, t)  # (n,)


def black_reach(B: np.ndarray, t: int) -> np.ndarray:
    """For each left half at time t, the longest black run of the center from time t it allows: 1 + the length of the
    alternating right end with cell -1 white (cell -k black exactly for even k)."""
    # B: (n, W)
    W = B.shape[1]
    pat = np.zeros(W, dtype=np.uint64)  # (W,)
    for k in range(2, 64 * W + 1, 2):
        pat[(k - 1) // 64] |= np.uint64(1) << np.uint64((k - 1) % 64)
    return 1 + _trailing_matches(B, pat, t)  # (n,)


def white_reach(B: np.ndarray, t: int, horizon: int) -> np.ndarray:
    """For each left half at time t, the longest white run of the center from time t it allows: the center stays white
    while column -1 (under the white driver) equals column 1, which reads 0^ell 1^(...) since column 1 can only turn
    from white to black during a white run; so the run is 1 + z + o for column -1 reading 0^z 1^o, read to `horizon`."""
    # B: (n, W)
    n = B.shape[0]
    reads = np.zeros((n, horizon), dtype=np.uint8)  # (n, horizon), column -1 at times t .. t + horizon - 1
    cur = B.copy()
    for i in range(horizon):
        reads[:, i] = (cur[:, 0] & np.uint64(1)).astype(np.uint8)
        cur = driven_step(cur, 0)
    z = np.argmax(reads == 1, axis=1)  # (n,)
    z[reads[:, :].max(axis=1) == 0] = horizon
    after = reads.copy()
    after[np.arange(horizon)[None, :] < z[:, None]] = 1
    o = np.argmax(after == 0, axis=1) - z  # (n,)
    o[after.min(axis=1) == 1] = horizon - z[after.min(axis=1) == 1]
    return 1 + z + o  # (n,)


def driver_bits(D: np.ndarray, t: int) -> list[int]:
    """Driver row D as the list c(0), ..., c(t - 1)."""
    # D: (W,)
    return [int((int(D[u // 64]) >> (u % 64)) & 1) for u in range(t)]


def naive_left_half(driver: list[int]) -> list[int]:
    """The left half after len(driver) steps, cell by cell: element k - 1 is cell -k (independent check)."""
    t = len(driver)
    cells = [0] * (t + 2)  # cells -1 .. -(t + 2), white
    for u in range(t):
        right = [driver[u]] + cells  # cell 0, -1, -2, ...
        cells = [(cells[k + 1] if k + 1 < len(cells) else 0) ^ (right[k + 1] | right[k]) for k in range(len(cells))]
    return cells[:t]


@dataclass
class DrivenRow:
    t: int
    rows: int
    black: int  # longest black run from time t over all drivers
    white: int  # longest white run from time t over all drivers (column 1 latching)
    black_driver: list[int]


def driven_table(steps: int, every: int = 1, white_horizon: int | None = None, progress: bool = False,
                 chunk: int = 1 << 20) -> Iterator[DrivenRow]:
    """Yield, for t <= steps (every `every` steps and at `steps`), N(t) and the longest black and white runs from time
    t that some driver allows, with a driver for the black run."""
    for t, B, D in driven_rows(steps, progress):
        if t % every and t != steps:
            continue
        br = black_reach(B, t)  # (n,)
        i = int(np.argmax(br))
        horizon = white_horizon if white_horizon is not None else t + 2
        white = max(int(white_reach(B[k:k + chunk], t, horizon).max()) for k in range(0, len(B), chunk))
        yield DrivenRow(t, len(B), int(br[i]), white, driver_bits(D[i], t))


def class_black_max(a: int, chunk_bits: int = 22) -> int:
    """The longest black run of column 0 from time a over every configuration whose cells left of column 0 are white
    and cell 0 black at time 0 (cells 1 .. a free; later cells cannot reach the run's first row). Rows are held in
    depth coordinates, where depth j at time t is cell j - t and one step is y' = (y << 2) ^ ((y << 1) | y)."""
    n = a + 1
    mask = np.uint64((1 << n) - 1)
    pattern = np.uint64(sum(1 << (a - k) for k in range(0, n, 2)))  # depth a - k black for even k
    best = 0
    total = 1 << a
    for base in range(0, total, 1 << chunk_bits):
        y = (np.arange(base, min(total, base + (1 << chunk_bits)), dtype=np.uint64) << np.uint64(1)) | np.uint64(1)  # (m,)
        for _ in range(a):
            y = ((y << np.uint64(2)) ^ ((y << np.uint64(1)) | y)) & mask
        diff = y ^ pattern  # (m,)
        L = np.full(len(y), n, dtype=np.int64)  # (m,)
        nz = diff != 0
        L[nz] = a - np.floor(np.log2(diff[nz].astype(np.float64))).astype(np.int64)
        best = max(best, int(L.max()))
    return best


# ---------------------------------------------------------------------------------------------------------------------
# 3. Cells forced in the past by a word
# ---------------------------------------------------------------------------------------------------------------------


def preimages(rows: np.ndarray) -> np.ndarray:
    """All one-step preimages: a word on cells 0..n-1 at time t + 1 has four preimages on cells -1..n at time t, one
    for each value of cells n - 1 and n, solved leftward by left permutivity."""
    # rows: (m, n)
    m, n = rows.shape
    out = np.zeros((4 * m, n + 2), dtype=np.uint8)  # (4m, n + 2), column i is cell i - 1
    target = np.repeat(rows, 4, axis=0)  # (4m, n)
    bound = np.tile(np.array([[0, 0], [0, 1], [1, 0], [1, 1]], dtype=np.uint8), (m, 1))  # (4m, 2)
    out[:, n], out[:, n + 1] = bound[:, 0], bound[:, 1]
    for x in range(n - 1, -1, -1):
        out[:, x] = target[:, x] ^ (out[:, x + 1] | out[:, x + 2])
    return out  # (4m, n + 2)


def forced_cells(word: list[int], steps: int) -> list[list[tuple[int, int]]]:
    """For s = 1 .. steps, the maximal intervals of cells (positions relative to the word's cell 0) on which all s-step
    preimages of the word agree."""
    rows = np.array([word], dtype=np.uint8)  # (1, n)
    out: list[list[tuple[int, int]]] = []
    for s in range(1, steps + 1):
        rows = np.unique(preimages(rows), axis=0)  # (m, n + 2s)
        same = np.nonzero(np.all(rows == rows[0], axis=0))[0] - s  # (k,)
        intervals: list[tuple[int, int]] = []
        for x in same.tolist():
            if intervals and intervals[-1][1] == x - 1:
                intervals[-1] = (intervals[-1][0], x)
            else:
                intervals.append((x, x))
        out.append(intervals)
    return out


def far_periods(word: list[int], steps: int) -> list[set[int]]:
    """For s = 1 .. steps, the set of smallest periods of the left third of the s-step preimages of `word` (the part
    farthest from the cells the leftward solution starts at)."""
    rows = np.array([word], dtype=np.uint8)  # (1, n)
    out: list[set[int]] = []
    for _ in range(steps):
        rows = preimages(rows)  # (m, n + 2s)
        part = rows[:, : rows.shape[1] // 3]  # (m, k)
        periods: set[int] = set()
        for p in range(1, part.shape[1] // 2):
            ok = np.all(part[:, p:] == part[:, :-p], axis=1)  # (m,)
            if ok.any():
                periods.add(p)
                part = part[~ok]
                if len(part) == 0:
                    break
        if len(part):
            periods.add(0)  # some row has no period below half its length
        out.append(periods)
    return out


# ---------------------------------------------------------------------------------------------------------------------


def run_mechanism(args: argparse.Namespace) -> None:
    m = mechanism(args.steps, args.half, args.min_len)
    print(f"steps {m.steps}: {m.black_runs} black runs, {m.white_runs} white runs")
    print(f"longest black run {m.longest_black[0]} from {m.longest_black[1]}, "
          f"longest white run {m.longest_white[0]} from {m.longest_white[1]}")
    print(f"black runs whose length is not the alternating length of row a: {m.black_identity_failures}")
    print(f"white runs whose length is not read off column -1 and ell: {m.white_identity_failures}")
    print(f"white runs of length >= {args.min_len} by how they end: {m.white_end_counts}")
    if m.long_white:
        ratio = np.array([e / L for e, L in m.long_white])  # (r,)
        print(f"  ell / L: min {ratio.min():.2f}, median {np.median(ratio):.2f}, max {ratio.max():.2f}")
    lb = m.long_black
    if lb:
        life = np.array([x[2] for x in lb])  # (r,)
        L = np.array([x[1] for x in lb])  # (r,)
        grow = np.array([x[3] for x in lb])  # (r,)
        print(f"black runs of length >= {args.min_len}: {len(lb)}")
        print(f"  domain lifetime (steps back with >= 2 cells): min {life.min()}, median {np.median(life):.0f}, "
              f"max {life.max()}; forced minimum (L - 1)/3: {((L - 1) // 3).min()} to {((L - 1) // 3).max()}")
        print(f"  lifetime / L: min {np.min(life / L):.2f}, median {np.median(life / L):.2f}, max {np.max(life / L):.2f}")
        excess = life - ((L - 2) // 3 + 1)  # (r,), steps beyond the forced lifetime
        vals, counts = np.unique(excess, return_counts=True)
        print(f"  lifetime beyond the forced trapezoid's: {dict(zip(vals.tolist(), counts.tolist()))}")
        off, cnt = np.unique(np.array(m.long_black_offset), return_counts=True)
        print(f"  max over s of |right end + 4s| (0: the forced trapezoid): {dict(zip(off.tolist(), cnt.tolist()))}")
        print(f"  longest domain behind the run / L: min {np.min(grow / L):.2f}, median {np.median(grow / L):.2f}, "
              f"max {np.max(grow / L):.2f}")


def run_class(args: argparse.Namespace) -> None:
    print("a  longest black run from time a: configurations white left of column 0 / every driver")
    table = {r.t: r.black for r in driven_table(args.steps)}
    for a in range(3, args.steps + 1):
        print(f"{a:>3} {class_black_max(a):>4} {table[a]:>4}", flush=True)


def run_driven(args: argparse.Namespace) -> None:
    print(f"{'t':>4} {'rows N(t)':>10} {'log2 N':>7} {'black':>6} {'white':>6} {'black/t':>8}")
    for r in driven_table(args.steps, args.every, progress=True):
        print(f"{r.t:>4} {r.rows:>10} {np.log2(r.rows):>7.2f} {r.black:>6} {r.white:>6} {r.black / r.t:>8.3f}",
              flush=True)


def run_forced(args: argparse.Namespace) -> None:
    n = args.length
    words = {"black block": [1] * n, "white block": [0] * n,
             "alternating, ends black": [(n - 1 - i + 1) % 2 for i in range(n)],
             "alternating, ends white": [(n - 1 - i) % 2 for i in range(n)]}
    for name, w in words.items():
        print(f"{name} of {n} cells:")
        for s, iv in enumerate(forced_cells(w, args.depth), start=1):
            print(f"  s = {s}: forced cells {iv if iv else 'none'}")
    for s, per in enumerate(far_periods([1] * args.length * 3, args.periods), start=1):
        print(f"black block of {3 * args.length} cells, s = {s}: periods far from the right end {sorted(per)}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("mechanism")
    p.add_argument("--steps", type=int, default=1 << 20)
    p.add_argument("--half", type=int, default=64)
    p.add_argument("--min-len", type=int, default=12)
    p.set_defaults(func=run_mechanism)
    p = sub.add_parser("driven")
    p.add_argument("--steps", type=int, default=150)
    p.add_argument("--every", type=int, default=25)
    p.set_defaults(func=run_driven)
    p = sub.add_parser("class")
    p.add_argument("--steps", type=int, default=24)
    p.set_defaults(func=run_class)
    p = sub.add_parser("forced")
    p.add_argument("--length", type=int, default=40)
    p.add_argument("--depth", type=int, default=6)
    p.add_argument("--periods", type=int, default=8)
    p.set_defaults(func=run_forced)
    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
