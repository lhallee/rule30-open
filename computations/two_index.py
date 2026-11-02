"""The spacetime diagram of one black cell as an array of two indices: right-edge cycles, row periods and 2-kernels.

Write R(j, t) = cell(t, t - j) for the single black cell: row j of this array is the j-th diagonal from the right edge,
Rd_j, which is periodic from time 0 with a period dividing 2^j. L_n, the cycle length of 1 under
Phi(x) = x xor (2x or 4x) modulo 2^n, is the least period of Rd_(n-1) (the kit's `TFunctionCycles.seed_rows_return_iff`
with `Rule30RightPeriods.per_mono_all`).

* `cycle_lengths`: L_1 .. L_n by level lifting (the kit's `TFunctionCycles.lift_iff`): the diagonal Rd_i is the prefix
  XOR of its input Rd_(i-1) or Rd_(i-2), and the cycle doubles at level i exactly when that input has odd weight over
  one cycle. Each level is a numpy prefix XOR over one cycle, so n = 61 (L_61 = 2^25) takes a few seconds.
* `white_runs`: W(2^m), the number of white cells immediately left of the right edge at time 2^m, from the integer rows;
  `white_runs_from_cycles` reads it off the L_n by the kit's `Rule30RightPeriods.per_iff_gap`
  (L_n <= 2^m iff W(2^m) >= n - 1).
* `diagonal_array`, `row_periods`: R(j, t) for an elementary rule from one cell, and the least period of each row, for
  Rules 30, 90 and 150 and for two synthetic 2-automatic arrays (`synthetic_array`), the controls of the kernel lemma
  of `Rule30Open.Complexity.TwoIndex`: a 2-automatic array whose rows are eventually periodic has row periods at most
  C (j + 1).
* `window_kernel_counts`: the number of distinct W x W windows of the 2-kernel elements
  (v, w) -> R(2^e v + r, 2^e w + s), r, s < 2^e, for e = 0 .. 7.
* `mahler_degrees`: the largest k with a nonzero coefficient of Rd_j in the binomial basis binom(t, k) mod 2 on one
  period (its Mahler degree), level by level.
* `transducer_sizes`: the number of states of the minimal transducer, read from the least significant bit, of
  Phi^(2^k), and of the right-edge steps of Rules 90 and 150 to the same powers.

Run as `python -m computations.two_index`.
"""

from __future__ import annotations

import argparse
import time

import numpy as np
from tqdm.auto import tqdm


# ---------------------------------------------------------------------------------------------------------------------
# Cycles of the right edge


def cycle_lengths(n: int, progress: bool = False) -> tuple[list[int], list[np.ndarray]]:
    """L_1 .. L_n by level lifting, and the diagonals Rd_0 .. Rd_(n-1), each over one least period.

    Returns `(lengths, diagonals)` with `lengths[i] = L_(i+1)`, the least period of Rd_i, and `diagonals[i]` the uint8
    array of Rd_i on [0, L_(i+1)) when that period is at most 2^20, and an empty array beyond (to bound memory).
    """
    lengths: list[int] = []
    diagonals: list[np.ndarray] = []
    prev2 = np.zeros(1, dtype=np.uint8)  # (1,), Rd_(-1), white
    prev1 = np.ones(1, dtype=np.uint8)  # (1,), Rd_0, black
    lengths.append(1)
    diagonals.append(prev1)
    levels = range(1, n)
    for i in tqdm(levels, desc="levels", disable=not progress, leave=False):
        period = prev1.size
        if prev2.size < period:
            prev2 = np.tile(prev2, period // prev2.size)  # (period,)
        inp = prev1 | prev2  # (period,), the input of Rd_i
        if int(inp.sum()) & 1:
            inp = np.tile(inp, 2)  # (2 period,): the cycle doubles
        cum = np.bitwise_xor.accumulate(inp)  # (P,), cum[t] = inp[0] ^ ... ^ inp[t]
        diag = np.empty_like(cum)  # (P,)
        diag[0] = 0  # Rd_i(0) is white for i >= 1
        diag[1:] = cum[:-1]
        lengths.append(diag.size)
        diagonals.append(diag if diag.size <= 1 << 20 else np.zeros(0, dtype=np.uint8))
        prev2, prev1 = prev1, diag
    return lengths, diagonals


def doubling_levels(lengths: list[int]) -> list[int]:
    """The levels n >= 2 with L_n = 2 L_(n-1)."""
    return [i + 1 for i in range(1, len(lengths)) if lengths[i] == 2 * lengths[i - 1]]


def longest_flat_run(lengths: list[int]) -> int:
    """The longest run of consecutive levels n >= 2 at which the cycle does not double."""
    best = run = 0
    for i in range(1, len(lengths)):
        run = run + 1 if lengths[i] == lengths[i - 1] else 0
        best = max(best, run)
    return best


def phi_cycle_length(n: int) -> int:
    """L_n by iterating Phi on integers modulo 2^n until 1 returns: an independent check for small n."""
    mask = (1 << n) - 1
    x, t = 1, 0
    while True:
        x = (x ^ ((x << 1) | (x << 2))) & mask
        t += 1
        if x == 1 & mask:
            return t


def white_runs(m_max: int, progress: bool = False) -> list[int]:
    """W(2^m) for m = 0 .. m_max: the white cells immediately left of the right edge at time 2^m, from the integer
    rows a(t + 1) = a(t) xor (2 a(t) or 4 a(t)), whose bit j is cell (t, t - j)."""
    out: list[int] = []
    a, t = 1, 0
    targets = [1 << m for m in range(m_max + 1)]
    for target in tqdm(targets, desc="rows", disable=not progress, leave=False):
        while t < target:
            a ^= (a << 1) | (a << 2)
            t += 1
        rest = a >> 1
        out.append((rest & -rest).bit_length() - 1)  # trailing zeros of a above the right edge
    return out


def white_runs_from_cycles(lengths: list[int]) -> list[int]:
    """W(2^m) read off L_1 .. L_N through L_n <= 2^m iff W(2^m) >= n - 1, for every m with L_N > 2^m."""
    out: list[int] = []
    m = 0
    while lengths[-1] > 1 << m:
        n = max(i + 1 for i in range(len(lengths)) if lengths[i] <= 1 << m)
        out.append(n - 1)
        m += 1
    return out


# ---------------------------------------------------------------------------------------------------------------------
# Arrays of two indices


def diagonal_array(rule: int, rows: int, times: int) -> np.ndarray:
    """R[j, t] = cell(t, t - j) of the elementary rule from one black cell, for j < rows and t < times."""
    width = 2 * times + 3
    origin = times + 1
    table = np.array([(rule >> k) & 1 for k in range(8)], dtype=np.uint8)  # (8,)
    row = np.zeros(width, dtype=np.uint8)  # (width,), cell x at index origin + x
    row[origin] = 1
    out = np.zeros((rows, times), dtype=np.uint8)  # (rows, times)
    js = np.arange(rows)  # (rows,)
    for t in range(times):
        idx = origin + t - js  # (rows,)
        ok = idx >= 0  # (rows,)
        out[js[ok], t] = row[idx[ok]]
        padded = np.concatenate(([0], row, [0])).astype(np.uint8)  # (width + 2,)
        row = table[4 * padded[:-2] + 2 * padded[1:-1] + padded[2:]]  # (width,)
    return out


def synthetic_array(kind: str, rows: int, times: int) -> np.ndarray:
    """Two 2-automatic arrays with periodic rows: 'thue' is the parity of popcount(j and t), 'mod3' is [t = j mod 3]."""
    j = np.arange(rows)[:, None]  # (rows, 1)
    t = np.arange(times)[None, :]  # (1, times)
    if kind == "thue":
        x = j & t  # (rows, times)
        parity = np.zeros_like(x)  # (rows, times)
        while np.any(x):
            parity ^= x & 1
            x >>= 1
        return parity.astype(np.uint8)
    if kind == "mod3":
        return ((t - j) % 3 == 0).astype(np.uint8)  # (rows, times)
    raise ValueError(kind)


def least_period(seq: np.ndarray, start: int = 0) -> int:
    """The least p >= 1 with seq[t + p] = seq[t] for every start <= t < len(seq) - p, searched up to half the length
    after `start`; 0 when none is found."""
    tail = seq[start:]  # (T,)
    for p in range(1, tail.size // 2 + 1):
        if np.array_equal(tail[p:], tail[:-p]):
            return p
    return 0


def row_periods(array: np.ndarray, start: int = 0) -> list[int]:
    """The least period of each row of `array`, from time `start` on, read on the window it covers."""
    return [least_period(array[j], start) for j in range(array.shape[0])]


def window_kernel_counts(array: np.ndarray, window: int, e_max: int) -> list[int]:
    """For e = 0 .. e_max, the number of distinct window x window blocks of the kernel elements
    (v, w) -> array[2^e v + r, 2^e w + s], r, s < 2^e, that fit inside `array`."""
    out: list[int] = []
    for e in range(e_max + 1):
        step = 1 << e
        seen: set[bytes] = set()
        base = step * np.arange(window)  # (window,)
        for r in range(step):
            for s in range(step):
                vj, wt = base + r, base + s  # (window,), (window,)
                if vj[-1] >= array.shape[0] or wt[-1] >= array.shape[1]:
                    continue
                seen.add(array[np.ix_(vj, wt)].tobytes())
        out.append(len(seen))
    return out


# ---------------------------------------------------------------------------------------------------------------------
# Mahler degrees and transducers


def mahler_coefficients(seq: np.ndarray) -> np.ndarray:
    """The coefficients a_k, k < P, of a sequence of period P = 2^m in the basis binom(t, k) mod 2, by the Moebius
    transform over the bits of t (Lucas: binom(t, k) is odd iff the bits of k are bits of t)."""
    w = seq.astype(np.uint8).copy()  # (P,)
    size = w.size
    i = 1
    while i < size:
        view = w.reshape(-1, 2, i)  # (P / 2i, 2, i)
        view[:, 1, :] ^= view[:, 0, :]
        i *= 2
    return w  # (P,)


def mahler_degree(seq: np.ndarray) -> int:
    """The largest k with a_k = 1, or -1 for the white sequence."""
    nz = np.flatnonzero(mahler_coefficients(seq))  # (d,)
    return int(nz[-1]) if nz.size else -1


def mahler_degrees(diagonals: list[np.ndarray], count: int) -> list[int]:
    """The Mahler degree of Rd_j on its least period, j < count."""
    return [mahler_degree(diagonals[j]) for j in range(count)]


Transducer = tuple[list[tuple[int, int]], list[tuple[int, int]]]  # (next state on 0 and 1, output on 0 and 1)


def phi_transducer(rule: int = 30) -> Transducer:
    """One step of an elementary rule in the frame of its right edge, x'_j = x_j xor g(x_(j-1), x_(j-2)), read from
    the least significant bit and minimized: g = or for Rule 30 (Phi, 3 states), g(a, b) = b for Rule 90 and
    g = xor for Rule 150. The state before minimizing is the pair of the last two input bits."""
    g = {30: lambda a, b: a | b, 90: lambda a, b: b, 150: lambda a, b: a ^ b}[rule]
    delta: list[tuple[int, int]] = []
    out: list[tuple[int, int]] = []
    for state in range(4):  # state = 2 * x_(j-1) + x_(j-2)
        a, b = state >> 1, state & 1
        delta.append(((0 << 1) | a, (1 << 1) | a))
        out.append((0 ^ g(a, b), 1 ^ g(a, b)))
    return minimize((delta, out))


def minimize(machine: Transducer) -> Transducer:
    """Moore refinement of a transducer whose states are all reachable from state 0; the start state stays 0."""
    delta, out = machine
    n = len(delta)
    labels = {o: i for i, o in enumerate(sorted(set(out)))}
    cls = [labels[out[s]] for s in range(n)]
    while True:
        keys: dict[tuple[int, int, int], int] = {}
        new = [keys.setdefault((cls[s], cls[delta[s][0]], cls[delta[s][1]]), len(keys)) for s in range(n)]
        if len(keys) == len(set(cls)):
            cls = new
            break
        cls = new
    order = {cls[0]: 0}
    for s in range(n):
        order.setdefault(cls[s], len(order))
    size = len(order)
    nd: list[tuple[int, int]] = [(0, 0)] * size
    no: list[tuple[int, int]] = [(0, 0)] * size
    for s in range(n):
        c = order[cls[s]]
        nd[c] = (order[cls[delta[s][0]]], order[cls[delta[s][1]]])
        no[c] = out[s]
    return nd, no


def compose(first: Transducer, second: Transducer) -> Transducer:
    """`second` after `first`, on the reachable pairs of states, minimized."""
    fd, fo = first
    gd, go = second
    index = {(0, 0): 0}
    order = [(0, 0)]
    delta: list[tuple[int, int]] = []
    out: list[tuple[int, int]] = []
    i = 0
    while i < len(order):
        s, u = order[i]
        nxt_row: list[int] = []
        out_row: list[int] = []
        for b in (0, 1):
            y = fo[s][b]
            nxt = (fd[s][b], gd[u][y])
            if nxt not in index:
                index[nxt] = len(order)
                order.append(nxt)
            nxt_row.append(index[nxt])
            out_row.append(go[u][y])
        delta.append((nxt_row[0], nxt_row[1]))
        out.append((out_row[0], out_row[1]))
        i += 1
    return minimize((delta, out))


def transducer_sizes(k_max: int, rule: int = 30, progress: bool = False) -> list[int]:
    """The number of states of the minimal transducer of the right-edge step of `rule` to the power 2^k,
    k = 0 .. k_max, by repeated squaring."""
    machine = phi_transducer(rule)
    sizes = [len(machine[0])]
    for _ in tqdm(range(k_max), desc="squarings", disable=not progress, leave=False):
        machine = compose(machine, machine)
        sizes.append(len(machine[0]))
    return sizes


def run_transducer(machine: Transducer, x: int, bits: int) -> int:
    """The low `bits` output bits of `machine` on the input x, least significant bit first."""
    delta, out = machine
    s, y = 0, 0
    for i in range(bits):
        b = (x >> i) & 1
        y |= out[s][b] << i
        s = delta[s][b]
    return y


# ---------------------------------------------------------------------------------------------------------------------


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--levels", type=int, default=61, help="compute L_1 .. L_n")
    parser.add_argument("--white", type=int, default=16, help="W(2^m) from the integer rows for m <= this")
    parser.add_argument("--rows", type=int, default=64, help="rows of the diagonal arrays for the row periods")
    parser.add_argument("--kernel-e", type=int, default=7, help="window kernel counts for e <= this")
    parser.add_argument("--mahler", type=int, default=50, help="Mahler degrees of Rd_j, j < this")
    parser.add_argument("--transducer", type=int, default=4, help="transducer sizes of Phi^(2^k), k <= this")
    parser.add_argument("--transducer-linear", type=int, default=3,
                        help="the same for the right-edge steps of Rules 90 and 150, k <= this")
    args = parser.parse_args()

    start = time.time()
    lengths, diagonals = cycle_lengths(args.levels, progress=True)
    print(f"L_n, n = 1 .. {args.levels}: log2 = {[x.bit_length() - 1 for x in lengths]}")
    print(f"doubling levels: {doubling_levels(lengths)}")
    print(f"longest run of levels without doubling: {longest_flat_run(lengths)}")
    ratios = [lengths[i] / (i + 1) for i in range(len(lengths))]
    print(f"L_n / n at n = 10, 20, 30, 40, 50, 61: {[round(ratios[n - 1], 1) for n in (10, 20, 30, 40, 50, 61) if n <= len(ratios)]}")
    print(f"log2(L_n) / n at the last level: {(lengths[-1].bit_length() - 1) / len(lengths):.3f}  ({time.time() - start:.1f} s)")

    from_cycles = white_runs_from_cycles(lengths)
    direct = white_runs(args.white, progress=True)
    agree = all(direct[m] == from_cycles[m] for m in range(min(len(direct), len(from_cycles))))
    print(f"W(2^m), m = 0 .. {len(from_cycles) - 1}, from the cycles: {from_cycles}")
    print(f"W(2^m) from the integer rows agrees for m <= {min(len(direct), len(from_cycles)) - 1}: {agree}")
    print(f"W(2^m) / 2^m: {[round(w / (1 << m), 4) for m, w in enumerate(from_cycles)]}")

    times = 1 << 12
    controls = {
        "rule 30": diagonal_array(30, args.rows, times),
        "rule 90": diagonal_array(90, args.rows, times),
        "rule 150": diagonal_array(150, args.rows, times),
        "popcount(j and t) mod 2": synthetic_array("thue", args.rows, times),
        "[t = j mod 3]": synthetic_array("mod3", args.rows, times),
    }
    for name, array in controls.items():
        periods = row_periods(array)
        if name == "rule 30":
            known = [j for j, p in enumerate(periods) if p > 0]
            assert all(periods[j] == lengths[j] for j in known if j < len(lengths))
            print(f"rule 30: the direct row periods agree with L_(j+1) for the {len(known)} rows j <= {known[-1]} "
                  f"whose period fits in {times} steps")
            periods = lengths[: args.rows]
        worst = max(p / (j + 1) for j, p in enumerate(periods))
        print(f"{name}: least row periods j < {len(periods)}: {periods}; max period / (j + 1) = {worst:.2f}")

    window = 16
    size = (1 << args.kernel_e) * window
    for rule in (30, 90, 150):
        array = diagonal_array(rule, size, size)
        print(f"rule {rule}: distinct {window} x {window} kernel windows, e = 0 .. {args.kernel_e}: "
              f"{window_kernel_counts(array, window, args.kernel_e)}")

    degrees = mahler_degrees(diagonals, args.mahler)
    print("j, least period P_j, Mahler degree K_j, K_j / P_j:")
    for j in range(args.mahler):
        mark = " doubling" if j >= 1 and lengths[j] == 2 * lengths[j - 1] else ""
        print(f"  {j:3d} {lengths[j]:8d} {degrees[j]:8d} {degrees[j] / lengths[j]:.4f}{mark}")

    print(f"minimal transducer sizes of Phi^(2^k), k = 0 .. {args.transducer}: "
          f"{transducer_sizes(args.transducer, progress=True)}  ({time.time() - start:.1f} s)")
    for rule in (90, 150):
        print(f"rule {rule}: minimal transducer sizes of its right-edge step to the power 2^k, "
              f"k = 0 .. {args.transducer_linear}: {transducer_sizes(args.transducer_linear, rule, progress=True)}"
              f"  ({time.time() - start:.1f} s)")


if __name__ == "__main__":
    main()
