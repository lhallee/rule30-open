"""The GF(2) rank of the center cell across a left cut of the cone, in full and on windowed rows through the T-function.

c_t is a Boolean function of the 2t + 1 cells x_{-t} .. x_t of row 0 (new x_j = x_{j-1} xor (x_j or x_{j+1})). The
*left setting* u is the a leftmost cells x_{-t} .. x_{-t+a-1} (bit i of u is x_{-t+i}, as in `cone_screening`), the
*right setting* v the other 2t + 1 - a cells. rank(t, a) is the GF(2) rank of the matrix [c_t(u, v)]; it is at most the
number N_L(t, a) of distinct rows, which is the width at level a of every ordered decision diagram that reads the row
from the left.

* `full_rank` computes rank(t, a) from the truth table: `cone_table` for t <= 12, the bit-packed in-place evolution
  `packed_center` for t = 13, 14 (2 GB at t = 14).
* `window_values` restricts the right settings to a word w of `length` cells after the cut, white beyond. On these rows
  c_t is bit a + length - 1 of Phi^t(N) modulo 2^(a + length), with Phi(x) = x xor (2x or 4x) the kit's T-function
  (`TFunction.Phi`) and N the D = a + length cells read with x_{-t} as the top bit (`window_number`), so the table costs
  2^D words and t steps of Phi whatever t is. Its rank, `window_rank`, is at most rank(t, a).
* `first_window_drop` finds the first t >= a + 4 at which the windowed rank with length a + 2 falls below
  rho(a) = 2 + floor(2^a / 3), scanning one period of Phi modulo 2^(2a + 2); `window_floor` gives the least windowed
  rank over a whole period, which is 1 for every fixed width (the window is the identity at t = 2^j, Lean
  `center_two_pow`).
* `stripe_basis` lists rho(a) left settings: x_{-t} black with every other cell white, and x_{-t} white with a word
  x_{-t+1} .. x_{-t+a-1} that has no prefix (10)^k 11. `subset_rank` gives the rank of their rows.
* `lift_test` is the test of an inductive route: a greedy family of left settings at level a - 1, independent at every t
  of a range, lifted to level a by appending the cell next to the cut, and checked for rho(a) independent members at
  every t of the next range.
* `stripe_coefficients` reads the algebraic normal form: the left monomials outside the stripe basis have coefficient
  functions that are zero or the constant 1, which is why the stripe basis spans the rows.
* `section_maps` and `closure_dimension`: one step moves the left setting by one of the three states of the kit's
  automaton 2369, chosen by the two right cells next to the cut, so every row space of the cut lies in the span of the
  top bits of all products of states, whose dimension `closure_dimension` computes.

    python -m computations.left_cut_rank --full 12             # rank(t, a) for t <= 12, every a <= t - 1 (2 min)
    python -m computations.left_cut_rank --packed 14 --max-a 12 # rank(14, a), a <= 12 (1 min, 2 GB)
    python -m computations.left_cut_rank --window 12           # windowed rank, a <= 12, t = a + 4 .. a + 12 (2 min)
    python -m computations.left_cut_rank --drops 10            # first t with windowed rank below rho(a), a = 3 .. 10
    python -m computations.left_cut_rank --basis 10            # rank of the stripe basis on windows, a <= 10 (2 min)
    python -m computations.left_cut_rank --lift 10 --extra 2   # the lifting test, a = 3 .. 10 (1 min)
    python -m computations.left_cut_rank --closure 13          # the closure dimension, a <= 13 (20 s)
    python -m computations.left_cut_rank --coefficients 10     # coefficients of the stripe monomials, t <= 10
"""

from __future__ import annotations

import argparse
import sys

import numpy as np

from tqdm.auto import tqdm

from computations.cone_screening import cone_table
from computations.wild_ideas import gf2_rank, insert

PATTERNS = [0xAAAA_AAAA_AAAA_AAAA, 0xCCCC_CCCC_CCCC_CCCC, 0xF0F0_F0F0_F0F0_F0F0, 0xFF00_FF00_FF00_FF00,
            0xFFFF_0000_FFFF_0000, 0xFFFF_FFFF_0000_0000]


def rho(a: int) -> int:
    """2 + floor(2^a / 3): the conjectured rank at the left cut after a cells, a <= t - 3."""
    return 2 + (1 << a) // 3


def rows_rank(matrix: np.ndarray) -> int:
    """The GF(2) rank of a 0/1 matrix, its rows packed into integers."""
    # matrix: (rows, columns) of 0/1
    packed = np.packbits(matrix.astype(np.uint8), axis=1, bitorder="little")  # (rows, ceil(columns / 8))
    return gf2_rank([int.from_bytes(row.tobytes(), "little") for row in packed])


def cut_matrix(table: np.ndarray, t: int, a: int) -> np.ndarray:
    """The truth table of c_t (bit i of the index is x_{-t+i}) as the matrix with left settings u as rows."""
    # table: (2^(2t+1),)
    return table.reshape(1 << (2 * t + 1 - a), 1 << a).T  # (2^a, 2^(2t+1-a)), entry [u, v]


def full_rank(t: int, a: int, table: np.ndarray | None = None) -> int:
    """rank(t, a) from the full truth table."""
    if table is None:
        table = cone_table(t)  # (2^(2t+1),)
    return rows_rank(cut_matrix(table, t, a))


def packed_center(t: int, progress: bool = False) -> np.ndarray:
    """c_t for all 2^(2t+1) rows, 64 to a word, evolved in place: bit j of the result is c_t of the row whose cell
    x_{-t+i} is bit 2t - i of j, so the left cells are the high bits of j. Needs 2t + 1 >= 7."""
    n = 2 * t + 1
    count = (1 << n) // 64
    words = np.arange(count, dtype=np.uint64)  # (2^n / 64,)

    def variable(bit: int) -> np.ndarray:
        """Bit `bit` of the row index, packed."""
        if bit < 6:
            return np.full(count, np.uint64(PATTERNS[bit]), dtype=np.uint64)  # (2^n / 64,)
        column = (words >> np.uint64(bit - 6)) & np.uint64(1)  # (2^n / 64,)
        column *= np.uint64(0xFFFF_FFFF_FFFF_FFFF)
        return column

    row = [variable(n - 1 - i) for i in range(n)]  # n x (2^n / 64,), row[i] is x_{-t+i}
    del words
    scratch = np.empty(count, dtype=np.uint64)  # (2^n / 64,)
    for _ in tqdm(range(t), desc=f"steps t={t}", disable=not progress, file=sys.stderr):
        for i in range(1, len(row) - 1):
            np.bitwise_or(row[i], row[i + 1], out=scratch)
            np.bitwise_xor(row[i - 1], scratch, out=row[i - 1])
        row.pop()
        row.pop()
    return row[0]  # (2^n / 64,)


def packed_rank(center: np.ndarray, t: int, a: int) -> int:
    """rank(t, a) from `packed_center`: the rows of the packed table with the same high a bits form one left setting
    (with its cells in reverse bit order, which does not change the rank)."""
    # center: (2^(2t+1) / 64,)
    rows = center.reshape(1 << a, -1)  # (2^a, 2^(2t+1-a) / 64)
    return gf2_rank([int.from_bytes(r.tobytes(), "little") for r in rows])


def phi(x: np.ndarray, mask: np.uint64) -> np.ndarray:
    """The kit's T-function Phi(x) = x xor (2x or 4x), modulo mask + 1."""
    # x: (m,)
    return (x ^ ((x << np.uint64(1)) | (x << np.uint64(2)))) & mask  # (m,)


def reverse_bits(index: np.ndarray, width: int) -> np.ndarray:
    """The integers with their `width` low bits in reverse order."""
    # index: (m,)
    out = np.zeros_like(index)  # (m,)
    for i in range(width):
        out |= ((index >> np.uint64(i)) & np.uint64(1)) << np.uint64(width - 1 - i)
    return out


def window_number(u: int, w: int, a: int, length: int) -> int:
    """N for the row with left setting u (a cells), then the word w (`length` cells), then white: cell x_{-t+i} is bit
    a + length - 1 - i of N."""
    cells = u | (w << a)
    return int(reverse_bits(np.array([cells], dtype=np.uint64), a + length)[0])


def window_values(a: int, length: int, ts: list[int]) -> dict[int, np.ndarray]:
    """For each t in ts, c_t on the rows with left setting u and right setting a word w of `length` cells after the
    cut, white beyond, through Phi^t modulo 2^(a + length). Needs a + length <= 2t + 1 for the cells to lie in the cone
    (beyond it they do not matter)."""
    width = a + length
    mask = np.uint64((1 << width) - 1)
    index = np.arange(1 << width, dtype=np.uint64)  # (2^D,), bit i is x_{-t+i}
    x = reverse_bits(index, width)  # (2^D,), N of each row
    out: dict[int, np.ndarray] = {}
    done = 0
    for t in sorted(ts):
        while done < t:
            x = phi(x, mask)
            done += 1
        top = ((x >> np.uint64(width - 1)) & np.uint64(1)).astype(np.uint8)  # (2^D,)
        out[t] = top.reshape(1 << length, 1 << a).T  # (2^a, 2^length), entry [u, w]
    return out


def window_rank(a: int, length: int, ts: list[int]) -> dict[int, int]:
    """The GF(2) rank of the windowed matrices of `window_values`."""
    return {t: rows_rank(m) for t, m in window_values(a, length, ts).items()}


def phi_period(width: int) -> int:
    """The period of Phi on the integers modulo 2^width."""
    mask = np.uint64((1 << width) - 1)
    start = np.arange(1 << width, dtype=np.uint64)  # (2^width,)
    x = phi(start, mask)  # (2^width,)
    period = 1
    while not np.array_equal(x, start):
        x = phi(x, mask)
        period += 1
    return period


def first_window_drop(a: int, progress: bool = False) -> tuple[int | None, int]:
    """The first t >= a + 4 at which the windowed rank with length a + 2 is below rho(a), scanning t = a + 4 ..
    a + 3 + P with P the period of Phi modulo 2^(2a+2) (the windowed matrix repeats with period P); and P."""
    width = 2 * a + 2
    mask = np.uint64((1 << width) - 1)
    period = phi_period(width)
    x = reverse_bits(np.arange(1 << width, dtype=np.uint64), width)  # (2^D,)
    for _ in range(a + 4):
        x = phi(x, mask)
    for t in tqdm(range(a + 4, a + 4 + period), desc=f"a={a}", disable=not progress, file=sys.stderr):
        top = ((x >> np.uint64(width - 1)) & np.uint64(1)).astype(np.uint8)  # (2^D,)
        if rows_rank(top.reshape(1 << (a + 2), 1 << a).T) < rho(a):
            return t, period
        x = phi(x, mask)
    return None, period


def window_floor(a: int, length: int, start: int, progress: bool = False) -> tuple[int, list[int], int]:
    """The least windowed rank at level a with words of `length` cells over t = start .. start + P - 1, P the period of
    Phi modulo 2^(a + length); the windowed matrix is periodic in t with period P, so this is the least value over every
    t >= start. Also the t of that range with rank below rho(a), and P."""
    width = a + length
    mask = np.uint64((1 << width) - 1)
    period = phi_period(width)
    x = reverse_bits(np.arange(1 << width, dtype=np.uint64), width)  # (2^D,)
    for _ in range(start):
        x = phi(x, mask)
    least = 1 << a
    below: list[int] = []
    for t in tqdm(range(start, start + period), desc=f"a={a} L={length}", disable=not progress, file=sys.stderr):
        top = ((x >> np.uint64(width - 1)) & np.uint64(1)).astype(np.uint8)  # (2^D,)
        r = rows_rank(top.reshape(1 << length, 1 << a).T)
        least = min(least, r)
        if r < rho(a):
            below.append(t)
        x = phi(x, mask)
    return least, below, period


def section_maps(a: int) -> list[np.ndarray]:
    """The three states of the kit's automaton 2369 on the a-bit numbers, as the step of the left setting: with the
    left setting U read with x_{-t} as the top bit and (p, q) the two right cells next to the cut, one step sends U to
    Phi(4U + 2p + q) >> 2 modulo 2^a; (p, q) = (0, 0) gives Phi, (0, 1) and (1, *) the other two states."""
    u = np.arange(1 << a, dtype=np.int64)  # (2^a,)
    out: list[np.ndarray] = []
    for low in (0, 1, 2):
        x = 4 * u + low  # (2^a,)
        out.append(((x ^ ((2 * x) | (4 * x))) >> 2) & ((1 << a) - 1))  # (2^a,)
    return out


def closure_dimension(a: int) -> int:
    """The dimension of the smallest space of functions of U that holds the top bit of U and is closed under
    composition with each of the three section maps: the span of the top bits of every product of states, which
    holds every row space of the left cut after a cells (for every t with at least two right cells)."""
    maps = section_maps(a)
    u = np.arange(1 << a, dtype=np.int64)  # (2^a,)
    top = ((u >> (a - 1)) & 1).astype(np.uint8)  # (2^a,)
    basis: dict[int, int] = {}
    insert(basis, packed_rows(top[None, :])[0])
    queue = [top]
    while queue:
        f = queue.pop()  # (2^a,)
        for h in maps:
            g = f[h]  # (2^a,), f composed with h
            if insert(basis, packed_rows(g[None, :])[0]):
                queue.append(g)
    return len(basis)


def stripe_basis(a: int) -> list[int]:
    """The left settings u (bit i is x_{-t+i}) with x_{-t} = 0 whose word x_{-t+1} .. x_{-t+a-1} has no prefix
    (10)^k 11, k >= 0, and the setting with x_{-t} = 1 and every other cell white: rho(a) settings, closed under turning
    black cells white. Conjecturally a basis of the rows at every t >= a + 3."""
    def starts_bad(word: str) -> bool:
        k = 0
        while word.startswith("10" * k):
            if word.startswith("10" * k + "11"):
                return True
            k += 1
            if 2 * k > len(word):
                return False
        return False

    out = [0, 1] if a >= 1 else [0]
    for u in range(2, 1 << a, 2):
        word = "".join(str((u >> i) & 1) for i in range(1, a))
        if not starts_bad(word):
            out.append(u)
    return sorted(out)


def anf(table: np.ndarray) -> np.ndarray:
    """The algebraic normal form over GF(2) of a truth table (Moebius transform): entry S is the coefficient of the
    monomial of the cells in S."""
    # table: (2^n,)
    out = table.astype(np.uint8).copy()  # (2^n,)
    n = out.size.bit_length() - 1
    for i in range(n):
        view = out.reshape(-1, 2, 1 << i)  # (2^(n-i-1), 2, 2^i)
        view[:, 1, :] ^= view[:, 0, :]
    return out


def stripe_coefficients(t: int, a: int, table: np.ndarray | None = None) -> dict[str, int]:
    """For the left monomials S (x_{-t} not in S) whose word x_{-t+1} .. x_{-t+a-1} has a prefix (10)^k 11: how many
    have coefficient function (of the right cells) zero, the constant 1, or anything else."""
    if table is None:
        table = cone_table(t)  # (2^(2t+1),)
    coefficients = cut_matrix(anf(table), t, a)  # (2^a, 2^(2t+1-a)), entry [S, T]
    basis = set(stripe_basis(a))
    kinds = {"zero": 0, "one": 0, "other": 0}
    for s in range(0, 1 << a, 2):
        if s in basis:
            continue
        row = coefficients[s]  # (2^(2t+1-a),)
        if not row.any():
            kinds["zero"] += 1
        elif row[0] == 1 and not row[1:].any():
            kinds["one"] += 1
        else:
            kinds["other"] += 1
    return kinds


def subset_rank(rows: list[int], members: list[int]) -> int:
    """The GF(2) rank of the listed rows."""
    return gf2_rank([rows[u] for u in members])


def reverse_index(u: int, a: int) -> int:
    """The row of `packed_center` that holds left setting u: its a cells in reverse bit order."""
    return int(reverse_bits(np.array([u], dtype=np.uint64), a)[0])


def packed_rows(matrix: np.ndarray) -> list[int]:
    """The rows of a 0/1 matrix as integers."""
    # matrix: (rows, columns)
    packed = np.packbits(matrix.astype(np.uint8), axis=1, bitorder="little")  # (rows, ceil(columns / 8))
    return [int.from_bytes(row.tobytes(), "little") for row in packed]


def greedy_family(rows_by_t: dict[int, list[int]], candidates: list[int], start: list[int] | None = None) -> list[int]:
    """Left settings from `candidates`, taken in order, kept when the family stays independent at every t."""
    bases: dict[int, dict[int, int]] = {t: {} for t in rows_by_t}  # t -> GF(2) basis
    family: list[int] = []
    for u in (start or []) + candidates:
        if u in family:
            continue
        trial = {t: dict(b) for t, b in bases.items()}
        if all(insert(trial[t], rows_by_t[t][u]) for t in rows_by_t):
            bases = trial
            family.append(u)
    return family


def lift_test(a: int, length: int, span: int = 9) -> dict[str, object]:
    """The lifting test at level a. B is the greedy family of left settings at level a - 1 (in the order 0, 1, ...)
    independent at every t in [a + 3, a + 2 + span]. Its lift appends the cell next to the cut, 0 and 1, to every member.
    Reported, for each t in [a + 4, a + 3 + span]: the rank of the lift and the rank of all left settings (both on the
    windowed columns of `length` cells), and the size of the greedy subfamily of the lift independent at every t at once,
    and of the lift extended greedily by other settings."""
    low_ts = list(range(a + 3, a + 3 + span))
    high_ts = list(range(a + 4, a + 4 + span))
    low = {t: packed_rows(m) for t, m in window_values(a - 1, length + 1, low_ts).items()}  # same cells, cut one left
    high = {t: packed_rows(m) for t, m in window_values(a, length, high_ts).items()}
    base = greedy_family(low, list(range(1 << (a - 1))))
    lift = [u | (bit << (a - 1)) for u in base for bit in (0, 1)]
    lift_ranks = {t: gf2_rank([high[t][u] for u in lift]) for t in high_ts}
    all_ranks = {t: gf2_rank(high[t]) for t in high_ts}
    uniform = greedy_family(high, lift)
    extended = greedy_family(high, list(range(1 << a)), start=uniform)
    return {"a": a, "base": len(base), "base_is_stripe_basis": base == stripe_basis(a - 1), "rho_low": rho(a - 1),
            "lift_ranks": lift_ranks, "all_ranks": all_ranks,
            "uniform": len(uniform), "extended": len(extended), "rho": rho(a)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--full", type=int, default=0, help="rank(t, a) for t <= this (at most 12)")
    parser.add_argument("--packed", type=int, default=0, help="rank(t, a) at this t from the packed table")
    parser.add_argument("--max-a", type=int, default=11)
    parser.add_argument("--window", type=int, default=0, help="windowed ranks for a <= this")
    parser.add_argument("--extra", type=int, default=0, help="window length a + 2 + extra")
    parser.add_argument("--drops", type=int, default=0, help="first windowed drop for a = 3 .. this")
    parser.add_argument("--lift", type=int, default=0, help="lifting test for a = 3 .. this")
    parser.add_argument("--basis", type=int, default=0, help="rank of the stripe basis on windows, a = 2 .. this")
    parser.add_argument("--closure", type=int, default=0, help="closure dimension for a = 1 .. this")
    parser.add_argument("--coefficients", type=int, default=0, help="coefficients of the stripe monomials, t <= this")
    args = parser.parse_args()
    if args.full:
        for t in tqdm(range(2, args.full + 1), desc="t", file=sys.stderr):
            table = cone_table(t)  # (2^(2t+1),)
            ranks = [full_rank(t, a, table) for a in range(1, t)]
            print(f"t={t}: rank(t, a) for a = 1 .. {t - 1}: {ranks}; rho: {[rho(a) for a in range(1, t)]}", flush=True)
    if args.packed:
        t = args.packed
        center = packed_center(t, progress=True)  # (2^(2t+1) / 64,)
        for a in range(1, args.max_a + 1):
            print(f"t={t} a={a}: rank {packed_rank(center, t, a)}, rho {rho(a)}", flush=True)
    if args.window:
        for a in tqdm(range(1, args.window + 1), desc="a", file=sys.stderr):
            ts = list(range(a + 4, a + 13))
            print(f"a={a} length={a + 2 + args.extra} rho={rho(a)}: {window_rank(a, a + 2 + args.extra, ts)}",
                  flush=True)
    if args.drops:
        for a in range(3, args.drops + 1):
            first, period = first_window_drop(a, progress=True)
            print(f"a={a}: first t >= a + 4 with windowed rank < rho = {rho(a)}: {first} (period of Phi mod "
                  f"2^{2 * a + 2}: {period})", flush=True)
    if args.basis:
        for a in tqdm(range(2, args.basis + 1), desc="a", file=sys.stderr):
            ts = list(range(a + 3, a + 13))
            rows = {t: packed_rows(m) for t, m in window_values(a, a + 4, ts).items()}
            basis = stripe_basis(a)
            ranks = {t: subset_rank(rows[t], basis) for t in ts}
            print(f"a={a}: |B_a| = {len(basis)}, rho = {rho(a)}, windowed rank of B_a (length a + 4) for t = "
                  f"{ts[0]} .. {ts[-1]}: {sorted(set(ranks.values()))}", flush=True)
    if args.coefficients:
        for t in tqdm(range(3, args.coefficients + 1), desc="t", file=sys.stderr):
            table = cone_table(t)  # (2^(2t+1),)
            kinds = {a: stripe_coefficients(t, a, table) for a in range(2, t)}
            print(f"t={t}: stripe monomials by a (zero, one, other): "
                  f"{[(a, k['zero'], k['one'], k['other']) for a, k in kinds.items()]}", flush=True)
    if args.closure:
        for a in tqdm(range(1, args.closure + 1), desc="a", file=sys.stderr):
            print(f"a={a}: closure dimension {closure_dimension(a)}, rho {rho(a)}", flush=True)
    if args.lift:
        for a in tqdm(range(3, args.lift + 1), desc="a", file=sys.stderr):
            print(lift_test(a, a + 2 + args.extra), flush=True)


if __name__ == "__main__":
    main()
