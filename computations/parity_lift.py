"""Parity models for the center cell: Walsh coefficients, Fourier sparsity and the GF(2) rank of the XOR lift.

c_t is a Boolean function of the 2t + 1 cells x_{-t} .. x_t of row 0 (Rule 30: new x_j = x_{j-1} xor (x_j or
x_{j+1})). Truth tables are indexed as in `cone_screening`: bit i of the index is x_{-t+i}. The restricted center f_t
is c_t with x_{-t} = x_{-t+1} = 0, a function of the 2t - 1 cells x_{-t+2} .. x_t (bit i of its index is x_{-t+2+i}).

* `rule_table` runs any elementary rule (Wolfram number) on bit-sliced rows: Rule 30 and the controls 45, 90, 120,
  150.
* `walsh` is the fast Walsh-Hadamard transform: W[a] = sum over x of (-1)^(f(x) xor a.x).
* `sparsity` counts the nonzero W[a]: the Fourier sparsity of f, which is the real rank of the +-1 matrix
  (-1)^f(x xor y).
* `gf2_rank` is Gaussian elimination over GF(2) on packed 64-bit words; `xor_lift_rank` applies it to the XOR lift
  M[x, y] = f(x xor y).
* `table_row` collects, for one rule and one t: the weight parity of f_t, the least |W| and the residues mod 4 of the
  Walsh coefficients of f_t, the sparsity of c_t, and the GF(2) ranks of the XOR lifts of f_t and of c_t.

    python -m computations.parity_lift --max-t 10 --rank-t 6      # the tables of ParityLift.md
"""

from __future__ import annotations

import argparse
import sys

import numpy as np

from tqdm.auto import tqdm

from computations.cone_screening import cone_table, variable_slices

RULES = (30, 45, 90, 120, 150)


def rule_table(t: int, rule: int) -> np.ndarray:
    """The center after t steps of the elementary rule `rule` for all 2^(2t+1) cone rows; bit i of the index is
    x_{-t+i}."""
    if rule == 30:
        return cone_table(t)  # (2^(2t+1),)
    row = variable_slices(2 * t + 1)  # (2t + 1) x (2^(2t+1),)
    for _ in range(t):
        new = []
        for i in range(1, len(row) - 1):
            a, b, c = row[i - 1], row[i], row[i + 1]  # (2^(2t+1),) each
            out = np.zeros_like(a)  # (2^(2t+1),)
            for k in range(8):
                if (rule >> k) & 1:
                    out |= (a == bool(k & 4)) & (b == bool(k & 2)) & (c == bool(k & 1))
            new.append(out)
        row = new  # (len - 2) x (2^(2t+1),)
    return row[0].astype(np.uint8)  # (2^(2t+1),)


def restrict(table: np.ndarray) -> np.ndarray:
    """f with its two lowest variables (x_{-t}, x_{-t+1}) set to 0."""
    # table: (2^n,)
    return table[0::4].copy()  # (2^(n-2),)


def walsh(table: np.ndarray) -> np.ndarray:
    """W[a] = sum over x of (-1)^(f(x) xor popcount(a & x)), by the fast Walsh-Hadamard transform."""
    # table: (2^n,)
    w = 1 - 2 * table.astype(np.int64)  # (2^n,)
    size = w.shape[0]
    h = 1
    while h < size:
        w = w.reshape(-1, 2, h)  # (2^n / 2h, 2, h)
        w = np.stack([w[:, 0] + w[:, 1], w[:, 0] - w[:, 1]], axis=1)  # (2^n / 2h, 2, h)
        h *= 2
    return w.reshape(size)  # (2^n,)


def sparsity(table: np.ndarray) -> int:
    """The number of nonzero Walsh coefficients of f."""
    return int(np.count_nonzero(walsh(table)))


def xor_lift(table: np.ndarray) -> np.ndarray:
    """The XOR lift M[x, y] = f(x xor y) as a 0/1 matrix."""
    # table: (2^n,)
    index = np.arange(table.shape[0])  # (2^n,)
    return table[index[:, None] ^ index[None, :]].astype(np.uint8)  # (2^n, 2^n)


def gf2_rank(matrix: np.ndarray, progress: bool = False) -> int:
    """The rank over GF(2) of a 0/1 matrix, by elimination on rows packed into 64-bit words."""
    # matrix: (rows, cols)
    rows, cols = matrix.shape
    pad = (-cols) % 64
    padded = np.concatenate([matrix.astype(np.uint8), np.zeros((rows, pad), dtype=np.uint8)], axis=1)
    packed = np.packbits(padded, axis=1, bitorder="little").view(np.uint64).copy()  # (rows, ceil(cols / 64))
    rank = 0
    for col in tqdm(range(cols), disable=not progress, desc="elimination", leave=False):
        word, bit = divmod(col, 64)
        mask = np.uint64(1) << np.uint64(bit)
        hits = np.nonzero(packed[rank:, word] & mask)[0]  # (k,)
        if hits.size == 0:
            continue
        pivot = rank + int(hits[0])
        if pivot != rank:
            packed[[rank, pivot]] = packed[[pivot, rank]]
        others = np.nonzero(packed[:, word] & mask)[0]  # (k',)
        others = others[others != rank]
        packed[others] ^= packed[rank]
        rank += 1
        if rank == rows:
            break
    return rank


def xor_lift_rank(table: np.ndarray, progress: bool = False) -> int:
    """The GF(2) rank of the XOR lift of f."""
    return gf2_rank(xor_lift(table), progress)


def table_row(t: int, rule: int, rank: bool, progress: bool = False) -> dict[str, int | None]:
    """The parity-model quantities of the rule's center after t steps (t >= 2)."""
    full = rule_table(t, rule)  # (2^(2t+1),)
    restricted = restrict(full)  # (2^(2t-1),)
    w = walsh(restricted)  # (2^(2t-1),)
    return {
        "t": t,
        "rule": rule,
        "weight_parity": int(restricted.sum()) % 2,
        "min_abs_walsh": int(np.abs(w).min()),
        "walsh_mod4": int(np.bitwise_or.reduce(1 << (w % 4))),  # bit r set when some W[a] is r mod 4
        "sparsity": sparsity(full),
        "rank_restricted": xor_lift_rank(restricted, progress) if rank else None,
        "rank_full": xor_lift_rank(full, progress) if rank else None,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--max-t", type=int, default=10, help="largest t for parities and sparsities")
    parser.add_argument("--rank-t", type=int, default=6, help="largest t for the GF(2) ranks")
    args = parser.parse_args()
    for t in tqdm(range(2, args.max_t + 1), desc="t"):
        for rule in RULES:
            row = table_row(t, rule, rank=t <= args.rank_t, progress=t >= 6)
            residues = [r for r in range(4) if (row["walsh_mod4"] >> r) & 1]
            tqdm.write(
                f"t={t:2d} rule={rule:3d} parity={row['weight_parity']} min|W|={row['min_abs_walsh']:4d} "
                f"W mod 4 in {residues} sparsity={row['sparsity']:9d} (2^(2t-1)={1 << (2 * t - 1)}) "
                f"rank f_t={row['rank_restricted']} rank c_t={row['rank_full']}"
            )
            sys.stdout.flush()


if __name__ == "__main__":
    main()
