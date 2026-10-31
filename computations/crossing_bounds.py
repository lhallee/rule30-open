"""Crossing-sequence bounds for one-tape machines that read the binary digits of n and answer c(n).

Cut the ell digits of n (least significant first, top digit 1) after the `cut` lowest ones. Machines in the kit's model
(`Rule30Problem3`) start on cell 0, so a run crosses the cut first to the right, and the crossing sequence is the list
of states just after each crossing. Two inputs with the same crossing sequence at a cut can have their halves
exchanged, so the inputs with one sequence form a rectangle A x B of low parts and high parts on which the answer
depends on one side only: the matrix S[a, b] = (-1)^c(n) restricted to the rectangle is u 1^T or 1 v^T with u, v signs.
For such a rectangle |A| |B| = u^T S 1 <= ||S|| sqrt(|A| |B|), hence |A| |B| <= ||S||^2 with ||S|| the operator norm.
With `states` states there are at most 1 + states + ... + states^L sequences of length at most L, so the share of inputs
with at most L crossings at the cut is at most (that count) * ||S||^2 / 2^(ell - 1), and the mean number of crossings at
the cut is at least the sum over L of the positive part of one minus this share. A step crosses one cut, so the sum over
cuts bounds the mean running time.

    python -m computations.crossing_bounds --max-ell 20          # norms and bounds for the center column and controls
"""

from __future__ import annotations

import argparse
import sys

import numpy as np

from tqdm.auto import tqdm

from computations.rule30 import center_column


def split_matrix(cells: np.ndarray, ell: int, cut: int) -> np.ndarray:
    """The signs (-1)^cells[n] for the n with `ell` binary digits, rows the `cut` lowest digits a, columns the other
    ell - 1 - cut digits below the top 1: n = a + 2^(ell-1) + 2^cut b."""
    # cells: (>= 2^ell,)
    assert 1 <= cut <= ell - 1 and len(cells) >= 1 << ell
    rows = np.arange(1 << cut, dtype=np.int64)[:, None]  # (2^cut, 1)
    cols = np.arange(1 << (ell - 1 - cut), dtype=np.int64)[None, :]  # (1, 2^(ell-1-cut))
    index = rows + (1 << (ell - 1)) + (cols << cut)  # (2^cut, 2^(ell-1-cut))
    return 1 - 2 * cells[index].astype(np.int8)  # (2^cut, 2^(ell-1-cut))


def operator_norm_squared(matrix: np.ndarray) -> float:
    """The largest eigenvalue of the Gram matrix on the smaller side, which is the squared operator norm."""
    # matrix: (r, c)
    wide = matrix.astype(np.float64)  # (r, c)
    gram = wide @ wide.T if wide.shape[0] <= wide.shape[1] else wide.T @ wide  # (min, min)
    return float(np.linalg.eigvalsh(gram)[-1])


def mean_crossings_bound(norm_squared: float, ell: int, states: int) -> float:
    """A lower bound on the mean number of crossings of one cut, over the 2^(ell-1) inputs of `ell` digits, for every
    machine with `states` states that answers by the matrix of norm^2 `norm_squared`."""
    assert states >= 1
    share_scale = norm_squared / 2.0 ** (ell - 1)
    count, power, bound = 0.0, 1.0, 0.0
    for _ in range(4 * ell + 8):  # sequences of length 0, 1, ...
        count += power
        share = count * share_scale  # at most this share of the inputs has this few crossings or fewer
        if share >= 1.0:
            break
        bound += 1.0 - share
        power *= states
    return bound


def cut_norms(cells: np.ndarray, ell: int, progress: bool = False) -> np.ndarray:
    """The squared operator norms of the split matrices of every cut 1 .. ell - 1."""
    # cells: (>= 2^ell,)
    norms = np.zeros(ell - 1)  # (ell - 1,)
    for cut in tqdm(range(1, ell), desc=f"norms, ell = {ell}", file=sys.stderr, disable=not progress):
        norms[cut - 1] = operator_norm_squared(split_matrix(cells, ell, cut))
    return norms  # (ell - 1,)


def mean_time_bound(norms: np.ndarray, ell: int, states: int) -> float:
    """The sum over cuts of `mean_crossings_bound`: a lower bound on the mean running time over the inputs of `ell`
    digits of every one-tape machine with `states` states that answers by the matrices behind `norms`."""
    # norms: (ell - 1,)
    return float(sum(mean_crossings_bound(value, ell, states) for value in norms))


def norm_ratios(norms: np.ndarray, ell: int) -> np.ndarray:
    """||S||^2 over (sqrt(rows) + sqrt(columns))^2 for every cut: about 1 for random signs, and the share of 2^(ell-1)
    divided by rank for a matrix of low rank."""
    # norms: (ell - 1,)
    cuts = np.arange(1, ell)  # (ell - 1,)
    return norms / (np.sqrt(2.0**cuts) + np.sqrt(2.0 ** (ell - 1 - cuts))) ** 2  # (ell - 1,)


def thue_morse(count: int) -> np.ndarray:
    """The Thue-Morse sequence, a 2-automatic control whose split matrices have rank 1."""
    index = np.arange(count, dtype=np.int64)  # (count,)
    parity = np.zeros(count, dtype=np.uint8)  # (count,)
    while index.any():
        parity ^= (index & 1).astype(np.uint8)
        index >>= 1
    return parity  # (count,)


def random_cells(count: int, seed: int) -> np.ndarray:
    """Independent fair bits, the control for a function with no structure."""
    return np.random.default_rng(seed).integers(0, 2, count).astype(np.uint8)  # (count,)


Machine = tuple[int, int, dict[tuple[int, int], tuple]]  # (last state, extra symbols, transition table)


def random_machine(rng: np.random.Generator, last_state: int, extra_symbols: int, halt_share: float = 0.25) -> Machine:
    """A random machine in the kit's model: states 0 .. last_state, symbols 0 (blank), 1 and 2 (the digits 0 and 1) and
    `extra_symbols` more. An entry is ("halt", answer) or ("go", state, symbol, move) with move -1, 0 or 1."""
    table: dict[tuple[int, int], tuple] = {}
    for state in range(last_state + 1):
        for symbol in range(extra_symbols + 3):
            if rng.random() < halt_share:
                table[state, symbol] = ("halt", int(rng.integers(0, 2)))
            else:
                table[state, symbol] = ("go", int(rng.integers(0, last_state + 1)), int(rng.integers(0, extra_symbols + 3)),
                                        int(rng.integers(-1, 2)))
    return last_state, extra_symbols, table


def run_machine(machine: Machine, value: int, ell: int, max_steps: int) -> tuple[int, int, list[list[int]]] | None:
    """Run on the digits of `value` (`ell` of them, least significant first, on cells 0 .. ell - 1, blanks elsewhere).
    Returns the answer, the number of steps and, for every cut 1 .. ell - 1, the states just after each crossing; None
    if the machine has not halted within `max_steps`."""
    _, _, table = machine
    tape = {i: 2 if (value >> i) & 1 else 1 for i in range(ell)}
    state, head, steps = 0, 0, 0
    sequences: list[list[int]] = [[] for _ in range(ell - 1)]  # cut c is the boundary between cells c - 1 and c
    while steps < max_steps:
        entry = table[state, tape.get(head, 0)]
        if entry[0] == "halt":
            return entry[1], steps + 1, sequences
        _, state, symbol, move = entry
        tape[head] = symbol
        steps += 1
        if move == 1 and 1 <= head + 1 <= ell - 1:
            sequences[head].append(state)  # cut head + 1
        elif move == -1 and 1 <= head <= ell - 1:
            sequences[head - 1].append(state)  # cut head
        head += move
    return None


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--min-ell", type=int, default=12)
    parser.add_argument("--max-ell", type=int, default=20)
    parser.add_argument("--states", type=int, nargs="+", default=[2, 3, 4, 8])
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    top = 1 << args.max_ell
    ensembles = {"center column": center_column(top), "random bits": random_cells(top, args.seed),
                 "Thue-Morse": thue_morse(top)}  # each (2^max_ell,)
    header = "ell  ensemble        max ratio  min ratio  " + "  ".join(f"bound q={q}" for q in args.states)
    print(header)
    for ell in range(args.min_ell, args.max_ell + 1):
        for name, cells in ensembles.items():
            norms = cut_norms(cells, ell, progress=ell >= 20)  # (ell - 1,)
            ratios = norm_ratios(norms, ell)  # (ell - 1,)
            bounds = "  ".join(f"{mean_time_bound(norms, ell, q):9.2f}" for q in args.states)
            print(f"{ell:3d}  {name:15s}  {ratios.max():9.3f}  {ratios.min():9.3f}  {bounds}")


if __name__ == "__main__":
    main()
