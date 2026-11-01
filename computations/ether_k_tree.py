"""The certificate behind `Rule30Open.PeriodTwo.EtherKTree`: every point of K whose tail from cell 28 on is the ether has a
defect that never reaches cell 28, and the same census for heads of up to 36 cells.

Write H(U) = (U >> 1) xor (U or (U << 1)) for the held map and K for the 2-adic U with H^t(U) odd at every odd t. The
ether is the cycle of four states of the held map on a ring of seven cells; at the alignment (a, o) its cell j is cell
(j + o) mod 7 of state a mod 4 (`ether_certificate.eth`). For a half U whose cells from `head` on are the ether, the
defect D_t = H^t(U) xor (the ether at phase a + t) follows a rule of its own (`ether_certificate.step`), and a defect
that stays below a fixed cell gives an eventually periodic orbit (`EtherCensus`).

The heads of a point of K form the tree of `no_k_tails16`: both values at an even cell, the one value at an odd cell d
that keeps bit 0 of H^d odd. `leaf_ok` is the test the Lean module runs at each leaf N (the number that holds the head
in the cells 0 .. head - 1 and the ether in the cells head .. 63): `breakRun` of `no_k_tails` finds an odd step below
64 at which bit 0 is 0, so no point of K has this head, or `ether_certificate.run_head` settles the defect of the head
(a closed strip of 13 cells or a repeat) with every cell below `bound`.

- `ether_tail(head, a, o)`: the ether in the cells head .. 63 at the alignment (a, o), 0 below (the Lean `etherTail`).
- `tree_leaves(head, a, o)`: the leaves of the tree of K under that tail, and the steps of H the walk spends at the odd
  cells (`colRaw`).
- `leaf_ok(leaf, head, a, o, rounds, bound, fuel)`: the test at a leaf, with how it passed.
- `census(head, rounds, bound, fuel)`: the test at every leaf of every alignment.
- `lean_section(head, rounds, bound, fuel)`: the census section of the Lean module.

    python -m computations.ether_k_tree --head 28 --bound 28     # heads of 28 cells, the census EtherKTree certifies
    python -m computations.ether_k_tree --head 36                # heads of 12 to 36 cells, about 5 minutes
    python -m computations.ether_k_tree --lean                   # the census section of the module
"""

from __future__ import annotations

import argparse
import sys

from tqdm.auto import tqdm

from computations.ether_certificate import background, closed_bits, run_head
from computations.no_k_tails16 import break_run, column_after

HEAD = 28  # the cells of a head in the Lean module
ROUNDS = 32  # rounds of `breakRun` at a leaf: the odd steps 1, 3, ..., 63
BOUND = 28  # the bound on the cells of the defect in `run_head` for heads of 28 cells: the head itself
FUEL = 16  # rounds of `run_head` at a leaf


def ether_tail(head: int, a: int, o: int) -> int:
    """The ether at the alignment (a, o) in the cells head .. 63, bit j the cell j, and 0 below (the Lean
    `etherTail`)."""
    return background(a, o, 64) & ~((1 << head) - 1)


def tree_leaves(head: int, a: int, o: int) -> tuple[list[int], int]:
    """The leaves of the tree of K over the cells 0 .. head - 1 under the ether at (a, o), as the numbers that hold the
    head and the tail, in the order the Lean `treeWith` visits them, and the steps of H spent at the odd cells."""
    leaves: list[int] = []
    steps = 0
    stack = [(0, ether_tail(head, a, o))]  # (the next cell d, the number with the cells below d chosen)
    while stack:
        d, n = stack.pop()
        if d == head:
            leaves.append(n)
        elif d % 2 == 0:
            stack.append((d + 1, n | (1 << d)))
            stack.append((d + 1, n))
        else:
            steps += d
            stack.append((d + 1, n if column_after(d, n) else n | (1 << d)))
    return leaves, steps


def leaf_ok(leaf: int, head: int, a: int, o: int, bits: list[int], rounds: int = ROUNDS, bound: int = BOUND,
            fuel: int = FUEL) -> dict[str, int]:
    """The Lean leaf test: `breakRun rounds leaf`, else `runHead` on the defect of the head, (leaf xor the ether) mod
    2^head. Returns `ok`, `how` (0 a break of K, 1 a closed strip, 2 a repeat, -1 a failure), `step` (of the break or
    of settling), `top` (the highest defect cell seen by `run_head`, -1 on a break) and `steps` (the steps of H taken)."""
    step, used = break_run(leaf, rounds)
    if step > 0:
        return {"ok": 1, "how": 0, "step": step, "top": -1, "steps": used}
    n = (leaf ^ background(a, o, 64)) & ((1 << head) - 1)  # the defect of the head at step 0
    r = run_head(bits, a, o, bound, fuel, n)
    return {"ok": r["ok"], "how": r["how"] if r["ok"] else -1, "step": r["step"], "top": r["top"],
            "steps": used + r["step"] + 4}


def census(head: int, rounds: int = ROUNDS, bound: int = BOUND, fuel: int = FUEL) -> dict[str, int]:
    """The leaf test at every leaf of the tree at all 28 alignments: the leaves, the breaks of K and the latest one, the
    leaves settled by a closed strip and by a repeat, the failures, the highest defect cell of a settled leaf, the
    latest settling step, and the steps of H of the walk and of the leaves (the cost of the kernel checks)."""
    bits = closed_bits()
    out = {"leaves": 0, "break": 0, "last_break": 0, "strip": 0, "repeat": 0, "failed": 0, "top": -1, "last_settle": 0,
           "tree_steps": 0, "leaf_steps": 0}
    alignments = [(a, o) for a in range(4) for o in range(7)]
    for a, o in tqdm(alignments, desc=f"heads of {head} cells", file=sys.stderr, leave=False):
        leaves, steps = tree_leaves(head, a, o)
        out["tree_steps"] += steps
        for leaf in leaves:
            r = leaf_ok(leaf, head, a, o, bits, rounds, bound, fuel)
            out["leaves"] += 1
            out["leaf_steps"] += r["steps"]
            if not r["ok"]:
                out["failed"] += 1
            elif r["how"] == 0:
                out["break"] += 1
                out["last_break"] = max(out["last_break"], r["step"])
            else:
                out["strip" if r["how"] == 1 else "repeat"] += 1
                out["top"] = max(out["top"], r["top"])
                out["last_settle"] = max(out["last_settle"], r["step"])
    return out


def lean_section(head: int = HEAD, rounds: int = ROUNDS, bound: int = BOUND, fuel: int = FUEL) -> str:
    """The census section of the Lean module: one kernel check per alignment, and their collection."""
    out = []
    for a in range(4):
        for o in range(7):
            out.append(f"theorem ktree_{a}_{o} : etherTreeOK {rounds} {head} {bound} {fuel} {a} {o} = true := by\n"
                       f"  decide +kernel")
    cases = "\n".join(f"  | {a}, {o}, _, _ => ktree_{a}_{o}" for a in range(4) for o in range(7))
    out.append(f"theorem ktree (a o : Nat) (ha : a < 4) (ho : o < 7) : etherTreeOK {rounds} {head} {bound} {fuel} a o = "
               f"true :=\n  match a, o, ha, ho with\n{cases}\n  | a + 4, _, ha, _ => absurd ha (by omega)\n"
               f"  | _, o + 7, _, ho => absurd ho (by omega)")
    return "\n\n".join(out)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--head", type=int, default=HEAD, help="the largest head; every multiple of 4 from 12 on")
    parser.add_argument("--rounds", type=int, default=ROUNDS)
    parser.add_argument("--bound", type=int, default=0,
                        help="the bound of run_head; 0 for BOUND with --lean and the head plus 7 in the census")
    parser.add_argument("--fuel", type=int, default=FUEL)
    parser.add_argument("--lean", action="store_true", help="print the census section of the Lean module")
    args = parser.parse_args()
    if args.lean:
        print(lean_section(args.head, args.rounds, args.bound or BOUND, args.fuel))
        return
    for head in range(12, args.head + 1, 4):
        r = census(head, args.rounds, args.bound or head + 7, args.fuel)
        print(f"heads of {head} cells: {r['leaves']} leaves, {r['break']} break K (latest at step {r['last_break']}), "
              f"{r['strip']} settle by a closed strip and {r['repeat']} by a repeat (latest at step "
              f"{r['last_settle']}, highest defect cell {r['top']}), {r['failed']} fail; "
              f"{r['tree_steps']} + {r['leaf_steps']} steps of H")


if __name__ == "__main__":
    main()
