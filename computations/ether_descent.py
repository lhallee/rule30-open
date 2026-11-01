"""The certificate behind `Rule30Open.PeriodTwo.EtherCensus16`: the census of `ether_certificate` with descent.

`ether_certificate.run_head` follows the defect of one head on the ether until it lies in a closed strip or repeats a
snapshot. The checker here, `run_descent` (the Lean `runDesc`), also settles a head when, after any step, the defect
is a number n below a bound `below`. The defect at step t is then the defect at step 0 of the half H^t(U), at the
alignment (a + t, o), whose head n is below `below`. The heads are checked in blocks of `block` heads, and the bound of
a block is its first head: once every head below it is bounded at the four phases of the offset, so is every head of
the block. The heads below 2^12 are the heads of `EtherCensus`, bounded there with the bound 61.

- `run_descent(bits, a, o, bound, fuel, head, below)`: the checker of one head, in rounds of four steps as
  `run_head`, with the descent test after each step. It fails when a step puts a defect cell at or above `bound`, or
  after `fuel` rounds.
- `census_descent(p, lo, bound, fuel, block)`: every head h with lo <= h < 2^p at all 28 alignments, in blocks.
- `lean_descent_census(p, lo, bound, fuel, chunk, block)`: the census section of the Lean module.

    python -m computations.ether_descent                      # heads of 16 cells, the census EtherCensus16 certifies
    python -m computations.ether_descent --lean > census.lean # the census section of the module
"""

from __future__ import annotations

import argparse
import sys

from tqdm.auto import tqdm

from computations.ether_certificate import closed_at, closed_bits, step

LOW = 12  # the heads below 2^LOW are those of `EtherCensus`


def run_descent(bits: list[int], a: int, o: int, bound: int, fuel: int, head: int, below: int) -> dict[str, int]:
    """The checker of one head with descent below `below` (the Lean `runDesc`). As `ether_certificate.run_head`, with
    one more way to settle: a step that leaves a defect n < below, at any step. Returns `ok`, `step` (the step of settling), `how` (1 a
    closed strip, 2 a repeat, 3 a descent, 0 a failure), `cell`, `period` or `target` (the smaller head), `top` (the
    highest top seen) and `rounds` (the rounds the checker opens, its cost in the kernel)."""
    n, snap, snap_t, nxt, t = head, head, 0, 4, 0
    best = n.bit_length() - 1
    for r in range(fuel):
        c = closed_at(bits, a, o, bound, n)
        if c >= 0:
            return {"ok": 1, "step": t, "how": 1, "cell": c, "top": best, "rounds": r + 1}
        if snap_t < t and n == snap:
            return {"ok": 1, "step": t, "how": 2, "period": t - snap_t, "top": best, "rounds": r + 1}
        m = n
        for k in range(4):
            m = step(a + k, o, m)
            best = max(best, m.bit_length() - 1)
            if m >> bound:
                return {"ok": 0, "step": t + k + 1, "how": 0, "top": best, "rounds": r + 1}
            if m < below:
                return {"ok": 1, "step": t + k + 1, "how": 3, "target": m, "top": best, "rounds": r + 1}
        if t == nxt:
            snap, snap_t, nxt = n, t, 2 * t
        n, t = m, t + 4
    return {"ok": 0, "step": t, "how": 0, "top": best, "rounds": fuel}


def census_descent(p: int, lo: int, bound: int, fuel: int, block: int,
                   alignments: list[tuple[int, int]] | None = None) -> dict[str, int]:
    """Every head h with lo <= h < 2^p at the given alignments (all 28 by default), with descent below the first head of
    its block (the blocks of `block` heads from `lo` on; `block` 1 is descent below the head itself): counts by way of settling, the
    highest top, the highest cell of a closed strip, the last settling step, the most rounds of one head, the failures,
    and the rounds in all (the cost of the kernel check)."""
    bits = closed_bits()
    if alignments is None:
        alignments = [(a, o) for a in range(4) for o in range(7)]
    out = {"heads": 0, "strip": 0, "repeat": 0, "descent": 0, "failed": 0, "top": -1, "cell": -1, "last": -1,
           "most": 0, "rounds": 0}
    for a, o in tqdm(alignments, desc=f"heads of {p} cells", file=sys.stderr, leave=False):
        for head in range(lo, 1 << p):
            r = run_descent(bits, a, o, bound, fuel, head, lo + (head - lo) // block * block)
            out["heads"] += 1
            out["rounds"] += r["rounds"]
            out["most"] = max(out["most"], r["rounds"])
            out["top"] = max(out["top"], r["top"])
            if not r["ok"]:
                out["failed"] += 1
                continue
            out["last"] = max(out["last"], r["step"])
            out[{1: "strip", 2: "repeat", 3: "descent"}[r["how"]]] += 1
            if r["how"] == 1:
                out["cell"] = max(out["cell"], r["cell"])
    return out


def lean_descent_census(p: int, lo: int, bound: int, fuel: int, chunk: int, block: int) -> str:
    """The census section of the Lean module: one kernel check per chunk of `chunk` heads at each alignment, in blocks
    of `block` heads (`descChunk`), and for each offset the chain of chunks from the heads below `lo` (`headsBelow_12`)
    to the heads below 2^p (`descUpTo`)."""
    assert ((1 << p) - lo) % chunk == 0 and chunk % block == 0 and lo == 1 << 12
    count, blocks = ((1 << p) - lo) // chunk, chunk // block
    out = []
    for o in range(7):
        for k in range(count):
            start = lo + chunk * k
            for a in range(4):
                out.append(f"theorem desc_{a}_{o}_{k} : descChunk {a} {o} {bound} {fuel} {start} {block} {blocks} = true "
                           f":= by\n  decide +kernel")
            prev = f"headsBelow_12 {o} {bound} (by decide) (by decide)" if k == 0 else f"descUpTo_{o}_{k - 1}"
            out.append(f"theorem descUpTo_{o}_{k} : HeadsBelow {o} {bound} {start + chunk} :=\n"
                       f"  headsBelow_chunk (by decide) rfl (by decide) ({prev})\n"
                       f"    (descChunk_phases desc_0_{o}_{k} desc_1_{o}_{k} desc_2_{o}_{k} desc_3_{o}_{k})")
    cases = "\n".join(f"  | {o}, _ => descUpTo_{o}_{count - 1}" for o in range(7))
    out.append(f"/-- **The census with descent**: at each offset and every phase, every head below `2 ^ {p}` is bounded "
               f"with the\nbound {bound}. -/\n"
               f"theorem descCensus (o : Nat) (ho : o < 7) : HeadsBelow o {bound} (2 ^ {p}) :=\n"
               f"  match o, ho with\n{cases}\n"
               f"  | o + 7, ho => absurd ho (by omega)")
    return "\n\n".join(out)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--bits", type=int, default=16)
    parser.add_argument("--low", type=int, default=1 << LOW)
    parser.add_argument("--bound", type=int, default=79)
    parser.add_argument("--fuel", type=int, default=110)
    parser.add_argument("--chunk", type=int, default=4096)
    parser.add_argument("--block", type=int, default=256)
    parser.add_argument("--lean", action="store_true", help="print the census section of the Lean module")
    args = parser.parse_args()
    if args.lean:
        print(lean_descent_census(args.bits, args.low, args.bound, args.fuel, args.chunk, args.block))
        return
    r = census_descent(args.bits, args.low, args.bound, args.fuel, args.block)
    print(f"heads h with {args.low} <= h < 2^{args.bits} at the 28 alignments, blocks of {args.block}: {r['heads']}; settled by a closed strip "
          f"{r['strip']}, by a repeat {r['repeat']}, by descent {r['descent']}, failed {r['failed']}; highest top "
          f"{r['top']}, highest strip cell {r['cell']}, last settling step {r['last']}; most rounds of one head "
          f"{r['most']}; {r['rounds']} rounds")


if __name__ == "__main__":
    main()
