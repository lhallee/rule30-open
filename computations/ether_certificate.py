"""The certificate behind `Rule30Open.PeriodTwo.EtherCensus`: closed strips and a census of heads on the ether.

This is the census of `defect_potential` rewritten as the checker that the Lean module runs in the kernel, step for
step, so that the counts here are the counts the kernel certifies. Write H(U) = (U >> 1) xor (U or (U << 1)) for the
held map, `eth(a, j)` for bit j mod 7 of ether state a mod 4 (`ETHER`, the cycle of the ring map on seven cells), and
take the background at alignment (a, o) to be B_t(j) = eth(a + t, j + o). The defect D_t = H^t(U) xor B_t is held as
a number, bit j the cell j.

- `step(a, o, n)`: one step of the defect at phase a, through the background of `WIDTH` = 128 cells, kept to 127 cells.
  It is exact while the top of the defect is at most 125 (the Lean lemma `enc_step`).
- `closed_bits()`: the 1,915 closed strips of 13 cells as 28 numbers of 2^13 bits, one per (phase, (c + o) mod 7),
  bit s the strip s (bit i of s the cell c - 12 + i). They are `defect_potential.closed_strips(13)`.
- `closure_ok()`: the closure check of the Lean module (`closedOK`): for each closed strip and each value of the cell
  below, the strip one step later is closed at the next phase and cell c + 1 stays clear.
- `run_head(a, o, bound, fuel, head)`: the checker of one head, as `runHead` in Lean, in rounds of four steps. At
  each step t that is a multiple of 4 it settles the head when the defect lies in a closed strip at a cell c with
  12 <= c < bound (one of the three least cells c >= max(top, 12) with (c + o) mod 7 = 5, the one residue that has
  closed strips), or when the defect equals the snapshot taken at step 4 2^k; it fails when a step puts a defect cell
  at or above `bound`, or after `fuel` rounds.
- `census(p, bound, fuel)`: every head of p cells at all 28 alignments.

    python -m computations.ether_certificate                        # the census the Lean module certifies, 12 cells
    python -m computations.ether_certificate --lean > census.lean   # its tables and census section, as in the module
"""

from __future__ import annotations

import argparse
import functools
import sys

from tqdm.auto import tqdm

from computations.defect_potential import ETHER, STRIP, closed_strips

WIDTH = 128  # cells of background in a step
MASK = (1 << (WIDTH - 1)) - 1  # a step keeps the cells 0 .. 126
RESIDUE = 5  # the residue of c + o modulo 7 at which every closed strip of 13 cells lies


def eth(a: int, j: int) -> bool:
    """Cell j of ether state a, both taken modulo the cycle (the Lean `eth`)."""
    return bool((ETHER[a % 4] >> (j % 7)) & 1)


def background(a: int, o: int, cells: int = WIDTH) -> int:
    """The background cells 0 .. cells - 1 at phase a and offset o, bit j the cell j (the Lean `bgL`)."""
    return _background(a % 4, o % 7, cells)


@functools.lru_cache(maxsize=None)
def _background(a: int, o: int, cells: int) -> int:
    """`background` for a phase below 4 and an offset below 7, computed once."""
    return sum(int(eth(a, j + o)) << j for j in range(cells))


def held(x: int) -> int:
    """The held map on a number (the Lean `heldNat`)."""
    return (x >> 1) ^ (x | (x << 1))


BACKGROUNDS = [[_background(a, o, WIDTH) for o in range(7)] for a in range(4)]  # `background` by phase and offset


def step(a: int, o: int, n: int) -> int:
    """One step of the defect n at phase a and offset o (the Lean `dstep`): `held` of n xor `background(a, o)`, xor
    `background(a + 1, o)`, read from `BACKGROUNDS` and written out, since the checkers call it millions of times."""
    x = n ^ BACKGROUNDS[a % 4][o % 7]
    return (((x >> 1) ^ (x | (x << 1))) ^ BACKGROUNDS[(a + 1) % 4][o % 7]) & MASK


def closed_bits() -> list[int]:
    """The closed strips of 13 cells as 28 numbers, entry 7 a + r the strips at phase a and (c + o) mod 7 = r."""
    member = closed_strips(STRIP)  # (4, 7, 2^13)
    out = []
    for a in range(4):
        for r in range(7):
            out.append(sum(1 << int(s) for s in member[a, r].nonzero()[0]))
    return out


def strip_step(a: int, r: int, s: int, below: int) -> tuple[int, int]:
    """The strip s at phase a and residue r one step later, with the cell `below` under it, and the new cell c + 1
    (the Lean `stripStep` and `stripRise`). Bit i of s is the cell c - 12 + i, whose background is eth(a, r + 2 + i)."""
    d = lambda i: below if i == -1 else ((s >> i) & 1 if 0 <= i < STRIP else 0)
    b = lambda i: int(eth(a, r + 2 + i))
    cell = lambda i: d(i + 1) ^ (((d(i) ^ b(i)) | (d(i - 1) ^ b(i - 1))) ^ (b(i) | b(i - 1)))
    return sum(cell(i) << i for i in range(STRIP)), cell(STRIP)


def closure_ok(bits: list[int]) -> bool:
    """Every closed strip steps to a closed strip at the next phase for both values below, and never rises."""
    for a in range(4):
        for r in range(7):
            for s in range(1 << STRIP):
                if not (bits[7 * a + r] >> s) & 1:
                    continue
                for below in (0, 1):
                    new, rise = strip_step(a, r, s, below)
                    if rise or not (bits[7 * ((a + 1) % 4) + r] >> new) & 1:
                        return False
    return True


def closed_at(bits: list[int], a: int, o: int, bound: int, n: int) -> int:
    """The cell c of a closed strip that holds the defect n, among the three candidates, or -1 (the Lean `closedAt`)."""
    base = max(n.bit_length() - 1, STRIP - 1)
    c = base + (12 - (base + o) % 7) % 7  # the least c >= base with (c + o) mod 7 = RESIDUE
    for cc in (c, c + 7, c + 14):
        if STRIP - 1 <= cc < bound and n >> (cc + 1) == 0 and \
                (bits[7 * (a % 4) + (cc + o) % 7] >> ((n >> (cc - STRIP + 1)) & ((1 << STRIP) - 1))) & 1:
            return cc
    return -1


def run_head(bits: list[int], a: int, o: int, bound: int, fuel: int, head: int) -> dict[str, int]:
    """The checker of one head (the Lean `runHead`), in rounds of four steps, so that every check falls at a step t
    that is a multiple of 4, where the phase is a again. A round settles the head when the defect lies in a closed strip
    (`closed_at`) or equals the snapshot; otherwise it takes four steps, fails if one of them puts a defect cell at or
    above `bound`, and takes a snapshot when t is 4, 8, 16, 32, ... Returns `ok` (1 when settled within `fuel` rounds),
    `step` (the step t of settling), `how` (1 a closed strip, 2 a repeat, 0 a failure), `cell` or `period`, and `top`,
    the highest top seen."""
    n, snap, snap_t, nxt, t = head, head, 0, 4, 0
    best = n.bit_length() - 1
    for _ in range(fuel):
        c = closed_at(bits, a, o, bound, n)
        if c >= 0:
            return {"ok": 1, "step": t, "how": 1, "cell": c, "top": best}
        if snap_t < t and n == snap:
            return {"ok": 1, "step": t, "how": 2, "period": t - snap_t, "top": best}
        m = n
        for k in range(4):
            m = step(a + k, o, m)
            best = max(best, m.bit_length() - 1)
            if m >> bound:
                return {"ok": 0, "step": t + k + 1, "how": 0, "top": best}
        if t == nxt:
            snap, snap_t, nxt = n, t, 2 * t
        n, t = m, t + 4
    return {"ok": 0, "step": t, "how": 0, "top": best}


def census(p: int, bound: int, fuel: int, alignments: list[tuple[int, int]] | None = None) -> dict[str, int]:
    """Every head of p cells at the given alignments (all 28 by default): counts by way of settling, the highest top,
    the highest cell of a closed strip, the last settling step, the number of failures, and the rounds the checker
    runs (the cost of the kernel check)."""
    bits = closed_bits()
    if alignments is None:
        alignments = [(a, o) for a in range(4) for o in range(7)]
    out = {"heads": 0, "strip": 0, "repeat": 0, "failed": 0, "top": -1, "cell": -1, "last": -1, "repeat_top": -1,
           "rounds": 0}
    for a, o in tqdm(alignments, desc=f"heads of {p} cells", file=sys.stderr, leave=False):
        for head in range(1 << p):
            r = run_head(bits, a, o, bound, fuel, head)
            out["heads"] += 1
            out["rounds"] += r["step"] // 4 + 1
            out["top"] = max(out["top"], r["top"])
            if not r["ok"]:
                out["failed"] += 1
                continue
            out["last"] = max(out["last"], r["step"])
            if r["how"] == 1:
                out["strip"] += 1
                out["cell"] = max(out["cell"], r["cell"])
            else:
                out["repeat"] += 1
                out["repeat_top"] = max(out["repeat_top"], r["top"])
    return out


def lean_tables() -> str:
    """The Lean tables `bgTab` (the background of 128 cells at the 28 alignments, entry 7 a + o) and `closedTab` (the
    closed strips at the four phases, residue 5)."""
    bits = closed_bits()
    bg = ", ".join(str(background(a, o)) for a in range(4) for o in range(7))
    closed = ",\n  ".join(str(bits[7 * a + RESIDUE]) for a in range(4))
    return f"def bgTab : List Nat := [{bg}]\n\ndef closedTab : List Nat := [\n  {closed}]"


def lean_census(p: int, bound: int, fuel: int, chunk: int) -> str:
    """The census section of the Lean module: one kernel check per chunk of `chunk` heads at each alignment, the
    heads of each alignment joined with `headsOK_append`, and `census` over the 28 alignments."""
    assert (1 << p) % chunk == 0
    count = (1 << p) // chunk
    out = []
    for a in range(4):
        for o in range(7):
            for k in range(count):
                out.append(f"theorem census_{a}_{o}_{k} : chunkOK {a} {o} {bound} {fuel} {chunk * k} {chunk} = true := by\n"
                           f"  decide +kernel")
    for a in range(4):
        for o in range(7):
            term = f"headsOK_of_chunk census_{a}_{o}_0"
            for k in range(1, count):
                term = f"headsOK_append ({term}) (headsOK_of_chunk census_{a}_{o}_{k})"
            out.append(f"theorem census_{a}_{o} : HeadsOK {a} {o} {bound} {fuel} 0 (2 ^ {p}) :=\n  {term}")
    cases = "\n".join(f"  | {a}, {o}, _, _ => census_{a}_{o}" for a in range(4) for o in range(7))
    out.append(f"/-- **The census**: every head of {p} cells at each of the 28 alignments passes the checker with the "
               f"bound {bound}\nand {fuel} rounds. -/\n"
               f"theorem census (a o : Nat) (ha : a < 4) (ho : o < 7) : HeadsOK a o {bound} {fuel} 0 (2 ^ {p}) :=\n"
               f"  match a, o, ha, ho with\n{cases}\n"
               f"  | a + 4, _, ha, _ => absurd ha (by omega)\n"
               f"  | _, o + 7, _, ho => absurd ho (by omega)")
    return "\n\n".join(out)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--bits", type=int, default=12)
    parser.add_argument("--bound", type=int, default=61)
    parser.add_argument("--fuel", type=int, default=80)
    parser.add_argument("--chunk", type=int, default=1024)
    parser.add_argument("--lean", action="store_true", help="print the tables and the census section of the Lean module")
    args = parser.parse_args()
    if args.lean:
        print(lean_tables() + "\n\n" + lean_census(args.bits, args.bound, args.fuel, args.chunk))
        return
    bits = closed_bits()
    print(f"closed strips: {sum(bin(b).count('1') for b in bits)}, closure {closure_ok(bits)}")
    r = census(args.bits, args.bound, args.fuel)
    print(f"heads of {args.bits} cells at the 28 alignments: {r['heads']}; settled by a closed strip {r['strip']}, "
          f"by a repeat {r['repeat']} (top at most {r['repeat_top']}), failed {r['failed']}; highest top {r['top']}, "
          f"highest strip cell {r['cell']}, last settling step {r['last']}; {r['rounds']} rounds")


if __name__ == "__main__":
    main()
