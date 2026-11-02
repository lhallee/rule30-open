"""The certificate behind `Rule30Open.PeriodTwo.NoKTails`: no head of up to 12 cells on four backgrounds is in K.

Write H(U) = (U >> 1) xor (U or (U << 1)) for the held map and K for the 2-adic U with H^t(U) odd at every odd t. A
background of `tail_census` is a cycle of P states of the held map on a ring of L cells; at the alignment (a, o) its
cell j is bit (j + o) mod L of state a mod P. For the backgrounds with (L, P) = (4, 8), (5, 5), (10, 15) and (12, 3)
the census of `tail_census` (item 4 of its entry) finds that every head of up to 12 cells breaks K within 33 steps.

Bit 0 of H^t(U) reads only the cells 0 .. t of U, so for t < 64 it is bit 0 of H^t(N) for the number N that holds the
cells 0 .. 63 of U: the head in the cells 0 .. 11 and the background in the cells 12 .. 63 (`tail_word`). A head of
p <= 12 cells is a head of 12 cells whose cells p .. 11 happen to be the background's. The cells 12 .. 63 depend on the
alignment only through the ring word read from cell o of state a, so the alignments share a few distinct tail words
(`tail_words`). The Lean checker `breakRun R N` steps N twice per round and succeeds when bit 0 is 0 after the first
step of a round, that is at an odd step 2 r + 1 < 2 R (`first_break`).

- `background(name, length)`: the states of the cycle of the ring word `name` (cell 0 first), from `held_shift`.
- `tail_words(states, length)`: the distinct tail words in order of first appearance over the alignments a < P,
  o < L, and for each alignment the index of its word (entry L a + o).
- `census(states, length)`: for each distinct word, the latest break over the 2^12 heads and the rounds the checker
  runs in all (its cost in the kernel).
- `lean_section(rounds)`: the data and census section of the Lean module, with `rounds` rounds for every background.

    python -m computations.no_k_tails           # the census, a few seconds
    python -m computations.no_k_tails --lean    # the background section of the Lean module
"""

from __future__ import annotations

import argparse
import sys

from tqdm.auto import tqdm

from computations.held_shift import held, ring_cycle, ring_next

# (name of the background as a ring word, cell 0 first; its spatial period L; its temporal period P; Lean tag)
BACKGROUNDS: tuple[tuple[str, int, int, str], ...] = (
    ("1000", 4, 8, "48"),
    ("11100", 5, 5, "55"),
    ("1110100000", 10, 15, "1015"),
    ("111110010000", 12, 3, "123"),
)
HEAD = 12  # the cells of a head
CELLS = 64  # the cells of U that the checker holds
ROUNDS = 17  # rounds of `breakRun`: the odd steps 1, 3, ..., 33


def background(name: str, length: int) -> list[int]:
    """The states of the cycle of the held map on a ring of `length` cells through the word `name` (cell 0 first), the
    state of `name` first, bit j the ring cell j."""
    transient, states = ring_cycle(int(name[::-1], 2), length)
    assert transient == 0, "the named word lies on its cycle"
    return states


def ring_cell(states: list[int], length: int, a: int, j: int) -> int:
    """Cell j of state a, both read cyclically (the Lean `ringCell`)."""
    return (states[a % len(states)] >> (j % length)) & 1


def tail_word(states: list[int], length: int, a: int, o: int) -> int:
    """Cells HEAD .. CELLS - 1 of the background at the alignment (a, o), in place: bit j the cell j (the Lean
    `tailWord`)."""
    return sum(ring_cell(states, length, a, j + o) << j for j in range(HEAD, CELLS))


def tail_words(states: list[int], length: int) -> tuple[list[int], list[int]]:
    """The distinct tail words in order of first appearance over the alignments (a, o), a < P and o < L in that order,
    and the index of each alignment's word, entry L a + o."""
    words: list[int] = []
    index: list[int] = []
    for a in range(len(states)):
        for o in range(length):
            w = tail_word(states, length, a, o)
            if w not in words:
                words.append(w)
            index.append(words.index(w))
    return words, index


def first_break(n: int, rounds: int) -> tuple[int, int]:
    """The checker `breakRun rounds n`: (the odd step 2 r + 1 at which bit 0 of H^(2 r + 1)(n) is first 0, or -1, and
    the rounds run)."""
    for r in range(rounds):
        n1 = held(n)
        if n1 % 2 == 0:
            return 2 * r + 1, r + 1
        n = held(n1)
    return -1, rounds


def census(states: list[int], length: int, rounds: int = ROUNDS) -> list[dict[str, int]]:
    """For each distinct tail word: the word, the latest break over the heads below 2^HEAD (-1 if a head does not
    break within `rounds` rounds) and the rounds run in all."""
    words, _ = tail_words(states, length)
    out = []
    for w in words:
        last, total = 0, 0
        for h in range(1 << HEAD):
            step, used = first_break(h | w, rounds)
            total += used
            last = -1 if step < 0 or last < 0 else max(last, step)
        out.append({"word": w, "last": last, "rounds": total})
    return out


def ring_step_ok(states: list[int], length: int) -> bool:
    """The Lean `ringStepOK`: each state steps to the next under the held map on the ring, and the last to the first."""
    return all(ring_next(states[a], length) == states[(a + 1) % len(states)] for a in range(len(states)))


def lean_list(values: list[int]) -> str:
    """A Lean list literal."""
    return "[" + ", ".join(str(v) for v in values) + "]"


def lean_section(rounds: int = ROUNDS) -> str:
    """The background section of the Lean module: for each background its states, the check that they are a cycle,
    its distinct tail words and the index of each alignment, one kernel check per word, and the theorem."""
    out = []
    for name, length, period, tag in BACKGROUNDS:
        states = background(name, length)
        assert len(states) == period and ring_step_ok(states, length)
        words, index = tail_words(states, length)
        k = len(words)
        out.append(f"/-! ### The background `{name}`: `L = {length}`, `P = {period}` -/")
        out.append(f"/-- The {period} states of the background `{name}` on a ring of {length} cells, bit `j` the ring "
                   f"cell `j`. -/\ndef bgStates{tag} : List Nat := {lean_list(states)}")
        out.append(f"theorem bgStates{tag}_cycle : ringStepOK bgStates{tag} {length} = true := by\n  decide +kernel")
        out.append(f"/-- The background `{name}` is a cycle of the held map on the ring of {length} cells. -/\n"
                   f"theorem bgStep{tag} (a j : Nat) : ringCell bgStates{tag} {length} (a + 1) j =\n"
                   f"    xor (ringCell bgStates{tag} {length} a (j + 1)) (ringCell bgStates{tag} {length} a j || "
                   f"ringCell bgStates{tag} {length} a (j + {length - 1})) :=\n"
                   f"  ringCell_step bgStates{tag} {length} (by decide) (by decide) bgStates{tag}_cycle a j")
        out.append(f"/-- The {k} distinct tail words of the background, cells {HEAD} to {CELLS - 1} in place. -/\n"
                   f"def bgWords{tag} : List Nat := {lean_list(words)}")
        out.append(f"/-- Entry `{length} a + o`: the index in `bgWords{tag}` of the tail word at the alignment "
                   f"`(a, o)`. -/\ndef bgIndex{tag} : List Nat := {lean_list(index)}")
        out.append(f"theorem bgIndex{tag}_ok : indexOK bgStates{tag} {length} {period} {k} bgWords{tag} bgIndex{tag} = "
                   f"true := by\n  decide +kernel")
        for i in range(k):
            out.append(f"theorem kcensus{tag}_{i} : censusOK {rounds} (bgWords{tag}.getD {i} 0) = true := by\n"
                       f"  decide +kernel")
        cases = "\n".join(f"  | {i}, _ => kcensus{tag}_{i}" for i in range(k))
        out.append(f"theorem kcensus{tag} (i : Nat) (hi : i < {k}) : censusOK {rounds} (bgWords{tag}.getD i 0) = true :=\n"
                   f"  match i, hi with\n{cases}\n  | i + {k}, hi => absurd hi (by omega)")
        out.append(f"/-- **No point of `K` has the background `{name}` from a cell `p ≤ {HEAD}` on**, at any alignment "
                   f"`(a, o)`. -/\n"
                   f"theorem no_k_tail_{tag} (u : Nat → Bool) (a o p : Nat) (hp : p ≤ {HEAD})\n"
                   f"    (hu : ∀ j, p ≤ j → u j = ringCell bgStates{tag} {length} a (j + o)) : ¬ InK u :=\n"
                   f"  not_inK_of_tables bgStates{tag} {length} {period} {rounds} bgWords{tag} bgIndex{tag} {k} "
                   f"(by decide) (by decide)\n"
                   f"    (by decide) (by decide) bgIndex{tag}_ok kcensus{tag} u a o p hp hu")
    return "\n\n".join(out)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--rounds", type=int, default=ROUNDS)
    parser.add_argument("--lean", action="store_true", help="print the background section of the Lean module")
    args = parser.parse_args()
    if args.lean:
        print(lean_section(args.rounds))
        return
    grand = 0
    for name, length, period, _ in tqdm(BACKGROUNDS, desc="backgrounds", file=sys.stderr, leave=False):
        states = background(name, length)
        rows = census(states, length, args.rounds)
        lasts = [r["last"] for r in rows]
        total = sum(r["rounds"] for r in rows)
        grand += total
        print(f"{name} (L {length}, P {period}): {period * length} alignments, {len(rows)} distinct tail words, "
              f"{len(rows) << HEAD} heads; latest break at step {-1 if -1 in lasts else max(lasts)}; "
              f"{total} rounds")
    print(f"{grand} rounds in all")


if __name__ == "__main__":
    main()
