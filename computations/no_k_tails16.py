"""The certificate behind `Rule30Open.PeriodTwo.NoKTails16`: on every background of the tail census besides the stripes
and the ether, no head of up to 16 cells is in K.

Write H(U) = (U >> 1) xor (U or (U << 1)) for the held map and K for the 2-adic U with H^t(U) odd at every odd t. A
background of `tail_census` is a cycle of P states of the held map on a ring of L cells; at the alignment (a, o) its
cell j is bit (j + o) mod L of state a mod P. Item 4 of the tail census finds that on each of its 12 backgrounds other
than the stripes and the ether (the vacuum and 11 that carry fronts) every head of up to 16 cells breaks K within 47
steps.

Bit 0 of H^t(U) is bit t of U xor a function of the bits below t, and reads no bit above t. So at an odd step d, of the
two values of cell d exactly one keeps bit 0 of H^d odd, whatever the cells above d are: the points of K with a given
tail form a binary tree that branches at the even cells and is forced at the odd ones. The checker `tree_run` walks
that tree over the cells 0 .. 15 of the head, with the cells 16 .. 63 the background and the cells of the head not yet
chosen 0, and at each of its 2^8 leaves runs the checker `breakRun` of `no_k_tails`, which must find an odd step
2 r + 1 < 2 R at which bit 0 is 0. This covers the 2^16 heads of a tail word with 256 runs instead of 65,536.

- `BACKGROUNDS`: the 12 backgrounds, by a state (cell 0 first), L, P and a Lean tag.
- `tail_words(states, length)`: the distinct tail words (cells 16 .. 63 in place) in order of first appearance over the
  alignments a < P, o < L, and for each alignment the index of its word (entry L a + o).
- `tree_run(word, rounds)`: the walk of the Lean `treeRun` on one tail word: the latest break over the leaves (-1 if a
  leaf does not break), the leaves, and the steps of H it takes (its cost in the kernel).
- `census(states, length)`: `tree_run` on every distinct tail word.
- `plain_steps(word)`: the steps of H of `breakRun` on all 2^16 heads of one word, the cost without the tree.
- `lean_section()`: the background section of the Lean module.

    python -m computations.no_k_tails16           # the census, a few seconds
    python -m computations.no_k_tails16 --lean    # the background section of the Lean module
    python -m computations.no_k_tails16 --compare # the walk against breakRun on every head, first word of each
"""

from __future__ import annotations

import argparse
import sys

from tqdm.auto import tqdm

from computations.held_shift import held
from computations.no_k_tails import background, lean_list, ring_cell, ring_step_ok

# (a state of the background as a ring word, cell 0 first; its spatial period L; its temporal period P; Lean tag),
# in the order of the table of the tail census, without the stripes and the ether
BACKGROUNDS: tuple[tuple[str, int, int, str], ...] = (
    ("0", 1, 1, "L1P1"),
    ("1000", 4, 8, "L4P8"),
    ("11100", 5, 5, "L5P5"),
    ("1010000", 7, 63, "L7P63"),
    ("11100000", 8, 40, "L8P40"),
    ("111000000", 9, 72, "L9P72"),
    ("100100000", 9, 171, "L9P171"),
    ("1110100000", 10, 15, "L10P15"),
    ("10010100000", 11, 17, "L11P17"),
    ("10100000000", 11, 154, "L11P154"),
    ("111110010000", 12, 3, "L12P3"),
    ("100100000000", 12, 102, "L12P102"),
)
HEAD = 16  # the cells of a head
CELLS = 64  # the cells of U that the checker holds
ROUNDS = 24  # rounds of `breakRun` at a leaf: the odd steps 1, 3, ..., 47
CHUNK = 32  # tail words per kernel check


def states_of(name: str, length: int) -> list[int]:
    """The states of the background through the ring word `name`, bit j the ring cell j."""
    return background(name, length)


def tail_word(states: list[int], length: int, a: int, o: int) -> int:
    """Cells HEAD .. CELLS - 1 of the background at the alignment (a, o), in place (the word that the Lean `wordOK` checks)."""
    return sum(ring_cell(states, length, a, j + o) << j for j in range(HEAD, CELLS))


def tail_words(states: list[int], length: int) -> tuple[list[int], list[int]]:
    """The distinct tail words in order of first appearance over the alignments (a, o), a < P and o < L in that order,
    and the index of each alignment's word, entry L a + o."""
    words: list[int] = []
    position: dict[int, int] = {}
    index: list[int] = []
    for a in range(len(states)):
        for o in range(length):
            w = tail_word(states, length, a, o)
            if w not in position:
                position[w] = len(words)
                words.append(w)
            index.append(position[w])
    return words, index


def column_after(d: int, n: int) -> int:
    """Bit 0 of H^d(n) (the Lean `colRaw`)."""
    for _ in range(d):
        n = held(n)
    return n & 1


def break_run(n: int, rounds: int) -> tuple[int, int]:
    """The Lean `breakRun rounds n`: (the odd step 2 r + 1 at which bit 0 of H^(2 r + 1)(n) is first 0, or -1; the
    steps of H taken)."""
    for r in range(rounds):
        n1 = held(n)
        if n1 % 2 == 0:
            return 2 * r + 1, 2 * r + 1
        n = held(n1)
    return -1, 2 * rounds


def tree_run(word: int, rounds: int = ROUNDS, head: int = HEAD) -> tuple[int, list[int], int]:
    """The Lean `treeRun rounds head 0 word`: (the latest break over the leaves, -1 if some leaf has none; the leaves,
    as the heads in the cells 0 .. head - 1; the steps of H taken)."""
    leaves: list[int] = []
    steps = 0
    latest = 0
    stack = [(0, word)]  # (the next cell d, the number with the cells below d chosen)
    while stack:
        d, n = stack.pop()
        if d == head:
            step, used = break_run(n, rounds)
            steps += used
            leaves.append(n & ((1 << head) - 1))
            latest = -1 if step < 0 or latest < 0 else max(latest, step)
        elif d % 2 == 0:
            stack.append((d + 1, n | (1 << d)))
            stack.append((d + 1, n))
        else:
            steps += d
            stack.append((d + 1, n if column_after(d, n) else n | (1 << d)))
    return latest, sorted(leaves), steps


def plain_steps(word: int, rounds: int = ROUNDS) -> int:
    """The steps of H that `breakRun rounds` takes on every head below 2^HEAD with the tail word `word`, without the
    tree (the census of `no_k_tails`, at heads of 16 cells)."""
    return sum(break_run(h | word, rounds)[1] for h in tqdm(range(1 << HEAD), desc="heads", file=sys.stderr,
                                                               leave=False))


def census(states: list[int], length: int, rounds: int = ROUNDS) -> list[dict[str, int]]:
    """For each distinct tail word: the word, the latest break over its leaves (-1 if a leaf does not break within
    `rounds` rounds), the leaves and the steps of H the walk takes."""
    words, _ = tail_words(states, length)
    out = []
    for w in words:
        latest, leaves, steps = tree_run(w, rounds)
        out.append({"word": w, "last": latest, "leaves": len(leaves), "steps": steps})
    return out


def lean_section(rounds: int = ROUNDS) -> str:
    """The background section of the Lean module: for each background its states, the check that they are a cycle,
    its distinct tail words in chunks of `CHUNK`, the rows of the index of each alignment, the check of the tables,
    one kernel check per chunk, and the theorem."""
    out = []
    for name, length, period, tag in BACKGROUNDS:
        states = states_of(name, length)
        assert len(states) == period and ring_step_ok(states, length)
        words, index = tail_words(states, length)
        chunks = [words[i:i + CHUNK] for i in range(0, len(words), CHUNK)]
        nc = len(chunks)
        rows = [index[length * a:length * (a + 1)] for a in range(period)]
        out.append(f"/-! ### The background `{name}`: `L = {length}`, `P = {period}` -/")
        out.append(f"/-- The {period} states of the background `{name}` on a ring of {length} cells, bit `j` the ring "
                   f"cell `j`. -/\ndef states{tag} : List Nat := {lean_list(states)}")
        out.append(f"theorem states{tag}_cycle : ringStepOK states{tag} {length} = true := by\n  decide +kernel")
        for c, chunk in enumerate(chunks):
            out.append(f"/-- Chunk {c} of the {len(words)} distinct tail words of the background, cells {HEAD} to "
                       f"{CELLS - 1} in place. -/\ndef words{tag}_{c} : List Nat := {lean_list(chunk)}")
        out.append(f"/-- The chunks of tail words. -/\ndef words{tag} : List (List Nat) := "
                   f"[{', '.join(f'words{tag}_{c}' for c in range(nc))}]")
        out.append(f"/-- Row `a`, entry `o`: the index of the tail word at the alignment `(a, o)`. -/\n"
                   f"def rows{tag} : List (List Nat) := [{', '.join(lean_list(r) for r in rows)}]")
        out.append(f"theorem tables{tag}_ok : tabOK {length} {nc} words{tag} states{tag} rows{tag} = true := by\n"
                   f"  decide +kernel")
        for c in range(nc):
            out.append(f"theorem ktree{tag}_{c} : wordsOK {rounds} words{tag}_{c} = true := by\n  decide +kernel")
        cases = "\n".join(f"  | {c}, _ => ktree{tag}_{c}" for c in range(nc))
        out.append(f"theorem ktree{tag} (c : Nat) (hc : c < {nc}) : wordsOK {rounds} (words{tag}.getD c []) = true :=\n"
                   f"  match c, hc with\n{cases}\n  | c + {nc}, hc => absurd hc (by omega)")
        out.append(f"/-- **No point of `K` has the background `{name}` from a cell `p ≤ {HEAD}` on**, at any alignment "
                   f"`(a, o)`. -/\n"
                   f"theorem no_k_tail16_{tag} (u : Nat → Bool) (a o p : Nat) (hp : p ≤ {HEAD})\n"
                   f"    (hu : ∀ j, p ≤ j → u j = ringCell states{tag} {length} a (j + o)) : ¬ InK u :=\n"
                   f"  not_inK_of_tree states{tag} {length} {period} {rounds} words{tag} rows{tag} {nc} (by decide) "
                   f"(by decide +kernel)\n    (by decide) (by decide) tables{tag}_ok ktree{tag} u a o p hp hu")
    return "\n\n".join(out)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--rounds", type=int, default=ROUNDS)
    parser.add_argument("--lean", action="store_true", help="print the background section of the Lean module")
    parser.add_argument("--compare", action="store_true",
                        help="the steps of the walk against breakRun on every head, for the first word of each background")
    args = parser.parse_args()
    if args.lean:
        print(lean_section(args.rounds))
        return
    if args.compare:
        for name, length, _, tag in BACKGROUNDS:
            word = tail_words(states_of(name, length), length)[0][0]
            plain, tree = plain_steps(word, args.rounds), tree_run(word, args.rounds)[2]
            print(f"{tag}: {plain} steps on every head, {tree} steps on the tree, ratio {plain / tree:.1f}")
        return
    total_words, total_steps = 0, 0
    for name, length, period, _ in tqdm(BACKGROUNDS, desc="backgrounds", file=sys.stderr, leave=False):
        rows = census(states_of(name, length), length, args.rounds)
        lasts = [r["last"] for r in rows]
        steps = sum(r["steps"] for r in rows)
        total_words += len(rows)
        total_steps += steps
        print(f"{name} (L {length}, P {period}): {period * length} alignments, {len(rows)} distinct tail words, "
              f"{len(rows) << HEAD} heads, {sum(r['leaves'] for r in rows)} leaves; latest break at step "
              f"{-1 if -1 in lasts else max(lasts)}; {steps} steps of H")
    print(f"{total_words} tail words, {total_words << HEAD} heads, {total_steps} steps of H in all")


if __name__ == "__main__":
    main()
