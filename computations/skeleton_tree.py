"""The skeleton tree: every eventual sequence of left diagonals that a configuration white left of a black cell can
settle to, followed with the pair map, branch by branch.

The left diagonals D_j(t) = cell(t, lo - t + j) of a configuration white left of a black cell lo obey D_{j+2}(t+1) =
D_j(t) xor (D_{j+1}(t) or D_{j+2}(t)). On aligned settled words of a common period P, D_{j+2} is a function of D_j and
D_{j+1} while D_{j+1} is not white (`settled_words.pair_next`). At a white diagonal w, D_{w+1}(t+1) = D_{w-1}(t) xor
D_{w+1}(t): with odd weight of D_{w-1} the period doubles and the two starting values give words that are rotations of
each other (one class), with even weight they give a word and its complement, two classes unless the complement is a
rotation. `Rule30Open.Diagonals.SkeletonTree` proves that both classes are realized by configurations white left of a
black cell (`branch_realized`), and `Rule30Open.Diagonals.DrivenSkeleton` that every such configuration takes one of
them (`skeleton_step`). So the eventual skeletons form a binary tree that branches at the white diagonals with no
doubling.

- `single_words`: the single cell's settled words, aligned at a time base that is a multiple of 64, from
  `settled_slope.stream`; they fix which child the single cell takes at each white diagonal of its own branch.
- `pair_next_int`, `accumulate`, `white_run`, `alternation`, `first_black`: one word at a time, as Python integers.
- `follow_tree`: every branch from depth 0 to `depth`, with its white diagonals, doublings, regimes, the largest white
  run g and largest antiphase alternation m of the settled pairs in each regime, and the front walk on the settled
  words (from w_1 = 1 on the single cell's branch, continued from the parent's walk at each branch point).

    python -m computations.skeleton_tree --depth 250000   # about 80 s, 0.1 GB
"""

from __future__ import annotations

import argparse
import resource
import sys
from dataclasses import dataclass, field

import numpy as np
from tqdm.auto import tqdm

from computations.settled_slope import least_periods, stream

# ---------------------------------------------------------------------------------------------------------------------
# Words as Python integers: bit r is the cell at a time congruent to r modulo P


def rot(w: int, k: int, P: int) -> int:
    """The word read from time k on: bit r of the result is bit (r + k) mod P of w."""
    k %= P
    return ((w >> k) | (w << (P - k))) & ((1 << P) - 1)


def least_rotation_int(w: int, P: int) -> int:
    """The least of the P rotations of w."""
    return min(rot(w, k, P) for k in range(P))


def pair_next_int(a: int, b: int, P: int) -> int:
    """For aligned P-words a = D_j and b = D_{j+1} with b not white: the P-periodic c = D_{j+2} with
    c(t+1) = a(t) xor (b(t) or c(t)), computed from the lowest black cell r of b, where c(r + 1) = not a(r)."""
    assert b != 0
    r = (b & -b).bit_length() - 1
    t = (r + 1) % P
    cur = 1 ^ ((a >> r) & 1)  # c(r + 1)
    c = 0
    for _ in range(P):
        c |= cur << t
        cur = ((a >> t) & 1) ^ (((b >> t) & 1) | cur)
        t = t + 1 if t + 1 < P else 0
    return c


def accumulate(x: int, P: int, y0: int) -> tuple[int, int]:
    """Behind a white diagonal: Y(t+1) = X(t) xor Y(t) from Y(0) = y0, with X a P-word. Returns (Y, Q) with Q = P for
    even weight of X and Q = 2P (Y anti-periodic) for odd weight."""
    Q = 2 * P if bin(x).count("1") % 2 else P
    y, cur = 0, y0
    for t in range(Q):
        y |= cur << t
        cur ^= (x >> (t % P)) & 1
    return y, Q


def double(w: int, P: int) -> int:
    """A P-word read as a 2P-word."""
    return w | (w << P)


def white_run(w: int, P: int) -> int:
    """The longest cyclic white run g of a P-word that is not white."""
    s = format(w, f"0{P}b")
    return max(len(r) for r in (s + s).split("1"))


def alternation(a: int, b: int, P: int) -> int:
    """The longest antiphase alternation of the settled pair (a, b) = (D_j, D_{j+1}): the largest number of consecutive
    times t at which b(t) != a(t), with a(t + 1) != a(t) between consecutive ones (the `settled_slope.alternations` of
    rows that cover the periodic part twice); -1 if it is unbounded (a alternates with period 2 and b = not a)."""
    m = (1 << P) - 1
    anti = a ^ b
    if anti == 0:
        return 0
    edge = anti & (a ^ rot(a, 1, P)) & rot(anti, 1, P)  # bit t: times t and t + 1 both antiphase and a changes
    if edge == m:
        return -1
    if edge == 0:
        return 1
    s = format(edge, f"0{P}b")
    return 1 + max(len(r) for r in (s + s).split("0"))


def first_black(w: int, P: int, t: int) -> int:
    """The least g >= 0 with bit (t + g) mod P of w black; w is not white."""
    x = rot(w, t, P)
    return (x & -x).bit_length() - 1


# ---------------------------------------------------------------------------------------------------------------------
# The single cell's words


@dataclass(frozen=True, slots=True)
class SingleWords:
    words: list[int]  # words[j] is the aligned word of D_j of length period[j]
    period: list[int]  # least power-of-two period of D_j
    base: int  # bit r of words[j] is D_j at time base + r; base is a multiple of 64


def single_words(depth: int, progress: bool = True) -> SingleWords:
    """The single cell's settled words of the diagonals 0 .. depth, from `settled_slope.stream` with window 256 and a
    base that is a multiple of 64. Every onset (with respect to period 64) is checked to be at or before the base."""
    window = 256
    steps = 64 * ((3 * depth // 2 + 2048) // 64) + window
    d = stream(depth, steps, period=64, window=window, progress=progress)
    base = steps - window
    assert base % 64 == 0 and int(d.onset.max()) <= base, "a diagonal settles after the base"
    period = least_periods(d.tail)  # (depth + 1,)
    assert (period > 0).all()
    weights = 1 << np.arange(64, dtype=object)  # (64,)
    words = [int((d.tail[:int(P), j].astype(object) * weights[:int(P)]).sum()) for j, P in enumerate(period)]
    return SingleWords(words, [int(P) for P in period], base)


# ---------------------------------------------------------------------------------------------------------------------
# The tree


@dataclass(slots=True)
class Regime:
    start: int  # first depth after the white diagonal that opens the regime (1 for the first regime)
    end: int  # the white diagonal that closes it, or the depth limit
    period: int  # common period of the words
    max_white: int = 0  # largest cyclic white run g_j of a word D_j, start <= j < end
    max_alt: int = 0  # largest antiphase alternation of a pair (D_{j-1}, D_j), start <= j < end
    alt_at: int = 0  # the least j at which it is attained
    walk: int = 0  # sum of the walk's steps w_{j+1} - w_j over start <= j < end
    ones: int = 0  # steps of 1 among them


@dataclass(slots=True)
class Branch:
    label: str  # "S" for the single cell's; a child adds ".<w>c" (the class not taken by its parent) at white w
    split: int  # the white diagonal at which it leaves its parent (0 for the single cell's)
    whites: list[tuple[int, bool, int]] = field(default_factory=list)  # (white diagonal w, doubling, walk time w_w)
    regimes: list[Regime] = field(default_factory=list)
    walk_end: int = 0  # w_j at the depth limit
    excess: int = 0  # max over j < depth of w_{j+1} - 2j, the parent's part included
    ratio: float = 0.0  # max of w_j / j over max(1,000, split) < j <= depth
    marks: dict[int, int] = field(default_factory=dict)  # w_j at every j divisible by 1,000, the parent's included
    max_white: int = 0  # W: largest g_j over every regime, the parent's part included
    max_alt: int = 0  # A: largest antiphase alternation over every regime, the parent's part included
    pruned: bool = False  # True if the branch reached a doubling to period 128 and was not followed


@dataclass(slots=True)
class State:
    a: int  # D_{j-1}
    b: int  # D_j
    P: int
    j: int
    tau: int  # the walk's time w_j
    label: str
    split: int
    regime: Regime
    excess: int
    marks: dict[int, int]
    max_white: int
    max_alt: int


def follow_tree(depth: int, single: SingleWords | None, max_period: int = 64,
                progress: bool = True) -> list[Branch]:
    """Every branch of the skeleton tree from depth 1 to `depth`. On the single cell's branch the child at each white
    diagonal j <= len(single.words) - 2 is the one whose word equals the single cell's D_{j+1}, and every word of the
    branch up to that depth is checked against the single cell's; beyond it, the child with starting value 0."""
    known = len(single.words) if single is not None else 2
    stack = [State(1, 1, 1, 1, 1, "S", 0, Regime(1, depth, 1), -(1 << 62), {}, 0, 0)]
    done: list[Branch] = []
    bar = tqdm(total=0, desc="tree", unit="depth", file=sys.stderr, mininterval=5, disable=not progress)
    while stack:
        s = stack.pop()
        br = Branch(s.label, s.split, excess=s.excess, marks=s.marks, max_white=s.max_white,
                    max_alt=s.max_alt)
        a, b, P, j, tau, reg = s.a, s.b, s.P, s.j, s.tau, s.regime
        bar.total += depth - j
        bar.refresh()
        while j < depth:
            on_single = br.label == "S" and j + 1 < known
            if b == 0:  # D_j white: close the regime, choose D_{j+1}
                reg.end = j
                br.regimes.append(reg)
                y, Q = accumulate(a, P, 0)
                doubled = Q == 2 * P
                br.whites.append((j, doubled, tau))
                kids = [y]
                if not doubled:
                    yc = y ^ ((1 << P) - 1)
                    if least_rotation_int(yc, P) != least_rotation_int(y, P):
                        kids.append(yc)
                    elif on_single:
                        kids.append(yc)  # the same class; keep both so that the aligned one can be chosen
                if on_single:
                    target = single.words[j + 1]
                    tP = single.period[j + 1]
                    match = [k for k in kids if k == (target if tP == Q else _expand(target, tP, Q))]
                    if not match and doubled:
                        match = [k for k in (y, rot(y, P, Q)) if k == _expand(target, tP, Q)]
                    assert match, f"no child matches the single cell at depth {j + 1}"
                    others = [k for k in kids if k != match[0]
                              and least_rotation_int(k, Q) != least_rotation_int(match[0], Q)]
                    y = match[0]
                else:
                    others = kids[1:]
                    y = kids[0]
                if Q > max_period:
                    br.pruned = True
                    break
                _walk_stats(br, tau, j)
                br.max_white, br.max_alt = max(br.max_white, reg.max_white), _alt_max(br.max_alt, reg.max_alt)
                for k in others:
                    stack.append(State(0, k, Q, j + 1, tau, f"{br.label}.{j}c", j, Regime(j + 1, depth, Q),
                                       br.excess, dict(br.marks), br.max_white, br.max_alt))
                a, b, P = 0, y, Q
                reg = Regime(j + 1, depth, Q)
                j += 1  # the walk does not move across a white diagonal
                bar.update(1)
                continue
            if on_single:
                assert _expand(single.words[j], single.period[j], P) == b, f"word {j} differs from the single cell"
            reg.max_white = max(reg.max_white, white_run(b, P))
            m = alternation(a, b, P)
            if (m < 0 or m > reg.max_alt) and reg.max_alt >= 0:
                reg.alt_at = j
            reg.max_alt = _alt_max(reg.max_alt, m)
            g = first_black(b, P, tau)
            reg.walk += g + 1
            reg.ones += g == 0
            tau += g + 1
            _walk_stats(br, tau, j)
            a, b = b, pair_next_int(a, b, P)
            j += 1
            bar.update(1)
        if not br.pruned:
            reg.end = depth
            br.regimes.append(reg)
            br.max_white, br.max_alt = max(br.max_white, reg.max_white), _alt_max(br.max_alt, reg.max_alt)
        br.walk_end = tau
        done.append(br)
    bar.close()
    return done


def _walk_stats(br: Branch, tau: int, j: int) -> None:
    """Records w_{j+1} = tau in the branch's largest excess over 2j and largest w_{j+1} / (j + 1) past 1,000."""
    br.excess = max(br.excess, tau - 2 * j)
    if j >= max(1000, br.split):
        br.ratio = max(br.ratio, tau / (j + 1))
    if (j + 1) % 1000 == 0:
        br.marks[j + 1] = tau


def _alt_max(x: int, y: int) -> int:
    """The larger of two alternations, -1 (unbounded) dominating."""
    return -1 if x < 0 or y < 0 else max(x, y)


def _expand(w: int, p: int, P: int) -> int:
    """A word of period p read as a word of length P (p divides P)."""
    out = 0
    for k in range(P // p):
        out |= w << (k * p)
    return out


# ---------------------------------------------------------------------------------------------------------------------


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--depth", type=int, default=250000, help="a multiple of 1,000")
    ap.add_argument("--single-depth", type=int, default=87900, help="depth of the single cell's words from evolution")
    args = ap.parse_args()
    single = single_words(args.single_depth)
    print(f"single cell's words to depth {args.single_depth}, base {single.base}")
    branches = follow_tree(args.depth, single)
    print(f"{len(branches)} branches to depth {args.depth}")
    single_branch = next(br for br in branches if br.label == "S")
    for br in sorted(branches, key=lambda r: (r.split, r.label)):
        print(f"\nbranch {br.label}: leaves its parent at {br.split}; walk w_{args.depth} = {br.walk_end}; "
              f"max w_(j+1) - 2j = {br.excess}; max w_j / j past max(1,000, split) = {br.ratio:.4f}; "
              f"W = {br.max_white}; "
              f"A = {br.max_alt}{' (pruned at period 128)' if br.pruned else ''}")
        lo = -(-max(br.split, 1) // 1000) * 1000
        n = args.depth - lo
        print(f"  mean step over {lo}..{args.depth}: {(br.marks[args.depth] - br.marks[lo]) / n:.4f}, single cell "
              f"{(single_branch.marks[args.depth] - single_branch.marks[lo]) / n:.4f}")
        print("  whites: " + ", ".join(f"{w}{' (doubling)' if d else ''} [walk {tw}]" for w, d, tw in br.whites
                                        if w >= br.split))
        for r in br.regimes:
            if r.end <= br.split:
                continue
            n = r.end - r.start
            mean = r.walk / n if n else float("nan")
            ones = r.ones / n if n else float("nan")
            print(f"  regime {r.start}..{r.end}: P {r.period}, {n} depths, largest g {r.max_white}, largest m "
                  f"{r.max_alt} (first at {r.alt_at}), walk mean {mean:.4f}, steps of 1 {ones:.4f}")
    peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2**20
    print(f"\npeak memory {peak:.2f} GB")


if __name__ == "__main__":
    main()
