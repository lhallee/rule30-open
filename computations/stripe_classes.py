"""The classes of the kit's stripe relation at time 0 or 1 on the rows supported in a box [-A, B], and the number of
distinct center columns of those rows.

A row of the box is an integer x < 2^(A+B+1) whose bit k is cell B - k (bit B is cell 0), the frame of the kit's
`Rule30StripeMeeting` with center index B; one step is `phi(a) = a ^ ((a << 1) | (a << 2))`.

- `stripe_words`, `valid_cut`, `stripe_related`, `s01`: the kit's `StripeWord` (generated from its three
  constructors), `StripeRelated`, and S01: stripe-related at time 0, or equal cell 0 and stripe-related at time 1.
- `classes`: the S01 classes of a box by union-find through cut keys; `classes_all_pairs` the same over all pairs.
- `rep`: the representative of `Rule30Open.Frames.StripeClassCount` (one S01 step to a row with cell B black, or the
  row itself); `formula(A, B)` = 2^(A+B) + 3 * 2^(A-1).
- `class_sizes`, `class_size_law`: the sizes of the S01 classes of each left part, against the law of
  `Rule30Open.Frames.StripeClassCount` (2^(B-1-k) classes of size k for k < B, one of size B, and the empty right half
  alone unless the left part ends in 0 1, when it joins the class of size B).
- `distinct_columns`: the number of distinct center-column prefixes of length T, by `stripe_classes.c`. By the Lean
  theorem `box_columns` a box has at most `formula(A, B)` center columns, so a count of `formula(A, B)` prefixes proves
  that the box has exactly that many center columns and that equal center columns are exactly the S01 classes.

    python -m computations.stripe_classes --classes 14             # S01 class counts, widths <= 14, about 15 s
    python -m computations.stripe_classes --sizes 13               # class-size law, widths <= 13, about 10 s
    python -m computations.stripe_classes --columns 18 --horizon 768  # column census, widths <= 18, about 6 min
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from functools import lru_cache

from tqdm.auto import tqdm

from computations.rule30 import step
from computations.seed_onsets import compiled


@lru_cache(maxsize=None)
def stripe_words(n: int) -> frozenset[tuple[bool, ...]]:
    """The kit's `StripeWord` of length n, bit 0 first: zs ++ [1], zs ++ [1, 1], xs ++ [0, 1], with zs all 0."""
    out: set[tuple[bool, ...]] = set()
    if n >= 1:
        out.add(tuple([False] * (n - 1) + [True]))
    if n >= 2:
        out.add(tuple([False] * (n - 2) + [True, True]))
    if n >= 3:
        out.update(w + (False, True) for w in stripe_words(n - 2))
    return frozenset(out)


def bit(a: int, i: int) -> int:
    return (a >> i) & 1


def valid_cut(a: int, j: int) -> bool:
    """Bits 0 .. j of a form a stripe word, bit j is 1 and bit j + 1 is 0."""
    low = tuple(bool(bit(a, i)) for i in range(j + 1))
    return bit(a, j) == 1 and bit(a, j + 1) == 0 and low in stripe_words(j + 1)


def stripe_related(a: int, b: int, c: int) -> bool:
    """The kit's `StripeRelated a b c`."""
    return a == b or any(valid_cut(a, j) and valid_cut(b, j) and a >> (j + 2) == b >> (j + 2) for j in range(c + 1))


def phi(a: int) -> int:
    """One Rule 30 step in the kit's frame (`Rule30StripeMeeting.Phi`)."""
    return a ^ ((a << 1) | (a << 2))


def s01(x: int, y: int, B: int) -> bool:
    """Stripe-related at time 0, or equal cell 0 and stripe-related at time 1."""
    return stripe_related(x, y, B) or (bit(x, B) == bit(y, B) and stripe_related(phi(x), phi(y), B + 1))


def formula(A: int, B: int) -> int:
    """2^(A+B) + 3 * 2^(A-1) for A, B >= 1; 2^(A+1) for B = 0; 2^B + 1 for A = 0."""
    if B == 0:
        return 1 << (A + 1)
    if A == 0:
        return (1 << B) + 1
    return (1 << (A + B)) + 3 * (1 << (A - 1))


class _UnionFind:
    def __init__(self) -> None:
        self.parent: dict[object, object] = {}

    def find(self, v: object) -> object:
        self.parent.setdefault(v, v)
        root = v
        while self.parent[root] != root:
            root = self.parent[root]
        while self.parent[v] != root:
            self.parent[v], v = root, self.parent[v]
        return root

    def union(self, u: object, v: object) -> None:
        self.parent[self.find(u)] = self.find(v)


def _labels(uf: _UnionFind, n: int) -> list[int]:
    roots: dict[object, int] = {}
    return [roots.setdefault(uf.find(x), len(roots)) for x in range(n)]


def classes(A: int, B: int) -> list[int]:
    """The class label of every row of the box. Two different rows are StripeRelated through cut j iff both cuts are
    valid and they agree above bit j + 1, so rows sharing the key (j, x >> (j + 2)) are related, and only those; at
    time 1 the key also carries cell 0."""
    n = 1 << (A + B + 1)
    uf = _UnionFind()
    for x in range(n):
        uf.find(x)
        for j in range(B + 1):
            if valid_cut(x, j):
                uf.union(x, ("t0", j, x >> (j + 2)))
        px = phi(x)
        for j in range(B + 2):
            if valid_cut(px, j):
                uf.union(x, ("t1", j, px >> (j + 2), bit(x, B)))
    return _labels(uf, n)


def class_size_law(B: int, ends01: bool) -> dict[int, int]:
    """The law for one left part and B >= 1, as {size: number of classes}: 2^(B-1-k) classes of size k for
    1 <= k <= B - 1 and one of size B among the nonempty right halves; the empty right half is a class of size 1, or,
    when the left part ends in 0 1, joins the class of size B."""
    law: dict[int, int] = {}
    for k in range(1, B):
        law[k] = law.get(k, 0) + (1 << (B - 1 - k))
    if ends01:
        law[B + 1] = law.get(B + 1, 0) + 1
    else:
        law[B] = law.get(B, 0) + 1
        law[1] = law.get(1, 0) + 1
    return law


def class_sizes(A: int, B: int) -> dict[int, dict[int, int]]:
    """For each left part lam = x >> B of the box, {size: number of S01 classes of that size}; a class never mixes left
    parts, so each class is counted under the left part of any of its rows."""
    lab = classes(A, B)
    count: dict[int, int] = {}
    for label in lab:
        count[label] = count.get(label, 0) + 1
    out: dict[int, dict[int, int]] = {}
    seen: set[int] = set()
    for x, label in enumerate(lab):
        if label in seen:
            continue
        seen.add(label)
        sizes = out.setdefault(x >> B, {})
        sizes[count[label]] = sizes.get(count[label], 0) + 1
    return out


def classes_all_pairs(A: int, B: int) -> list[int]:
    """The class label of every row of the box, by union-find over all pairs (small boxes only)."""
    n = 1 << (A + B + 1)
    uf = _UnionFind()
    for x in range(n):
        uf.find(x)
        for y in range(x + 1, n):
            if s01(x, y, B):
                uf.union(x, y)
    return _labels(uf, n)


def stripe_low(n: int) -> int:
    """The stripe word of length n with bit 0 black: bit i < n is 1 iff i = 0 or i + n is odd."""
    return sum(1 << i for i in range(n) if i == 0 or (i + n) % 2 == 1)


def rep(x: int, B: int) -> int:
    """The representative: m = lowest black bit; one move at time 0 (bit m + 1 white, m <= B) or time 1 (bit m + 1
    black, m < B) to a row with bit 0 black; otherwise the row itself."""
    if x == 0:
        return 0
    m = (x & -x).bit_length() - 1
    if m == 0 or m > B:
        return x
    if bit(x, m + 1) == 0:
        return x - (1 << m) + stripe_low(m + 1)
    if m < B:
        return x - (1 << m) + stripe_low(m)
    return x


def column(x: int, A: int, B: int, T: int) -> tuple[int, ...]:
    """The first T center cells of the row x, by `rule30.step` (bit i is cell i - off)."""
    off = A + T + 2
    row = sum(1 << (B - k + off) for k in range(A + B + 1) if bit(x, k))
    out = []
    for _ in range(T):
        out.append((row >> off) & 1)
        row = step(row)
    return tuple(out)


def distinct_columns(A: int, B: int, T: int) -> int:
    """The number of distinct center-column prefixes of length T (a multiple of 64, at most 2048) in the box, by
    `stripe_classes.c`."""
    binary = compiled("stripe_classes", ("-O2", "-w"))
    run = subprocess.run([str(binary), str(A), str(B), str(T)], stdout=subprocess.PIPE, text=True, check=True)
    return int(run.stdout.split()[4])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--classes", type=int, default=0, help="S01 class counts on every box up to this width")
    parser.add_argument("--sizes", type=int, default=0, help="the class-size law on every box up to this width")
    parser.add_argument("--columns", type=int, default=0, help="column census on every box up to this width")
    parser.add_argument("--horizon", type=int, default=768)
    args = parser.parse_args()
    if args.classes:
        boxes = [(A, W - 1 - A) for W in range(1, args.classes + 1) for A in range(W)]
        for A, B in tqdm(boxes, desc="S01 classes", file=sys.stderr, mininterval=5):
            k = len(set(classes(A, B)))
            print(f"[-{A}, {B}]: {k} classes, formula {formula(A, B)}{'' if k == formula(A, B) else '  DIFFERENT'}")
    if args.sizes:
        boxes = [(A, W - 1 - A) for W in range(2, args.sizes + 1) for A in range(W - 1)]
        bad = 0
        for A, B in tqdm(boxes, desc="class sizes", file=sys.stderr, mininterval=5):
            for lam, sizes in class_sizes(A, B).items():
                if sizes != class_size_law(B, lam % 4 == 1):
                    bad += 1
                    print(f"[-{A}, {B}], left part {lam}: {sizes} against {class_size_law(B, lam % 4 == 1)}")
        print(f"class-size law on {len(boxes)} boxes with B >= 1 up to width {args.sizes}: {bad} left parts differ")
    if args.columns:
        boxes = [(A, W - 1 - A) for W in range(1, args.columns + 1) for A in range(W)]
        for A, B in tqdm(boxes, desc="column census", file=sys.stderr, mininterval=5):
            d = distinct_columns(A, B, args.horizon)
            print(f"[-{A}, {B}]: {d} distinct prefixes of length {args.horizon}, formula {formula(A, B)}"
                  f"{'' if d == formula(A, B) else '  SHORT'}")


if __name__ == "__main__":
    main()
