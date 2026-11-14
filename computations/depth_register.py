"""The left recurrence read sideways, as a register in the depth direction: what it says about the weights of the words.

On aligned words of a common period P (bit t of an integer is the cell at time t mod P), three consecutive left
diagonals A = W_{d-2}, B = W_{d-1}, C = W_d of an eternal orbit satisfy C(t+1) = A(t) xor (B(t) or C(t)) for every t.

- `next_words`: every P-periodic C that solves the step for given (A, B): one if B is not white, zero or two if it is.
- `is_step`: whether (A, B, C) solves the step.
- `weight_identity`: checks |A| + |B| = |B and C| + 2 |A and (B or C)| on every solving triple of period P (the
  sum of the step over one period; see the entry).
- `window_min`: the least total weight of K consecutive words W_1, ..., W_K that solve the step at each position and
  have no two consecutive white words (as in every eternal orbit with a black frame cell), found by a pruned search,
  with a minimizer.
- `transplant`: the same window at a larger period, with the words' bits kept at their positions; `is_window` checks
  it.

    python -m computations.depth_register          # the table of the entry, about 1 min
"""

from __future__ import annotations

import sys

from tqdm.auto import tqdm


def bit(w: int, t: int) -> int:
    return (w >> t) & 1


def is_step(a: int, b: int, c: int, P: int) -> bool:
    """Whether C(t+1) = A(t) xor (B(t) or C(t)) for every t mod P."""
    return all(bit(c, (t + 1) % P) == bit(a, t) ^ (bit(b, t) | bit(c, t)) for t in range(P))


def next_words(a: int, b: int, P: int) -> list[int]:
    """Every P-periodic C with (A, B, C) solving the step."""
    out: list[int] = []
    for c0 in (0, 1):
        c = [c0] + [0] * (P - 1)  # (P,) the cells of C
        for t in range(P - 1):
            c[t + 1] = bit(a, t) ^ (bit(b, t) | c[t])
        w = sum(v << t for t, v in enumerate(c))
        if is_step(a, b, w, P) and w not in out:
            out.append(w)
    return out


def weight_identity(P: int) -> int:
    """Check |A| + |B| = |B & C| + 2 |A & (B | C)| on every solving triple of period P; returns the number checked."""
    n = 0
    for a in range(1 << P):
        for b in range(1 << P):
            for c in next_words(a, b, P):
                lhs = bin(a).count("1") + bin(b).count("1")
                rhs = bin(b & c).count("1") + 2 * bin(a & (b | c)).count("1")
                if lhs != rhs:
                    raise AssertionError((a, b, c))
                n += 1
    return n


def is_window(ws: list[int], P: int) -> bool:
    """Every three consecutive words solve the step, and no two consecutive words are white."""
    ok = all(is_step(ws[i], ws[i + 1], ws[i + 2], P) for i in range(len(ws) - 2))
    return ok and all(ws[i] or ws[i + 1] for i in range(len(ws) - 1))


def window_min(P: int, K: int) -> tuple[int, list[int]]:
    """Least total weight of a window of K >= 2 words of period P (see `is_window`), and a minimizer."""
    pc = [bin(i).count("1") for i in range(1 << P)]  # (2^P,) weights
    best, arg = 10 ** 9, [0] * K
    for a in range(1 << P):
        for b in range(1 << P):
            if a == 0 and b == 0:
                continue
            stack = [(a, b, pc[a] + pc[b], [a, b])]
            while stack:
                x, y, w, ws = stack.pop()
                if w >= best:
                    continue
                if len(ws) == K:
                    best, arg = w, ws
                    continue
                for z in next_words(x, y, P):
                    if y == 0 and z == 0:
                        continue
                    stack.append((y, z, w + pc[z], ws + [z]))
    return best, arg


def transplant(ws: list[int], P: int) -> list[int]:
    """The same words, read at period P (the bits keep their positions)."""
    return [w & ((1 << P) - 1) for w in ws]


def main() -> None:
    jobs = [(P, K) for K in (3, 4, 5, 6) for P in (6, 8, 10)] + [(6, 8), (8, 8)]
    print("| K | P | least weight of K consecutive words | density | minimizer, low bits |")
    print("|---:|---:|---:|---:|---|")
    for P, K in tqdm(jobs, desc="windows", file=sys.stderr):
        w, ws = window_min(P, K)
        print(f"| {K} | {P} | {w} | {w / (K * P):.4f} | {', '.join(format(x, 'b') for x in ws)} |")
    print("identity checked on", weight_identity(8), "triples of period 8")


if __name__ == "__main__":
    main()
