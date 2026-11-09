---
title: The structure of Rule 30's light-like map does not decide its ergodicity, because Rule 180's light-like map shares it and is not ergodic
category: random-rows
problems: [2]
status: negative
kind: barrier
---

# The structure of Rule 30's light-like map does not decide its ergodicity, because Rule 180's light-like map shares it and is not ergodic

**Question.** Is the light-like map $G = \sigma F$, $(Gy)_i = y_i \oplus (y_{i+1} \lor y_{i+2})$, ergodic (or mixing)
for the uniform measure $\lambda$ on the half-lines? [Light-like rigidity](../../findings/random-rows/lightlike-rigidity.md)
needs it, and [light-like mixing](../../findings/random-rows/lightlike-mixing.md) gives the reductions and the numbers:
every correlation tested is below $10^{-4}$ from lag 48.

**Routes tried, and where each stops.**

1. *A rotation factor from the automaton group.* On a block of $m$ cells $G$ acts by the frozen-boundary steps of
   group 2369, all in the coset $\Phi N$ of the normal closure $N$ of $\langle \sigma, \tau \rangle$, and
   $\Gamma / N$ is cyclic. If $N$ were not transitive on some level, the $N$-orbit of the block would rotate
   deterministically and give an eigenvalue. It is transitive on every level ($\Phi$ fixes 0 and the group is level
   transitive; computed to level 22), so there is no such factor.
2. *Bootstrapping through the self-similarity.* $(X_0, G)$ is a $\mathbb{Z}/2$ extension of a copy of itself, and an
   invariant function splits into a twisted part per cell and a tail part, constant since the tail of $\lambda$ is
   trivial. A non-ergodic $G$ would have invariant bits $b_n = y_n \oplus \beta(y_{>n})$, fair coins independent of the
   cells to their right, with ergodic components on which each cell is a function of the cells to its right. This is
   consistent with the trivial tail, with the shift acting exactly on the components, and with the flip of cell 0
   commuting with $G$ and exchanging $b_0$; no contradiction arises.
3. *The unimodular case* ([light-like mixing](../../findings/random-rows/lightlike-mixing.md), item 6). If the twisted
   equation has a solution of modulus 1, the flips of cells 0 and 1 turn it into an eigenfunction with eigenvalue $-1$,
   which is the same twisted equation for the hold cocycle $[y_0 = y_1 = 0]$; the chain closes on itself.
4. *The Fourier fixed point.* The law of two adjacent light lines is a fixed point of a linear map on characteristic
   functions, $\rho(k) = 2^{-k} \sum_{A, B \subseteq [0, k)} (-1)^{k - |A \cup B|} Z(A, B)$ with $Z$ the characteristic
   function one level further right. The cancellation is in the signs; Cauchy and Schwarz give only
   $|\rho(k)| \le 2^k \sqrt{p_k}$ with $p_k$ the collision probability of the pair of lines on $[0, k)$. Since
   $p_k \ge 4^{-k}$ the bound is never below 1, and $p_k \ge 2^{-H}$ with $H$ the entropy of the pair on $[0, k)$, so
   with $H$ near $0.68 k$ bits it grows like $2^{0.66 k}$.
5. *Independence from distinct feet.* Cells on distinct light lines are independent fair coins (the kit's
   `Mixing.measure_cells`), which kills every correlation except those with two cells on one line, the ones in question.
   For entropy it gives $h(\sigma^a G^b) \ge |a| \log 2$ and nothing for $a = 0$.
6. **The barrier.** Rule 180's light-like map $H$, $(Hy)_i = y_i \oplus (y_{i+1} \land \lnot y_{i+2})$, has all of the
   above: it is permutive in its own cell and nonlinear in the two to its right, it is a skew product over a copy of
   itself with the flip of cell 0 commuting with it, it preserves $\lambda$, and it is invertible almost everywhere
   (an image reading $00$ at $q, q + 1$ forces $y_q = 0$, which fixes every cell left of $q$, as $010$ does for
   Rule 30). Yet $H$ is not ergodic: each of its
   light lines is constant on the white times of the next one (in Lean,
   [LightLike180](../../Rule30Open/Analogs/LightLike180.md)), so its light line 0 is constant on an invariant set of
   measure exactly $2/3$. Any argument that uses only these features proves a false statement for Rule 180.

**What it means.** A proof that $G$ is ergodic has to use the OR: something Rule 30's two right cells do that
$y_{i+1} \land \lnot y_{i+2}$ does not. The sampled correlations separate the four classes of nonlinear left-permutive
elementary rules (30, 45, 120 decay, 180 does not), but no argument here turns that into a proof. Exactness is
settled the other way: $G$ is invertible almost everywhere, so it is not exact
([LightLine](../../Rule30Open/RandomRows/LightLine.md)).
