---
title: The left half is not a patchwork of ether domains
category: period-two
problems: [1]
status: negative
kind: refuted
---

# The left half is not a patchwork of ether domains

**Picture tried.** Beside an alternating center, column 1 is the 36-periodic $AAAB$ pattern with occasional phase slips
([the right channel](../../findings/period-two/right-channel.md)). If each slip only created a localized wall between
two phases of a periodic background, the left half rebuilt from column 1 would be a patchwork of ether domains
separated by walls, and a period-two proof could track the walls.

**Refuted.** A single phase slip at time $s$ changes the left half rebuilt sideways in its whole backward cone
$\{(t, -k) : s - k \le t \le s\}$, and the density of changed cells rises to about 1/2 by depth 512. Slips do not make
localized walls.

**Related.** The periodic left half that the periodic pair (center $01$, column 1 $= 0100110100$) rebuilds has spatial
period 155 and is unstable: one flipped cell keeps about half of column $-1$ different for 3,000 steps. The stripe
background partly heals, keeping 3 differences near the column after about 500 steps. So an eventually periodic center
would need an ether-like layer near the center that the random emissions from the left side's settling front keep
destroying; that is a heuristic, not a proof.

**Evidence.** Quoted from code that is not in this repository.
