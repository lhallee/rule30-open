/* The front walk on every pair word of period P: the largest cycle mean of the cycles inside the regimes' cycles of
   the pair map, and the excess of the walk over slope num/den, by pair orbits.

   A state is (A, B, f): the walk is on diagonal i with aligned words A = D_i, B = D_{i+1} of period P (bit t is the
   cell at time t mod P) and w_i = f mod P. One step of the walk:

     A != 0: d = least d >= 0 with A(f + d) = 1, cost d + 1, phase f + d + 1; the next pair is (B, C) with
             C = pair_next(A, B) if B != 0; if B = 0 it is (0, Y) with Y(t + 1) = Y(t) xor A(t), for both values of
             Y(0), when A has even weight (the period is kept), and the walk leaves period P (the period doubles) when
             A has odd weight;
     A == 0: the crossing of a white diagonal, cost 0, phase f, next pair (B, pair_next(0, B)).

   Every step moves one depth, so its weight at slope gamma = num/den is den * cost - num (units of 1/den).

   The pair map F(A, B) = (B, C) is injective, so the pairs fall into chains, from (0, Y) to (X, 0), one for each
   Y != 0, and cycles of F with no white word. A chain's end (X, 0) crosses to the starts of the chains of Y0(X) and
   Y1(X), or leaves period P. The program walks every chain and every cycle of F once with all P phases at a time:

   - for each chain and start phase: the cost and the number of steps to the chain's end, the end phase, and the
     largest prefix of the weights (written to the summary file for the cycle means through crossings);
   - the excess E(s) = max(0, w(s) + max over successors E(s')) of every state of the chains, from the fixed point of
     the chain starts and one backward pass over each chain;
   - for each cycle of F: the cycles of the phase map once around it (the largest mean cost of them), and E on it.

   Output (stdout), one key and value per line: pairs, chains, chain_pairs, longest_chain, fcycles, fcycle_pairs,
   mu_f (num/den of the largest cycle mean inside cycles of F, 0/1 if none), mu_f_state, mu_p (the same over the cycles
   of F whose pairs have least period P), chain_fixed (1 if the chain
   starts reach a fixed point, else 0: a cycle through crossings above gamma), R_chain, R_start, R_double (the
   largest E over the chain states, the chain starts, the starts whose Y is anti-periodic), R_cycle (over the
   states of cycles of F, -1 if a cycle there is above gamma), and the states attaining them.

   Files (optional): SUMMARY gets, for Y = 0 .. 2^P - 1, int64 steps[Y], int64 end[Y], then int64 cost[Y][f] and
   int64 endphase[Y][f] (Y = 0 unused); DUMP gets int32 E[(A << P | B) * P + f] for every state (-1 for (0, 0, f)).

   Build: cc -O2 walk_eigen.c -o walk_eigen
   Run:   ./walk_eigen P num den [SUMMARY|-] [DUMP|-]        (2 <= P <= 16) */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef int64_t i64;
typedef __int128 i128;

static int P, NUM, DEN;
static uint32_t MASK;
static int8_t *gap; /* gap[a * P + f]: least d >= 0 with a(f + d) = 1, -1 for a = 0 */

static uint32_t pair_next(uint32_t a, uint32_t b) {
    /* b != 0: the P-periodic c with c(t + 1) = a(t) xor (b(t) or c(t)), from the lowest black cell r of b */
    int r = __builtin_ctz(b);
    int t = (r + 1) % P;
    int cur = !((a >> r) & 1);
    uint32_t c = (uint32_t)cur << t;
    for (int k = 1; k < P; k++) {
        int nb = ((a >> t) & 1) ^ (((b >> t) & 1) | cur);
        t = (t + 1) % P;
        cur = nb;
        c |= (uint32_t)cur << t;
    }
    return c;
}

static uint32_t integrate(uint32_t a) {
    /* Y(0) = 0, Y(t + 1) = Y(t) xor a(t) */
    uint32_t y = 0, cur = 0;
    for (int t = 0; t + 1 < P; t++) {
        cur ^= (a >> t) & 1;
        y |= cur << (t + 1);
    }
    return y;
}

static uint32_t rot(uint32_t y, int k) {
    return k % P ? ((y >> k) | (y << (P - k))) & MASK : y;
}

/* the least period of the pair (a, b): the least q dividing P with both words invariant under rotation by q */
static int pair_period(uint32_t a, uint32_t b) {
    for (int q = 1; q < P; q++)
        if (P % q == 0 && rot(a, q) == a && rot(b, q) == b) return q;
    return P;
}

static int anti(uint32_t y) {
    if (P % 2) return 0;
    int h = P / 2;
    uint32_t r = ((y >> h) | (y << (P - h))) & MASK;
    return r == ((~y) & MASK);
}

/* one step from pair (a, b) at phase f: the weight, the next phase */
static inline void step(uint32_t a, int f, int *w, int *cost, int *nf) {
    if (a == 0) {
        *cost = 0;
        *nf = f;
    } else {
        int d = gap[(size_t)a * P + f];
        *cost = d + 1;
        *nf = (f + d + 1) % P;
    }
    *w = DEN * *cost - NUM;
}

static uint32_t *buf; /* pairs of the chain or cycle being walked */
static size_t cap;

static void push(size_t n, uint32_t p) {
    if (n >= cap) {
        cap = cap ? 2 * cap : 1 << 16;
        buf = realloc(buf, cap * sizeof(uint32_t));
        if (!buf) { fprintf(stderr, "out of memory\n"); exit(1); }
    }
    buf[n] = p;
}

static uint8_t *seen; /* bitmap over the 4^P pairs */
#define SEEN(p) ((seen[(p) >> 3] >> ((p) & 7)) & 1)
#define MARK(p) (seen[(p) >> 3] |= (uint8_t)(1u << ((p) & 7)))

static int32_t *dump;

/* walk the chain from (0, y), store its pairs in buf, return the number of pairs */
static size_t walk_chain(uint32_t y) {
    uint32_t a = 0, b = y;
    size_t n = 0;
    for (;;) {
        uint32_t p = (a << P) | b;
        MARK(p);
        push(n++, p);
        if (b == 0) break;
        uint32_t c = pair_next(a, b);
        a = b;
        b = c;
    }
    return n;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: walk_eigen P num den [SUMMARY|-] [DUMP|-]\n"); return 1; }
    P = atoi(argv[1]); NUM = atoi(argv[2]); DEN = atoi(argv[3]);
    if (P < 2 || P > 16) { fprintf(stderr, "P out of range\n"); return 1; }
    const char *sumfile = argc > 4 && strcmp(argv[4], "-") ? argv[4] : NULL;
    const char *dumpfile = argc > 5 && strcmp(argv[5], "-") ? argv[5] : NULL;
    MASK = (1u << P) - 1;
    size_t W = (size_t)1 << P, NP = W * W;
    gap = malloc(W * P);
    for (size_t a = 0; a < W; a++)
        for (int f = 0; f < P; f++) {
            int d = -1;
            if (a)
                for (d = 0; !((a >> ((f + d) % P)) & 1); d++) {}
            gap[a * P + f] = (int8_t)d;
        }
    seen = calloc(NP / 8 + 1, 1);
    if (dumpfile) {
        dump = malloc(NP * P * sizeof(int32_t));
        if (!dump) { fprintf(stderr, "out of memory\n"); return 1; }
        for (size_t i = 0; i < NP * P; i++) dump[i] = -1;
    }
    i64 *csteps = calloc(W, sizeof(i64)), *cend = calloc(W, sizeof(i64));
    i64 *ccost = calloc(W * P, sizeof(i64)), *cphase = calloc(W * P, sizeof(i64));
    i64 *cS = calloc(W * P, sizeof(i64)), *cM = calloc(W * P, sizeof(i64)), *Es = calloc(W * P, sizeof(i64));
    uint32_t *y0 = malloc(W * sizeof(uint32_t));
    for (size_t x = 0; x < W; x++) y0[x] = integrate((uint32_t)x);
    int ph[32], wt, co, nf;
    i64 S[32], Mx[32], C[32];

    /* 1. chains: summaries per start phase */
    size_t chain_pairs = 0, longest = 0;
    for (uint32_t y = 1; y < W; y++) {
        if (y % 64 == 0 || y == W - 1) fprintf(stderr, "\rchains %u/%zu", y, W - 1);
        size_t n = walk_chain(y);
        chain_pairs += n;
        if (n > longest) longest = n;
        for (int f = 0; f < P; f++) { ph[f] = f; S[f] = 0; Mx[f] = 0; C[f] = 0; }
        for (size_t k = 0; k < n; k++) {
            uint32_t a = buf[k] >> P;
            for (int f = 0; f < P; f++) {
                step(a, ph[f], &wt, &co, &nf);
                ph[f] = nf; S[f] += wt; C[f] += co;
                if (S[f] > Mx[f]) Mx[f] = S[f];
            }
        }
        csteps[y] = (i64)n;
        cend[y] = buf[n - 1] >> P;
        for (int f = 0; f < P; f++) {
            ccost[y * P + f] = C[f]; cphase[y * P + f] = ph[f];
            cS[y * P + f] = S[f]; cM[y * P + f] = Mx[f];
        }
    }
    fprintf(stderr, "\n");

    /* 2. the chain starts: E(y, f) = max(M, S + max(E(Y0, g), E(Y1, g))) when the end keeps the period */
    int fixed = 0;
    size_t nodes = (W - 1) * P;
    for (size_t round = 0; round <= nodes + 1; round++) {
        int changed = 0;
        for (uint32_t y = 1; y < W; y++) {
            uint32_t x = (uint32_t)cend[y];
            int keep = !(__builtin_popcount(x) & 1);
            uint32_t ya = y0[x], yb = (~y0[x]) & MASK;
            for (int f = 0; f < P; f++) {
                i64 v = cM[y * P + f];
                if (keep) {
                    int g = (int)cphase[y * P + f];
                    i64 e = Es[ya * P + g] > Es[yb * P + g] ? Es[ya * P + g] : Es[yb * P + g];
                    if (cS[y * P + f] + e > v) v = cS[y * P + f] + e;
                }
                if (v != Es[y * P + f]) { Es[y * P + f] = v; changed = 1; }
            }
        }
        if (!changed) { fixed = 1; break; }
    }

    /* 3. backward over each chain: E at every chain state */
    i64 Rchain = -1, Rstart = -1, Rdouble = -1;
    uint64_t argchain = 0, argstart = 0, argdouble = 0;
    if (fixed) {
        i64 E[32], En[32];
        for (uint32_t y = 1; y < W; y++) {
            if (y % 64 == 0 || y == W - 1) fprintf(stderr, "\rchain states %u/%zu", y, W - 1);
            size_t n = walk_chain(y);
            uint32_t x = buf[n - 1] >> P;
            int keep = !(__builtin_popcount(x) & 1);
            uint32_t ya = y0[x], yb = (~y0[x]) & MASK;
            for (int g = 0; g < P; g++) {
                En[g] = 0;
                if (keep) En[g] = Es[ya * P + g] > Es[yb * P + g] ? Es[ya * P + g] : Es[yb * P + g];
            }
            for (size_t k = n; k-- > 0;) {
                uint32_t p = buf[k], a = p >> P;
                for (int f = 0; f < P; f++) {
                    step(a, f, &wt, &co, &nf);
                    i64 v = wt + En[nf];
                    E[f] = v > 0 ? v : 0;
                    if (E[f] > Rchain) { Rchain = E[f]; argchain = (uint64_t)p * P + f; }
                    if (dump) dump[(size_t)p * P + f] = (int32_t)E[f];
                }
                memcpy(En, E, sizeof(E));
            }
            for (int f = 0; f < P; f++) {
                if (E[f] != Es[y * P + f]) { fprintf(stderr, "inconsistent chain start\n"); return 2; }
                if (E[f] > Rstart) { Rstart = E[f]; argstart = (uint64_t)y * P + f; }
                if (anti(y) && E[f] > Rdouble) { Rdouble = E[f]; argdouble = (uint64_t)y * P + f; }
            }
        }
        fprintf(stderr, "\n");
    }

    /* 4. cycles of F */
    size_t fcycles = 0, fcycle_pairs = 0;
    i64 mun = 0, mud = 1; /* largest cycle mean found, as a fraction */
    i64 mpn = 0, mpd = 1; /* the same over the cycles of F whose pairs have least period P */
    i64 Rcycle = -1;
    uint64_t argmu = 0, argcycle = 0;
    int cycle_above = 0;
    size_t done = 0;
    for (uint64_t q0 = 0; q0 < NP; q0++) {
        uint32_t p0 = (uint32_t)q0;
        if (SEEN(p0)) continue;
        uint32_t a = p0 >> P, b = p0 & MASK;
        if (a == 0 || b == 0) continue; /* every such pair is on a chain */
        size_t n = 0;
        uint32_t p = p0;
        do {
            MARK(p);
            push(n++, p);
            uint32_t c = pair_next(p >> P, p & MASK);
            p = ((p & MASK) << P) | c;
            if (n > NP) { fprintf(stderr, "not a cycle of F\n"); return 2; }
        } while (p != p0);
        fcycles++;
        fcycle_pairs += n;
        done += n;
        if (fcycles % 1024 == 0) fprintf(stderr, "\rcycles of F: %zu pairs of %zu", done, NP);
        for (int f = 0; f < P; f++) { ph[f] = f; S[f] = 0; Mx[f] = 0; C[f] = 0; }
        for (size_t k = 0; k < n; k++) {
            uint32_t aa = buf[k] >> P;
            for (int f = 0; f < P; f++) {
                step(aa, ph[f], &wt, &co, &nf);
                ph[f] = nf; S[f] += wt; C[f] += co;
                if (S[f] > Mx[f]) Mx[f] = S[f];
            }
        }
        int primitive = pair_period(a, b) == P;
        /* cycles of the lap map f -> ph[f] */
        int color[32];
        int above = 0;
        for (int f = 0; f < P; f++) color[f] = 0;
        for (int f = 0; f < P; f++) {
            if (color[f]) continue;
            int v = f;
            while (!color[v]) { color[v] = 1; v = ph[v]; }
            if (color[v] == 1) { /* a new cycle through v */
                i64 tc = 0, ts = 0, m = 0;
                int u = v;
                do { tc += C[u]; ts += S[u]; m++; u = ph[u]; } while (u != v);
                i64 len = m * (i64)n;
                if ((i128)tc * mud > (i128)mun * len) { mun = tc; mud = len; argmu = (uint64_t)p0 * P + v; }
                if (primitive && (i128)tc * mpd > (i128)mpn * len) { mpn = tc; mpd = len; }
                if (ts > 0) above = 1;
            }
            v = f;
            while (color[v] == 1) { color[v] = 2; v = ph[v]; }
        }
        if (above) { cycle_above = 1; continue; }
        if (cycle_above) continue;
        /* E at p0: E0(f) = max(M(f), S(f) + E0(ph f)), then backward around the cycle */
        i64 E0[32], E[32], En[32];
        for (int f = 0; f < P; f++) E0[f] = 0;
        for (int it = 0; it <= 2 * P + 2; it++) {
            int ch = 0;
            for (int f = 0; f < P; f++) {
                i64 v = Mx[f] > S[f] + E0[ph[f]] ? Mx[f] : S[f] + E0[ph[f]];
                if (v != E0[f]) { E0[f] = v; ch = 1; }
            }
            if (!ch) break;
        }
        memcpy(En, E0, sizeof(E0));
        for (size_t k = n; k-- > 0;) {
            uint32_t q = buf[k], aa = q >> P;
            for (int f = 0; f < P; f++) {
                step(aa, f, &wt, &co, &nf);
                i64 v = wt + En[nf];
                E[f] = v > 0 ? v : 0;
                if (E[f] > Rcycle) { Rcycle = E[f]; argcycle = (uint64_t)q * P + f; }
                if (dump) dump[(size_t)q * P + f] = (int32_t)E[f];
            }
            memcpy(En, E, sizeof(E));
        }
        for (int f = 0; f < P; f++)
            if (E[f] != E0[f]) { fprintf(stderr, "inconsistent cycle potential\n"); return 2; }
    }
    fprintf(stderr, "\n");
    if (cycle_above) Rcycle = -1;

    printf("pairs %zu\nchains %zu\nchain_pairs %zu\nlongest_chain %zu\n", NP, W - 1, chain_pairs, longest);
    printf("fcycles %zu\nfcycle_pairs %zu\n", fcycles, fcycle_pairs);
    printf("mu_f %lld %lld\nmu_f_state %llu\n", (long long)mun, (long long)mud, (unsigned long long)argmu);
    printf("mu_p %lld %lld\n", (long long)mpn, (long long)mpd);
    printf("chain_fixed %d\n", fixed);
    printf("R_chain %lld\nR_chain_state %llu\nR_start %lld\nR_start_state %llu\nR_double %lld\nR_double_state %llu\n",
           (long long)Rchain, (unsigned long long)argchain, (long long)Rstart, (unsigned long long)argstart,
           (long long)Rdouble, (unsigned long long)argdouble);
    printf("R_cycle %lld\nR_cycle_state %llu\n", (long long)Rcycle, (unsigned long long)argcycle);
    if (sumfile) {
        FILE *fp = fopen(sumfile, "wb");
        fwrite(csteps, sizeof(i64), W, fp);
        fwrite(cend, sizeof(i64), W, fp);
        fwrite(ccost, sizeof(i64), W * P, fp);
        fwrite(cphase, sizeof(i64), W * P, fp);
        fclose(fp);
    }
    if (dumpfile) {
        FILE *fp = fopen(dumpfile, "wb");
        fwrite(dump, sizeof(int32_t), NP * P, fp);
        fclose(fp);
    }
    return 0;
}
