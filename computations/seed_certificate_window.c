/* The window abstraction of seed_certificate.py, depth by depth: an upper bound U_j on the front R_j = max(T_0 .. T_j)
   of every seed row, for j <= J.

   A seed row is white left of a black cell; its left diagonals follow D_{i+2}(t+1) = D_i(t) xor (D_{i+1}(t) or
   D_{i+2}(t)) from D_i(0) = x_i, D_0 = 1, D_{-1} = D_{-2} = 0. The abstract state at depth j is
     - the periodic pair word: (D_{j-1}, D_j) on the times R_j .. R_j + P - 1 (A in bits 0 .. P-1, B in bits P .. 2P-1),
       P a multiple of every period met;
     - the age a = min(R_j, h);
     - the window: (D_{j-1}, D_j) on R_j - h .. R_j - 1 (A in bits 0 .. h-1, B in bits h .. 2h-1), zero below R_j - a.
   The transition with free value c sets D_{j+1}(R_j - a) = c (the cell x_{j+1} at time 0 when a < h), runs the
   recurrence to R_j + 3P, and reads the increment R_{j+1} - R_j as one more than the last u >= 0 with
   D_{j+1}(R_j + u) != D_{j+1}(R_j + u + P) (0 if none). A mismatch at u >= P means the next diagonal does not repeat with
   period P (only behind a diagonal white on a whole period): the program then stops with exit code 3. The value of a
   state is the largest R_j over the abstract paths that reach it; U_j is the largest value at depth j.

   The pair word at each depth is held in a table of at most MAXW words; the values are dense arrays indexed by
   (word, age, window).

   Build: cc -O3 -march=native -fopenmp seed_certificate_window.c -o seed_certificate_window
   Run:   ./seed_certificate_window J h P
   The onset of D_{j+1} itself is at most R_j + tau, tau one more than the last time u >= R_j - a with
   D_{j+1}(u) != D_{j+1}(u + P) (exact), or -a if there is none; V_{j+1} is the largest R_j + tau, so T_j <= V_j for every
   seed.

   Output: "j U_j V_j states words" for j = 0 .. J. */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXW 64

static uint8_t F[2][256][256]; /* F[d][a][b]: bit k = D(8q + k + 1) given D(8q) = d, A and B bytes */

static void init_table(void) {
    for (int d = 0; d < 2; d++)
        for (int a = 0; a < 256; a++)
            for (int b = 0; b < 256; b++) {
                int s = d, out = 0;
                for (int k = 0; k < 8; k++) {
                    s = ((a >> k) & 1) ^ (((b >> k) & 1) | s);
                    out |= s << k;
                }
                F[d][a][b] = (uint8_t)out;
            }
}

static int h, P, J;
static int32_t onset_bound; /* the largest R + tau over the transitions of one depth */

/* One transition. Returns the increment, or -1 if the next diagonal leaves period P; *tau bounds T_{j+1} - R_j (exact
   unless the next diagonal repeats from R_j - a on, then -a). */
static int step(uint32_t pw, int a, uint32_t win, int c, uint32_t *npw, int *na, uint32_t *nwin, int *tau) {
    const uint64_t mP = (1ULL << P) - 1, mh = (1ULL << h) - 1;
    uint64_t wa = pw & mP, wb = (pw >> P) & mP;
    uint64_t ta = wa | (wa << P) | (wa << (2 * P)), tb = wb | (wb << P) | (wb << (2 * P));
    uint64_t A = (win & mh) | (ta << h), B = (((uint64_t)win >> h) & mh) | (tb << h);
    int Q = h + 3 * P, q = h - a, cv = c;
    uint64_t C = 0;
    for (; q < Q && (q & 7); q++) {
        C |= (uint64_t)cv << q;
        cv = (int)((A >> q) & 1) ^ ((int)((B >> q) & 1) | cv);
    }
    for (; q < Q; q += 8) {
        int out = F[cv][(A >> q) & 0xFF][(B >> q) & 0xFF];
        C |= (uint64_t)((cv | (out << 1)) & 0xFF) << q;
        cv = out >> 7;
    }
    uint64_t Cr = C >> h;
    uint64_t mism = (Cr ^ (Cr >> P)) & ((1ULL << (2 * P)) - 1);
    if (mism >> P) return -1;
    int delta = mism ? 64 - __builtin_clzll(mism) : 0;
    uint64_t full = (C ^ (C >> P)) & ((1ULL << (h + 2 * P)) - 1) & ~((1ULL << (h - a)) - 1);
    *tau = full ? 64 - __builtin_clzll(full) - h : -a;
    int age = a + delta < h ? a + delta : h;
    uint64_t keep = h ? ((mh >> (h - age)) << (h - age)) & mh : 0;
    *na = age;
    *nwin = (uint32_t)(((B >> delta) & keep) | (((C >> delta) & keep) << h));
    *npw = (uint32_t)(((B >> (delta + h)) & mP) | (((C >> (delta + h)) & mP) << P));
    return delta;
}

static int find_word(uint32_t *words, int *nw, uint32_t w) {
    int n = __atomic_load_n(nw, __ATOMIC_ACQUIRE);
    for (int i = 0; i < n; i++)
        if (words[i] == w) return i;
    int i;
#pragma omp critical(words)
    {
        i = -1;
        for (int k = 0; k < *nw; k++)
            if (words[k] == w) i = k;
        if (i < 0) {
            if (*nw >= MAXW) {
                fprintf(stderr, "more than %d pair words\n", MAXW);
                exit(4);
            }
            words[*nw] = w;
            i = *nw;
            __atomic_store_n(nw, *nw + 1, __ATOMIC_RELEASE);
        }
    }
    return i;
}

static void atomic_max(int32_t *p, int32_t v) {
    int32_t old = __atomic_load_n(p, __ATOMIC_RELAXED);
    while (v > old && !__atomic_compare_exchange_n(p, &old, v, 0, __ATOMIC_RELAXED, __ATOMIC_RELAXED)) {
    }
}

int main(int argc, char **argv) {
    if (argc < 4) {
        fprintf(stderr, "usage: %s J h P\n", argv[0]);
        return 2;
    }
    J = atoi(argv[1]);
    h = atoi(argv[2]);
    P = atoi(argv[3]);
    if (J < 0 || h < 0 || h > 12 || P < 1 || P > 16 || h + 3 * P > 64) {
        fprintf(stderr, "bad arguments\n");
        return 2;
    }
    init_table();
    const size_t nwin = (size_t)1 << (2 * h), slab = (size_t)(h + 1) * nwin;
    int32_t *V[2];
    uint32_t words[2][MAXW];
    int nw[2] = {1, 0};
    for (int k = 0; k < 2; k++) {
        V[k] = malloc(MAXW * slab * sizeof(int32_t));
        if (!V[k]) {
            fprintf(stderr, "out of memory\n");
            return 5;
        }
    }
    memset(V[0], 0xFF, MAXW * slab * sizeof(int32_t));
    memset(V[1], 0xFF, MAXW * slab * sizeof(int32_t));
    words[0][0] = ((1u << P) - 1) << P; /* (D_{-1}, D_0) = (white, black) */
    V[0][0] = 0;                        /* age 0, window 0, R_0 = 0 */
    printf("0 0 0 1 1\n");
    for (int j = 0; j < J; j++) {
        int cur = j & 1, nxt = cur ^ 1;
        nw[nxt] = 0; /* V[nxt] is all -1: cleared at start and after each use */
        int bad = 0;
        onset_bound = -1;
#pragma omp parallel for schedule(dynamic, 1)
        for (long task = 0; task < (long)nw[cur] * (h + 1); task++) {
            int i = (int)(task / (h + 1)), a = (int)(task % (h + 1));
            const int32_t *row = V[cur] + (size_t)i * slab + (size_t)a * nwin;
            for (size_t w = 0; w < nwin; w++) {
                int32_t R = row[w];
                if (R < 0) continue;
                for (int c = 0; c < 2; c++) {
                    uint32_t npw, nwn;
                    int na, tau;
                    int d = step(words[cur][i], a, (uint32_t)w, c, &npw, &na, &nwn, &tau);
                    if (d < 0) {
                        bad = 1;
                        continue;
                    }
                    atomic_max(&onset_bound, R + tau);
                    int k = find_word(words[nxt], &nw[nxt], npw);
                    atomic_max(V[nxt] + (size_t)k * slab + (size_t)na * nwin + nwn, R + d);
                }
            }
        }
        if (bad) {
            fflush(stdout);
            fprintf(stderr, "depth %d: a transition leaves period %d\n", j, P);
            return 3;
        }
        int32_t best = -1;
        long states = 0;
        for (size_t x = 0; x < (size_t)nw[nxt] * slab; x++)
            if (V[nxt][x] >= 0) {
                states++;
                if (V[nxt][x] > best) best = V[nxt][x];
            }
        printf("%d %d %d %ld %d\n", j + 1, best, onset_bound, states, nw[nxt]);
        memset(V[cur], 0xFF, (size_t)nw[cur] * slab * sizeof(int32_t));
        if ((j + 1) % 1000 == 0) {
            fprintf(stderr, "\rdepth %d", j + 1);
            fflush(stderr);
        }
        fflush(stdout);
    }
    fprintf(stderr, "\n");
    return 0;
}
