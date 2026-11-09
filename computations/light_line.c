/* The light lines t -> (H^t y)_j of the light-like map H(y)_i = y_i ^ eta(y_{i+1}, y_{i+2}) on half-lines,
   from the uniform measure.  eta is a truth table tt with bit (2u + v) = eta(u, v): Rule 30 is tt = 14 (or),
   Rule 180 is tt = 4 (u and not v).  Used by computations/light_line.py.

   exact TT KMAX            the exact law of the letter process on times 0..K-1, K <= KMAX <= 31, in integer
                            counts out of 4^K.  The letter of level j at time t is (A, B) =
                            (eta(c^j_t, c^{j+1}_t), c^j_t); the law of level j comes from the law of level j + 1
                            through a two-state transducer with a fair initial state (state c^j_t, output
                            (eta(p, B_in), p), then p ^= A_in), and mu_K = Q^2(mu_{K-1} with a letter appended).
                            Prints per K: support size, entropy in bits, and the numerators over 4^K of
                            rho(K) = E(-1)^{sum A}, rhoPi(K) = E(-1)^{sum (1 + B)}, rhoDet(K) = E(-1)^{sum (1 + A(1-B))}.
   mc WLOG T R SEED LAGS... Monte Carlo of C(S, R, k) = E chi_S(H^k y) chi_R(y) for the masks S, R in MASKS (env,
                            comma separated subsets of {0,1,2,3} as bit masks; default "1" = rho), Rule 30 only:
                            W = 2^WLOG lines, T steps, R independent rows; prints the sum and the sum of
                            squares over the rows of the per-row estimate. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#ifdef _OPENMP
#include <omp.h>
#endif

typedef struct { uint64_t w; uint64_t c; } ent;

/* log2 without libm: x = m 2^e with m in [1, 2), log m = 2 atanh((m - 1)/(m + 1)) by its series */
static double log2_(double x) {
    uint64_t b; memcpy(&b, &x, 8);
    int e = (int)((b >> 52) & 0x7FF) - 1023;
    b = (b & 0x000FFFFFFFFFFFFFULL) | 0x3FF0000000000000ULL;
    double m; memcpy(&m, &b, 8);
    double z = (m - 1) / (m + 1), z2 = z * z, term = z, s = 0;
    for (int k = 1; k < 80; k += 2) { s += term / k; term *= z2; }
    return e + 2 * s / 0.69314718055994530942;
}
static int eta[4];

static void rsort(ent *a, ent *tmp, uint64_t n, int bits) {
    static uint64_t cnt[65537];
    int passes = 0;
    for (int sh = 0; sh < bits; sh += 16) {
        memset(cnt, 0, sizeof cnt);
        for (uint64_t i = 0; i < n; i++) cnt[((a[i].w >> sh) & 0xFFFF) + 1]++;
        for (int i = 0; i < 65536; i++) cnt[i + 1] += cnt[i];
        for (uint64_t i = 0; i < n; i++) tmp[cnt[(a[i].w >> sh) & 0xFFFF]++] = a[i];
        ent *s = a; a = tmp; tmp = s; passes++;
    }
    if (passes & 1) memcpy(tmp, a, n * sizeof(ent));
}
static uint64_t merge(ent *a, uint64_t n) {
    uint64_t m = 0;
    for (uint64_t i = 0; i < n; i++) {
        if (m > 0 && a[m - 1].w == a[i].w) a[m - 1].c += a[i].c;
        else a[m++] = a[i];
    }
    return m;
}
static inline uint64_t transduce(uint64_t w, int K, int p) {
    uint64_t out = 0;
    for (int t = 0; t < K; t++) {
        int B = (w >> (2 * t)) & 1, A = (w >> (2 * t + 1)) & 1;
        out |= (uint64_t)(p | (eta[2 * p + B] << 1)) << (2 * t);
        p ^= A;
    }
    return out;
}
static int run_exact(int tt, int Kmax) {
    if (Kmax > 31) { fprintf(stderr, "K <= 31\n"); return 1; }
    for (int i = 0; i < 4; i++) eta[i] = (tt >> i) & 1;
    ent *cur = malloc(sizeof(ent)); uint64_t n = 1; cur[0].w = 0; cur[0].c = 1;
    for (int K = 1; K <= Kmax; K++) {
        uint64_t m = n;
        ent *a = malloc(2 * n * sizeof(ent));
        memcpy(a, cur, n * sizeof(ent)); free(cur);
        for (int it = 0; it < 2; it++) {
            ent *o = malloc(2 * m * sizeof(ent)), *tmp = malloc(2 * m * sizeof(ent));
            if (!o || !tmp) { fprintf(stderr, "alloc failed at K=%d\n", K); return 1; }
            for (uint64_t i = 0; i < m; i++) {
                o[2 * i].w = transduce(a[i].w, K, 0); o[2 * i].c = a[i].c;
                o[2 * i + 1].w = transduce(a[i].w, K, 1); o[2 * i + 1].c = a[i].c;
            }
            free(a);
            rsort(o, tmp, 2 * m, 2 * K);
            free(tmp);
            m = merge(o, 2 * m);
            a = realloc(o, (it == 0 ? 2 * m : m) * sizeof(ent));
        }
        cur = a; n = m;
        unsigned __int128 tot = 0; __int128 r1 = 0, r2 = 0, r3 = 0; double H = 0, D = 1.0 / (double)(1ULL << (2 * K));
        for (uint64_t i = 0; i < n; i++) {
            uint64_t c = cur[i].c, w = cur[i].w; tot += c;
            double p = (double)c * D; H -= p * log2_(p);
            int pa = 0, pb = 0, pd = 0;
            for (int t = 0; t < K; t++) {
                int B = (w >> (2 * t)) & 1, A = (w >> (2 * t + 1)) & 1;
                pa ^= A; pb ^= 1 ^ B; pd ^= 1 ^ (A & (1 ^ B));
            }
            r1 += pa ? -(__int128)c : (__int128)c;
            r2 += pb ? -(__int128)c : (__int128)c;
            r3 += pd ? -(__int128)c : (__int128)c;
        }
        printf("%d %llu %d %.12f %lld %lld %lld\n", K, (unsigned long long)n,
               tot == ((unsigned __int128)1 << (2 * K)), H, (long long)r1, (long long)r2, (long long)r3);
        fflush(stdout);
    }
    free(cur);
    return 0;
}

static inline uint64_t splitmix(uint64_t *s) {
    uint64_t z = (*s += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static int run_mc(int Wlog, int T, int R, uint64_t seed0, int nl, int *lags, int nm, int *masks) {
    uint64_t W = 1ULL << Wlog, WW = W / 64;
    uint64_t L = W + 2 * (uint64_t)T + 256, LW = L / 64 + 2;
    int npair = nm * nm;
    double *sum = calloc((size_t)npair * nl, sizeof(double)), *sum2 = calloc((size_t)npair * nl, sizeof(double));
    #pragma omp parallel
    {
        uint64_t *row = malloc(LW * sizeof(uint64_t));
        uint64_t *hist = malloc((uint64_t)(T + 1) * (WW + 1) * sizeof(uint64_t));
        uint64_t *X = malloc((uint64_t)nm * (T + 1) * WW * sizeof(uint64_t));
        double *loc = malloc((size_t)npair * nl * sizeof(double));
        #pragma omp for schedule(dynamic, 1)
        for (int r = 0; r < R; r++) {
            uint64_t s = seed0 * 1000003ULL + (uint64_t)r * 7919ULL + 12345;
            for (uint64_t w = 0; w < LW; w++) row[w] = splitmix(&s);
            /* every word but the last is updated; stale cells move left by 2 per step and W + 2T < 64(LW - 1) */
            for (int t = 0; t <= T; t++) {
                if (t > 0)
                    for (uint64_t w = 0; w + 1 < LW; w++) {
                        uint64_t a = row[w], b = row[w + 1];
                        row[w] = a ^ (((a >> 1) | (b << 63)) | ((a >> 2) | (b << 62)));
                    }
                memcpy(hist + (uint64_t)t * (WW + 1), row, (WW + 1) * sizeof(uint64_t));
            }
            for (int mi = 0; mi < nm; mi++)
                for (int t = 0; t <= T; t++) {
                    const uint64_t *h = hist + (uint64_t)t * (WW + 1);
                    uint64_t *x = X + ((uint64_t)mi * (T + 1) + t) * WW;
                    for (uint64_t w = 0; w < WW; w++) {
                        uint64_t v = 0;
                        for (int a = 0; a < 4; a++) if (masks[mi] >> a & 1)
                            v ^= a == 0 ? h[w] : ((h[w] >> a) | (h[w + 1] << (64 - a)));
                        x[w] = v;
                    }
                }
            for (int si = 0; si < nm; si++) for (int ri = 0; ri < nm; ri++)
                for (int li = 0; li < nl; li++) {
                    int k = lags[li]; uint64_t diff = 0, cnt = 0;
                    for (int t = 0; t + k <= T; t++) {
                        const uint64_t *A = X + ((uint64_t)si * (T + 1) + t + k) * WW;
                        const uint64_t *B = X + ((uint64_t)ri * (T + 1) + t) * WW;
                        for (uint64_t w = 0; w < WW; w++) diff += __builtin_popcountll(A[w] ^ B[w]);
                        cnt += W;
                    }
                    loc[((size_t)si * nm + ri) * nl + li] = 1.0 - 2.0 * (double)diff / (double)cnt;
                }
            #pragma omp critical
            for (size_t i = 0; i < (size_t)npair * nl; i++) { sum[i] += loc[i]; sum2[i] += loc[i] * loc[i]; }
        }
        free(row); free(hist); free(X); free(loc);
    }
    for (int si = 0; si < nm; si++) for (int ri = 0; ri < nm; ri++) for (int li = 0; li < nl; li++) {
        size_t i = ((size_t)si * nm + ri) * nl + li;
        printf("%d %d %d %.17e %.17e\n", masks[si], masks[ri], lags[li], sum[i], sum2[i]);
    }
    free(sum); free(sum2);
    return 0;
}

int main(int argc, char **argv) {
    if (argc >= 4 && strcmp(argv[1], "exact") == 0) return run_exact(atoi(argv[2]), atoi(argv[3]));
    if (argc >= 7 && strcmp(argv[1], "mc") == 0) {
        int nl = argc - 6; int *lags = malloc(nl * sizeof(int));
        for (int i = 0; i < nl; i++) lags[i] = atoi(argv[6 + i]);
        int masks[16], nm = 0;
        const char *env = getenv("MASKS");
        char buf[256]; strncpy(buf, env ? env : "1", 255); buf[255] = 0;
        for (char *tok = strtok(buf, ","); tok && nm < 16; tok = strtok(NULL, ",")) masks[nm++] = atoi(tok);
        return run_mc(atoi(argv[2]), atoi(argv[3]), atoi(argv[4]), strtoull(argv[5], 0, 10), nl, lags, nm, masks);
    }
    fprintf(stderr, "usage: light_line exact TT KMAX | light_line mc WLOG T R SEED LAGS...\n");
    return 1;
}
