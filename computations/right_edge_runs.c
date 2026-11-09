/* The right edge of the single black cell of Rule 30 in its own frame: the rows h(t) = Phi^t(1) modulo 2^128, with
   Phi(y) = y xor (2y or 4y), the kit's `TFunction`. Bit j of h(t) is the cell (t, t - j), on the right diagonal R_j.

   Modes (rows in hexadecimal, 32 digits, bit 0 the lowest):

     runs K       iterates Phi from 1 to time 2^K (K <= 62). At each time 2^k, k <= K, it prints "row k J h", where
                  J = v_2(h(2^k) - 1) - 1 is the white run W(2^k) beside the right edge (exact while J + 1 < 128; the
                  program prints J = 127 when the row is 1 modulo 2^128) and h = h(2^k) modulo 2^128. At each time
                  2^K - 2^k, k < K, it prints "back k h" with h = h(2^K - 2^k) modulo 2^128: since the cycle of 1
                  modulo 2^n has length L_n, this is h(-2^k) = Phi^(-2^k)(1) modulo 2^n for every n with L_n dividing
                  2^K, that is for n <= W(2^K) + 1. Progress on stderr every 2^30 steps.
     phi K m      for k = 0, ..., K: nu = v_2(h(2^k) - 1) = W(2^k) + 1 and the isometry
                  phi_k(y) = (Phi^(2^k)(1 + 2^nu y) - 1) / 2^nu modulo 2^m, for y = 0, ..., 2^m - 1, as the line
                  "phi k nu phi_k(0) ... phi_k(2^m - 1)" (decimal); it stops at the first k with nu + m > 128.

   Build: cc -O2 right_edge_runs.c -o right_edge_runs */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef unsigned __int128 u128;

static inline u128 phi_step(u128 y) { return y ^ ((y << 1) | (y << 2)); }

static int ctz128(u128 x) {
    uint64_t lo = (uint64_t)x, hi = (uint64_t)(x >> 64);
    if (lo) return __builtin_ctzll(lo);
    if (hi) return 64 + __builtin_ctzll(hi);
    return 128;
}

static void print_hex(u128 x) {
    printf("%016llx%016llx", (unsigned long long)(x >> 64), (unsigned long long)x);
}

/* Phi^n(y) modulo 2^128, with progress on stderr every 2^30 steps when `label` is not NULL */
static u128 phi_power(u128 y, uint64_t n, uint64_t *clock, const char *label) {
    const uint64_t chunk = 1ULL << 30;
    while (n > 0) {
        uint64_t m = n < chunk ? n : chunk;
        for (uint64_t i = 0; i < m; i++) y = phi_step(y);
        n -= m;
        if (clock) *clock += m;
        if (label) {
            fprintf(stderr, "\r%s: time %llu", label, (unsigned long long)(clock ? *clock : 0));
            fflush(stderr);
        }
    }
    return y;
}

static int runs(int K) {
    if (K < 0 || K > 62) { fprintf(stderr, "runs needs 0 <= K <= 62\n"); return 2; }
    /* the event times, in increasing order: 2^k for k < K, then 2^K - 2^k for k = K - 1, ..., 0, and 2^K last (the
       time 2^(K-1) is both the forward time of K - 1 and the back time of K - 1) */
    uint64_t times[128];
    int kind[128], index[128], count = 0;
    for (int k = 0; k < K; k++) { times[count] = 1ULL << k; kind[count] = 0; index[count] = k; count++; }
    for (int k = K - 1; k >= 0; k--) {
        times[count] = (1ULL << K) - (1ULL << k); kind[count] = 1; index[count] = k; count++;
    }
    times[count] = 1ULL << K; kind[count] = 0; index[count] = K; count++;
    u128 y = 1;
    uint64_t t = 0;
    for (int e = 0; e < count; e++) {
        y = phi_power(y, times[e] - t, &t, t + (1ULL << 30) <= times[e] ? "runs" : NULL);
        if (kind[e] == 0) {
            int v = ctz128(y - 1);
            printf("row %d %d ", index[e], v - 1);
        } else {
            printf("back %d ", index[e]);
        }
        print_hex(y);
        printf("\n");
        fflush(stdout);
    }
    fprintf(stderr, "\n");
    return 0;
}

static int phis(int K, int m) {
    if (K < 0 || K > 62 || m < 1 || m > 16) { fprintf(stderr, "phi needs 0 <= K <= 62 and 1 <= m <= 16\n"); return 2; }
    const u128 mask = ((u128)1 << m) - 1;
    for (int k = 0; k <= K; k++) {
        uint64_t n = 1ULL << k;
        u128 h = phi_power(1, n, NULL, NULL);
        int nu = ctz128(h - 1);
        if (nu + m > 128) { fprintf(stderr, "k = %d: nu + m > 128, stopped\n", k); break; }
        printf("phi %d %d", k, nu);
        for (uint64_t y = 0; y < (1ULL << m); y++) {
            u128 z = phi_power(1 + ((u128)y << nu), n, NULL, NULL);
            printf(" %llu", (unsigned long long)(((z - 1) >> nu) & mask));
        }
        printf("\n");
        fflush(stdout);
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc == 3 && argv[1][0] == 'r') return runs(atoi(argv[2]));
    if (argc == 4 && argv[1][0] == 'p') return phis(atoi(argv[2]), atoi(argv[3]));
    fprintf(stderr, "usage: right_edge_runs runs K | phi K m\n");
    return 2;
}
