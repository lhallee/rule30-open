/* Forced runs of the kit's wedge hypotheses BWH and RW (kit main, Rule30WedgeBridge), for wedge_hypotheses.py.

   Symbols are 0..3, phi is the kit's table, boundary q = 3 - q. For a stream e the cone has antidiagonals
     D_k[t] = cone(t, k - t),  D_k[0] = 3 - e_k,  D_k[1] = phi(e_{k-1}, D_k[0]),  D_k[t] = phi(D_{k-1}[t-2], D_k[t-1]),
   so inverse(k) = D_k[k], and the wedge diagonals are W_k[m] = peel^m(inverse)(k - m),
     W_k[0] = D_k[k],  W_k[m] = phi(W_{k-1}[m-1], W_k[m-1]),
   so wedge n e (k - n) = W_k[n]. phi(a, .) is a bijection for every a, so given e_0 .. e_{k-1} and the value
   W_k[n] = c, the backward pass W_k[m-1] = pinv(W_{k-1}[m-1], W_k[m]), D_k[k] = W_k[0],
   D_k[t-1] = pinv(D_{k-1}[t-2], D_k[t]), e_k = 3 - pinv(e_{k-1}, D_k[1]) gives the one symbol e_k (of four) that keeps
   the wedge equal to c, and the whole of D_k and W_k on the way.

   Every binary prefix e_0 .. e_{n-1} (bit i of the prefix index is 1 when e_i = 2) is a leaf of the free tree; from each
   leaf and each c in {2, 3} the forced run appends the forced symbol while it is binary (and, in RW mode, while it does
   not put 1 after 1 at a position >= n), up to the length cap.

   Build: cc -O3 -march=native -fopenmp wedge_hypotheses.c -o wedge_hypotheses
   Run:   ./wedge_hypotheses n mode cap dump_from split
     mode 0: BWH runs, mode 1: RW runs (hard-core guard from position n).
     cap: the largest length a run may reach; dump_from: runs that reach this length are printed;
     split: the first `split` symbols are split among the OpenMP threads.
   Output: "C c L count" for every c and length L in n .. cap (the number of leaves whose run reaches length L),
           "S c prefix reach" for every run with reach >= dump_from,
           "R c r count" in mode 1, for r = 0, 1, 2: runs reaching 2n + r + 2 with e_{2n+r-1} = 1, e_{2n+r} = 2. */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>

static const uint8_t PHI[4][4] = {{0, 1, 3, 2}, {3, 2, 1, 0}, {3, 2, 0, 1}, {3, 2, 1, 0}};
static uint8_t PINV[4][4];

#define MAXL 160

typedef struct {
    uint8_t e[MAXL];
    uint8_t D[MAXL][MAXL];
    uint8_t W[MAXL][MAXL];
    uint64_t cnt[2][MAXL];
    uint64_t rw[2][3];
} Work;

static int n, mode, cap, dump_from, split;

static void forward(Work *w, int k) {
    uint8_t *D = w->D[k], *P = k > 0 ? w->D[k - 1] : NULL;
    D[0] = 3 - w->e[k];
    if (k >= 1) D[1] = PHI[w->e[k - 1]][D[0]];
    for (int t = 2; t <= k; t++) D[t] = PHI[P[t - 2]][D[t - 1]];
    uint8_t *V = w->W[k], *Q = k > 0 ? w->W[k - 1] : NULL;
    V[0] = D[k];
    int top = k < n ? k : n;
    for (int m = 1; m <= top; m++) V[m] = PHI[Q[m - 1]][V[m - 1]];
}

/* The forced symbol at k >= n >= 1 for wedge value c, filling D_k and W_k; returns it (0..3). */
static int forced(Work *w, int k, int c) {
    uint8_t *V = w->W[k], *Q = w->W[k - 1];
    V[n] = (uint8_t)c;
    for (int m = n; m >= 1; m--) V[m - 1] = PINV[Q[m - 1]][V[m]];
    uint8_t *D = w->D[k], *P = w->D[k - 1];
    D[k] = V[0];
    for (int t = k; t >= 2; t--) D[t - 1] = PINV[P[t - 2]][D[t]];
    D[0] = PINV[w->e[k - 1]][D[1]];
    return 3 - D[0];
}

static void run(Work *w, uint64_t prefix) {
    for (int ci = 0; ci < 2; ci++) {
        int c = 2 + ci, k = n;
        w->cnt[ci][n]++;
        while (k < cap) {
            int s = forced(w, k, c);
            if (s != 1 && s != 2) break;
            if (mode == 1 && w->e[k - 1] == 1 && s == 1) break;
            w->e[k] = (uint8_t)s;
            k++;
            w->cnt[ci][k]++;
            if (mode == 1) {
                for (int r = 0; r < 3; r++)
                    if (k == 2 * n + r + 2 && w->e[2 * n + r - 1] == 1 && w->e[2 * n + r] == 2) w->rw[ci][r]++;
            }
        }
        if (k >= dump_from) {
#pragma omp critical
            printf("S %d %llu %d\n", c, (unsigned long long)prefix, k);
        }
    }
}

static void dfs(Work *w, int k, uint64_t prefix) {
    if (k == n) { run(w, prefix); return; }
    for (int s = 1; s <= 2; s++) {
        w->e[k] = (uint8_t)s;
        forward(w, k);
        dfs(w, k + 1, prefix | ((uint64_t)(s - 1) << k));
    }
}

int main(int argc, char **argv) {
    if (argc != 6) { fprintf(stderr, "usage: n mode cap dump_from split\n"); return 2; }
    n = atoi(argv[1]); mode = atoi(argv[2]); cap = atoi(argv[3]); dump_from = atoi(argv[4]); split = atoi(argv[5]);
    if (n < 1 || n > 62 || cap >= MAXL || cap < n || split > n || split < 0) { fprintf(stderr, "bad arguments\n"); return 2; }
    for (int a = 0; a < 4; a++)
        for (int b = 0; b < 4; b++) PINV[a][PHI[a][b]] = (uint8_t)b;
    uint64_t total[2][MAXL], rw[2][3];
    memset(total, 0, sizeof total); memset(rw, 0, sizeof rw);
    long tasks = 1L << split;
#pragma omp parallel
    {
        Work *w = calloc(1, sizeof(Work));
#pragma omp for schedule(dynamic, 1)
        for (long task = 0; task < tasks; task++) {
            for (int k = 0; k < split; k++) {
                w->e[k] = (uint8_t)(1 + ((task >> k) & 1));
                forward(w, k);
            }
            dfs(w, split, (uint64_t)task);
        }
#pragma omp critical
        {
            for (int ci = 0; ci < 2; ci++) {
                for (int L = 0; L < MAXL; L++) total[ci][L] += w->cnt[ci][L];
                for (int r = 0; r < 3; r++) rw[ci][r] += w->rw[ci][r];
            }
        }
        free(w);
    }
    for (int ci = 0; ci < 2; ci++)
        for (int L = n; L <= cap; L++) printf("C %d %d %llu\n", 2 + ci, L, (unsigned long long)total[ci][L]);
    if (mode == 1)
        for (int ci = 0; ci < 2; ci++)
            for (int r = 0; r < 3; r++) printf("R %d %d %llu\n", 2 + ci, r, (unsigned long long)rw[ci][r]);
    return 0;
}
