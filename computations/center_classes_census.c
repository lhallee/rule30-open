/* The census of center_classes.py: the first T1 center cells of every row of a box, or of every row with a fixed left
   part, sorted, and the groups of rows whose T1 cells agree.

   A row is an integer x whose bit k is cell B - k, so cell 0 is bit B: the frame of the kit's Rule30StripeMeeting with
   center index B. One step is the kit's Phi(y) = y xor ((y << 1) | (y << 2)), and the center cell at time t is bit
   B + t of Phi^t(x). Bit i of Phi(y) reads bits i, i - 1 and i - 2 of y only, so y is kept modulo 2^(B + T1).

   Modes:

     box A B T1       every nonzero row supported in [-A, B] (A + B + 1 <= 26)
     part L B T1      every row (L << B) | r with r < 2^B: the left part L (bit 0 of L is cell 0) and every right half
                      inside [1, B] (B <= 26, (L << B) < 2^31)

   T1 <= 192 and B + T1 <= 256. Output: one line "G x1 x2 ..." per group of two or more rows whose first T1 center
   cells agree, then "# groups=<number> members=<rows in groups>", "# lcp_left_edge=<l> pair=<x>,<y>": the longest
   common prefix (at most T1) of two nonzero rows with different left edges, or -1 if every row has the same left edge,
   and "# lcp_groups=<l>": the longest common prefix of two rows whose first T1 cells differ, or -1. Two rows that
   maximize the common prefix under a condition that tells them apart can be taken adjacent in the sorted order,
   since the common prefix of two rows is the least over the adjacent pairs between them. Progress on stderr.

   Build: cc -O2 center_classes_census.c -o center_classes_census */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define NW 4 /* words of the row in the moving frame: B + T1 <= 256 */
#define CW 3 /* words of the packed column: T1 <= 192 */

static int B, T1;
static uint64_t *cols; /* (n, CW): center cell t is bit 63 - t % 64 of word t / 64 */
static uint32_t *rows; /* (n,): the row whose column is cols[i] */

static void phi(uint64_t *y) {
    uint64_t s[NW];
    for (int i = 0; i < NW; i++)
        s[i] = (y[i] << 1) | (y[i] << 2) | (i ? (y[i - 1] >> 63) | (y[i - 1] >> 62) : 0);
    for (int i = 0; i < NW; i++) y[i] ^= s[i];
}

static int cmp_index(const void *a, const void *b) {
    uint32_t i = *(const uint32_t *)a, j = *(const uint32_t *)b;
    const uint64_t *u = cols + (size_t)i * CW, *v = cols + (size_t)j * CW;
    for (int w = 0; w < CW; w++)
        if (u[w] != v[w]) return u[w] < v[w] ? -1 : 1;
    return rows[i] < rows[j] ? -1 : rows[i] > rows[j];
}

static int common_prefix(uint32_t i, uint32_t j) {
    const uint64_t *u = cols + (size_t)i * CW, *v = cols + (size_t)j * CW;
    for (int w = 0; w < CW; w++) {
        uint64_t d = u[w] ^ v[w];
        if (d) {
            int l = w * 64 + __builtin_clzll(d);
            return l < T1 ? l : T1;
        }
    }
    return T1;
}

static int left_edge(uint32_t x) { return B - (31 - __builtin_clz(x)); } /* x != 0 */

int main(int argc, char **argv) {
    if (argc != 5 || (strcmp(argv[1], "box") && strcmp(argv[1], "part"))) {
        fprintf(stderr, "usage: center_classes_census box A B T1 | part L B T1\n");
        return 1;
    }
    int box = !strcmp(argv[1], "box");
    unsigned long first = strtoul(argv[2], 0, 10); /* A, or the left part L */
    B = atoi(argv[3]);
    T1 = atoi(argv[4]);
    int width = box ? (int)first + B + 1 : B;
    if (B < 0 || width < 1 || width > 26 || T1 < 1 || T1 > CW * 64 || B + T1 > NW * 64 ||
        (!box && first >= (1ul << (31 - B)))) {
        fprintf(stderr, "out of range\n");
        return 1;
    }
    uint32_t n = (uint32_t)1 << width, base = box ? 0 : (uint32_t)(first << B), start = box ? 1 : 0;
    uint32_t m = n - start;
    cols = calloc((size_t)m * CW, sizeof(uint64_t));
    rows = malloc((size_t)m * sizeof(uint32_t));
    uint32_t *order = malloc((size_t)m * sizeof(uint32_t));
    if (!cols || !rows || !order) {
        fprintf(stderr, "out of memory\n");
        return 1;
    }
    int top = B + T1; /* bits of the row that the first T1 center cells read */
    for (uint32_t r = start; r < n; r++) {
        uint32_t i = r - start, x = base | r;
        uint64_t y[NW] = {x, 0, 0, 0};
        uint64_t *c = cols + (size_t)i * CW;
        rows[i] = x;
        order[i] = i;
        for (int t = 0; t < T1; t++) {
            int k = B + t;
            if ((y[k >> 6] >> (k & 63)) & 1) c[t >> 6] |= (uint64_t)1 << (63 - (t & 63));
            phi(y);
            for (int w = 0; w < NW; w++) {
                int lo = w * 64;
                if (lo >= top) y[w] = 0;
                else if (lo + 64 > top) y[w] &= ((uint64_t)1 << (top - lo)) - 1;
            }
        }
        if ((r & 0xFFFFF) == 0 && r) fprintf(stderr, "\r%u/%u rows", r, n);
    }
    if (n > 0xFFFFF) fprintf(stderr, "\n");
    qsort(order, m, sizeof(uint32_t), cmp_index);
    long groups = 0, members = 0;
    int best_edge = -1, best_groups = -1;
    uint32_t edge_pair[2] = {0, 0}, g0 = 0;
    for (uint32_t k = 1; k <= m; k++) {
        int l = k < m ? common_prefix(order[k - 1], order[k]) : -1;
        if (l < T1 && l > best_groups) best_groups = l;
        if (k < m) {
            uint32_t x = rows[order[k - 1]], y = rows[order[k]];
            if (x && y && left_edge(x) != left_edge(y) && l > best_edge) {
                best_edge = l;
                edge_pair[0] = x;
                edge_pair[1] = y;
            }
        }
        if (l != T1) {
            if (k - g0 >= 2) {
                groups++;
                members += k - g0;
                putchar('G');
                for (uint32_t j = g0; j < k; j++) printf(" %u", rows[order[j]]);
                putchar('\n');
            }
            g0 = k;
        }
    }
    printf("# groups=%ld members=%ld\n", groups, members);
    printf("# lcp_left_edge=%d pair=%u,%u\n", best_edge, edge_pair[0], edge_pair[1]);
    printf("# lcp_groups=%d\n", best_groups);
    free(cols);
    free(rows);
    free(order);
    return 0;
}
