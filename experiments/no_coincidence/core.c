// Bitsliced evaluator for reversible circuits of gates  t ^= f(c1, c2),
// f a 2-input boolean function given as a 4-bit truth table (index 2*a+b).
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>

static inline uint64_t apply_f(int f, uint64_t a, uint64_t b) {
    uint64_t m0 = -(uint64_t)(f & 1), m1 = -(uint64_t)((f >> 1) & 1);
    uint64_t m2 = -(uint64_t)((f >> 2) & 1), m3 = -(uint64_t)((f >> 3) & 1);
    return (m0 & ~a & ~b) | (m1 & ~a & b) | (m2 & a & ~b) | (m3 & a & b);
}

// state: W rows of nwords each (row-major). In-place.
void eval_words(int W, int m, const int *g, uint64_t *st, long nwords) {
    for (int k = 0; k < m; k++) {
        int t = g[4*k], c1 = g[4*k+1], c2 = g[4*k+2], f = g[4*k+3];
        uint64_t *T = st + (long)t*nwords, *A = st + (long)c1*nwords, *B = st + (long)c2*nwords;
        for (long w = 0; w < nwords; w++) T[w] ^= apply_f(f, A[w], B[w]);
    }
}

// Count |C(S) ∩ S| where S = {inputs whose last nz wires are 0}; x = first W-nz wires
// (W-nz >= 6). Points enumerated by index s in [0, 2^(W-nz)), wire i = bit i of s.
#define CH 64
long count_S(int W, int nz, int m, const int *g, int nthreads) {
    int nx = W - nz;
    long nwords = 1L << (nx - 6);
    long nchunks = (nwords + CH - 1) / CH;
    long total = 0;
    static const uint64_t pat[6] = {0xAAAAAAAAAAAAAAAAULL, 0xCCCCCCCCCCCCCCCCULL,
        0xF0F0F0F0F0F0F0F0ULL, 0xFF00FF00FF00FF00ULL, 0xFFFF0000FFFF0000ULL, 0xFFFFFFFF00000000ULL};
    #pragma omp parallel for num_threads(nthreads) reduction(+:total) schedule(static)
    for (long ch = 0; ch < nchunks; ch++) {
        uint64_t st[64][CH];
        long w0 = ch * CH, nw = nwords - w0 < CH ? nwords - w0 : CH;
        for (int i = 0; i < W; i++)
            for (long w = 0; w < nw; w++) {
                uint64_t v;
                if (i < 6 && i < nx) v = pat[i];
                else if (i < nx) v = (((w0 + w) >> (i - 6)) & 1) ? ~0ULL : 0ULL;
                else v = 0;
                st[i][w] = v;
            }
        for (int k = 0; k < m; k++) {
            int t = g[4*k], c1 = g[4*k+1], c2 = g[4*k+2], f = g[4*k+3];
            for (long w = 0; w < nw; w++) st[t][w] ^= apply_f(f, st[c1][w], st[c2][w]);
        }
        for (long w = 0; w < nw; w++) {
            uint64_t acc = ~0ULL;
            for (int i = nx; i < W; i++) acc &= ~st[i][w];
            total += __builtin_popcountll(acc);
        }
    }
    return total;
}
