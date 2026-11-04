// Exhaustive check of Lemma 1, Lemma 2 (abstract thresholds and the note's), on all digraphs with n vertices.
// All roots are fixed to vertex 0 by symmetry when root0 = 1. Planarity: n <= 4 always; n = 5 only K5 excluded; n = 6 is sampled and filtered by Kuratowski test.
// usage: ex2 n mode seed samples
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <vector>
#include <random>
#include <algorithm>
using namespace std;
typedef uint32_t u32;
typedef unsigned long long ull;
int n;
u32 out_[8], inn_[8], und_[8];
static inline u32 reachm(int s, u32 allowed) {
    u32 seen = 1u << s, fr = seen;
    while (fr) {
        int u = __builtin_ctz(fr); fr &= fr - 1;
        u32 nw = out_[u] & allowed & ~seen;
        seen |= nw; fr |= nw;
    }
    return seen;
}
static inline int connmax(u32 allowed) {
    int best = 0; u32 left = allowed;
    while (left) {
        int s = __builtin_ctz(left);
        u32 seen = 1u << s, fr = seen;
        while (fr) {
            int u = __builtin_ctz(fr); fr &= fr - 1;
            u32 nw = und_[u] & allowed & ~seen;
            seen |= nw; fr |= nw;
        }
        left &= ~seen;
        best = max(best, __builtin_popcount(seen));
    }
    return best;
}
ull cnt_dg, cnt_root, cnt_tree, cnt_pair, cnt_nomid, cnt_below, fail_l2, fail_l2h, cnt_paths, cnt_classes, fail_l1, cnt_lowseen, cnt_abs;
ull cnt_absnomid, cnt_abslow;
int par_[8];
u32 Q; int nq;
u32 R[8]; // reach in D[Q]
// spanning out-trees: enumerate parent choice for each non-root vertex of Q, acyclic
vector<int> verts;
static inline int pathmask(int v, int z, int *seq) {
    // returns path from z to v in seq, length, using par_
    int tmp[8], k = 0, x = v;
    while (x != z) { tmp[k++] = x; x = par_[x]; }
    tmp[k++] = z;
    for (int i = 0; i < k; i++) seq[i] = tmp[k - 1 - i];
    return k;
}
void report(const char *what, int z, int u, int v, int W) {
    printf("FAIL %s n=%d z=%d u=%d v=%d W=%d Q=%x arcs:", what, n, z, u, v, W, Q);
    for (int a = 0; a < n; a++) for (int b = 0; b < n; b++) if (out_[a] >> b & 1) printf(" %d>%d", a, b);
    printf(" par:");
    for (int a = 0; a < n; a++) if (Q >> a & 1) printf(" %d", par_[a]);
    printf("\n"); fflush(stdout);
}
// Lemma 2 with general thresholds: high iff f >= h, low iff f <= l, X the bound on connected components.
void pair_check(int z, int u, int v, int hthr, int lthr, int X, bool *abs_any, int W) {
    int a[8], b[8];
    int la = pathmask(u, z, a), lb = pathmask(v, z, b);
    u32 mask = 0;
    for (int i = 0; i < la; i++) mask |= 1u << a[i];
    for (int i = 0; i < lb; i++) mask |= 1u << b[i];
    if (connmax(Q & ~mask) > X) return;
    cnt_pair++;
    #define F(x) __builtin_popcount(R[x])
    if (F(z) < hthr) return;
    int ca = 0; while (ca + 1 < la && F(a[ca + 1]) >= hthr) ca++;
    int cb = 0; while (cb + 1 < lb && F(b[cb + 1]) >= hthr) cb++;
    // prefix property
    for (int i = ca + 1; i < la; i++) if (F(a[i]) >= hthr) { report("prefix", z, u, v, W); fail_l2++; }
    for (int i = cb + 1; i < lb; i++) if (F(b[i]) >= hthr) { report("prefix", z, u, v, W); fail_l2++; }
    if (ca + 1 < la && F(a[ca + 1]) > lthr) return;
    if (cb + 1 < lb && F(b[cb + 1]) > lthr) return;
    cnt_nomid++;
    if (ca + 1 < la || cb + 1 < lb) cnt_lowseen++;
    int c1 = a[ca], c2 = b[cb];
    int pick = ((R[c1] >> c2 & 1) && !(R[c2] >> c1 & 1)) ? c2 : c1;
    if (F(pick) < hthr) { report("L_not_high", z, u, v, W); fail_l2++; }
    for (int y = 0; y < n; y++) if ((R[pick] >> y & 1)) {
        bool inL = R[y] >> pick & 1;
        if (inL) continue;
        cnt_below++;
        if (F(y) >= hthr) { report("high_below", z, u, v, W); fail_l2h++; }
    }
}
void tree_rec(int idx, int z) {
    if (idx == (int)verts.size()) {
        // acyclic check
        for (int i = 0; i < (int)verts.size(); i++) {
            int x = verts[i], steps = 0;
            while (x != z && steps <= n) { x = par_[x]; steps++; }
            if (x != z) return;
        }
        cnt_tree++;
        for (int u = 0; u < n; u++) if (Q >> u & 1)
            for (int v = u; v < n; v++) if (Q >> v & 1) {
                // the note's thresholds, every W with z high
                for (int W = nq; 8 * nq > 7 * W; W++) {
                    int hthr = 7 * W / 8 + 1;               // f > 7W/8
                    int lthr = (W % 16 == 0 ? W / 16 - 1 : W / 16); // f < W/16
                    pair_check(z, u, v, hthr, lthr, 3 * nq / 4, nullptr, W);
                }
                // abstract thresholds: any h, l, X with X + 2 l < h, X >= 1. This is what the proof uses.
                for (int X = 0; X <= nq; X++) for (int l = 0; X + 2 * l < nq; l++) {
                    int h = X + 2 * l + 1;
                    cnt_abs++;
                    pair_check(z, u, v, h, l, X, nullptr, -1);
                }
            }
        return;
    }
    int x = verts[idx];
    u32 cand = inn_[x] & Q;
    while (cand) {
        int p = __builtin_ctz(cand); cand &= cand - 1;
        par_[x] = p;
        tree_rec(idx + 1, z);
    }
}
// Lemma 1: all simple paths from z in D[Q]
int seqp[8];
void l1_check(int k, u32 onp) {
    cnt_paths++;
    int m = seqp[k];
    u32 rest = Q & ~onp;
    // keys
    int headkey[8];
    for (int y = 0; y < n; y++) headkey[y] = -1;
    int tail[8];
    for (int i = 0; i <= k; i++) {
        u32 hs = out_[seqp[i]] & rest;
        while (hs) {
            int y = __builtin_ctz(hs); hs &= hs - 1;
            int key = (k - i) * 16 + y;
            if (headkey[y] < 0 || key < headkey[y]) { headkey[y] = key; tail[y] = seqp[i]; }
        }
    }
    int order[8], no = 0;
    for (int y = 0; y < n; y++) if (headkey[y] >= 0) order[no++] = y;
    sort(order, order + no, [&](int a, int b) { return headkey[a] < headkey[b]; });
    u32 left = rest;
    u32 rm = R[m];
    for (int i = 0; i < no; i++) {
        int y = order[i];
        if (!(left >> y & 1)) continue;
        u32 g = reachm(y, left);
        left &= ~g;
        cnt_classes++;
        bool inM = (R[tail[y]] >> m & 1) && (rm >> tail[y] & 1);
        if (inM) { if (g & ~rm) { fail_l1++; report("l1a", seqp[0], m, y, 0); } }
        else { if (g & rm) { fail_l1++; report("l1b", seqp[0], m, y, 0); } }
    }
    if (left) { fail_l1++; report("l1cover", seqp[0], m, 0, 0); }
    u32 nx = out_[m] & Q & ~onp;
    while (nx) {
        int v = __builtin_ctz(nx); nx &= nx - 1;
        seqp[k + 1] = v;
        l1_check(k + 1, onp | 1u << v);
    }
}
bool planar_small(int nn) {
    // n<=4 planar; n=5: only K5; n=6: reject if underlying has K5 or K33 minor by simple edge count and subset tests
    int m = 0;
    for (int i = 0; i < nn; i++) m += __builtin_popcount(und_[i]);
    m /= 2;
    if (nn <= 4) return true;
    if (nn == 5) return m < 10;
    if (m > 3 * nn - 6) return false;
    // n=6: check K5 subgraph on any 5 vertices, K33 subgraph on any split, K5 minor by contraction of one edge
    for (int d = 0; d < 6; d++) { // K5 on V - d
        bool ok = true;
        for (int a = 0; a < 6 && ok; a++) if (a != d) for (int b = a + 1; b < 6; b++) if (b != d) if (!(und_[a] >> b & 1)) { ok = false; break; }
        if (ok) return false;
    }
    for (int s = 0; s < 64; s++) if (__builtin_popcount(s) == 3 && (s & 1)) {
        bool ok = true;
        for (int a = 0; a < 6 && ok; a++) if (s >> a & 1) for (int b = 0; b < 6; b++) if (!(s >> b & 1)) if (!(und_[a] >> b & 1)) { ok = false; break; }
        if (ok) return false;
    }
    // contraction of an edge to K5
    for (int a = 0; a < 6; a++) for (int b = a + 1; b < 6; b++) if (und_[a] >> b & 1) {
        int vs[5], k = 0; u32 adjc = (und_[a] | und_[b]) & ~(1u << a | 1u << b);
        for (int i = 0; i < 6; i++) if (i != a && i != b) vs[k++] = i;
        bool ok = true;
        for (int i = 0; i < 4 && ok; i++) { if (!(adjc >> vs[i] & 1)) ok = false; for (int j = i + 1; j < 4; j++) if (!(und_[vs[i]] >> vs[j] & 1)) ok = false; }
        if (ok) return false;
    }
    return true;
}
void process(int z) {
    Q = reachm(z, (1u << n) - 1);
    nq = __builtin_popcount(Q);
    cnt_root++;
    for (int v = 0; v < n; v++) if (Q >> v & 1) R[v] = reachm(v, Q); else R[v] = 0;
    verts.clear();
    for (int v = 0; v < n; v++) if ((Q >> v & 1) && v != z) verts.push_back(v);
    tree_rec(0, z);
    seqp[0] = z;
    l1_check(0, 1u << z);
}
int main(int argc, char **argv) {
    n = atoi(argv[1]);
    int mode = atoi(argv[2]); // 0 exhaustive from root 0, 1 random
    ull seed = strtoull(argv[3], 0, 10);
    ull samples = strtoull(argv[4], 0, 10);
    int bits = n * (n - 1);
    vector<pair<int, int>> pairs;
    for (int a = 0; a < n; a++) for (int b = 0; b < n; b++) if (a != b) pairs.push_back({a, b});
    mt19937_64 rng(seed);
    ull total = mode == 0 ? (1ULL << bits) : samples;
    for (ull it = 0; it < total; it++) {
        ull g = mode == 0 ? it : rng();
        if (mode == 1) { double p = (rng() % 100 + 5) / 110.0; g = 0; for (int i = 0; i < bits; i++) if ((rng() % 10000) < p * 10000) g |= 1ULL << i; }
        for (int i = 0; i < n; i++) { out_[i] = inn_[i] = und_[i] = 0; }
        for (int i = 0; i < bits; i++) if (g >> i & 1) {
            int a = pairs[i].first, b = pairs[i].second;
            out_[a] |= 1u << b; inn_[b] |= 1u << a; und_[a] |= 1u << b; und_[b] |= 1u << a;
        }
        if (!planar_small(n)) continue;
        cnt_dg++;
        process(0);
    }
    printf("{\"n\":%d,\"mode\":%d,\"digraphs\":%llu,\"roots\":%llu,\"trees\":%llu,\"valid_pair_threshold_cases\":%llu,\"no_mid_cases\":%llu,\"cases_with_low_next\":%llu,\"below_vertices\":%llu,\"paths_l1\":%llu,\"classes_l1\":%llu,\"FAIL_l2_other\":%llu,\"FAIL_l2_high_below\":%llu,\"FAIL_l1\":%llu}\n",
           n, mode, cnt_dg, cnt_root, cnt_tree, cnt_pair, cnt_nomid, cnt_lowseen, cnt_below, cnt_paths, cnt_classes, fail_l2, fail_l2h, fail_l1);
}
