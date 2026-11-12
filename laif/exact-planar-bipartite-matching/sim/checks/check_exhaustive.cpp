// Independent exhaustive checks of notes/GENERAL_DFS.md, Lemmas 1, 2, 3, 5(a), 5(b) and Kao's Theorem 2 as used in Corollary 4.
// Written from the text of the note, no repo code. Vertices are bits. Pendant sink stars are carried as weights:
// w[v] = 1 + k_v, where k_v leaves hang from v by arcs v -> leaf. A leaf has reach 1. This is an honest unweighted digraph, planar
// if the base digraph is planar with a planar placement of the leaves (always possible: a star attached in a face).
//
// lane1 n            all digraphs on n vertices, all roots, all simple paths R from z: Lemma 1, partition, classes rooted
// lane2 n seed count pendant lane: Lemma 2 and 5, every F, every pair of ends, with the real constants; count=0 is exhaustive on digraphs
// lane3 n num den seed count  Lemma 3 proof steps on strongly connected digraphs, all pairs of disjoint paths, threshold num/den
// lane4 n            Kao Theorem 2: every DFS tree, every root, median in last-visit order leaves no SCC of more than half; plus negative control
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>
#include <algorithm>
#include <random>
#include <map>
#include <string>
#include <functional>
using namespace std;
typedef unsigned M;
typedef unsigned long long U;
static int n;
static M out_[8], in_[8];
static inline int ctz_(M x) { return __builtin_ctz(x); }
static inline int pc(M x) { return __builtin_popcount(x); }
static M fwd(int s, M allow) {
    M seen = 1u << s, fr = seen;
    while (fr) { int u = ctz_(fr); fr &= fr - 1; M nw = out_[u] & allow & ~seen; seen |= nw; fr |= nw; }
    return seen;
}
static M bwd(int s, M allow) {
    M seen = 1u << s, fr = seen;
    while (fr) { int u = ctz_(fr); fr &= fr - 1; M nw = in_[u] & allow & ~seen; seen |= nw; fr |= nw; }
    return seen;
}
static M scc(int s, M allow) { return fwd(s, allow) & bwd(s, allow); }
static void setg(U code) {
    int b = 0; memset(out_, 0, sizeof out_); memset(in_, 0, sizeof in_);
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (i != j) { if (code >> b & 1) { out_[i] |= 1u << j; in_[j] |= 1u << i; } b++; }
}
// K5 (underlying complete on 5 vertices) is the only nonplanar graph on at most 5 vertices. For n=6, K3,3 and K5-containing graphs need a test:
// a graph on 6 vertices is nonplanar iff it contains a subdivision of K5 or K3,3. We test by edge count and exhaustive minor search below.
static bool und(int a, int b) { return (out_[a] >> b & 1) || (out_[b] >> a & 1); }
static bool has_k5(M S) { // S has 5 vertices pairwise adjacent, or subdivision with one extra vertex on one edge
    vector<int> v; for (int i = 0; i < n; i++) if (S >> i & 1) v.push_back(i);
    int c = 0, m = v.size();
    for (int i = 0; i < m; i++) for (int j = i + 1; j < m; j++) if (und(v[i], v[j])) c++;
    return m == 5 && c == 10;
}
// Exact planarity for n<=6 by the Kuratowski minor test: contract or delete; graphs are tiny.
static bool nonplanar_rec(vector<vector<char>> a) {
    int m = a.size(); int e = 0;
    for (int i = 0; i < m; i++) for (int j = i + 1; j < m; j++) e += a[i][j];
    if (m < 5) return false;
    if (m >= 3 && e > 3 * m - 6) return true;
    if (m == 5) return e == 10;
    if (m == 6) { // K3,3 spanning?
        int id[6];
        for (int mask = 0; mask < 64; mask++) if (__builtin_popcount(mask) == 3 && (mask & 1)) {
            bool ok = true;
            for (int i = 0; i < 6 && ok; i++) for (int j = 0; j < 6 && ok; j++) if ((mask >> i & 1) && !(mask >> j & 1) && !a[i][j]) ok = false;
            if (ok) return true;
        }
    }
    // try contracting any edge (a minor test is complete by Wagner)
    for (int i = 0; i < m; i++) for (int j = i + 1; j < m; j++) if (a[i][j]) {
        vector<vector<char>> b(m - 1, vector<char>(m - 1, 0));
        vector<int> map_(m); int t = 0;
        for (int k = 0; k < m; k++) { if (k == j) map_[k] = i > j ? i - 1 : i; else map_[k] = t++; }
        // recompute map so i keeps its slot
        t = 0; for (int k = 0; k < m; k++) { if (k != j) map_[k] = t++; } map_[j] = map_[i];
        for (int x = 0; x < m; x++) for (int y = 0; y < m; y++) if (a[x][y] && map_[x] != map_[y]) b[map_[x]][map_[y]] = 1;
        if (nonplanar_rec(b)) return true;
    }
    return false;
}
static bool planar_now() {
    if (n <= 4) return true;
    vector<vector<char>> a(n, vector<char>(n, 0));
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (i != j && und(i, j)) a[i][j] = 1;
    return !nonplanar_rec(a);
}

// ------------------------------------------------------------- the Split Lemma, by the literal definitions
struct Cls { int head; int tail; M set; };
// path R[0..k], Q; returns classes that count. key = (k - i, id).
static int split(const int *R, int k1, M Q, Cls *res, long &fail) {
    M Rm = 0; for (int i = 0; i < k1; i++) Rm |= 1u << R[i];
    M rest = Q & ~Rm; int k = k1 - 1;
    int key1[8], key2[8], tail[8]; bool head[8];
    for (int z = 0; z < n; z++) { head[z] = false; key1[z] = 1000; }
    for (int i = 0; i < k1; i++) {
        M a = out_[R[i]] & rest;
        while (a) { int z = ctz_(a); a &= a - 1; int f = k - i; if (!head[z] || f < key1[z]) { head[z] = true; key1[z] = f; key2[z] = z; tail[z] = R[i]; } }
    }
    int e1[8], e2[8]; for (int y = 0; y < n; y++) e1[y] = 1000, e2[y] = 1000;
    for (int z = 0; z < n; z++) if (head[z]) {
        M r = fwd(z, rest); while (r) { int y = ctz_(r); r &= r - 1; if (key1[z] < e1[y] || (key1[z] == e1[y] && key2[z] < e2[y])) { e1[y] = key1[z]; e2[y] = key2[z]; } }
    }
    int c = 0; M cov = 0;
    for (int z = 0; z < n; z++) if (head[z] && e1[z] == key1[z] && e2[z] == key2[z]) {
        M K = 0; for (int y = 0; y < n; y++) if ((rest >> y & 1) && e1[y] == key1[z] && e2[y] == key2[z]) K |= 1u << y;
        res[c++] = {z, tail[z], K}; if (cov & K) fail++; cov |= K;
        if (fwd(z, K) != K) fail++;
    }
    if (cov != rest) fail++;
    return c;
}

static long l1_paths = 0, l1_classes = 0, l1_fail = 0, l1_graphs = 0, l1_a = 0, l1_b = 0;
static void l1_rec(int *R, int k1, M onpath, M Q) {
    Cls c[8]; int nc = split(R, k1, Q, c, l1_fail);
    int m = R[k1 - 1]; M Mm = scc(m, Q), rm = fwd(m, Q);
    l1_paths++;
    for (int i = 0; i < nc; i++) {
        l1_classes++;
        if (Mm >> c[i].tail & 1) { l1_a++; if (c[i].set & ~rm) l1_fail++; }
        else { l1_b++; if (c[i].set & rm) l1_fail++; }
    }
    M a = out_[m] & Q & ~onpath;
    while (a) { int z = ctz_(a); a &= a - 1; R[k1] = z; l1_rec(R, k1 + 1, onpath | 1u << z, Q); }
}
static void lane1() {
    int bits = n * (n - 1); int R[8]; M all = (1u << n) - 1;
    for (U code = 0; code < (1ULL << bits); code++) {
        setg(code); l1_graphs++;
        for (int z = 0; z < n; z++) { M Q = fwd(z, all); R[0] = z; l1_rec(R, 1, 1u << z, Q); }
    }
    printf("{\"lane\":1,\"n\":%d,\"digraphs\":%ld,\"paths\":%ld,\"classes\":%ld,\"tail_in\":%ld,\"tail_out\":%ld,\"fail\":%ld}\n", n, l1_graphs, l1_paths, l1_classes, l1_a, l1_b, l1_fail);
}

// ------------------------------------------------------------- Lemma 2 and Lemma 5 with pendant weights
static int wt[8];
static long long W_;
static long wsum(M s) { long t = 0; while (s) { int v = ctz_(s); s &= s - 1; t += wt[v]; } return t; }
struct L2 { long tries, valid, midcase, pivot, lemma2_reachchecks, fail2, fail2high, fail5a, midclasses, cycles, fail5b, l5bclasses, l5bv, fail5btail, noL, nonsimple, trees; };
static L2 l2;
// connected components of the underlying graph on allowed, largest weight.
static long maxcomp(M allow) {
    long best = 0; M left = allow;
    while (left) {
        int s = ctz_(left); M seen = 1u << s, fr = seen;
        while (fr) { int u = ctz_(fr); fr &= fr - 1; M nw = (out_[u] | in_[u]) & allow & ~seen; seen |= nw; fr |= nw; }
        left &= ~seen; best = max(best, wsum(seen));
    }
    return best;
}
static inline bool high(long f) { return 8 * f > 7 * W_; }
static inline bool low(long f) { return 16 * f < W_; }
static long fQ(int v, M Q) { return wsum(fwd(v, Q)); }

// Weighted version of the split: a class of base vertices weighs wsum; leaves of vertices on R are single classes of size 1 and never bad, when W >= 2.
static void all_cycles(M L, vector<vector<int>> &out) {
    // simple directed cycles of D[L] with least vertex as start, plus single vertices.
    for (int s = 0; s < n; s++) if (L >> s & 1) {
        out.push_back({s});
        vector<int> st = {s};
        function<void(M)> *dummy = nullptr; (void)dummy;
        struct R { static void go(int s, M L, vector<int> &st, M on, vector<vector<int>> &out) {
            int u = st.back(); M a = out_[u] & L;
            if (a >> s & 1 && st.size() >= 2) out.push_back(st);
            a &= ~on; while (a) { int v = ctz_(a); a &= a - 1; if (v > s) { st.push_back(v); go(s, L, st, on | 1u << v, out); st.pop_back(); } }
        } };
        R::go(s, L, st, 1u << s, out);
    }
}
static bool heavy_left(M L, M S, int num, int den) {
    M left = L & ~S; int sz = pc(L);
    while (left) { int s = ctz_(left); M c = scc(s, L & ~S); left &= ~c; if (den * pc(c) > num * sz) return true; }
    return false;
}
static void check_pass(int z, M Q, const int *par, int e1, int e2) {
    // paths of F from z to e1, e2
    int p[2][8], pl[2];
    for (int t = 0; t < 2; t++) { int v = t ? e2 : e1, b[8], c = 0; while (true) { b[c++] = v; if (v == z) break; v = par[v]; } pl[t] = c; for (int i = 0; i < c; i++) p[t][i] = b[c - 1 - i]; }
    M U_ = 0; for (int t = 0; t < 2; t++) for (int i = 0; i < pl[t]; i++) U_ |= 1u << p[t][i];
    long big = maxcomp(Q & ~U_);
    long q = wsum(Q);
    // leaves of removed vertices are singletons; those are small. The hypothesis of the lemma:
    if (4 * big > 3 * q) return;
    l2.valid++;
    int ci[2], ni[2];
    for (int t = 0; t < 2; t++) {
        int i = 0; while (i + 1 < pl[t] && high(fQ(p[t][i + 1], Q))) i++;
        ci[t] = p[t][i]; ni[t] = i + 1 < pl[t] ? p[t][i + 1] : -1;
    }
    // a path could also end at a leaf of its last vertex: that n_i has reach 1, which is low once W > 16, and changes nothing
    int mid = -1;
    for (int t = 0; t < 2; t++) if (ni[t] >= 0 && !low(fQ(ni[t], Q))) { mid = t; break; }
    if (mid >= 0) {
        l2.midcase++;
        int R[8], k1 = 0; for (int i = 0; i < pl[mid]; i++) { R[k1++] = p[mid][i]; if (p[mid][i] == ni[mid]) break; }
        Cls c[8]; long fl = 0; int nc = split(R, k1, Q, c, fl); l2.fail5a += fl;
        for (int i = 0; i < nc; i++) { l2.midclasses++; if (16 * wsum(c[i].set) > 15 * W_) l2.fail5a++; }
        return;
    }
    l2.pivot++;
    bool c1c2 = fwd(ci[0], Q) >> ci[1] & 1, c2c1 = fwd(ci[1], Q) >> ci[0] & 1;
    int nm = (c1c2 && !c2c1) ? ci[1] : ci[0];
    M L = scc(nm, Q);
    if (!high(fQ(nm, Q))) l2.fail2++;
    M below = fwd(nm, Q) & ~L; M b = below;
    while (b) { int y = ctz_(b); b &= b - 1; l2.lemma2_reachchecks++; if (high(fQ(y, Q))) l2.fail2++; }
    // Lemma 5(b), for every cycle C of D[L] with no heavy component left, and every vertex c of least depth
    vector<vector<int>> cy; all_cycles(L, cy);
    int depth[8]; memset(depth, -1, sizeof depth); depth[z] = 0;
    for (int it = 0; it < n; it++) for (int v = 0; v < n; v++) if ((Q >> v & 1) && v != z && depth[par[v]] >= 0) depth[v] = depth[par[v]] + 1;
    int sizeL = pc(L);
    for (auto &C : cy) {
        M Cm = 0; for (int v : C) Cm |= 1u << v;
        if (heavy_left(L, Cm, 3, 4)) continue;
        int d = 100; for (int v : C) d = min(d, depth[v]);
        for (int ix = 0; ix < (int)C.size(); ix++) if (depth[C[ix]] == d) {
            int cc = C[ix]; int b_[8], bl = 0, v = cc; while (true) { b_[bl++] = v; if (v == z) break; v = par[v]; }
            int R[8], k1 = 0; for (int i = bl - 1; i >= 0; i--) R[k1++] = b_[i];
            for (int j = 1; j < (int)C.size(); j++) R[k1++] = C[(ix + j) % C.size()];
            M on = 0; bool simple = true; for (int i = 0; i < k1; i++) { if (on >> R[i] & 1) simple = false; on |= 1u << R[i]; if (i && !(out_[R[i - 1]] >> R[i] & 1)) simple = false; }
            if (!simple) { l2.nonsimple++; continue; }
            l2.cycles++;
            Cls cl[8]; long fl = 0; int nc = split(R, k1, Q, cl, fl); l2.fail5b += fl;
            for (int i = 0; i < nc; i++) {
                if (16 * wsum(cl[i].set) <= 15 * W_) continue;
                l2.l5bclasses++;
                if (!(L >> cl[i].tail & 1) || !(L >> cl[i].head & 1)) l2.fail5btail++;
                M Qp = cl[i].set, s_ = Qp;
                while (s_) {
                    int vv = ctz_(s_); s_ &= s_ - 1;
                    if (!high(wsum(fwd(vv, Qp)))) continue;
                    l2.l5bv++;
                    M S = scc(vv, Qp);
                    if (S & ~(L & ~Cm)) l2.fail5b++;
                    if (4 * pc(S) > 3 * sizeL) l2.fail5b++;
                }
            }
        }
    }
}
static void trees(int z, M Q, int v, int *par) {
    // enumerate every spanning out-tree of D[Q] from z, by a parent choice per vertex, rejecting cycles at the end
    while (v < n && (!(Q >> v & 1) || v == z)) v++;
    if (v == n) {
        for (int x = 0; x < n; x++) if ((Q >> x & 1) && x != z) { int y = x, c = 0; while (y != z && c < 8) { y = par[y]; c++; } if (y != z) return; }
        l2.trees++;
        for (int e1 = 0; e1 < n; e1++) if (Q >> e1 & 1) for (int e2 = e1; e2 < n; e2++) if (Q >> e2 & 1) { l2.tries++; check_pass(z, Q, par, e1, e2); check_pass(z, Q, par, e2, e1); }
        return;
    }
    M a = in_[v] & Q;
    while (a) { int u = ctz_(a); a &= a - 1; par[v] = u; trees(z, Q, v + 1, par); }
}
static void lane2(unsigned seed, long count) {
    int bits = n * (n - 1); mt19937_64 rng(seed); M all = (1u << n) - 1;
    static const int opts[] = {1, 2, 4, 6, 8, 11, 16, 25, 40, 60};
    int no = sizeof opts / sizeof opts[0]; int par[8];
    long dg = 0, planar = 0;
    long total = count ? count : (1L << bits);
    for (long it = 0; it < total; it++) {
        U code = count ? (rng() & ((1ULL << bits) - 1)) : (U)it;
        setg(code); dg++;
        if (!planar_now()) continue;
        planar++;
        int tries = 6;
        for (int t = 0; t < tries; t++) {
            for (int v = 0; v < n; v++) wt[v] = opts[rng() % no];
            for (int z = 0; z < n; z++) {
                M Q = fwd(z, all); long q = wsum(Q);
                if (q < 17) continue; // below this nothing is low, and the leaves are not separate from the base
                W_ = q + (rng() % 3 == 0 ? (long)(rng() % (q / 16 + 1)) : 0);
                if (!high(q)) continue;
                trees(z, Q, 0, par);
            }
        }
    }
    printf("{\"lane\":2,\"n\":%d,\"digraphs\":%ld,\"planar\":%ld,\"trees\":%ld,\"pairs\":%ld,\"valid\":%ld,\"mid\":%ld,\"pivot\":%ld,\"reach_checks\":%ld,\"fail_L2\":%ld,\"fail_5a\":%ld,\"mid_classes\":%ld,\"cycles\":%ld,\"bad_after_cycle\":%ld,\"high_v\":%ld,\"fail_5b\":%ld,\"fail_tail\":%ld,\"R_not_simple\":%ld}\n",
           n, dg, planar, l2.trees, l2.tries, l2.valid, l2.midcase, l2.pivot, l2.lemma2_reachchecks, l2.fail2, l2.fail5a, l2.midclasses, l2.cycles, l2.l5bclasses, l2.l5bv, l2.fail5b, l2.fail5btail, l2.nonsimple);
}

// ------------------------------------------------------------- Lemma 3, proof steps
static int TN, TD; // threshold
static long l3_pairs = 0, l3_fail = 0, l3_graphs = 0, l3_cyc = 0, l3_single = 0, l3_link = 0, l3_disjoint = 0, l3_dropped = 0, l3_failp[8];
static M heavy(M L, M S) { // heavy component of D[L\S] or 0
    M left = L & ~S; int sz = pc(L);
    while (left) { int s = ctz_(left); M c = scc(s, L & ~S); left &= ~c; if (TD * pc(c) > TN * sz) return c; }
    return 0;
}
static bool get_link(int a, M X, int b, M Y, M forbid_inner, vector<int> &out, mt19937_64 &rng) {
    M both = X & Y;
    if (!both) { l3_disjoint++; return false; }
    // pick a random common vertex
    vector<int> vs; { M t = both; while (t) { vs.push_back(ctz_(t)); t &= t - 1; } }
    int w = vs[rng() % vs.size()];
    // a -> w inside X, by a BFS with random neighbour order
    int pa[8], pb[8]; memset(pa, -1, sizeof pa); memset(pb, -1, sizeof pb);
    { vector<int> q = {a}; pa[a] = a; for (size_t i = 0; i < q.size(); i++) { int u = q[i]; vector<int> nb; M t = out_[u] & X; while (t) { nb.push_back(ctz_(t)); t &= t - 1; } shuffle(nb.begin(), nb.end(), rng); for (int v : nb) if (pa[v] < 0) { pa[v] = u; q.push_back(v); } } }
    { vector<int> q = {b}; pb[b] = b; for (size_t i = 0; i < q.size(); i++) { int u = q[i]; vector<int> nb; M t = in_[u] & Y; while (t) { nb.push_back(ctz_(t)); t &= t - 1; } shuffle(nb.begin(), nb.end(), rng); for (int v : nb) if (pb[v] < 0) { pb[v] = u; q.push_back(v); } } }
    if (pa[w] < 0 || pb[w] < 0) { l3_failp[0]++; return false; }
    vector<int> first; { int v = w; while (v != a) { first.push_back(v); v = pa[v]; } first.push_back(a); reverse(first.begin(), first.end()); }
    vector<int> second; { int v = w; while (v != b) { second.push_back(v); v = pb[v]; } second.push_back(b); }
    size_t k = 0; bool got = false; int at = -1;
    for (; k < first.size() && !got; k++) for (size_t j = 0; j < second.size(); j++) if (second[j] == first[k]) { at = j; got = true; break; }
    k--;
    out.clear();
    for (size_t i = 0; i <= k; i++) out.push_back(first[i]);
    for (size_t j = at + 1; j < second.size(); j++) out.push_back(second[j]);
    M on = 0; for (int v : out) { if (on >> v & 1) { l3_failp[1]++; return false; } on |= 1u << v; }
    for (size_t i = 1; i + 1 < out.size(); i++) if (forbid_inner >> out[i] & 1) { l3_failp[2]++; return false; }
    for (size_t i = 0; i + 1 < out.size(); i++) if (!(out_[out[i]] >> out[i + 1] & 1)) { l3_failp[3]++; return false; }
    return true;
}
// Trim, as in the note. Returns false if dropped.
static bool trim(M L, const vector<int> &P, M O, vector<int> &seg, M &Xo, M &Yo) {
    M S = O;
    if (!heavy(L, O)) { return false; }
    int s = P.size(); int i = -1; M pref = 0;
    for (int t = 0; t < s; t++) { M before = S | pref; pref |= 1u << P[t]; if (!heavy(L, O | pref)) { i = t; Xo = heavy(L, before); break; } }
    if (i < 0) { l3_failp[4]++; return false; }
    if (!(Xo >> P[i] & 1)) l3_failp[5]++;
    int h = -1; M segm = 0;
    for (int t = i; t >= 0; t--) { M before = O | segm; segm |= 1u << P[t]; if (!heavy(L, O | segm)) { h = t; Yo = heavy(L, before); break; } }
    if (h < 0) { l3_failp[4]++; return false; }
    if (!(Yo >> P[h] & 1)) l3_failp[6]++;
    seg.assign(P.begin() + h, P.begin() + i + 1);
    return true;
}
static void lemma3(M L, const vector<int> &A, const vector<int> &B, mt19937_64 &rng) {
    M Am = 0, Bm = 0; for (int v : A) Am |= 1u << v; for (int v : B) Bm |= 1u << v;
    vector<int> Ap, Bp, U_; M X1 = 0, Y1 = 0, X2 = 0, Y2 = 0; M Apm = 0, Bpm = 0;
    bool ka = trim(L, A, Bm, Ap, X1, Y1);
    for (int v : Ap) Apm |= 1u << v;
    bool kb = trim(L, B, Apm, Bp, X2, Y2);
    for (int v : Bp) Bpm |= 1u << v;
    if (heavy(L, Apm | Bpm)) l3_failp[7]++;
    if (!ka && !kb) { l3_fail++; return; }
    if (!ka || !kb) { U_ = ka ? Ap : Bp; l3_dropped++; }
    else {
        int a = Ap.back(), b = Bp[0];
        if ((X1 & (Bpm | (Apm & ~(1u << a)))) || (Y2 & (Apm | (Bpm & ~(1u << b))))) l3_fail++;
        vector<int> mid;
        if (!get_link(a, X1, b, Y2, Apm | Bpm, mid, rng)) { l3_fail++; return; }
        l3_link++;
        U_ = Ap; for (size_t i = 1; i + 1 < mid.size(); i++) U_.push_back(mid[i]); for (int v : Bp) U_.push_back(v);
    }
    M Um = 0; for (int v : U_) { if (Um >> v & 1) { l3_fail++; return; } Um |= 1u << v; }
    for (size_t i = 0; i + 1 < U_.size(); i++) if (!(out_[U_[i]] >> U_[i + 1] & 1)) { l3_fail++; return; }
    if (heavy(L, Um)) { l3_fail++; return; }
    // Close
    int t = -1; M pref = 0, X = 0;
    for (size_t i = 0; i < U_.size(); i++) { M before = pref; pref |= 1u << U_[i]; if (!heavy(L, pref)) { t = i; X = heavy(L, before); break; } }
    if (t < 0) { l3_fail++; return; }
    int s = -1; M seg = 0, Y = 0;
    for (int i = t; i >= 0; i--) { M before = seg; seg |= 1u << U_[i]; if (!heavy(L, seg)) { s = i; Y = heavy(L, before); break; } }
    if (s < 0) { l3_fail++; return; }
    vector<int> C;
    if (s == t) { C = {U_[t]}; l3_single++; }
    else {
        M inner = 0; for (int i = s; i <= t; i++) inner |= 1u << U_[i];
        vector<int> q; if (!get_link(U_[t], X, U_[s], Y, inner, q, rng)) { l3_fail++; return; }
        for (int i = s; i <= t; i++) C.push_back(U_[i]);
        for (size_t i = 1; i + 1 < q.size(); i++) C.push_back(q[i]);
        l3_cyc++;
    }
    M Cm = 0; for (int v : C) { if (Cm >> v & 1) l3_fail++; Cm |= 1u << v; }
    if (C.size() > 1) for (size_t i = 0; i < C.size(); i++) if (!(out_[C[i]] >> C[(i + 1) % C.size()] & 1)) l3_fail++;
    if (heavy(L, Cm)) l3_fail++;
}
static void allpaths(M L, vector<vector<int>> &res) {
    res.push_back({});
    for (int s = 0; s < n; s++) if (L >> s & 1) {
        struct R { static void go(M L, vector<int> &st, M on, vector<vector<int>> &res) {
            res.push_back(st); M a = out_[st.back()] & L & ~on;
            while (a) { int v = ctz_(a); a &= a - 1; st.push_back(v); go(L, st, on | 1u << v, res); st.pop_back(); }
        } };
        vector<int> st = {s}; R::go(L, st, 1u << s, res);
    }
}
static void lane3(unsigned seed, long count) {
    int bits = n * (n - 1); mt19937_64 rng(seed); M all = (1u << n) - 1;
    long total = count ? count : (1L << bits); long sc = 0;
    for (long it = 0; it < total; it++) {
        U code = count ? (rng() & rng() & ((1ULL << bits) - 1)) | (rng() & ((1ULL << bits) - 1) & rng()) : (U)it;
        setg(code); l3_graphs++;
        if (scc(0, all) != all) continue;
        sc++;
        vector<vector<int>> ps; allpaths(all, ps);
        size_t lim = count ? 4000 : ps.size() * ps.size();
        if (count) {
            for (size_t c = 0; c < lim; c++) {
                auto &A = ps[rng() % ps.size()]; auto &B = ps[rng() % ps.size()];
                M Am = 0, Bm = 0; for (int v : A) Am |= 1u << v; for (int v : B) Bm |= 1u << v;
                if (Am & Bm) continue;
                if (heavy(all, Am | Bm)) continue;
                l3_pairs++; lemma3(all, A, B, rng);
            }
        } else for (auto &A : ps) for (auto &B : ps) {
            M Am = 0, Bm = 0; for (int v : A) Am |= 1u << v; for (int v : B) Bm |= 1u << v;
            if (Am & Bm) continue;
            if (heavy(all, Am | Bm)) continue;
            l3_pairs++; lemma3(all, A, B, rng);
        }
    }
    printf("{\"lane\":3,\"n\":%d,\"thresh\":\"%d/%d\",\"digraphs\":%ld,\"strong\":%ld,\"pairs\":%ld,\"cycles\":%ld,\"single\":%ld,\"links\":%ld,\"dropped\":%ld,\"heavy_disjoint\":%ld,\"fail\":%ld,\"failp\":[%ld,%ld,%ld,%ld,%ld,%ld,%ld,%ld]}\n",
           n, TN, TD, l3_graphs, sc, l3_pairs, l3_cyc, l3_single, l3_link, l3_dropped, l3_disjoint, l3_fail, l3_failp[0], l3_failp[1], l3_failp[2], l3_failp[3], l3_failp[4], l3_failp[5], l3_failp[6], l3_failp[7]);
}

// ------------------------------------------------------------- Kao's Theorem 2, every DFS of every strongly connected digraph
static long l4_trees = 0, l4_fail = 0, l4_ctrl_fail = 0, l4_ctrl = 0, l4_graphs = 0;
static void l4_check(int r, const vector<int> &order, const int *parent) {
    // order is last-visit order of a real DFS. f = median.
    int N = order.size(); int fidx = (N + 1) / 2 - 1; // smallest f with f >= N/2
    if (N == 0) return;
    int v = order[fidx]; M P = 0; int x = v; while (true) { P |= 1u << x; if (x == r) break; x = parent[x]; }
    M all = 0; for (int y : order) all |= 1u << y;
    M left = all & ~P; int big = 0;
    while (left) { int s = ctz_(left); M c = scc(s, all & ~P); left &= ~c; big = max(big, pc(c)); }
    l4_trees++;
    if (2 * big > N) l4_fail++;
    // negative control: the first vertex of the order, whose path is short
    int v2 = order[0]; P = 0; x = v2; while (true) { P |= 1u << x; if (x == r) break; x = parent[x]; }
    left = all & ~P; big = 0;
    while (left) { int s = ctz_(left); M c = scc(s, all & ~P); left &= ~c; big = max(big, pc(c)); }
    l4_ctrl++; if (2 * big > N) l4_ctrl_fail++;
}
static void dfs_all(int u, M seen, int *parent, vector<int> &post, vector<int> &stack_, int r) {
    // every possible DFS: at u choose any unseen out-neighbour next, or finish u if none
    M a = out_[u] & ~seen;
    if (!a) {
        post.push_back(u); stack_.pop_back();
        if (stack_.empty()) { l4_check(r, post, parent); }
        else { int w = stack_.back(); dfs_all(w, seen, parent, post, stack_, r); }
        stack_.push_back(u); post.pop_back();
        return;
    }
    while (a) { int v = ctz_(a); a &= a - 1; parent[v] = u; stack_.push_back(v); dfs_all(v, seen | 1u << v, parent, post, stack_, r); stack_.pop_back(); }
}
static void lane4() {
    int bits = n * (n - 1); M all = (1u << n) - 1;
    for (U code = 0; code < (1ULL << bits); code++) {
        setg(code); if (scc(0, all) != all) continue;
        l4_graphs++;
        for (int r = 0; r < n; r++) { int parent[8]; vector<int> post, st = {r}; dfs_all(r, 1u << r, parent, post, st, r); }
    }
    printf("{\"lane\":4,\"n\":%d,\"strong\":%ld,\"dfs_runs\":%ld,\"fail\":%ld,\"control_runs\":%ld,\"control_fired\":%ld}\n", n, l4_graphs, l4_trees, l4_fail, l4_ctrl, l4_ctrl_fail);
}

int main(int argc, char **argv) {
    string m = argv[1]; n = atoi(argv[2]);
    if (m == "lane1") lane1();
    else if (m == "lane2") lane2(atoi(argv[3]), atol(argv[4]));
    else if (m == "lane3") { TN = atoi(argv[3]); TD = atoi(argv[4]); lane3(atoi(argv[5]), atol(argv[6])); }
    else if (m == "lane4") lane4();
    else if (m == "planar") { // self test of planar_now on the classic cases
        n = 5; setg((1ULL << 20) - 1); printf("K5 planar? %d\n", planar_now());
        n = 6; setg(0); for (int a : {0, 1, 2}) for (int b : {3, 4, 5}) { out_[a] |= 1u << b; in_[b] |= 1u << a; } printf("K33 planar? %d\n", planar_now());
        n = 6; setg(0); for (int a = 0; a < 6; a++) { int b = (a + 1) % 6; out_[a] |= 1u << b; in_[b] |= 1u << a; } printf("C6 planar? %d\n", planar_now());
        n = 5; setg((1ULL << 20) - 1); out_[0] &= ~2u; in_[1] &= ~1u; out_[1] &= ~1u; in_[0] &= ~2u; printf("K5-e planar? %d\n", planar_now());
    }
    return 0;
}
