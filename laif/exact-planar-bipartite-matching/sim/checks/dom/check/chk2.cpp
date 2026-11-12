// Independent checker for notes/DOMINATORS.md. Shares no code with sim/. All definitions are taken from the note's text.
//   chk exh N [part parts]       all digraphs on N vertices with root 0 reaching all, all entry sets, all simple paths
//   chk abs K                    all tables (A,B) on K positions: Lemmas 2b,5,6, marks, Lemma 7, algebraic form
//   chk absrand K SEED SECS      random tables
//   chk rnd SEED SECS            random digraphs and structured long paths
//   chk chain N                  full recursion on all digraphs on N vertices
//   chk chainrnd SEED SECS       full recursion on random digraphs
//   chk ctl SEED SECS            negative controls
#include <algorithm>
#include <cassert>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <random>
#include <string>
#include <vector>
using namespace std;
typedef unsigned long long u64;
static const int INF = 1000000, NONE = -1, MAXK = 62, MAXL = 7;
static int CTL = 0;
static bool NOEXCL = false;
static map<string, long long *> REG;
static long long &reg(const char *s) {
    auto it = REG.find(s);
    if (it != REG.end()) return *it->second;
    long long *p = new long long(0);
    REG[s] = p;
    return *p;
}
#define CNT(name) do { static long long &c_ = reg(name); c_++; } while (0)
#define MAXC(name, v) do { static long long &c_ = reg(name); if ((long long)(v) > c_) c_ = (v); } while (0)
static int WIT = 3;
static void dumpg();
#define FAIL(name, cond) do { if (cond) { static long long &c_ = reg("FAIL." name); c_++; if (WIT > 0 && !CTL) { WIT--; printf("WITNESS %s line %d\n", name, __LINE__); dumpg(); } } } while (0)

static int n;
static u64 adj_[64], radj_[64];
static u64 gQ, gE;
static int gR[64], gk;
static void dumpg() {
    printf("n=%d Q=%llx E=%llx R=", n, gQ, gE);
    for (int i = 1; i <= gk; i++) printf("%d ", gR[i]);
    printf("\narcs:");
    for (int u = 0; u < n; u++) for (int v = 0; v < n; v++) if (adj_[u] >> v & 1) printf(" %d>%d", u, v);
    printf("\n");
}
static inline int ctz(u64 x) { return __builtin_ctzll(x); }
static inline int pc(u64 x) { return __builtin_popcountll(x); }
static inline u64 bit(int v) { return 1ULL << v; }
static u64 reach(u64 src, u64 allow) {
    u64 seen = src & allow, fr = seen;
    while (fr) {
        int v = ctz(fr);
        fr &= fr - 1;
        u64 nw = adj_[v] & allow & ~seen;
        seen |= nw;
        fr |= nw;
    }
    return seen;
}
static void build_radj() {
    for (int v = 0; v < n; v++) radj_[v] = 0;
    for (int u = 0; u < n; u++) for (int v = 0; v < n; v++) if (adj_[u] >> v & 1) radj_[v] |= bit(u);
}

// ----------------- Section 5 on tables -----------------
struct Sec5 {
    int k;
    int m[MAXK + 2];
    int lam[MAXL][MAXK + 2], dlt[MAXL][MAXK + 2];
    int levels;
};

// Adef/Bdef are the note's exact values, Ac/Bc what vertices compute. truem may be null: then m is by the definition.
static bool closed_(const int *A, const int *B, int j, int x) {
    for (int t = j + 1; t < x; t++) if (!(A[t] >= j && B[t] < x)) return false;
    return true;
}

static void sec5(int k, const int *Adef, const int *Bdef, const int *Ac, const int *Bc, Sec5 &o) {
    o.k = k;
    int L = 0;
    while ((1 << L) < k) L++;
    o.levels = L;
    for (int l = 0; l < L; l++) for (int t = 0; t <= k + 1; t++) o.lam[l][t] = o.dlt[l][t] = NONE;
    for (int j = 1; j <= k; j++) o.m[j] = j + 1;
    static int X[MAXL][MAXK + 2], first[MAXL][MAXK + 2], g[MAXL][MAXK + 3];
    // Step 2
    for (int lev = 0; lev < L; lev++) {
        int size = 1 << lev;
        for (int lo = 1; lo + size <= k; lo += 2 * size) {
            int c = lo + size - 1, r = min(k, lo + 2 * size - 1);
            int pref = -INF;
            int last = NONE;
            for (int x = c + 1; x <= r + 1; x++) {
                if (x >= c + 2) {
                    bool good = pref < x || CTL == 8;
                    if (good) last = x;
                }
                g[lev][x] = last;
                if (x <= r) pref = max(pref, Bc[x]);
            }
            int tcirc = INF;
            for (int a = lo; a <= c; a++) first[lev][a] = 0;
            for (int t = r; t >= c + 1; t--) {
                if (Ac[t] < lo) tcirc = t;
                else if (Ac[t] <= c) first[lev][Ac[t]] = t;
            }
            int run = min(r + 1, tcirc);
            for (int j = lo; j <= c; j++) {
                X[lev][j] = run;
                if (first[lev][j]) run = min(run, first[lev][j]);
                // X by its definition
                int d = r + 1;
                for (int t = c + 1; t <= r; t++) if (Ac[t] < j) { d = t; break; }
                FAIL("X_formula", d != X[lev][j]);
            }
            int sa = INF, sb = -INF;
            for (int j = c; j >= lo; j--) {
                int x = g[lev][X[lev][j]];
                bool cand = x != NONE && (sa >= j || CTL == 6) && (sb < x || CTL == 7);
                // Lemma 5 against the definition, with the note's exact A and B
                int truth = NONE;
                for (int y = r + 1; y >= c + 2; y--) if (closed_(Adef, Bdef, j, y)) { truth = y; break; }
                FAIL("lemma5", (cand ? x : NONE) != truth);
                if (cand) { o.m[j] = max(o.m[j], x); CNT("n.candidates"); }
                sa = min(sa, Ac[j]);
                sb = max(sb, Bc[j]);
            }
        }
    }
    // m against the definition: largest x with (j,x) closed
    for (int j = 1; j <= k; j++) {
        int d = j + 1;
        for (int x = k + 1; x > j; x--) if (closed_(Adef, Bdef, j, x)) { d = x; break; }
        FAIL("m_vs_closed", d != o.m[j]);
    }
    // Lemma 2(b), algebraic
    for (int j = 1; j <= k; j++) for (int jj = j + 1; jj < o.m[j] && jj <= k; jj++) FAIL("laminar", o.m[jj] > o.m[j]);
    // Step 3
    u64 occ = 0;
    for (int lev = 0; lev < L; lev++) {
        int size = 1 << lev;
        occ = 0;
        for (int lo = 1; lo + size <= k; lo += 2 * size) {
            int c = lo + size - 1, r = min(k, lo + 2 * size - 1);
            int ch[MAXK + 2], s = 0;
            for (int j = lo; j <= c; j++) if (o.m[j] > c + 1 || (CTL == 12 && o.m[j] > c)) ch[s++] = j;
            MAXC("max.chain", s);
            for (int i = 0; i + 1 < s; i++) {
                FAIL("chain_sorted", o.m[ch[i]] < o.m[ch[i + 1]]);
                if (o.m[ch[i]] == o.m[ch[i + 1]]) CNT("n.equal_m");
            }
            for (int i = 0; i < s; i++) if (o.m[ch[i]] > r + 1) CNT("n.m_beyond_segment");
            int cur = NONE;
            for (int a = lo; a <= c; a++) {
                if (o.m[a] > c + 1 || (CTL == 12 && o.m[a] > c)) cur = a;
                o.lam[lev][a] = cur;
            }
            // Lemma 6
            for (int i = 0; i + 1 < s; i++) {
                int mi = o.m[ch[i]], mn = o.m[ch[i + 1]];
                if (mn < mi && mi <= r + 1) {
                    int xx = X[lev][ch[i + 1]];
                    FAIL("lemma6_X", !(xx >= mn && xx < mi));
                    if (xx <= r) FAIL("lemma6_A", !(Ac[xx] >= ch[i] && Ac[xx] < ch[i + 1]));
                    else FAIL("lemma6_range", true);
                    CNT("chk.lemma6");
                }
            }
            int markv[MAXK + 3];
            bool marked[MAXK + 3];
            for (int t = c + 1; t <= r + 1; t++) marked[t] = false;
            int sends[MAXK + 2];
            for (int i = 0; i <= s; i++) sends[i] = 0;
            // rings
            for (int a = lo; a <= c; a++) {
                int idx = -1;
                for (int i = 0; i < s; i++) if (ch[i] <= a) idx = i;
                if (idx < 0 || idx + 1 >= s) continue;
                int j0 = ch[idx], j1 = ch[idx + 1];
                if (o.m[j1] < o.m[j0] && o.m[j0] <= r && first[lev][a] && first[lev][a] == X[lev][j1]) {
                    sends[idx]++;
                    int ta = first[lev][a];
                    int pos = g[lev][ta];
                    FAIL("ring_pos", pos != o.m[j1]);
                    if (pos == NONE) continue;
                    FAIL("ring_order", pos > ta);
                    FAIL("mark_twice", marked[pos]);
                    marked[pos] = true;
                    markv[pos] = CTL == 11 ? j1 : j0;
                    for (int q = pos; q <= ta; q++) {
                        FAIL("routes_meet", occ >> q & 1);
                        occ |= bit(q);
                    }
                    CNT("n.ring_marks");
                }
            }
            for (int i = 0; i + 1 < s; i++) {
                bool want = o.m[ch[i + 1]] < o.m[ch[i]] && o.m[ch[i]] <= r;
                FAIL("ring_one_sender", want ? sends[i] != 1 : sends[i] != 0);
            }
            // the rest
            int Jidx = -1;
            for (int i = 0; i < s; i++) if (o.m[ch[i]] > r) Jidx = i;
            int plus = Jidx + 1;
            if (plus < s && o.m[ch[plus]] <= r && CTL != 10) {
                int pos = o.m[ch[plus]];
                FAIL("mark_twice", marked[pos]);
                marked[pos] = true;
                markv[pos] = Jidx >= 0 ? ch[Jidx] : NONE;
                if (Jidx >= 0) CNT("n.rest_marks_J"); else CNT("n.rest_marks_none");
            }
            cur = s ? ch[s - 1] : NONE;
            for (int t = c + 1; t <= r; t++) {
                if (marked[t]) cur = markv[t];
                o.dlt[lev][t] = cur;
                int tr = NONE;
                for (int i = 0; i < s; i++) if (o.m[ch[i]] > t) tr = ch[i];
                if (CTL != 12) FAIL("delta", tr != cur);
                CNT("chk.delta");
            }
        }
    }
}

static int read_path(const Sec5 &o, int t) {
    if (CTL == 16) {
        for (int lev = o.levels - 1; lev >= 0; lev--) if (o.dlt[lev][t] != NONE) return o.dlt[lev][t];
        return NONE;
    }
    for (int lev = 0; lev < o.levels; lev++) if (o.dlt[lev][t] != NONE) return o.dlt[lev][t];
    return NONE;
}
static int read_off(const Sec5 &o, int a, int b) {
    if (a == 0) return NONE;
    if (a == b) { CNT("n.readoff_a_eq_b"); return a; }
    int lev = 31 - __builtin_clz((unsigned)((a - 1) ^ (b - 1)));
    int x = o.lam[lev][a], y = o.dlt[lev][b];
    if (x != NONE && y != NONE) { CNT("n.readoff_same_seg"); return CTL == 9 ? max(x, y) : min(x, y); }
    if (CTL == 15) {
        for (int l2 = o.levels - 1; l2 > lev; l2--) if (o.dlt[l2][b] != NONE) return o.dlt[l2][b];
        return NONE;
    }
    for (int l2 = lev + 1; l2 < o.levels; l2++) if (o.dlt[l2][b] != NONE) { CNT("n.readoff_higher"); return o.dlt[l2][b]; }
    CNT("n.readoff_none");
    return NONE;
}

// ----------------- One path on a digraph -----------------
struct Cls { int head; u64 K; u64 EK; };

// Returns last dominator on R of each vertex of Q (vertex, or -1) by the note's computation, and the classes.
// full: compare everything with brute force.
static void path_step(u64 Q, u64 E, const int *R, int k, int *rec, vector<Cls> *out, bool full) {
    gQ = Q; gE = E; gk = k;
    for (int i = 1; i <= k; i++) gR[i] = R[i];
    u64 Rm = 0;
    int pos[64];
    for (int i = 1; i <= k; i++) { Rm |= bit(R[i]); pos[R[i]] = i; }
    u64 O = Q & ~Rm;
    u64 feed[MAXK + 2];
    feed[0] = reach(E & O, O);
    if (CTL == 1) feed[0] = 0;
    for (int i = 1; i <= k; i++) feed[i] = reach(adj_[R[i]] & O, O);
    int a[64], b[64];
    for (u64 w = O; w; w &= w - 1) {
        int y = ctz(w);
        a[y] = INF; b[y] = -INF;
        for (int i = 0; i <= k; i++) if (feed[i] >> y & 1) { a[y] = min(a[y], i); b[y] = max(b[y], i); }
        if (CTL != 1) FAIL("every_y_fed", a[y] == INF);
        FAIL("b_at_least_1", b[y] < 1);
        if (a[y] == INF) a[y] = b[y] = 0;
        if (CTL == 2) a[y] = b[y];
        if (a[y] == 0) CNT("n.a0");
    }
    // A, B by the definition of the note, and what p_t can compute
    int A[MAXK + 3], B[MAXK + 3], Ac[MAXK + 3], Bc[MAXK + 3];
    for (int t = 0; t <= k + 1; t++) A[t] = Ac[t] = INF, B[t] = Bc[t] = -INF;
    for (int t = 2; t <= k; t++) {
        int v = R[t];
        u64 in = radj_[v] & Q;
        for (int i = 0; i <= k; i++) {
            if (!NOEXCL && (i == t || i == t - 1)) continue;
            bool direct = i == 0 ? (E >> v & 1) != 0 : (adj_[R[i]] >> v & 1) != 0;
            if (CTL == 5 && i == 0) direct = false;
            bool via = (in & feed[i]) != 0;
            if (CTL == 3) via = false;
            if (direct || via) { A[t] = min(A[t], i); B[t] = max(B[t], i); }
        }
        if ((E >> v & 1) && CTL != 5) { Ac[t] = min(Ac[t], 0); Bc[t] = max(Bc[t], 0); }
        for (u64 w = in; w; w &= w - 1) {
            int u = ctz(w);
            if (Rm >> u & 1) {
                int i = pos[u];
                if (NOEXCL || (i != t && i != t - 1)) { Ac[t] = min(Ac[t], i); Bc[t] = max(Bc[t], i); }
            } else if (CTL != 3) {
                Ac[t] = min(Ac[t], a[u]);
                Bc[t] = max(Bc[t], b[u]);
            }
        }
        if (CTL == 4) { B[t] = min(B[t], t - 1); Bc[t] = min(Bc[t], t - 1); }
        if (A[t] == INF) CNT("n.t_no_jump");
        if (B[t] > t) CNT("n.t_back_jump");
        if (A[t] != Ac[t] || B[t] != Bc[t]) { CNT("n.t_def_differs_from_computed"); if (NOEXCL) FAIL("noexcl_not_exact", true); }
    }
    if (full) {
        // the comparisons with A and B agree for all j < t < x
        for (int t = 2; t <= k; t++) for (int j = 1; j < t; j++) for (int x = t + 1; x <= k + 1; x++)
            FAIL("computed_equals_def", (A[t] >= j && B[t] < x) != (Ac[t] >= j && Bc[t] < x));
    }
    Sec5 o;
    if (k > MAXK) abort();
    sec5(k, A, B, Ac, Bc, o);
    MAXC("max.k", k);
    if (k == 1) CNT("n.k1");
    // read off
    for (int t = 1; t <= k; t++) { int d = read_path(o, t); rec[R[t]] = d == NONE ? -1 : R[d]; }
    for (u64 w = O; w; w &= w - 1) { int y = ctz(w); int d = read_off(o, a[y], b[y]); rec[y] = d == NONE ? -1 : R[d]; }

    // the classes, by the note's definition of keys
    int ekey[64], ehead[64];
    for (u64 w = O; w; w &= w - 1) ekey[ctz(w)] = INF, ehead[ctz(w)] = -1;
    int hkey[64];
    u64 heads = 0;
    for (u64 w = O; w; w &= w - 1) {
        int h = ctz(w);
        int deep = -1;
        for (int i = 1; i <= k; i++) if (adj_[R[i]] >> h & 1) deep = i;
        if (deep < 0) continue;
        heads |= bit(h);
        hkey[h] = (k - deep) * 64 + h;
    }
    for (u64 w = heads; w; w &= w - 1) {
        int h = ctz(w);
        u64 got = reach(bit(h), O);
        for (u64 q = got; q; q &= q - 1) { int y = ctz(q); if (hkey[h] < ekey[y]) { ekey[y] = hkey[h]; ehead[y] = h; } }
    }
    vector<Cls> cl;
    u64 cover = 0;
    for (u64 w = heads; w; w &= w - 1) {
        int h = ctz(w);
        if (ehead[h] != h) continue;
        u64 K = 0;
        for (u64 q = O; q; q &= q - 1) { int y = ctz(q); if (ehead[y] == h) K |= bit(y); }
        cover |= K;
        // E_K of the note
        u64 EK = 0;
        for (u64 q = K; q; q &= q - 1) {
            int y = ctz(q);
            bool ent = (E >> y & 1) != 0;
            bool outarc = (radj_[y] & Q & ~K) != 0;
            if (CTL == 13) outarc = (radj_[y] & Rm) != 0;
            if (CTL == 14) ent = false;
            if (ent || outarc) EK |= bit(y);
        }
        cl.push_back({h, K, EK});
    }
    FAIL("classes_cover", cover != O);
    if (out) *out = cl;
    if (!full) return;

    // ----------- brute force -----------
    u64 Rj[MAXK + 2];
    int m[MAXK + 2];
    for (int j = 1; j <= k; j++) {
        u64 p = bit(R[j]);
        Rj[j] = reach(E & ~p, Q & ~p);
        m[j] = k + 1;
        for (int t = j + 1; t <= k; t++) if (Rj[j] >> R[t] & 1) { m[j] = t; break; }
        FAIL("m_algorithm", m[j] != o.m[j]);
        CNT("chk.m");
        if (m[j] > j + 1) CNT("n.long_interval");
    }
    // Lemma 1
    for (int j = 1; j <= k; j++) {
        for (int i = 1; i <= k; i++) if (i != j) FAIL("lemma1a", ((Rj[j] >> R[i] & 1) != 0) != (i < j || i >= m[j]));
        for (u64 w = O; w; w &= w - 1) {
            int y = ctz(w);
            FAIL("lemma1b", ((Rj[j] >> y & 1) != 0) != (a[y] < j || b[y] >= m[j]));
            CNT("chk.lemma1b");
        }
    }
    // Lemma 2
    for (int j = 1; j <= k; j++) {
        FAIL("lemma2a_closed", !closed_(A, B, j, m[j]));
        for (int x = m[j] + 1; x <= k + 1; x++) FAIL("lemma2a_largest", closed_(A, B, j, x));
        for (int jj = j + 1; jj < m[j] && jj <= k; jj++) FAIL("lemma2b", m[jj] > m[j]);
    }
    // all dominators in the flow graph of Q
    u64 Dom[64];
    u64 reachW[64];
    for (u64 w = Q; w; w &= w - 1) {
        int v = ctz(w);
        reachW[v] = reach(E & ~bit(v), Q & ~bit(v));
        Dom[v] = 0;
    }
    for (u64 w = Q; w; w &= w - 1) {
        int v = ctz(w);
        for (u64 q = Q & ~reachW[v] & ~bit(v); q; q &= q - 1) Dom[ctz(q)] |= bit(v);
    }
    // Lemma 3
    for (int t = 1; t <= k; t++) {
        int y = R[t];
        FAIL("lemma3a_on_R", Dom[y] & ~Rm);
        int best = NONE;
        for (int j = 1; j < t; j++) if (m[j] > t) best = j;
        int last = NONE;
        for (int j = 1; j <= k; j++) if (j != t && (Dom[y] >> R[j] & 1)) last = j;
        FAIL("lemma3a_last", best != last);
        FAIL("readoff_path", (best == NONE ? -1 : R[best]) != rec[y]);
        CNT("chk.readoff_path");
    }
    for (u64 w = O; w; w &= w - 1) {
        int y = ctz(w);
        u64 want = 0;
        int best = NONE;
        for (int j = 1; j <= a[y] && j <= k; j++) if (m[j] > b[y]) { want |= bit(R[j]); best = j; }
        FAIL("lemma3b_set", want != (Dom[y] & Rm));
        // order: each on R dominates each off R, and in the order of indices
        for (u64 q = Dom[y] & Rm; q; q &= q - 1) {
            int pj = ctz(q);
            for (u64 s = Dom[y] & ~Rm; s; s &= s - 1) FAIL("lemma3b_before", !(Dom[ctz(s)] >> pj & 1));
            for (u64 s = Dom[y] & Rm; s; s &= s - 1) if (pos[ctz(s)] > pos[pj]) FAIL("lemma3b_order", !(Dom[ctz(s)] >> pj & 1));
        }
        FAIL("readoff_off", (best == NONE ? -1 : R[best]) != rec[y]);
        CNT("chk.readoff_off");
    }
    // Step 1: b from e, a from its keys, connected disjoint parts, keys along arcs
    int akey[64];
    for (u64 w = O; w; w &= w - 1) akey[ctz(w)] = INF;
    for (u64 w = O; w; w &= w - 1) {
        int h = ctz(w);
        int least = INF;
        if (E >> h & 1) least = 0;
        for (int i = k; i >= 1; i--) if (adj_[R[i]] >> h & 1) least = min(least, i);
        if (least == INF) continue;
        int key = least * 64 + h;
        for (u64 q = reach(bit(h), O); q; q &= q - 1) { int y = ctz(q); akey[y] = min(akey[y], key); }
    }
    for (u64 w = O; w; w &= w - 1) {
        int y = ctz(w);
        FAIL("b_from_key", k - ekey[y] / 64 != b[y]);
        if (CTL != 1 && CTL != 2) FAIL("a_from_key", akey[y] / 64 != a[y]);
        for (u64 q = adj_[y] & O; q; q &= q - 1) {
            FAIL("akey_not_monotone", akey[ctz(q)] > akey[y]);
            FAIL("ekey_not_monotone", ekey[ctz(q)] > ekey[y]);
        }
        // a path from the best head stays in its class
        int h = akey[y] % 64;
        u64 cl_a = 0;
        for (u64 q = O; q; q &= q - 1) if (akey[ctz(q)] == akey[y]) cl_a |= bit(ctz(q));
        FAIL("a_head_path_in_class", !(reach(bit(h), cl_a) >> y & 1));
    }
    // sets A_a and B_b
    if (CTL != 1 && CTL != 2) for (int s = 1; s <= k; s++) {
        u64 Aa = bit(R[s]), Bb = bit(R[s]);
        for (u64 w = O; w; w &= w - 1) { int y = ctz(w); if (a[y] == s) Aa |= bit(y); if (b[y] == s) Bb |= bit(y); }
        FAIL("A_a_connected_from_p", reach(bit(R[s]), Aa) != Aa);
        FAIL("B_b_connected_from_p", reach(bit(R[s]), Bb) != Bb);
    }
    // a leaf has a neighbour in A_a
    for (int t = 2; t <= k; t++) {
        int aa = Ac[t];
        if (aa >= 1 && aa < t - 1) {
            u64 Aa = bit(R[aa]);
            for (u64 w = O; w; w &= w - 1) if (a[ctz(w)] == aa) Aa |= bit(ctz(w));
            FAIL("leaf_neighbour_computed", !(radj_[R[t]] & Aa));
            CNT("chk.leaf");
        }
        int ad = A[t];
        if (ad >= 1 && ad != INF) {
            u64 Aa = bit(R[ad]);
            for (u64 w = O; w; w &= w - 1) if (a[ctz(w)] == ad) Aa |= bit(ctz(w));
            if (!(radj_[R[t]] & Aa)) {
                CNT("n.def_A_leaf_sentence_false");
                if (NOEXCL) FAIL("noexcl_leaf", true);
                FAIL("def_A_leaf_false_below_t", ad < t);
            }
        }
    }
    // Lemma 4
    for (const Cls &c : cl) {
        FAIL("class_rooted", reach(bit(c.head), c.K) != c.K);
        FAIL("head_is_entry", !(c.EK >> c.head & 1));
        for (u64 q = c.K; q; q &= q - 1) {
            int y = ctz(q);
            FAIL("lemma4a", Dom[y] & ~Rm & ~c.K);
            for (u64 s = c.K & ~bit(y); s; s &= s - 1) {
                int wv = ctz(s);
                bool inK = !(reach(c.EK & ~bit(wv), c.K & ~bit(wv)) >> y & 1);
                bool inQ = (Dom[y] >> wv & 1) != 0;
                FAIL("lemma4b", inK != inQ);
                CNT("chk.lemma4b");
            }
        }
    }
}

// ----------------- Enumerations -----------------
static void all_paths(u64 Q, u64 E, int *R, int k, u64 used, long long &count) {
    int rec[64];
    path_step(Q, E, R, k, rec, nullptr, true);
    count++;
    for (u64 w = adj_[R[k]] & Q & ~used; w; w &= w - 1) {
        int v = ctz(w);
        R[k + 1] = v;
        all_paths(Q, E, R, k + 1, used | bit(v), count);
    }
}

static void load(u64 code, int nn) {
    n = nn;
    int idx = 0;
    for (int u = 0; u < n; u++) adj_[u] = 0;
    for (int u = 0; u < n; u++) for (int v = 0; v < n; v++) if (u != v) { if (code >> idx & 1) adj_[u] |= bit(v); idx++; }
    build_radj();
}

static void report(const char *title) {
    printf("== %s\n", title);
    long long fails = 0;
    for (auto &kv : REG) {
        if (kv.first.rfind("FAIL.", 0) == 0) fails += *kv.second;
        printf("%s=%lld\n", kv.first.c_str(), *kv.second);
    }
    printf("TOTAL_FAILS=%lld\n", fails);
}

static void exh(int nn, int part, int parts) {
    long long digs = 0, used = 0, paths = 0, ents = 0;
    u64 tot = 1ULL << (nn * (nn - 1));
    for (u64 code = 0; code < tot; code++) {
        if ((int)(code % parts) != part) continue;
        digs++;
        load(code, nn);
        u64 all = (1ULL << nn) - 1;
        if (reach(1, all) != all) continue;
        used++;
        for (u64 sub = 0; sub < (1ULL << (nn - 1)); sub++) {
            u64 E = 1 | (sub << 1);
            int R[64];
            R[1] = 0;
            ents++;
            all_paths(all, E, R, 1, 1, paths);
        }
    }
    printf("exh n=%d digraphs=%lld rooted=%lld entrysets=%lld paths=%lld\n", nn, digs, used, ents, paths);
    report("exh");
}

// abstract tables
static void abs_check(int k, const int *A, const int *B) {
    Sec5 o;
    sec5(k, A, B, A, B, o);
    // read off for all a <= b
    for (int b = 1; b <= k; b++) {
        int last = NONE;
        for (int j = 1; j < b; j++) if (o.m[j] > b) last = j;
        FAIL("abs_path", read_path(o, b) != last);
        for (int a = 0; a <= b; a++) {
            int tr = NONE;
            for (int j = 1; j <= a; j++) if (o.m[j] > b) tr = j;
            FAIL("abs_lemma7", read_off(o, a, b) != tr);
            CNT("chk.abs_lemma7");
        }
    }
}
static void abs_all(int k) {
    vector<pair<int, int>> opt;
    opt.push_back({INF, -INF});
    for (int a = 0; a <= k; a++) for (int b = a; b <= k; b++) opt.push_back({a, b});
    int A[MAXK + 3], B[MAXK + 3];
    for (int t = 0; t <= k + 1; t++) A[t] = INF, B[t] = -INF;
    long long tables = 0;
    vector<int> idx(k + 1, 0);
    while (true) {
        for (int t = 2; t <= k; t++) A[t] = opt[idx[t]].first, B[t] = opt[idx[t]].second;
        abs_check(k, A, B);
        tables++;
        int t = 2;
        while (t <= k && ++idx[t] == (int)opt.size()) idx[t++] = 0;
        if (t > k) break;
    }
    printf("abs k=%d options=%zu tables=%lld\n", k, opt.size(), tables);
    report("abs");
}

static double now() { return chrono::duration<double>(chrono::steady_clock::now().time_since_epoch()).count(); }

static void abs_rand(int k, unsigned seed, double secs) {
    mt19937 rng(seed);
    double t0 = now();
    long long tables = 0;
    int A[MAXK + 3], B[MAXK + 3];
    while (now() - t0 < secs) {
        int kk = k / 2 + rng() % (k - k / 2 + 1);
        kk = max(kk, 2);
        for (int t = 0; t <= kk + 1; t++) A[t] = INF, B[t] = -INF;
        int style = rng() % 3;
        for (int t = 2; t <= kk; t++) {
            if (rng() % 3 == 0) continue;
            int a, b;
            if (style == 0) { a = rng() % (kk + 1); b = a + rng() % (kk - a + 1); }
            else if (style == 1) { a = max(0, t - 1 - (int)(rng() % 4)); b = min(kk, t + (int)(rng() % 3) - 1); if (b < a) b = a; }
            else {
                // nested: mostly forward jumps from early positions, back jumps from close positions
                int mid = kk / 2;
                a = t > mid ? max(1, mid - (t - mid) + (int)(rng() % 3)) : t - 1;
                b = rng() % 4 == 0 ? min(kk, t + 2) : a;
                if (b < a) b = a;
            }
            A[t] = a; B[t] = b;
        }
        abs_check(kk, A, B);
        tables++;
    }
    printf("absrand kmax=%d seed=%u tables=%lld\n", k, seed, tables);
    report("absrand");
}

// generators
static void rnd_sparse(mt19937 &rng, int nn, double dens) {
    n = nn;
    for (int u = 0; u < n; u++) adj_[u] = 0;
    uniform_real_distribution<double> U(0, 1);
    for (int u = 0; u < n; u++) for (int v = 0; v < n; v++) if (u != v && U(rng) < dens / n) adj_[u] |= bit(v);
    build_radj();
}
// directed path 0..k-1, nested chords both ways, some through vertices off the path, off-path bushes
static void rnd_nested(mt19937 &rng, int k, int extra) {
    n = k + extra;
    for (int u = 0; u < n; u++) adj_[u] = 0;
    for (int i = 0; i + 1 < k; i++) adj_[i] |= bit(i + 1);
    int nxt = k;
    vector<pair<int, int>> st;
    st.push_back({0, k - 1});
    while (!st.empty()) {
        auto [lo, hi] = st.back();
        st.pop_back();
        if (hi - lo < 2 || rng() % 5 == 0) continue;
        int aa = lo + rng() % (hi - lo - 1);
        int bb = aa + 2 + rng() % (hi - aa - 1);
        int u = aa, v = bb;
        if (rng() % 3 == 0) swap(u, v);
        if (nxt < n && rng() % 2) {
            adj_[u] |= bit(nxt);
            adj_[nxt] |= bit(v);
            if (nxt + 1 < n && rng() % 3 == 0) { adj_[nxt] |= bit(nxt + 1); adj_[nxt + 1] |= bit(lo + rng() % (hi - lo + 1)); nxt++; }
            nxt++;
        } else adj_[u] |= bit(v);
        st.push_back({lo, aa});
        st.push_back({aa, bb});
        st.push_back({bb, hi});
    }
    build_radj();
}
// many nested forward jumps around a middle, so that chains are long and many rings occur
static void rnd_rings(mt19937 &rng, int k) {
    n = k;
    for (int u = 0; u < n; u++) adj_[u] = 0;
    for (int i = 0; i + 1 < k; i++) adj_[i] |= bit(i + 1);
    int lo = 1 + rng() % 2, hi = k - 1 - rng() % 2;
    while (hi - lo > 2) {
        adj_[lo] |= bit(hi);
        if (rng() % 3 == 0 && hi - 2 > lo + 1) { adj_[hi] |= bit(hi - 2); hi -= 2; }
        lo += 1 + rng() % 3;
        hi -= 1 + rng() % 3;
    }
    build_radj();
}

static void random_path(mt19937 &rng, u64 Q, int z, int *R, int &k, double stop) {
    k = 1;
    R[1] = z;
    u64 used = bit(z);
    uniform_real_distribution<double> U(0, 1);
    while (k < MAXK && U(rng) >= stop) {
        u64 w = adj_[R[k]] & Q & ~used;
        if (!w) break;
        int c = rng() % pc(w);
        while (c--) w &= w - 1;
        int v = ctz(w);
        R[++k] = v;
        used |= bit(v);
    }
}

static void rnd(unsigned seed, double secs) {
    mt19937 rng(seed);
    double t0 = now();
    long long runs = 0;
    while (now() - t0 < secs) {
        int style = rng() % 4;
        if (style == 0) rnd_sparse(rng, 4 + rng() % 24, 0.8 + (rng() % 30) / 10.0);
        else if (style == 1) { int k = 4 + rng() % 40; rnd_nested(rng, k, rng() % 18); }
        else if (style == 2) rnd_rings(rng, 6 + rng() % 50);
        else { int k = 3 + rng() % 20; rnd_nested(rng, k, 4 + rng() % 30); }
        u64 all = n == 64 ? ~0ULL : (1ULL << n) - 1;
        int z = style == 0 ? rng() % n : 0;
        u64 Q = reach(bit(z), all);
        int R[64], k;
        double stop = (style == 0) ? 0.05 : 0.0;
        // on structured instances follow the spine when possible
        if (style != 0 && rng() % 4) {
            k = 0;
            for (int v = z; v < n; v++) { if (k && !(adj_[R[k]] >> v & 1)) break; R[++k] = v; if (k >= MAXK) break; }
        } else random_path(rng, Q, z, R, k, stop);
        u64 E = bit(z);
        if (rng() % 2) {
            double pe = (rng() % 3) * 0.04;
            uniform_real_distribution<double> U(0, 1);
            for (u64 w = Q; w; w &= w - 1) if (U(rng) < pe) E |= bit(ctz(w));
        }
        int rec[64];
        path_step(Q, E, R, k, rec, nullptr, true);
        runs++;
    }
    printf("rnd seed=%u runs=%lld\n", seed, runs);
    report("rnd");
}

// ----------------- Full recursion -----------------
static int FINAL[64];
static mt19937 *CHAIN_RNG;
static long long passes_ = 0;
static void solve_small(u64 Q, u64 E) {
    u64 Dom[64];
    for (u64 w = Q; w; w &= w - 1) Dom[ctz(w)] = 0;
    for (u64 w = Q; w; w &= w - 1) {
        int v = ctz(w);
        u64 got = reach(E & ~bit(v), Q & ~bit(v));
        for (u64 q = Q & ~got & ~bit(v); q; q &= q - 1) Dom[ctz(q)] |= bit(v);
    }
    for (u64 w = Q; w; w &= w - 1) {
        int y = ctz(w);
        int best = -1, bc = -1;
        for (u64 q = Dom[y]; q; q &= q - 1) { int d = ctz(q); if (pc(Dom[d]) > bc) { bc = pc(Dom[d]); best = d; } }
        if (best >= 0) FINAL[y] = best;
    }
}
static void chain(u64 Q, u64 E, int root, int thr, double stop, u64 H_all) {
    if (pc(Q) < thr) { CNT("n.small"); solve_small(Q, E); return; }
    int R[64], k;
    random_path(*CHAIN_RNG, Q, root, R, k, stop);
    int rec[64];
    vector<Cls> cl;
    path_step(Q, E, R, k, rec, &cl, false);
    passes_++;
    for (u64 w = Q; w; w &= w - 1) {
        int y = ctz(w);
        if (rec[y] >= 0) {
            if (CTL == 17 && FINAL[y] >= 0) continue;
            FINAL[y] = rec[y];
        }
    }
    for (Cls &c : cl) {
        u64 EK = c.EK;
        if (CTL == 18) {
            // literal reading: an arc from anywhere outside the class marks an entry, also from vertices of H not reached from r
            for (u64 q = c.K; q; q &= q - 1) { int y = ctz(q); if (radj_[y] & H_all & ~c.K) EK |= bit(y); }
        }
        chain(c.K, EK, c.head, thr, stop, H_all);
    }
}
static bool chain_once(mt19937 &rng, int r, int thr, double stop) {
    CHAIN_RNG = &rng;
    u64 all = n == 64 ? ~0ULL : (1ULL << n) - 1;
    u64 Q = reach(bit(r), all);
    for (int v = 0; v < n; v++) FINAL[v] = -1;
    chain(Q, bit(r), r, thr, stop, all);
    // brute: last dominator in H from r
    u64 Dom[64];
    for (u64 w = Q; w; w &= w - 1) Dom[ctz(w)] = 0;
    for (u64 w = Q; w; w &= w - 1) {
        int v = ctz(w);
        u64 got = (v == r) ? 0 : reach(bit(r), Q & ~bit(v));
        for (u64 q = Q & ~got & ~bit(v); q; q &= q - 1) Dom[ctz(q)] |= bit(v);
    }
    bool ok = true;
    for (u64 w = Q; w; w &= w - 1) {
        int y = ctz(w);
        if (y == r) { if (FINAL[y] != -1) ok = false; continue; }
        int best = -1, bc = -1;
        for (u64 q = Dom[y]; q; q &= q - 1) { int d = ctz(q); if (pc(Dom[d]) > bc) { bc = pc(Dom[d]); best = d; } }
        if (FINAL[y] != best) ok = false;
        CNT("chk.final_idom");
        if (best != r) CNT("n.final_nontrivial");
    }
    FAIL("final_tree", !ok);
    CNT("chk.chain_runs");
    return ok;
}
static void chain_all(int nn) {
    mt19937 rng(12345);
    u64 tot = 1ULL << (nn * (nn - 1));
    long long cases = 0;
    for (u64 code = 0; code < tot; code++) {
        load(code, nn);
        for (int r = 0; r < nn; r++) {
            for (int thr : {1, 2, 3}) for (double stop : {0.0, 0.3, 0.7}) { chain_once(rng, r, thr, stop); cases++; }
        }
    }
    printf("chain n=%d digraphs=%llu runs=%lld passes=%lld\n", nn, tot, cases, passes_);
    report("chain");
}
static void chain_rnd(unsigned seed, double secs) {
    mt19937 rng(seed);
    double t0 = now();
    long long runs = 0;
    while (now() - t0 < secs) {
        int style = rng() % 3;
        if (style == 0) rnd_sparse(rng, 4 + rng() % 40, 0.8 + (rng() % 30) / 10.0);
        else if (style == 1) { int k = 4 + rng() % 40; rnd_nested(rng, k, rng() % 18); }
        else rnd_rings(rng, 6 + rng() % 50);
        int r = style ? 0 : rng() % n;
        chain_once(rng, r, 1 + rng() % 12, (rng() % 3) * 0.1);
        runs++;
    }
    printf("chainrnd seed=%u runs=%lld passes=%lld\n", seed, runs, passes_);
    report("chainrnd");
}

// ----------------- Controls -----------------
static void ctl_run(unsigned seed, double secs) {
    for (int c : {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18}) {
        CTL = c;
        for (auto &kv : REG) *kv.second = 0;
        mt19937 rng(seed);
        double t0 = now();
        long long runs = 0;
        while (now() - t0 < secs) {
            int style = rng() % 3;
            if (style == 0) rnd_sparse(rng, 4 + rng() % 16, 1.0 + (rng() % 24) / 10.0);
            else if (style == 1) { int k = 4 + rng() % 30; rnd_nested(rng, k, rng() % 12); }
            else rnd_rings(rng, 6 + rng() % 40);
            int z = style ? 0 : rng() % n;
            u64 all = (1ULL << n) - 1;
            u64 Q = reach(bit(z), all);
            int R[64], k;
            if (c >= 13 && c != 15 && c != 16) {
                // chain-level rules
                chain_once(rng, z, 1 + rng() % 4, 0.1);
                // and the path step check of Lemma 4
                random_path(rng, Q, z, R, k, 0.1);
                int rec[64];
                path_step(Q, bit(z), R, k, rec, nullptr, true);
            } else {
                if (style && rng() % 4) {
                    k = 0;
                    for (int v = z; v < n; v++) { if (k && !(adj_[R[k]] >> v & 1)) break; R[++k] = v; if (k >= MAXK) break; }
                } else random_path(rng, Q, z, R, k, 0.05);
                u64 E = bit(z);
                uniform_real_distribution<double> U(0, 1);
                if (rng() % 2) for (u64 w = Q; w; w &= w - 1) if (U(rng) < 0.05) E |= bit(ctz(w));
                int rec[64];
                path_step(Q, E, R, k, rec, nullptr, true);
            }
            runs++;
        }
        long long fails = 0;
        string which;
        for (auto &kv : REG) if (kv.first.rfind("FAIL.", 0) == 0 && *kv.second) {
            fails += *kv.second;
            which += " " + kv.first.substr(5) + ":" + to_string(*kv.second);
        }
        printf("ctl %d runs=%lld fails=%lld%s\n", c, runs, fails, which.c_str());
        fflush(stdout);
    }
    CTL = 0;
}

int main(int argc, char **argv) {
    NOEXCL = getenv("NOEXCL") != nullptr;
    string cmd = argv[1];
    if (cmd == "exh") exh(atoi(argv[2]), argc > 3 ? atoi(argv[3]) : 0, argc > 4 ? atoi(argv[4]) : 1);
    else if (cmd == "abs") abs_all(atoi(argv[2]));
    else if (cmd == "absrand") abs_rand(atoi(argv[2]), atoi(argv[3]), atof(argv[4]));
    else if (cmd == "rnd") rnd(atoi(argv[2]), atof(argv[3]));
    else if (cmd == "chain") chain_all(atoi(argv[2]));
    else if (cmd == "chainrnd") chain_rnd(atoi(argv[2]), atof(argv[3]));
    else if (cmd == "ctl") ctl_run(atoi(argv[2]), atof(argv[3]));
    return 0;
}
