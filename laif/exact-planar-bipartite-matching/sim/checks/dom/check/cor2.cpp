// Corollary 2 of notes/DOMINATORS.md by brute force, all digraphs on N vertices, or random ones.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <random>
#include <string>
#include <vector>
using namespace std;
typedef unsigned long long u64;
static int n;
static u64 adj_[64], radj_[64];
static inline int ctz(u64 x) { return __builtin_ctzll(x); }
static inline int pc(u64 x) { return __builtin_popcountll(x); }
static inline u64 bit(int v) { return 1ULL << v; }
static u64 reachA(const u64 *A, u64 src, u64 allow) {
    u64 seen = src & allow, fr = seen;
    while (fr) { int v = ctz(fr); fr &= fr - 1; u64 nw = A[v] & allow & ~seen; seen |= nw; fr |= nw; }
    return seen;
}
static int scc_count(const u64 *A, const u64 *RA, u64 V) {
    int c = 0;
    u64 left = V;
    while (left) {
        int v = ctz(left);
        u64 f = reachA(A, bit(v), V), b = reachA(RA, bit(v), V);
        left &= ~(f & b);
        c++;
    }
    return c;
}
struct Res { long long c[32]; };
static long long cnt[32];
enum { DIGS, SAP_CHECKS, SAP_TRUE, SAP_BAD, OUTN_CHECKS, OUTN_BAD, ROOT_CHECKS, ROOT_BAD, BR_CHECKS, BR_TRUE, BR_BAD, BROUT_BAD, CROSS_BAD, DIAM_CHECKS, DIAM_2D1_BAD, DIAM_2D2_BAD, CTL_FWDONLY_DIFF, CTL_NOROOT_DIFF, CTL_BRFWD_DIFF, CTL_INN_DIFF, NOPLANAR, EQUIV_BAD, ARCDIFF };
static const char *NAMES[] = {"digraphs", "sap_checks", "sap_true", "FAIL.sap", "outn_checks", "FAIL.outneighbour", "root_checks", "FAIL.root", "bridge_checks", "bridge_true", "FAIL.bridge", "FAIL.bridge_outneighbour", "FAIL.cross_arc_bridge", "diam_checks", "diam_exceeds_2D+1", "FAIL.diam_exceeds_2D+2", "ctl_fwd_only_diff", "ctl_no_root_test_diff", "ctl_bridge_fwd_only_diff", "ctl_in_neighbour_rule_diff", "x", "FAIL.equiv", "x"};
static int witdiam = 2;

// immediate dominator of each vertex of C from s in A; idom[s]=-1
static void idoms(const u64 *A, u64 C, int s, int *idom, u64 *Dom) {
    for (u64 w = C; w; w &= w - 1) Dom[ctz(w)] = 0;
    for (u64 w = C; w; w &= w - 1) {
        int v = ctz(w);
        u64 got = v == s ? 0 : reachA(A, bit(s), C & ~bit(v));
        for (u64 q = C & ~got & ~bit(v); q; q &= q - 1) Dom[ctz(q)] |= bit(v);
    }
    for (u64 w = C; w; w &= w - 1) {
        int y = ctz(w);
        int best = -1, bc = -1;
        for (u64 q = Dom[y]; q; q &= q - 1) { int d = ctz(q); if (pc(Dom[d]) > bc) { bc = pc(Dom[d]); best = d; } }
        idom[y] = best;
    }
}

static int ecc_all(const vector<u64> &U, int N, bool &conn) {
    int D = 0;
    conn = true;
    u64 all = N == 64 ? ~0ULL : (1ULL << N) - 1;
    for (int s = 0; s < N; s++) {
        u64 seen = bit(s), fr = seen;
        int d = 0;
        while (true) {
            u64 nw = 0;
            for (u64 w = fr; w; w &= w - 1) nw |= U[ctz(w)];
            nw &= ~seen;
            if (!nw) break;
            seen |= nw; fr = nw; d++;
        }
        if (seen != all) conn = false;
        D = max(D, d);
    }
    return D;
}

static void one() {
    cnt[DIGS]++;
    for (int v = 0; v < n; v++) radj_[v] = 0;
    for (int u = 0; u < n; u++) for (u64 w = adj_[u]; w; w &= w - 1) radj_[ctz(w)] |= bit(u);
    u64 all = (1ULL << n) - 1;
    int c0 = scc_count(adj_, radj_, all);
    // brute force
    bool sap[64];
    for (int v = 0; v < n; v++) sap[v] = scc_count(adj_, radj_, all & ~bit(v)) > c0;
    // components
    u64 left = all;
    while (left) {
        int s = ctz(left);
        u64 C = reachA(adj_, bit(s), all) & reachA(radj_, bit(s), all);
        left &= ~C;
        s = ctz(C);   // least identifier
        int idf[64], idr[64];
        u64 Df[64], Dr[64];
        idoms(adj_, C, s, idf, Df);
        idoms(radj_, C, s, idr, Dr);
        for (u64 w = C & ~bit(s); w; w &= w - 1) {
            int v = ctz(w);
            bool f = false, r = false;
            for (u64 q = C; q; q &= q - 1) { if (Df[ctz(q)] >> v & 1) f = true; if (Dr[ctz(q)] >> v & 1) r = true; }
            cnt[SAP_CHECKS]++;
            if (sap[v]) cnt[SAP_TRUE]++;
            if ((f || r) != sap[v]) cnt[SAP_BAD]++;
            if (f != sap[v]) cnt[CTL_FWDONLY_DIFF]++;
            // the strong connectivity form
            u64 rest = C & ~bit(v);
            bool sc = reachA(adj_, bit(s), rest) == rest && reachA(radj_, bit(s), rest) == rest;
            if (sc == sap[v]) cnt[EQUIV_BAD]++;
            // out-neighbour with idom = v
            bool of = false, orv = false, inn = false;
            for (u64 q = adj_[v] & C; q; q &= q - 1) if (idf[ctz(q)] == v) of = true;
            for (u64 q = radj_[v] & C; q; q &= q - 1) if (idr[ctz(q)] == v) orv = true;
            for (u64 q = radj_[v] & C; q; q &= q - 1) if (idf[ctz(q)] == v) inn = true;
            cnt[OUTN_CHECKS]++;
            if (of != f || orv != r) cnt[OUTN_BAD]++;
            if (inn != f) cnt[CTL_INN_DIFF]++;
        }
        // the root: one run of identifiers on C without s
        cnt[ROOT_CHECKS]++;
        u64 rest = C & ~bit(s);
        bool notsc = rest && scc_count(adj_, radj_, rest) > 1;
        if (notsc != sap[s]) cnt[ROOT_BAD]++;
        if (sap[s]) cnt[CTL_NOROOT_DIFF]++;
    }
    // bridges through subdivision
    int nn = n;
    u64 A2[64], R2[64];
    for (int v = 0; v < 64; v++) A2[v] = R2[v] = 0;
    struct Arc { int u, v, x; };
    vector<Arc> arcs;
    for (int u = 0; u < n; u++) for (u64 w = adj_[u]; w; w &= w - 1) arcs.push_back({u, ctz(w), nn++});
    if (nn > 64) return;
    for (auto &e : arcs) { A2[e.u] |= bit(e.x); A2[e.x] |= bit(e.v); R2[e.x] |= bit(e.u); R2[e.v] |= bit(e.x); }
    left = all;
    u64 full2 = nn == 64 ? ~0ULL : (1ULL << nn) - 1;
    while (left) {
        int s0 = ctz(left);
        u64 C = reachA(adj_, bit(s0), all) & reachA(radj_, bit(s0), all);
        left &= ~C;
        int s = ctz(C);
        // subdivided D[C]
        u64 C2 = C;
        for (auto &e : arcs) if ((C >> e.u & 1) && (C >> e.v & 1)) C2 |= bit(e.x);
        int idf[64], idr[64];
        u64 Df[64], Dr[64];
        idoms(A2, C2, s, idf, Df);
        idoms(R2, C2, s, idr, Dr);
        for (auto &e : arcs) {
            bool inside = (C >> e.u & 1) && (C >> e.v & 1);
            if (!((C >> e.u & 1) || (C >> e.v & 1))) continue;
            adj_[e.u] &= ~bit(e.v);
            radj_[e.v] &= ~bit(e.u);
            bool br = scc_count(adj_, radj_, all) > c0;
            adj_[e.u] |= bit(e.v);
            radj_[e.v] |= bit(e.u);
            if (!inside) { if (br) cnt[CROSS_BAD]++; continue; }
            bool f = false, r = false;
            for (u64 q = C2; q; q &= q - 1) { if (Df[ctz(q)] >> e.x & 1) f = true; if (Dr[ctz(q)] >> e.x & 1) r = true; }
            cnt[BR_CHECKS]++;
            if (br) cnt[BR_TRUE]++;
            if ((f || r) != br) cnt[BR_BAD]++;
            if (f != br) cnt[CTL_BRFWD_DIFF]++;
            bool fo = idf[e.v] == e.x, ro = idr[e.u] == e.x;
            if (fo != f || ro != r) cnt[BROUT_BAD]++;
        }
    }
    // diameter of the subdivided network, G the underlying graph of H
    vector<u64> U(n, 0), U2(nn, 0);
    for (auto &e : arcs) {
        U[e.u] |= bit(e.v); U[e.v] |= bit(e.u);
        U2[e.u] |= bit(e.x); U2[e.x] |= bit(e.u); U2[e.v] |= bit(e.x); U2[e.x] |= bit(e.v);
    }
    bool cg, cg2;
    int D = ecc_all(U, n, cg);
    if (cg && n >= 2) {
        int D2 = ecc_all(U2, nn, cg2);
        cnt[DIAM_CHECKS]++;
        if (D2 > 2 * D + 1) {
            cnt[DIAM_2D1_BAD]++;
            if (witdiam > 0) {
                witdiam--;
                printf("diam witness n=%d D=%d D2=%d arcs:", n, D, D2);
                for (auto &e : arcs) printf(" %d>%d", e.u, e.v);
                printf("\n");
            }
        }
        if (D2 > 2 * D + 2) cnt[DIAM_2D2_BAD]++;
    }
}

int main(int argc, char **argv) {
    string cmd = argv[1];
    if (cmd == "all") {
        n = atoi(argv[2]);
        u64 tot = 1ULL << (n * (n - 1));
        for (u64 code = 0; code < tot; code++) {
            int idx = 0;
            for (int u = 0; u < n; u++) adj_[u] = 0;
            for (int u = 0; u < n; u++) for (int v = 0; v < n; v++) if (u != v) { if (code >> idx & 1) adj_[u] |= bit(v); idx++; }
            one();
        }
    } else {
        mt19937_64 rng(atoi(argv[2]));
        long long runs = atoll(argv[3]);
        for (long long i = 0; i < runs; i++) {
            n = 6 + rng() % 4;
            double p = (1.2 + (rng() % 30) / 10.0) / n;
            uniform_real_distribution<double> U(0, 1);
            for (int u = 0; u < n; u++) adj_[u] = 0;
            for (int u = 0; u < n; u++) for (int v = 0; v < n; v++) if (u != v && U(rng) < p) adj_[u] |= bit(v);
            int m = 0;
            for (int u = 0; u < n; u++) m += pc(adj_[u]);
            if (n + m > 64) continue;
            one();
        }
    }
    for (int i = 0; i < 23; i++) if (strcmp(NAMES[i], "x")) printf("%s=%lld\n", NAMES[i], cnt[i]);
    return 0;
}
