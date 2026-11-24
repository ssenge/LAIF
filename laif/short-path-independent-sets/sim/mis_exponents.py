"""Exponents (nats per vertex) for MIS on random d-regular graphs (configuration model):
phi(a) = lim (1/n) ln E[#independent sets of size a n]; enumeration of all independent sets costs i(G) <= n E[i(G)] whp.
Markov chain search at fugacity lam <= 1 costs T = 1/pi_lam(E*) = sum_x lam^(|x|-|x*|) / |X*| >= i(G) / |X*|."""
import numpy as np
from math import lgamma, log
from scipy.optimize import minimize_scalar

def phi(a, d):     # closed form of the first-moment exponent
    if a <= 0: return 0.0
    H = -a * log(a) - (1 - a) * log(1 - a)
    return H + d * (1 - a) * log(1 - a) - 0.5 * d * (1 - 2 * a) * log(1 - 2 * a)

def ln_EN(n, k, d):  # exact ln E[N_k] in the configuration model
    lf = lambda m: lgamma(m + 1)
    ldf = lambda m: lf(m) - (m // 2) * log(2) - lf(m // 2)          # (m-1)!! for even m: m!/(2^{m/2}(m/2)!)
    return lf(n) - lf(k) - lf(n - k) + lf(d * (n - k)) - lf(d * (n - 2 * k)) + ldf(d * (n - 2 * k)) - ldf(d * n)

def phi_max(d):
    r = minimize_scalar(lambda a: -phi(a, d), bounds=(1e-9, 0.5 - 1e-9), method="bounded", options=dict(xatol=1e-13))
    return -r.fun, r.x

def alpha_first_moment(d):  # largest a with phi(a) >= 0: whp upper bound on alpha*
    lo, hi = phi_max(d)[1], 0.5 - 1e-12
    for _ in range(200):
        m = (lo + hi) / 2; lo, hi = (m, hi) if phi(m, d) > 0 else (lo, m)
    return lo

def alpha_greedy(d):        # whp lower bound on alpha* from the limit of the greedy algorithm [8]
    return 0.5 * (1 - (d - 1) ** (-2 / (d - 2)))

def psi(a, d):
    """lim (1/n) ln E[#maximal independent sets of size a n]: phi(a) minus the log-probability that the d a n edges of S
    cover every outside vertex, from [x^{dk}]((1+x)^d - 1)^{n-k} against C(d(n-k), dk) (saddle point, minimized over x)."""
    if a <= 0 or a >= 0.5: return -np.inf
    b = d * a / (1 - a)                                  # S-edges per outside vertex
    if b < 1: return -np.inf                             # fewer edges than outside vertices: no maximal set
    def f(t):                                            # ln((1+x)^d - 1) - b ln x with x = e^t, overflow-free
        u = d * np.logaddexp(0.0, t)
        return u + np.log(-np.expm1(-u)) - b * t
    r = minimize_scalar(f, bounds=(-60, 60), method="bounded", options=dict(xatol=1e-12))
    lncov = (1 - a) * r.fun                              # (1/n) ln [x^{dk}]((1+x)^d - 1)^{n-k}
    H = lambda p: -p * np.log(p) - (1 - p) * np.log(1 - p)
    lnall = d * (1 - a) * H(b / d)                       # (1/n) ln C(d(n-k), dk)
    return phi(a, d) + lncov - lnall


def psi_max(d):
    grid = np.exp(np.linspace(np.log(0.5 / d), np.log(0.4999), 20001)); v = np.array([psi(a, d) for a in grid]); i = int(np.nanargmax(v))
    r = minimize_scalar(lambda a: -psi(a, d), bounds=(grid[max(i - 1, 0)], grid[min(i + 1, len(grid) - 1)]), method="bounded", options=dict(xatol=1e-13))
    return -r.fun, r.x


def kappa(d):
    """Exponent (bits) of the runtime guarantee 2^(kappa n) of Markov chain search at the uniqueness threshold lam_c,
    as in Proposition 5.22 of 2410.23270, with |x*| <= 2 ln(d) n / d; the smaller of the two readings of log there."""
    lam = (d - 1) ** (d - 1) / (d - 2) ** d
    tail = 1 / (2 * d) + np.log2(1 + lam) / 2
    return min(-2 * np.log2(lam) * np.log(d) / d, -2 * np.log2(lam) * np.log2(d) / d) + tail


def annealed_T(d, lam):
    """(1/n) ln of sum_x lam^(|x| - |x*|) with |x*| at the first-moment threshold and N_k at its first moment (estimate)."""
    a1 = alpha_first_moment(d)
    return max(phi(a, d) - (a1 - a) * np.log(lam) for a in np.linspace(1e-7, a1, 20001))


def test():
    import itertools, networkx as nx
    from math import comb
    for d in (3, 5, 20):                                       # closed form against exact first moments
        for a in (0.05, 0.1, 0.2):
            n = 2_000_000; k = int(a * n)
            assert abs(ln_EN(n, k, d) / n - phi(k / n, d)) < 1e-4
    def ln_EM(n, k, d):                                        # exact first moment of maximal sets of size k
        g = [0] + [comb(d, j) for j in range(1, d + 1)]; poly = [1]; K = d * k
        for _ in range(n - k):
            new = [0] * min(len(poly) + d, K + 1)
            for i, p in enumerate(poly):
                if p:
                    for j in range(1, d + 1):
                        if i + j <= K: new[i + j] += p * g[j]
            poly = new
        c = poly[K] if len(poly) > K else 0
        return ln_EN(n, k, d) + (log(c) if c else -np.inf) - log(comb(d * (n - k), K))
    for d, a in ((6, 0.2), (10, 0.2), (10, 0.15)):            # psi is the limit, from above at rate log(n)/n
        e1, e2 = ln_EM(200, int(a * 200), d) / 200, ln_EM(400, int(a * 400), d) / 400
        assert e1 < e2 < psi(a, d) and psi(a, d) - e2 < 0.6 * (psi(a, d) - e1), (d, a, e1, e2, psi(a, d))
    rng = np.random.default_rng(1)                             # brute force on small graphs
    for trial in range(30):
        n = int(rng.integers(6, 15)); G = nx.gnp_random_graph(n, float(rng.uniform(0.15, 0.6)), seed=int(rng.integers(1 << 30)))
        ind = [S for r in range(n + 1) for S in itertools.combinations(range(n), r)
               if all(not G.has_edge(u, v) for u, v in itertools.combinations(S, 2))]
        m = max(len(S) for S in ind); opt = sum(len(S) == m for S in ind)
        maximal = sum(all(any(G.has_edge(v, u) for u in S) for v in range(n) if v not in S) for S in ind)
        assert maximal == sum(1 for _ in nx.find_cliques(nx.complement(G)))
        for lam in (1.0, 0.5, 0.1):
            T = sum(lam ** (len(S) - m) for S in ind) / opt  # expected samples of Markov chain search
            assert len(ind) <= opt * T * (1 + 1e-12)
        for lam in (0.05, 0.3, 1.0):                           # single-site heat-bath chain (eq. (39) of 2410.23270): gap <= 1/n
            idx = {S: i for i, S in enumerate(ind)}; P = np.zeros((len(ind), len(ind)))
            for S in ind:
                for v in range(n):
                    if v in S: P[idx[S], idx[tuple(u for u in S if u != v)]] += 1 / (n * (1 + lam))
                    elif all(not G.has_edge(u, v) for u in S): P[idx[S], idx[tuple(sorted(S + (v,)))]] += lam / (n * (1 + lam))
                P[idx[S], idx[S]] = 1 - P[idx[S]].sum()
            pi = np.array([lam ** len(S) for S in ind]); pi /= pi.sum(); D = np.sqrt(pi)
            ev = np.sort(np.linalg.eigvalsh((D[:, None] * P) / D[None, :]))
            assert 1 - ev[-2] <= 1 / n + 1e-12, (n, lam, 1 - ev[-2])
            xs = [S for S in ind if len(S) == m][0]             # Delta_P stability at a maximum set forces Delta_P >= q
            q = P[idx[xs]][[idx[tuple(u for u in xs if u != v)] for v in xs]].sum()
            assert abs(q - m / (n * (1 + lam))) < 1e-12
    for d in (6, 20, 100):                                     # maximal sets are a subset of all independent sets
        assert psi_max(d)[0] <= phi_max(d)[0]
    print("mis_exponents self-checks passed")


def row(d):
    """All exponents in nats per vertex. lam_c: uniqueness threshold (Theorems 5.17, 5.19 of 2410.23270);
    lam_rr = 1/(2 sqrt(d-1) - 1) (Theorem 5.21). LT: whp lower bound on (1/n) ln(1/pi_lam(E*)) from the empty set and the
    greedy bound alpha* >= alpha_g. c_bound: upper bound (1 + lam)/24 on c in Theorem 4.2 at lam_c (Delta_P >= |x*|/(n(1+lam)),
    omega <= delta/2 <= 1/(2n), gamma <= 1, eta(1-eta) <= 1/4; |x*| cancels). holds: psi <= (1 - 2 c_bound) LT, i.e.
    listing maximal sets takes at most the square of the quantum runtime bound."""
    lam_c = float(np.exp((d - 1) * np.log(d - 1) - d * np.log(d - 2))); lam_rr = 1 / (2 * np.sqrt(d - 1) - 1)
    pm, am = phi_max(d); ag = alpha_greedy(d); a1 = alpha_first_moment(d); ps = psi_max(d)[0] * (1 + 1e-4)   # rounded up (relative)
    tail = phi(ag, d) if ag >= am else pm
    LT = lambda lam: ag * np.log(1 / lam) - tail
    cb = (1 + lam_c) / 24
    r = dict(d=d, psi=ps, phi_max=pm, alpha_greedy=ag, alpha_first_moment=a1, lam_c=lam_c, lam_rr=lam_rr,
             LT_c=LT(lam_c), c_bound=cb, holds_c=bool(ps <= (1 - 2 * cb) * LT(lam_c)), LT_rr=LT(lam_rr),
             kappa_bits=kappa(d) if d <= 10 ** 6 else None)
    for name, lam in (("c", lam_c), ("rr", lam_rr)):
        ta = annealed_T(d, lam); r["annealed_T_" + name] = ta; r["annealed_cstar_" + name] = 0.5 - ps / (2 * ta)
    return r


def table(path):
    import json
    ds = sorted(set([6, 8, 10, 15] + list(range(20, 450)) + [10 ** 4, 10 ** 5, 10 ** 6, 10 ** 7]
                    + [int(x) for x in np.unique(np.round(np.exp(np.linspace(np.log(100), np.log(1e9), 300))))]))
    ds = [d for d in ds if d <= 10 ** 7]   # shortcut: the float evaluation of psi loses accuracy beyond about 1e8
    rows = [row(d) for d in ds]
    json.dump(rows, open(path, "w"), indent=1)
    ok = sorted(r["d"] for r in rows if r["holds_c"]); lo = ok[0]
    hi = max(d for d in ok if all(r["holds_c"] for r in rows if lo <= r["d"] <= d))
    assert all(not r["holds_c"] for r in rows if r["d"] < lo)
    marg = min(((1 - 2 * r["c_bound"]) * r["LT_c"] / r["psi"] - 1, r["d"]) for r in rows if lo <= r["d"] <= hi)
    print("holds for every listed d from", lo, "to", hi, "; smallest relative margin", marg)
    for r in rows:
        if r["d"] in (6, 10, 20, 50, 100, 200, 449, 500, 1000, 10 ** 4, 10 ** 5, 10 ** 6, 10 ** 7, 10 ** 8, 10 ** 9) or r["d"] in (lo, hi):
            print(f"{r['d']:8d} psi {r['psi']:.6f} LT_c {r['LT_c']:+.6f} c< {r['c_bound']:.4f} holds {r['holds_c']}  "
                  f"ann_c* {r['annealed_cstar_c']:+.3f} ann_c*_rr {r['annealed_cstar_rr']:+.3f}")


if __name__ == "__main__":
    import sys, json
    if sys.argv[1:] == ["test"]:
        test(); sys.exit()
    table(sys.argv[1])
