"""Safe phased elimination (README, Algorithm) in d = 2 with m = 1 constraint, on polygons.
The mean estimator is modelled by its guarantee: an estimate within eta of the mean in every coordinate, with a
sign pattern chosen against the learner (alternating worst case), at a cost of ceil(1/eta) queries at that action.
Asserts: every queried action is feasible, a* survives every phase, the estimates are within e_l on C_l, and the
regret of every phase is at most the per-phase bound in the proof of Theorem 1. The design here is a conditional-gradient
design with g <= 2r and full range (asserted), in place of the sparsified design of the README; the accuracy is asserted
directly. Error signs: alternating (mode "alt") or independent random signs per coordinate (mode "rand").
Double precision limits the check to T <= 1e7."""
import math, sys, numpy as np
from scipy.optimize import linprog
d = 2
def clip(V, h, c):                         # polygon V (ccw vertices) intersected with {x : h.x <= c}
    out = []
    for i in range(len(V)):
        p, q = V[i], V[(i + 1) % len(V)]; fp, fq = h @ p - c, h @ q - c
        if fp <= 0: out.append(p)
        if fp * fq < 0: out.append(p + (q - p) * fp / (fp - fq))
    return out
def design(P):                              # conditional-gradient G-optimal design on the points P (rows); returns support, weights
    P = np.array(P); k = len(P); pi = np.full(k, 1 / k)
    for _ in range(5000):
        V = (P.T * pi) @ P; Vi = np.linalg.pinv(V); g = np.einsum('ij,jk,ik->i', P, Vi, P); j = g.argmax()
        r = np.linalg.matrix_rank(V, 1e-12)
        if g[j] <= 2 * r: break
        gam = (g[j] / r - 1) / (g[j] - 1); pi *= 1 - gam; pi[j] += gam
    assert g[j] <= 2 * r * (1 + 1e-9), "design did not converge"
    assert r == np.linalg.matrix_rank(P, 1e-12), "range of V"
    keep = pi > 1e-12; return P[keep], pi[keep] / pi[keep].sum(), r
def run(T, seed, mode="alt"):
    rng = np.random.default_rng(seed)
    A = [0.95 * np.array([math.cos(t), math.sin(t)]) for t in np.linspace(0, 2 * math.pi, 9)[:-1] + rng.uniform(0, 1)]
    th = rng.normal(size=d); th *= rng.uniform(0.5, 1) / np.linalg.norm(th)
    ph = rng.normal(size=d); ph *= rng.uniform(0.5, 1) / np.linalg.norm(ph)
    u = rng.uniform(-0.3, 0.3, d); Gam = rng.choice([0.02, 0.1, 0.4]); al = ph @ u + Gam
    # a*: maximize th.x over polygon A intersected with ph.x <= al (vertices of the clipped polygon)
    F = clip(A, ph, al); astar = max(F, key=lambda x: th @ x); mu = th @ astar; Du = mu - th @ u
    t = 0; reg = 0.0; sgn = [1]
    def qme(a, eta):                        # estimate of (th.a, ph.a), worst-case-signed error, cost ceil(1/eta)
        nonlocal t, reg
        assert ph @ a <= al + 1e-12, "unsafe query"
        q = min(math.ceil(1 / eta), T - t); t += q; reg += q * (mu - th @ a); sgn[0] = -sgn[0]
        s2 = sgn[0] * np.array([1, -1]) if mode == "alt" else rng.choice([-1, 1], 2)
        return np.array([th @ a, ph @ a]) + eta * s2
    # warm-up at u
    j = 0
    while True:
        j += 1; om = 2.0 ** -j; w = qme(u, om)
        Gh = al - w[1] - om
        if Gh >= 16 * om or t >= T: break
    if t >= T: return reg, Du, Gam, 0
    assert om <= Gam / 16 + 1e-12 and 7 * Gam / 8 - 1e-12 <= Gh <= Gam + 1e-12
    assert t <= 72 / Gam + math.log2(36 / Gam) + 1, "warm-up queries"
    C = [np.array(v) for v in A]; e_prev = 1.0; phases = 0
    while t < T:
        phases += 1; e = e_prev / 2; rho = Gh / (Gh + 2 * e_prev)
        M = [(1 - rho) * u + rho * x for x in C]
        S, pi, r = design(M); eta = rho * e / (6 * math.sqrt(d))
        reg0 = reg; Y = np.array([qme(a, eta) for a in S])
        if t >= T and len(Y) < len(S): break
        V = (S.T * pi) @ S; Vi = np.linalg.pinv(V); ghat = Vi @ (S.T * pi) @ Y        # columns: theta, phi
        def est(x, col):                    # estimate of <g, x> for x in C via the mixture and the warm-up value at u
            m = (1 - rho) * u + rho * x; return ((m @ ghat[:, col]) - (1 - rho) * w[col]) / rho
        for x in C:
            assert abs(est(x, 0) - th @ x) <= e + 1e-9 and abs(est(x, 1) - ph @ x) <= e + 1e-9, "accuracy"
        assert max(mu - th @ x for x in C) <= 30 / 7 * e_prev * (1 + Du / Gam) + 1e-9, "Lemma 4"
        assert max(mu - th @ ((1 - rho) * u + rho * x) for x in C) <= 46 / 7 * e_prev * (1 + Du / Gam) + 1e-9, "gap of mixtures"
        Qbd = len(S) * (6 * math.sqrt(d) / (rho * e) + 1) * (46 / 7 * e_prev * (1 + Du / Gam)) * 1.0001
        assert reg - reg0 <= Qbd + 1e-9, "phase regret bound"
        # affine estimates as (h, b): est(x) = h.x + b
        hb = [(rho * ghat[:, c] / rho, ((1 - rho) * (u @ ghat[:, c]) - (1 - rho) * w[c]) / rho) for c in (0, 1)]
        # R*: max over y = (1 - s) u + w2, w2 in s C, of the pessimistic reward, subject to the pessimistic constraint
        Hc = []; Vc = np.array(C)
        for i in range(len(C)):                # halfplanes of C from its ccw vertices
            p, q = Vc[i], Vc[(i + 1) % len(C)]; n = np.array([q[1] - p[1], p[0] - q[0]])
            if np.linalg.norm(n) > 1e-14: Hc.append((n, n @ p))
        (hT, bT), (hP, bP) = hb
        c = -np.r_[-(w[0] - om) + (bT - e), hT]         # variables (s, w2); objective (1-s)(w0-om) + hT.w2 + s(bT-e)
        Aub = [np.r_[-(w[1] + om) + (bP + e), hP]]; bub = [al - (w[1] + om)]
        for n, cc in Hc: Aub.append(np.r_[-cc, n]); bub.append(0.0)
        res = linprog(c, A_ub=Aub, b_ub=bub, bounds=[(0, 1)] + [(None, None)] * d, method="highs")
        Rstar = -res.fun + (w[0] - om) if res.status == 0 else -np.inf
        C = clip(C, hP, al - bP + e); C = clip(C, -hT, -(Rstar - e - bT))
        assert len(C) >= 1 and any(np.allclose(astar, x) for x in C) or point_in(C, astar), "a* eliminated"
        e_prev = e
    return reg, Du, Gam, phases
def point_in(C, p):
    if len(C) < 3: return min(np.linalg.norm(p - x) for x in C) < 1e-9 if C else False
    V = np.array(C); return all(((V[(i + 1) % len(V)] - V[i])[0] * (p - V[i])[1] - (V[(i + 1) % len(V)] - V[i])[1] * (p - V[i])[0]) >= -1e-9 for i in range(len(V)))
if __name__ == "__main__":
    for mode in ["alt", "rand"]:
     print(f"mode {mode}; T, seeds 0..9: regret / ((1 + Delta(u)/Gamma) log2 T), max over seeds; phases")
     for T in [10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6, 10 ** 7]:          # shortcut: double precision, cond(V) ~ 1e11 at T = 1e8
         rs, ph_ = [], []
         for s in range(10):
             reg, Du, Gam, P = run(T, s, mode); rs.append(reg / ((1 + Du / Gam) * math.log2(T))); ph_.append(P)
         print(f"T=1e{int(math.log10(T))}: max ratio {max(rs):.2f}, mean {np.mean(rs):.2f}, phases {min(ph_)}..{max(ph_)}", flush=True)
