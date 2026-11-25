"""n-stage herbivore, fixed-rate cull on one stage. Reproduction by the last stage, regulated by summer forage G;
all stages browse saplings S; maturation j -> j+1 at rate k_j * S (fed by browse).
Equilibrium of:  G = KG (1 - a.x / rG),  S = KS (1 - b.x / rS),
  x_1' = phi G x_n - (k_1 S + d_1 + h_1) x_1,
  x_j' = k_{j-1} S x_{j-1} - (k_j S + d_j + h_j) x_j   (k_n = 0).
Checks: a cull on stage 1 always raises S (claim 2); a cull on the last stage can lower S (claim 3)."""
import sys
import numpy as np
from scipy.optimize import brentq

def v_of(S, k, d, h):
    """residence times per newborn: v_1 = 1/(k1 S + d1 + h1), v_j = k_{j-1} S v_{j-1}/(k_j S + d_j + h_j)."""
    n = len(d); v = np.zeros(n); out = k*S + d + h
    v[0] = 1/out[0]
    for j in range(1, n): v[j] = k[j-1]*S*v[j-1]/out[j]
    return v

def equilibrium(par, h):
    """Reduce to one equation in S: R0 = phi G v_n = 1 gives G; G = KG(1 - B a.v/rG) gives B; then S = KS(1 - B b.v/rS)."""
    k, d, a, b, phi, KG, rG, KS, rS = par
    def resid(S):
        v = v_of(S, k, d, h)
        G = 1/(phi*v[-1])
        if G >= KG: return np.nan
        B = (1 - G/KG)*rG/(a@v)
        return S - KS*(1 - B*(b@v)/rS)
    Ss = np.linspace(1e-6, KS*(1-1e-9), 4001)
    r = np.array([resid(s) for s in Ss])
    roots = [brentq(resid, Ss[i], Ss[i+1]) for i in range(len(Ss)-1) if np.isfinite(r[i]) and np.isfinite(r[i+1]) and r[i]*r[i+1] < 0]
    return roots

if __name__ == "__main__":
    rng = np.random.default_rng(int(sys.argv[1])); N = int(sys.argv[2]); n = int(sys.argv[3])
    res = {1: [0, 0, 0], n: [0, 0, 0]}
    for _ in range(N):
        k = np.r_[np.exp(rng.uniform(np.log(0.3), np.log(5), n-1)), 0.0]
        d = np.exp(rng.uniform(np.log(0.02), np.log(0.5), n))
        a = np.r_[np.zeros(n-1), 1.0]; b = np.exp(rng.uniform(np.log(0.3), np.log(5), n))
        par = (k, d, a, b, np.exp(rng.uniform(0, 3)), 1.0, 1.0, 1.0, rng.uniform(0.5, 3))
        r0 = equilibrium(par, np.zeros(n))
        if len(r0) != 1: continue
        for st in (1, n):
            h = np.zeros(n); h[st-1] = 0.05
            r1 = equilibrium(par, h)
            if len(r1) != 1: res[st][2] += 1; continue
            res[st][0 if r1[0] > r0[0] else 1] += 1
    print(f"n={n}: cull on stage 1 [S up, S down, skip] = {res[1]};  cull on stage {n}: {res[n]}")
