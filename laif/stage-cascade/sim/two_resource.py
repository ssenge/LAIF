"""Cascade sign with an ontogenetic niche shift: adult reproduction limited by summer forage G,
juveniles and adults browse saplings S in winter, juvenile maturation fed by browse.
  G' = rG G (1 - G/KG) - iA A G
  S' = rS S (1 - S/KS) - (bJ J + bA A) S
  J' = e iA A G - (k bJ S + dJ + pJ W) J
  A' = k bJ S J - (dA + pA W) A
  W' = W (eW (pJ J + pA A) - dW)
Prints how often the predator lowers S (reversed cascade), by predation mode."""
import sys
import numpy as np
from scipy.optimize import fsolve

def rhs(x, p):
    G, S, J, A, W = x
    rG, KG, iA, rS, KS, bJ, bA, e, k, dJ, dA, pJ, pA, eW, dW = p
    return np.array([rG*G*(1-G/KG) - iA*A*G, rS*S*(1-S/KS) - (bJ*J + bA*A)*S,
                     e*iA*A*G - (k*bJ*S + dJ + pJ*W)*J, k*bJ*S*J - (dA + pA*W)*A,
                     W*(eW*(pJ*J + pA*A) - dW)])

def stable_eq(p, withW, rng, tries=60):
    n = 5 if withW else 4
    f = lambda y: rhs(np.r_[y, np.zeros(5-n)], p)[:n]
    found = []
    for _ in range(tries):
        y0 = np.r_[rng.uniform(0.05, 1, 2), np.exp(rng.uniform(-3, 1, 3))][:n]
        y, _, ok, _ = fsolve(f, y0, full_output=True)
        if ok != 1 or np.any(y <= 1e-9) or np.max(np.abs(f(y))) > 1e-10: continue
        if any(np.allclose(y, z, rtol=1e-6) for z in found): continue
        h = 1e-7; Jm = np.array([(f(y + h*np.eye(n)[j]) - f(y - h*np.eye(n)[j]))/(2*h) for j in range(n)]).T
        if np.max(np.linalg.eigvals(Jm).real) < -1e-9: found.append(y)
    return found

if __name__ == "__main__":
    rng = np.random.default_rng(int(sys.argv[1])); N = int(sys.argv[2])
    for mode in ("J", "A"):
        cnt = {"up": 0, "down": 0, "skip": 0}; ex = None
        for _ in range(N):
            rG, KG, rS, KS = 1.0, 1.0, rng.uniform(0.2, 2), 1.0
            iA, bJ, bA = np.exp(rng.uniform(np.log(0.5), np.log(20), 3))
            e, k = rng.uniform(0.1, 0.9), rng.uniform(0.1, 1)
            dJ, dA = np.exp(rng.uniform(np.log(0.01), np.log(0.5), 2))
            pJ, pA = (1.0, 0.0) if mode == "J" else (0.0, 1.0)
            p = [rG, KG, iA, rS, KS, bJ, bA, e, k, dJ, dA, pJ, pA, 1.0, 0.0]
            s0 = stable_eq(p, False, rng)
            if len(s0) != 1: cnt["skip"] += 1; continue
            x0 = s0[0]; p[14] = (pJ*x0[2] + pA*x0[3])*rng.uniform(0.2, 0.95)
            s1 = [y for y in stable_eq(p, True, rng) if y[4] > 1e-8]
            if len(s1) != 1: cnt["skip"] += 1; continue
            x1 = s1[0]
            if x1[1] < x0[1] - 1e-9:
                cnt["down"] += 1; ex = ex or (np.round(p, 3), np.round(x0, 4), np.round(x1, 4))
            else: cnt["up"] += 1
        print(mode, cnt)
        if ex: print("   p =", ex[0], "\n   G,S,J,A before:", ex[1], "\n   G,S,J,A,W after:", ex[2])
