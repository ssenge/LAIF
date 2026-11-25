"""Sign of the trophic cascade when a stage-selective predator invades.

Model (biomass, deterministic):
  R' = r R (1 - R/K) - (iJ J + iA A) R                  saplings (browsable regeneration)
  J' = e iA A R - k iJ R J - dJ J - pJ W J               juveniles: born from adult intake, mature with own intake
  A' = k iJ R J - dA A - pA W A                          adults
  W' = W (eW (pJ J + pA A) - dW)                         predator
Compares the stable equilibrium without W and with W (when W can invade); reports the sign of the change in R.
"""
import sys
import numpy as np
from scipy.optimize import fsolve

def rhs(x, p, withW=True):
    R, J, A, W = x
    if not withW:
        W = 0.0
    r, K, iJ, iA, e, k, dJ, dA, pJ, pA, eW, dW = p
    return np.array([r*R*(1-R/K) - (iJ*J + iA*A)*R,
                     e*iA*A*R - k*iJ*R*J - dJ*J - pJ*W*J,
                     k*iJ*R*J - dA*A - pA*W*A,
                     W*(eW*(pJ*J + pA*A) - dW) if withW else 0.0])

def jac(x, p, withW, h=1e-7):
    n = 4 if withW else 3
    J = np.zeros((n, n))
    for j in range(n):
        d = np.zeros(4); d[j] = h*max(1.0, abs(x[j]))
        J[:, j] = ((rhs(x+d, p, withW) - rhs(x-d, p, withW))/(2*d[j]))[:n]
    return J

def equilibria(p, withW, rng, tries=40):
    out = []
    n = 4 if withW else 3
    for _ in range(tries):
        x0 = np.exp(rng.uniform(-3, 2, 4)); x0[0] = rng.uniform(0.01, 1)*p[1]
        if not withW: x0[3] = 0
        f = lambda y: rhs(np.r_[y, np.zeros(4-n)], p, withW)[:n]
        y, info, ok, _ = fsolve(f, x0[:n], full_output=True)
        if ok != 1 or np.any(y <= 1e-9) or np.max(np.abs(f(y))) > 1e-9:
            continue
        x = np.r_[y, np.zeros(4-n)]
        if any(np.allclose(x, z, rtol=1e-6) for z in out):
            continue
        out.append(x)
    stable = [x for x in out if np.max(np.linalg.eigvals(jac(x, p, withW)).real) < -1e-9]
    return out, stable

def sample(rng, mode):
    r, K = 1.0, 1.0
    iJ, iA = np.exp(rng.uniform(np.log(0.5), np.log(20), 2))
    e = rng.uniform(0.1, 0.9); k = rng.uniform(0.1, 1.0)
    dJ, dA = np.exp(rng.uniform(np.log(0.01), np.log(0.5), 2))
    pJ, pA = {"J": (1.0, 0.0), "A": (0.0, 1.0), "mix": tuple(rng.uniform(0, 1, 2))}[mode]
    eW = 1.0; dW = 0.0  # dW set below relative to the predator-free state
    return [r, K, iJ, iA, e, k, dJ, dA, pJ, pA, eW, dW]

if __name__ == "__main__":
    rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    for mode in ("J", "A", "mix"):
        cnt = {"up": 0, "down": 0, "skip": 0}; ex = None
        for _ in range(N):
            p = sample(rng, mode)
            _, st0 = equilibria(p, False, rng)
            if len(st0) != 1:
                cnt["skip"] += 1; continue
            x0 = st0[0]
            food = p[8]*x0[1] + p[9]*x0[2]
            p[11] = p[10]*food*rng.uniform(0.2, 0.9)          # predator can invade
            _, st1 = equilibria(p, True, rng)
            st1 = [x for x in st1 if x[3] > 1e-8]
            if len(st1) != 1:
                cnt["skip"] += 1; continue
            x1 = st1[0]
            if x1[0] < x0[0] - 1e-9:
                cnt["down"] += 1; ex = ex or (p, x0, x1)
            else:
                cnt["up"] += 1
        print(mode, cnt)
        if ex:
            p, x0, x1 = ex
            print("   example p =", np.round(p, 4), "\n   R,J,A without W:", np.round(x0[:3], 4), " with W:", np.round(x1, 4))
