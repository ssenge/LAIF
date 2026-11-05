"""The quantum exponent of the label scheme for Subset Balancing on [-d:d], at a given solution profile.
A label is a pair of integer intervals S, T with S - T inside [-d:d]. Each coordinate of value c in a label takes
(x, y) in S x T with x - y = c. The minimum over the joint distribution uses exact gradients."""
import math, sys
import numpy as np
from scipy.optimize import minimize

LN2 = math.log(2)

def wide_labels(d):
    """The labels of full width s + t = 2d."""
    return [(s, 2*d - s, s - d) for s in range(2*d + 1)]

def labels(d):
    out = []
    for s in range(0, 2*d + 1):
        for t in range(0, 2*d + 1 - s):
            for o in range(-2*d, 2*d + 1):          # S = [0 : s], T = [o : o+t]
                if -o - t >= -d and s - o <= d:
                    out.append((s, t, o))
    return out

class Scheme:
    def __init__(self, d, labs):
        self.d, self.labs = d, labs
        cells = [(L, x, o + y) for L, (s, t, o) in enumerate(labs) for x in range(s + 1) for y in range(t + 1)]
        self.c = np.array([x - y for _, x, y in cells])
        self.L = np.array([L for L, _, _ in cells])
        self.x = np.array([x for _, x, _ in cells])
        self.y = np.array([y for _, _, y in cells])
        self.n = len(cells)
        code = lambda *a: np.unique(np.stack(a, axis=1), axis=0, return_inverse=True)[1].ravel()
        self.kL, self.kC = code(self.L), code(self.c)
        self.kCL, self.kXL, self.kYL = code(self.c, self.L), code(self.x, self.L), code(self.y, self.L)
        self.kAll = np.arange(self.n)
        # a (c, L) class with more than one pair has varying representations
        self.varying = np.bincount(self.kCL)[self.kCL] > 1

    def H(self, q, k):
        m = np.bincount(k, weights=q)
        m = np.maximum(m, 1e-300)
        grad = -np.log2(m)[k] - 1/LN2
        return float(-(m*np.log2(m)).sum()), grad

    def parts(self, q):
        hL, gL = self.H(q, self.kL)
        hCL, gCL = self.H(q, self.kCL)
        hC, gC = self.H(q, self.kC)
        hA, gA = self.H(q, self.kAll)
        hX, gX = self.H(q, self.kXL)
        hY, gY = self.H(q, self.kYL)
        a, da = hC + hL - hCL, gC + gL - gCL
        a0, da0 = hA - hCL, gA - gCL
        ux, dux = hX - hL, gX - gL
        uy, duy = hY - hL, gY - gL
        return (a, a0, ux, uy), (da, da0, dux, duy)

    def value(self, q):
        q = np.maximum(q, 1e-15)
        (a, a0, ux, uy), (da, da0, dux, duy) = self.parts(q)
        u, du = (ux, dux) if ux >= uy else (uy, duy)
        if 4*u - 10*a0 >= 0:
            return a/2 + (4*u - 3*a0)/7, da/2 + (4*du - 3*da0)/7
        return (a/2 + a0, da/2 + da0) if a0 >= 2/3*(u - a0) else (a/2 + 2/3*(u - a0), da/2 + 2/3*(du - da0))

    def empty_start(self, pi):
        """All mass on the two labels with one constant list, split evenly: the scheme with no representations."""
        d = self.d
        q = np.zeros(self.n)
        for i in range(self.n):
            lab = self.labs[self.L[i]]
            if lab in ((2*d, 0, d), (0, 2*d, -d)) and self.c[i] in pi:
                q[i] = pi[self.c[i]]/2
        return q

    def support_margin(self, q, pi):
        """1 - pi(0) minus the mass on which representations vary; it must be positive."""
        return 1 - pi.get(0, 0.0) - float(q[self.varying].sum())

    def solve(self, pi, starts=4, seed=0, warm=None, margin=1e-3):
        rng = np.random.default_rng(seed)
        cs = sorted(pi)
        idx = {c: np.where(self.c == c)[0] for c in cs}
        cons = [{"type": "eq", "fun": (lambda q, c=c: q[idx[c]].sum() - pi[c]),
                 "jac": (lambda q, c=c: (self.c == c).astype(float))} for c in cs]
        cons.append({"type": "ineq", "fun": lambda q: self.support_margin(q, pi) - margin,
                     "jac": lambda q: -self.varying.astype(float)})
        bounds = [(0, 1) if c in pi else (0, 0) for c in self.c]
        best = (9.0, None)
        tries = ([warm] if warm is not None else []) + [self.empty_start(pi)] + [None]*starts
        for q0 in tries:
            if q0 is None:
                q0 = np.zeros(self.n)
                for c in cs:
                    q0[idx[c]] = rng.dirichlet(np.ones(len(idx[c])))*pi[c]
            r = minimize(self.value, q0, jac=True, method="SLSQP", bounds=bounds, constraints=cons,
                         options=dict(maxiter=400, ftol=1e-10))
            q = np.maximum(r.x, 0)
            if abs(q.sum() - 1) < 1e-6 and self.support_margin(q, pi) > 0 and r.fun < best[0]:
                best = (float(r.fun), q)
        return best

def profile(d, w):
    pi = {0: w[0]} if w[0] > 0 else {}
    for c in range(1, d + 1):
        if w[c] > 0:
            pi[c] = pi[-c] = w[c]/2
    return pi

def entropy(pi):
    return -sum(v*math.log2(v) for v in pi.values() if v > 0)

if __name__ == "__main__":
    S = Scheme(1, labels(1))
    print(f"d=1 p=.25 L={S.solve(profile(1, [.25, .75]), starts=8)[0]:.5f}")
