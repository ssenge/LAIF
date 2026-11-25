"""Search for pure single-mode states psi in span{|0>,...,|D-1>} maximizing
gap(psi) = ln int |W| - (H_{1/2}(Q) - ln(4 pi)), with H_{1/2}(Q) = 2 ln int sqrt(Q).
A positive gap would violate the conjecture of 2611.30969. Grid quadrature on [-L, L]^2."""
import sys, numpy as np
from math import factorial
from scipy.special import eval_genlaguerre
from scipy.optimize import minimize

def tables(D, L, K):
    x = np.linspace(-L, L, K); X, Y = np.meshgrid(x, x); A = X + 1j * Y; h2 = (x[1] - x[0]) ** 2
    r2 = np.abs(A) ** 2
    Wmn = np.zeros((D, D) + A.shape, complex)                 # W_{mn}(alpha), <m| W-operator |n>
    for m in range(D):
        for n in range(D):
            if m >= n:
                c = (2 / np.pi) * (-1) ** n * np.sqrt(factorial(n) / factorial(m))
                Wmn[m, n] = c * (2 * np.conj(A)) ** (m - n) * np.exp(-2 * r2) * eval_genlaguerre(n, m - n, 4 * r2)
                Wmn[n, m] = np.conj(Wmn[m, n])
    coh = np.array([np.exp(-r2 / 2) * np.conj(A) ** n / np.sqrt(factorial(n)) for n in range(D)])   # <alpha|n>
    return Wmn, coh, h2

def gap(c, T):
    Wmn, coh, h2 = T
    W = np.real(np.einsum("m,mnij,n->ij", np.conj(c), Wmn, c))
    Q = np.abs(np.einsum("nij,n->ij", coh, c)) ** 2 / np.pi
    N = np.log(np.abs(W).sum() * h2)
    H = 2 * np.log(np.sqrt(Q).sum() * h2)
    return N - (H - np.log(4 * np.pi)), W.sum() * h2

def vec(p, D):
    c = p[:D] + 1j * np.r_[0, p[D:]]
    return c / np.linalg.norm(c)

if __name__ == "__main__":
    D = int(sys.argv[1]); rng = np.random.default_rng(int(sys.argv[2]))
    T = tables(D, 8.0, 241)
    if D > 3:                                                # cross-term check: (|0> + 0.1|3>) has negative W
        c = np.zeros(D, complex); c[0] = 1; c[3] = 0.1; c /= np.linalg.norm(c)
        assert gap(c, T)[0] > -1 and np.exp(gap(c, T)[0]) > 0 and np.abs(np.einsum("m,mnij,n->ij", np.conj(c), T[0], c).real).sum() * T[2] > 1.005
    for n in range(D):                                       # number-state sanity check
        e = np.zeros(D); e[n] = 1; g, s = gap(e.astype(complex), T); assert abs(s - 1) < 1e-6
        print("number state", n, "gap", round(-g, 6))
    best = -np.inf
    for t in range(int(sys.argv[3]) if len(sys.argv) > 3 else 40):
        p0 = rng.normal(size=2 * D - 1)
        res = minimize(lambda p: -gap(vec(p, D), T)[0], p0, method="Nelder-Mead", options={"maxiter": 4000, "xatol": 1e-7, "fatol": 1e-10})
        g = -res.fun
        if g > best: best, bc = g, vec(res.x, D)
    print("D", D, "max of N - R:", best, "state", np.round(bc, 4))
