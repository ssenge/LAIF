"""Browsing trap: tree species i with canopy share C_i, saplings in k height classes, browsers at density D with a
multi-species Type II functional response.  Per-sapling browse rate of species i:
   phi_i = a pi_i D / (1 + a h sum_j pi_j N_j),  N_j = total browsable saplings of species j.
Browsed saplings die at rate mu*phi_i; unbrowsed classes advance at rate g_i; background death m.
Seed input f_i C_i into class 1 on free space (1 - sum C); escape from class k recruits to the canopy.
  n_{i,1}' = f_i C_i (1 - sum C) - (g_i + m + mu phi_i) n_{i,1}
  n_{i,c}' = g_i n_{i,c-1} - (g_i + m + mu phi_i) n_{i,c}
  C_i'     = e g_i n_{i,k} - mC_i C_i
Sweeps D up and down from both states and reports the hysteresis (collapse and recovery densities)."""
import sys
import numpy as np
from scipy.integrate import solve_ivp

def make(par):
    f, g, mC, pi, k, a, h, mu, m, e = par
    S = len(f)
    def rhs(t, y, D):
        n = y[:S*k].reshape(S, k); C = y[S*k:]
        N = n.sum(1)
        phi = a*pi*D/(1 + a*h*(pi@N))
        out = g + m + mu*phi
        dn = np.empty_like(n)
        dn[:, 0] = f*C*max(0.0, 1 - C.sum()) - out*n[:, 0]
        dn[:, 1:] = g[:, None]*n[:, :-1] - out[:, None]*n[:, 1:]
        dC = e*g*n[:, -1] - mC*C
        return np.r_[dn.ravel(), dC]
    return rhs, S

def settle(rhs, y0, D, T=3000):
    sol = solve_ivp(rhs, (0, T), y0, args=(D,), method="LSODA", rtol=1e-8, atol=1e-11)
    return sol.y[:, -1]

if __name__ == "__main__":
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    # one palatable species (fir-like): f, g, mC, pi
    par = (np.array([2.0]), np.array([0.5]), np.array([0.02]), np.array([1.0]), k, 1.0, 0.5, 1.0, 0.05, 0.05)
    rhs, S = make(par)
    Ds = np.linspace(0.0, 3.0, 61)
    y = np.r_[np.full(S*k, 1.0), np.full(S, 0.5)]
    up = []
    for D in Ds:
        y = settle(rhs, y, D); up.append(y[-S:].copy()); y = np.maximum(y, 0)
    down = []
    for D in Ds[::-1]:
        y = np.maximum(y, 1e-6); y = settle(rhs, y, D); down.append(y[-S:].copy())
    down = down[::-1]
    for D, u, w in zip(Ds, up, down):
        print(f"D={D:4.2f}  C from high state {u[0]:.4f}   C after recovery sweep {w[0]:.4f}")
