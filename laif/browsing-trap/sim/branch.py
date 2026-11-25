"""Exact equilibrium branch of the one-species browsing-trap model (see trap.py), parametrized by the canopy share C.
At equilibrium the per-sapling exit rate O = g + m + mu*phi must equal O*(C) = ((1-C)/kappa)^(1/k), kappa = mC/(e f g^k).
Then phi = (O* - g - m)/mu, N = f C (1-C)/O* * sum_{c<k} (g/O*)^c, and D(C) = phi (1 + a h N)/a.
Recovery density D_r = D(0+) (invasion threshold); collapse density D_c = max_C D(C); hysteresis iff D_c > D_r."""
import sys
import numpy as np
from trap import make, settle

def D_of_C(C, f, g, mC, k, a, h, mu, m, e):
    kappa = mC/(e*f*g**k)
    O = ((1 - C)/kappa)**(1/k)
    phi = (O - g - m)/mu
    N = f*C*(1 - C)/O*sum((g/O)**c for c in range(k))
    return np.where(phi >= 0, phi*(1 + a*h*N)/a, np.nan)

if __name__ == "__main__":
    f, g, mC, a, mu, m, e = 2.0, 0.5, 0.02, 1.0, 1.0, 0.05, 0.05
    for k in (1, 2, 4, 8):
        for h in (0.5, 5.0, 50.0):
            C = np.linspace(1e-6, 0.999, 20001)
            D = D_of_C(C, f, g, mC, k, a, h, mu, m, e)
            Dr = D[0]; i = np.nanargmax(D); Dc = D[i]
            print(f"k={k} h={h:5.1f}  D_r={Dr:.4f}  D_c={Dc:.4f} at C={C[i]:.3f}  width={Dc-Dr:.4f}")
    # ODE check of bistability at a D between D_r and D_c for k=4, h=50
    k, h = 4, 50.0
    C = np.linspace(1e-6, 0.999, 20001); D = D_of_C(C, f, g, mC, k, a, h, mu, m, e)
    Dmid = 0.5*(D[0] + np.nanmax(D))
    rhs, S = make((np.array([f]), np.array([g]), np.array([mC]), np.array([1.0]), k, a, h, mu, m, e))
    hi = settle(rhs, np.r_[np.full(k, 1.0), 0.6], Dmid, T=20000)[-1]
    lo = settle(rhs, np.r_[np.full(k, 1e-3), 1e-3], Dmid, T=20000)[-1]
    print(f"ODE at D={Dmid:.4f}: from high start C={hi:.4f}, from low start C={lo:.6f}")
    assert hi > 0.05 and lo < 1e-4, "expected bistability"
