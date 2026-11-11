"""Three random bases: solve for (psi, u) with I(u) = 0 at a state where every outcome has q > 0.
Unknowns psi, u in C^d. Equations: Re(conj<b|psi> <b|u>) = 0 for every outcome b, Im<psi|u> = 0, |psi| = |u| = 1.
Solution set has expected real dimension d - 2 (plus the joint phase)."""
import sys
import numpy as np
from scipy.optimize import least_squares
from scipy.stats import unitary_group


def split(x, d):
    return x[:d] + 1j * x[d:2 * d], x[2 * d:3 * d] + 1j * x[3 * d:]


def resid(x, Ws):
    d = Ws.shape[1]; psi, u = split(x, d)
    a = Ws @ psi; b = Ws @ u          # rows of Ws are <b_x|, all bases stacked
    return np.concatenate([(a.conj() * b).real, [np.vdot(psi, u).imag, np.vdot(psi, psi).real - 1, np.vdot(u, u).real - 1]])


def solve(Us, starts, rng):
    d = Us[0].shape[0]; Ws = np.vstack([U.conj().T for U in Us]); best = None
    for _ in range(starts):
        r = least_squares(resid, rng.normal(size=4 * d) / np.sqrt(2 * d), args=(Ws,), xtol=1e-15, ftol=1e-15, gtol=1e-15, method="trf", max_nfev=4000)
        psi, u = split(r.x, d)
        qmin = np.min(np.abs(Ws @ psi) ** 2)
        res = np.max(np.abs(r.fun))
        cand = (res, -qmin, r.x)
        if res < 1e-13 and qmin > 1e-6:   # regular zero found
            return res, qmin, r.x
        if best is None or cand[:2] < best[:2]: best = cand
    return best[0], -best[1], best[2]


if __name__ == "__main__":
    K = int(sys.argv[1]); rng = np.random.default_rng(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    n = int(sys.argv[3]) if len(sys.argv) > 3 else 10
    for d in [2, 3, 4, 5, 6, 8, 10, 12]:
        found = 0; worst = []
        for inst in range(n):
            Us = [unitary_group.rvs(d, random_state=rng) for _ in range(K)]
            res, q, x = solve(Us, 40, rng)
            ok = res < 1e-13 and q > 1e-6
            found += ok; worst.append((res, q))
        print(f"K={K} d={d}: regular zero found in {found}/{n} instances; max residual {max(w[0] for w in worst):.1e}, min q at zeros {min(w[1] for w in worst):.1e}", flush=True)
