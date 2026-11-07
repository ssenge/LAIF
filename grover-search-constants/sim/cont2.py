"""Continuum limit for schedules whose ratios repeat with period P, k fixed per round (alpha = 1), random offset."""
import numpy as np
from scipy.optimize import minimize
from cont import s
def Cp(logr, al=1.0, M=300):
    r = np.exp(logr); P = len(r); L = np.log(r).sum()          # log-period
    if np.any(r < 1.02): return 9
    tot = 0
    for u in (np.arange(M) + 0.5) / M:
        # sequence of log y: start far below, steps log r cyclic; random offset u * L
        ly = -14 + u * L; surv, e, i = 1.0, 0.0, 0
        while ly < 9 and surv > 1e-15:
            y = np.exp(ly); e += surv * y * (1 + al) / 2; surv *= s(y, al); ly += np.log(r[i % P]); i += 1
        tot += e
    return tot / M
if __name__ == "__main__":
    for P in (1, 2, 3):
        best = None
        for start in ([np.log(1.59)] * P, list(np.log(np.linspace(1.3, 2.0, P)))):
            res = minimize(Cp, start, method="Nelder-Mead", options={"xatol": 1e-4, "fatol": 1e-6, "maxiter": 400})
            if best is None or res.fun < best.fun: best = res
        print(P, "C = %.5f" % best.fun, "ratios", np.round(np.exp(best.x), 4))
