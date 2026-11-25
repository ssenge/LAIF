"""Corrected one-step bound (1/2)||e^{Delta Lind} - Phi_Delta||_diamond <= Delta^2 ||L||_inf^2 (d/2 + e^{1/d} ||L||_inf^2)
for Delta <= 1/(2d): tested with exact SDP diamond norms on random and structured L. Also checks that the bound
is not vacuous: the nilpotent L = |0><1| comes within a factor < 2 of it."""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "NUMEXPR_NUM_THREADS", "RAYON_NUM_THREADS"):
    os.environ[_v] = "1"          # single core: set before numpy, scipy and cvxpy load their thread pools

import warnings, numpy as np
from scipy.linalg import expm
from wml import step, lind, diamond
warnings.filterwarnings("ignore")
rng = np.random.default_rng(7); worst = 0
for d in (2, 3, 4, 5):
    Ls = []
    for _ in range(12):
        L = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        if rng.random() < 0.5: L = np.outer(L[:, 0], L[0].conj())       # rank one
        Ls.append(L / np.linalg.norm(L))
    N = np.zeros((d, d), complex); N[0, 1] = 1; Ls.append(N)
    for L in Ls:
        Delta = rng.uniform(0.02, 1) / (2 * d); n2 = np.linalg.norm(L, 2)**2
        err = 0.5 * diamond(expm(Delta * lind(L)) - step(L, Delta), d)
        b = Delta**2 * n2 * (d / 2 + np.exp(1 / d) * n2)
        worst = max(worst, err / b); assert err <= b * (1 + 1e-6), (d, err, b)
    print("d=%d ok, worst ratio so far %.4f" % (d, worst), flush=True)
