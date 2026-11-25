"""Numerical sup over jump operators L (||L||_2 = 1) of the leading WML constant c(L) = ||E_L||_diamond / 2."""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "NUMEXPR_NUM_THREADS", "RAYON_NUM_THREADS"):
    os.environ[_v] = "1"          # single core: set before numpy, scipy and cvxpy load their thread pools

import sys, warnings, numpy as np
from scipy.optimize import minimize
from wml import error_map, diamond
warnings.filterwarnings("ignore")
d = int(sys.argv[1]); rng = np.random.default_rng(d)
def c(x):
    L = (x[:d * d] + 1j * x[d * d:]).reshape(d, d); L /= np.linalg.norm(L)
    return 0.5 * diamond(error_map(L), d)
best = (0, None)
nil = np.zeros(2 * d * d); nil[1] = 1          # L = |0><1|
starts = [nil + 0.05 * rng.normal(size=2 * d * d)] + [rng.normal(size=2 * d * d) for _ in range(5)]
for x0 in starts:
    r = minimize(lambda x: -c(x), x0, method="Nelder-Mead", options={"maxfev": 1500 if d < 4 else 600, "xatol": 1e-5, "fatol": 1e-7})
    if -r.fun > best[0]: best = (-r.fun, r.x)
    print("start -> c = %.5f" % -r.fun, flush=True)
print("d=%d  sup c found %.5f   nilpotent (2d-3)/4 = %.5f   upper d/2+1 = %.3f   paper (2d+3)/8 = %.4f"
      % (d, best[0], (2 * d - 3) / 4, d / 2 + 1, (2 * d + 3) / 8))
L = (best[1][:d * d] + 1j * best[1][d * d:]).reshape(d, d); L /= np.linalg.norm(L)
print("singular values of the best L:", np.round(np.linalg.svd(L, compute_uv=False), 4), " eigenvalues:", np.round(np.linalg.eigvals(L), 4))
