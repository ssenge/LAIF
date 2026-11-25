
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "NUMEXPR_NUM_THREADS", "RAYON_NUM_THREADS"):
    os.environ[_v] = "1"          # single core: set before numpy, scipy and cvxpy load their thread pools
import numpy as np
from wml import error_map, diamond, sop_lr
# sanity: ||id - U.U+||_diamond for U = diag(1, e^{i a}) is 2 sin(a/2)... check d=2, a=pi/3 -> 1
U = np.diag([1, np.exp(1j * np.pi / 3)]); val = diamond(np.eye(4) - sop_lr(U, U.conj().T), 2)
print("SDP check: %.6f (expect 1)" % val); assert abs(val - 1) < 1e-5
for d in (2, 3, 4, 5):
    out = []
    for th in np.linspace(0, np.pi / 2, 7):
        v = np.zeros(d); v[0] = 1; w = np.zeros(d); w[0] = np.cos(th); w[1] = np.sin(th)
        L = np.outer(v, w).astype(complex)
        out.append((round(th, 3), round(0.5 * diamond(error_map(L), d), 5)))
    print("d=%d  rank-one |v><w|, angle(v,w) -> c = ||E||/2:" % d, out, " paper LB d/32 = %.4f, UB (2d+3)/8 = %.4f" % (d / 32, (2 * d + 3) / 8))
