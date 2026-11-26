"""Theorem 5, numerically: the optimal one-copy channel over the orbits of |0><0| and of (|0><0| + delta E_ab)/norm
(a set whose programs span all program operators) has error/t^2 -> (d-1)/4 as t -> 0, with an O(t) deficit."""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "RAYON_NUM_THREADS"):
    os.environ[_v] = "1"
import warnings; warnings.filterwarnings("ignore")
from opt2 import solve
for d in (2, 3):
    W = ["proj"] + ["near%d_%d_%s" % (a, b, p) for a in range(d) for b in range(d) for p in ("re", "im")]
    vals = []
    for t in (0.04, 0.02, 0.01):
        v = solve(1, d, t, W)[0] / t**2; vals.append(v)
        print("d=%d t=%.2f  optimal one-copy error / t^2 = %.4f   (d-1)/4 = %.4f" % (d, t, v, (d - 1) / 4), flush=True)
    c = (d - 1) / 4
    assert vals[0] < vals[1] < vals[2] < c + 2e-3                         # increasing towards (d-1)/4
    assert 1.6 < (c - vals[0]) / (c - vals[1]) < 2.4 and 1.6 < (c - vals[1]) / (c - vals[2]) < 2.4   # deficit O(t)
print("ok")
