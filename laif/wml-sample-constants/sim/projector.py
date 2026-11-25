"""WML lower bound with the projector L = |0><0| (the witness of [1, Thm 10]): input |0><0| is fixed by e^{t Lind},
the one-step error is Delta^2 (d-1)/4 + O(Delta^3), and the errors add up linearly for every t, so
n * error / t^2 -> (d-1)/4 for all t (compared with d/32 in [1, Thm 10]). Certificate: the plain state |0><0|."""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "RAYON_NUM_THREADS"):
    os.environ[_v] = "1"
import numpy as np
from scipy.linalg import expm
from wml import step, lind
for d in (2, 3, 5, 8):
    L = np.zeros((d, d), complex); L[0, 0] = 1; X = np.zeros((d, d)); X[0, 0] = 1; x = X.reshape(-1, order="F")
    for t in (0.02, 0.5, 2.0, 8.0):
        n = 400 * (int(2 * d * t) + 1)
        P = np.linalg.matrix_power(step(L, t / n), n)
        Y = ((expm(t * lind(L)) - P) @ x).reshape(d, d, order="F")
        val = n * 0.5 * np.abs(np.linalg.eigvalsh((Y + Y.conj().T) / 2)).sum() / t**2
        print("d=%d t=%4.2f n=%6d  n*err/t^2 = %.4f   (d-1)/4 = %.4f   [1, Thm 10] d/32 = %.4f" % (d, t, n, val, (d - 1) / 4, d / 32))
        assert abs(val - (d - 1) / 4) < 0.02 * (d - 1) / 4 and val > d / 32
