"""n-step WML error for L = |0><1| against Lemma 2 of [1]: (1/2)||e^{t Lind} - Phi_{t/n}^n||_diamond <= (2d+3) t^2 / (8n)
for n > 2dt. Lower bound certificate: the state |1><1| (no reference system). Also the first-order check of the program
convention: (Phi_Delta - id)/Delta -> Lind(L) for the brute-force step."""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "NUMEXPR_NUM_THREADS", "RAYON_NUM_THREADS"):
    os.environ[_v] = "1"          # single core: set before numpy, scipy and cvxpy load their thread pools

import numpy as np
from scipy.linalg import expm
from wml import step, lind, brute_step
d = 5; L = np.zeros((d, d), complex); L[0, 1] = 1
h = 1e-6; fo = (brute_step(L, h) - np.eye(d * d)) / h
print("first order of the brute-force step vs Lind(L): %.1e" % np.abs(fo - lind(L)).max()); assert np.abs(fo - lind(L)).max() < 1e-4
X = np.zeros((d, d)); X[1, 1] = 1; x = X.reshape(-1, order="F")
for d in (5, 6, 8, 12):
    L = np.zeros((d, d), complex); L[0, 1] = 1; X = np.zeros((d, d)); X[1, 1] = 1; x = X.reshape(-1, order="F")
    for t in (0.02, 0.1, 0.5):
        for n in (int(2 * d * t) + 1, 10 * (int(2 * d * t) + 1), 100 * (int(2 * d * t) + 1)):
            P = np.linalg.matrix_power(step(L, t / n), n)
            Y = ((expm(t * lind(L)) - P) @ x).reshape(d, d, order="F")
            err = 0.5 * np.abs(np.linalg.eigvalsh((Y + Y.conj().T) / 2)).sum()
            bound = (2 * d + 3) * t**2 / (8 * n)
            print("d=%2d t=%.2f n=%5d  error %.4e  Lemma 2 bound %.4e  ratio %.4f  n*err/t^2 %.4f (vs (2d-3)/4 = %.3f)"
                  % (d, t, n, err, bound, err / bound, n * err / t**2, (2 * d - 3) / 4))
