"""Exact one-step WML error for L = |0><1| against Lemma 4 of [1]: (1/2)||e^{Delta Lind} - Phi_Delta||_diamond
<= Delta^2 (2d+3)/8 ||L||_inf^2 for Delta < 1/(2d). Lower bound from an explicit input (no reference system needed):
rho = |1><1|, so the certificate is a plain trace norm."""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "NUMEXPR_NUM_THREADS", "RAYON_NUM_THREADS"):
    os.environ[_v] = "1"          # single core: set before numpy, scipy and cvxpy load their thread pools

import numpy as np
from scipy.linalg import expm
from wml import step, lind, diamond, brute_step
for d in (4, 5, 6, 8):
    L = np.zeros((d, d), complex); L[0, 1] = 1
    for Delta in (0.5 / (2 * d), 0.1 / (2 * d)):
        Err = expm(Delta * lind(L)) - step(L, Delta)
        X = np.zeros((d, d)); X[1, 1] = 1
        Y = (Err @ X.reshape(-1, order="F")).reshape(d, d, order="F")
        cert = 0.5 * np.abs(np.linalg.eigvalsh((Y + Y.conj().T) / 2)).sum()
        dia = 0.5 * diamond(Err, d) if d <= 6 else float("nan")
        bound = Delta**2 * (2 * d + 3) / 8
        print("d=%d Delta=%.5f  input |1><1|: %.6e  diamond: %.6e  Lemma 4 bound: %.6e  ratio cert/bound %.4f"
              % (d, Delta, cert, dia, bound, cert / bound))
        if d >= 5 and Delta < 0.02: assert cert > bound
# the exact step itself, from the definition of WML, for d = 5 (system 1, program 2,3: dimension 125; dense
# superoperator of size 15625^2, about 8 GB, so only with the argument --brute)
import sys
if "--brute" not in sys.argv: raise SystemExit
d = 5; L = np.zeros((d, d), complex); L[0, 1] = 1; Delta = 0.005
B = brute_step(L, Delta); X = np.zeros((d, d)); X[1, 1] = 1
Y = ((expm(Delta * lind(L)) - B) @ X.reshape(-1, order="F")).reshape(d, d, order="F")
cert = 0.5 * np.abs(np.linalg.eigvalsh((Y + Y.conj().T) / 2)).sum()
print("d=5 Delta=0.005 brute-force WML step, input |1><1|: %.6e  vs Lemma 4 bound %.6e" % (cert, Delta**2 * 13 / 8))
assert cert > Delta**2 * 13 / 8
