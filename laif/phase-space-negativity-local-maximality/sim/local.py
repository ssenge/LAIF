"""Directional check near the vacuum: psi_t = (|0> + t phi)/sqrt(1 + t^2), phi orthogonal to |0>.
Predicted: R(t) - N(t) ~ t^2 (S/2 - 1), S = sum_n |phi_n|^2 2^n, when S > 2; for phi = |1>, ~ t^4 / 2.
N = ln int|W|, R = 2 ln int sqrt(Q) - ln(4 pi)."""
import numpy as np
from search import tables, gap
D = 6
T = tables(D, 8.0, 481)
dirs = {"|1>": [0, 1, 0, 0, 0, 0], "|2>": [0, 0, 1, 0, 0, 0], "|3>": [0, 0, 0, 1, 0, 0],
        "(|1>+|2>)/sqrt2": [0, 1, 1, 0, 0, 0], "(|1>+i|3>)/sqrt2": [0, 1, 0, 1j, 0, 0]}
for name, v in dirs.items():
    phi = np.array(v, complex); phi /= np.linalg.norm(phi)
    S = float(np.sum(np.abs(phi) ** 2 * 2.0 ** np.arange(D)))
    for t in [0.2, 0.1, 0.05, 0.025]:
        c = np.zeros(D, complex); c[0] = 1; c = c + t * phi; c /= np.linalg.norm(c)
        g = -gap(c, T)[0]
        pred = t ** 2 * (S / 2 - 1) if S > 2 + 1e-12 else t ** 4 / 2
        print(f"{name:18s} S={S:5.2f} t={t:5.2f}  R-N={g:.6e}  predicted={pred:.6e}  ratio={g / pred:.4f}")
        assert g > 0
