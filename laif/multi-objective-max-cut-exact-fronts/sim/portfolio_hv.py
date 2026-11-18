"""Normalized hypervolumes of the exact mean-variance and mean-CVaR fronts, with the normalization of arXiv:2609.13790
(anchors x = 1 and x = 0, reference point (1.05, 1.05), both objectives minimized). Usage: python -I portfolio_hv.py ../data/portfolio_s0_k4.npz"""
import sys
import os
import numpy as np, moocore
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from scipy.stats import norm
from pareto_dp import nondom

d = np.load(sys.argv[1]); mu, Sig, P, X = d["mu"], d["Sig"], d["P"], d["X"]
n = len(mu); one = np.ones(n); R1, V1 = mu.sum(), one @ Sig @ one
ret, var = P[:, 0], -P[:, 1]
assert np.allclose(X @ mu, ret) and np.allclose(np.einsum("ij,jk,ik->i", X, Sig, X), var)
print(f"mu: sum={R1:.4f} range=[{mu.min():.4f}, {mu.max():.4f}]  1'Sig1={V1:.4f}  dense eig check skipped")
def hv(f1, f2):                                     # minimization, reference (1.05, 1.05)
    F = nondom(-np.column_stack([f1, f2])); return moocore.hypervolume(-F, ref=np.array([1.05, 1.05])), len(F)
h, k = hv((R1 - ret) / R1, var / V1)
print(f"mean-variance: exact Pareto points={len(P)} normalized HV={h:.4f}")
for a in (0.90, 0.95, 0.99):
    kap = norm.pdf(norm.ppf(a)) / (1 - a); cv = -ret + kap * np.sqrt(np.maximum(var, 0)); C1 = -R1 + kap * np.sqrt(V1)
    F = nondom(np.column_stack([ret, -cv]))      # exact mean-CVaR front: non-dominated part of the mean-variance set
    h, k = hv((R1 - F[:, 0]) / R1, -F[:, 1] / C1)
    print(f"mean-CVaR alpha={a}: kappa={kap:.4f} CVaR(1)={C1:.4f} exact points={k} normalized HV={h:.4f}")

# The epsilon-constraint reference of [2609.13790]: min variance s.t. normalized loss <= eps, 1000 equidistant eps in [0, 1].
# Each solution is a point of the exact front (lowest variance among points with f1 <= eps), so it is read off P.
f1, f2 = (R1 - ret) / R1, var / V1
sel = sorted({int(np.flatnonzero(f1 <= e + 1e-12)[np.argmin(f2[f1 <= e + 1e-12])]) for e in np.linspace(0, 1, 1000)})
h, k = hv(f1[sel], f2[sel]); print(f"eps-CM with 1000 values on the exact front: points={len(sel)} normalized HV={h:.4f}")
for a in (0.90, 0.95, 0.99):
    kap = norm.pdf(norm.ppf(a)) / (1 - a); C1 = -R1 + kap * np.sqrt(V1); cv = -ret[sel] + kap * np.sqrt(var[sel])
    h, k = hv(f1[sel], cv / C1); print(f"  its mean-CVaR alpha={a}: points={k} normalized HV={h:.4f}")
