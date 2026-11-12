"""Certified worst-case calls of the bounded-variance mean estimator (me_design.py) for one delta and several
sigma/eps: the design fixes the bands and the angle width eta; every AE run uses eps_AE = sin(eta)/2 and level
alpha = 0.9 delta / (2L - 1); ae_bound.best certifies its worst-case calls to A. Prints one JSON line per point.

usage: certify.py delta inv_eps..."""
import sys, os, json
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "ae"))
import ae_bound, me_design
delta = float(sys.argv[1])
for inv in map(float, sys.argv[2:]):
    eps = 1 / inv
    _, D = me_design.design(eps, delta)
    L = D["L"]; e_ae = np.sin(D["eta"]) / 2; al = 0.9 * delta / (2 * L - 1)
    assert me_design.error(1 + D["r"] ** 2, D["b"], D["rho"], L, D["eta"], D["eta"]) <= eps
    a_last, (q, fsum, a_calls) = ae_bound.best(e_ae, al, 2, 1, 1)
    assert fsum <= al
    total = D["n0"] + (2 * L - 1) * a_calls
    print(json.dumps(dict(delta=delta, inv_eps=inv, design=D, eps_ae=e_ae, alpha=al, alpha_last=a_last,
                          ae_calls=a_calls, total=total, c=total * eps, classical_lb=None)), flush=True)
