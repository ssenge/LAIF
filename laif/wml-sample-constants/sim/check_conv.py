"""Convention checks for opt.py: the full WML channel S (x) P -> S (one copy, time t) is covariant under cov_rep,
its reduction to a witness equals the WML step of wml.py, and the SDP value is at most the WML error."""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "RAYON_NUM_THREADS"):
    os.environ[_v] = "1"
import numpy as np
from scipy.linalg import expm
from scipy.stats import unitary_group
from opt import cov_rep, program, witness, choi_of_sop, solve
from wml import lind, step, diamond

def wml_full_choi(d, t):
    G = np.eye(d).reshape(-1); SW = np.zeros((d * d, d * d))
    for i in range(d):
        for j in range(d): SW[i * d + j, j * d + i] = 1
    M = np.kron(np.eye(d), np.outer(G, G)) @ np.kron(SW, np.eye(d)) / np.sqrt(d)
    U = expm(t * lind(M)); D = d**3
    J = np.zeros((D * d, D * d), complex)
    for a in range(D):
        for b in range(D):
            X = np.zeros((D, D)); X[a, b] = 1
            Y = (U @ X.reshape(-1, order="F")).reshape(D, D, order="F").reshape(d, d * d, d, d * d)
            J[a * d:(a + 1) * d, b * d:(b + 1) * d] = np.einsum("ajbj->ab", Y)
    return J

for d in (2, 3):
    t = 0.1; J = wml_full_choi(d, t)
    R = cov_rep(unitary_group.rvs(d, random_state=1), 1)
    assert np.abs(R @ J @ R.conj().T - J).max() < 1e-10
    for nm in ("nil", "proj"):
        L = witness(nm, d); K = np.kron(np.kron(np.eye(d), program(L).T), np.eye(d))
        JL = np.einsum("apcbqc->ab", (K @ J).reshape(d, d * d, d, d, d * d, d).transpose(0, 2, 1, 3, 5, 4).reshape(d, d, d * d, d, d, d * d)) if False else None
        X = (K @ J).reshape(d, d * d, d, d, d * d, d)            # (s, p, o ; s', p', o')
        JL = np.einsum("spotqu,pq->sotu", X, np.eye(d * d)).reshape(d * d, d * d)
        assert np.abs(JL - choi_of_sop(step(L, t), d)).max() < 1e-10, nm
    err = {nm: 0.5 * diamond(step(witness(nm, d), t) - expm(t * lind(witness(nm, d))), d) for nm in ("nil", "proj")}
    val, _, _ = solve(1, d, t, ["nil", "proj"])
    print("d=%d t=%.2f  WML errors %s   optimal one-copy error %.4e" % (d, t, {k: round(v, 6) for k, v in err.items()}, val))
    assert val <= max(err.values()) + 1e-6
print("ok")
