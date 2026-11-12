"""The determinant energy of floor_k.energy equals <Phi|H|Phi> from exact second quantization (random nk=2 toy)."""
import itertools, numpy as np, openfermion as of
import floor_k, test_dflam
rng = np.random.default_rng(5)
nk, nmo, naux = 2, 2, 3
L = np.empty((nk, nk), dtype=object)
for k1 in range(nk):
    for k2 in range(k1, nk):
        X = rng.normal(size=(naux, nmo, nmo)) + 1j * rng.normal(size=(naux, nmo, nmo))
        if k1 == k2: X = 0.5 * (X + X.conj().transpose(0, 2, 1))
        L[k1, k2], L[k2, k1] = X, X.conj().transpose(0, 2, 1)
h = rng.normal(size=(nk, nmo, nmo)) + 1j * rng.normal(size=(nk, nmo, nmo)); h = 0.5 * (h + h.conj().transpose(0, 2, 1))
H = of.get_sparse_operator(test_dflam.fermion_H(h, L, nk), 2 * nk * nmo).toarray()
idx = lambda k, p, s: 2 * (k * nmo + p) + s
for trial in range(5):
    # random k-diagonal determinant: per k and spin, a random unitary and occupations
    Da, Db, ops = [], [], []
    state = None
    occs = {(k, s): rng.integers(0, nmo + 1) for k in range(nk) for s in range(2)}
    U = {(k, s): np.linalg.qr(rng.normal(size=(nmo, nmo)) + 1j * rng.normal(size=(nmo, nmo)))[0] for k in range(nk) for s in range(2)}
    psi = np.zeros(2**(2 * nk * nmo), complex); psi[0] = 1
    for (k, s), n in occs.items():
        for j in range(n):
            op = sum((of.FermionOperator(((idx(k, p, s), 1),), U[k, s][p, j]) for p in range(nmo)), of.FermionOperator())
            psi = of.get_sparse_operator(op, 2 * nk * nmo) @ psi
    psi /= np.linalg.norm(psi)
    Da = [U[k, 0][:, :occs[k, 0]] @ U[k, 0][:, :occs[k, 0]].conj().T for k in range(nk)]
    Db = [U[k, 1][:, :occs[k, 1]] @ U[k, 1][:, :occs[k, 1]].conj().T for k in range(nk)]
    # convention check: D = C C^dagger gives <a_p^dag a_q> = D[q,p]
    E_ed = (psi.conj() @ H @ psi).real
    E_mine = floor_k.energy(h, L, Da, Db, nk)[0]
    assert abs(E_ed - E_mine) < 1e-9, (E_ed, E_mine)
print("determinant energies match ED")
