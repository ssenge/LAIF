"""Exact matchgate shadows on m = 3 modes: the discrete matchgate group is enumerated
(signed permutations of the 2m self-adjoint generators of the fermionic algebra), the shadow channel is formed exactly, and
the second moment of the estimator of a determinant-state fidelity is compared with b(m) of bvar.py."""
import numpy as np, itertools
from bvar import b_exact
from math import comb
rng = np.random.default_rng(7)
m = 3; D = 2 ** m
X = np.array([[0, 1], [1, 0]]); Y = np.array([[0, -1j], [1j, 0]]); Z = np.diag([1, -1]); I2 = np.eye(2)
def kron(*a):
    r = np.eye(1)
    for x in a: r = np.kron(r, x)
    return r
gam = []
for j in range(m):
    pre = [Z] * j; post = [I2] * (m - j - 1)
    gam += [kron(*pre, X, *post), kron(*pre, Y, *post)]
def orth(U):  # U gamma_a U^dag = sum_b R_ba gamma_b
    return np.array([[np.trace(gam[b].conj().T @ U @ gam[a] @ U.conj().T).real / D for b in range(2 * m)] for a in range(2 * m)])
gens = [(np.eye(D) + gam[a] @ gam[a + 1]) / np.sqrt(2) for a in range(2 * m - 1)] + [gam[0]]
key = lambda R: tuple(np.rint(R).astype(int).ravel())
seen = {key(np.eye(2 * m)): np.eye(D, dtype=complex)}; frontier = list(seen.values())
while frontier:
    nxt = []
    for U in frontier:
        for g in gens:
            V = g @ U; k = key(orth(V))
            if k not in seen: seen[k] = V; nxt.append(V)
    frontier = nxt
G = list(seen.values())
assert len(G) == 2 ** (2 * m) * 720, len(G)
# shadow channel as a D^2 x D^2 matrix on vec(X)
E = np.eye(D)
Msup = np.zeros((D * D, D * D), complex)
for U in G:
    for b in range(D):
        v = U.conj().T @ E[:, b]
        P = np.outer(v, v.conj()).reshape(-1)
        Msup += np.outer(P, P.conj())
Msup /= len(G)
# predicted inverse: sum_l C(2m,2l)/C(m,l) P_{2l} on even monomials of the generators; check M on them
for S in itertools.chain.from_iterable(itertools.combinations(range(2 * m), k) for k in range(0, 2 * m + 1, 2)):
    op = np.eye(D, dtype=complex)
    for a in S: op = op @ gam[a]
    out = (Msup @ op.reshape(-1)).reshape(D, D)
    l = len(S) // 2
    assert np.allclose(out, op * comb(m, l) / comb(2 * m, 2 * l)), S
Minv = np.linalg.pinv(Msup)
# number operator sectors
occ = np.array([bin(b).count("1") for b in range(D)])
def slater(Uorb):  # columns = orbitals, creation a_j^dag = (gam_{2j} - i gam_{2j+1})/2
    adag = [(gam[2 * j] - 1j * gam[2 * j + 1]) / 2 for j in range(m)]
    vac = np.zeros(D, complex); vac[0] = 1
    # vacuum of a_j: a_j |0..0> = 0 with JW convention: check
    a = [x.conj().T for x in adag]
    for x in a: assert np.allclose(x @ vac, 0)
    s = vac
    for k in range(Uorb.shape[1]):
        s = sum(Uorb[j, k] * adag[j] for j in range(m)) @ s
    return s / np.linalg.norm(s)
bm = float(b_exact(m)); worst = 0
for n in (1, 2):
    for trial in range(6):
        Q, _ = np.linalg.qr(rng.normal(size=(m, n)) + 1j * rng.normal(size=(m, n)))
        s = slater(Q); O = np.outer(s, s.conj())
        Oinv = (Minv.conj().T @ O.reshape(-1)).reshape(D, D)  # adjoint of M^-1 applied to O
        A = np.zeros((D, D), complex)
        for U in G:
            for bb in range(D):
                v = U.conj().T @ E[:, bb]
                o = (v.conj() @ Oinv @ v).real
                A += o ** 2 * np.outer(v, v.conj())
        A /= len(G)
        sec = np.where(occ == n)[0]
        # the n-particle sector in the JW occupation basis is spanned by basis states with n ones
        w = np.linalg.eigvalsh(A[np.ix_(sec, sec)]).max()
        # unbiasedness on a random n-particle state
        psi = np.zeros(D, complex); psi[sec] = rng.normal(size=len(sec)) + 1j * rng.normal(size=len(sec)); psi /= np.linalg.norm(psi)
        mean = sum(abs(np.vdot(U.conj().T @ E[:, bb], psi)) ** 2 * (( U.conj().T @ E[:, bb]).conj() @ Oinv @ (U.conj().T @ E[:, bb])).real for U in G for bb in range(D)) / len(G)
        assert abs(mean - abs(np.vdot(s, psi)) ** 2) < 1e-9
        assert w <= bm + 1e-9, (n, w, bm)
        worst = max(worst, w)
print("group size", len(G), "channel eigenvalues ok, estimator unbiased")
print("largest second moment over determinant-state projectors and n-particle states:", round(worst, 6), " b(3) =", bm)
