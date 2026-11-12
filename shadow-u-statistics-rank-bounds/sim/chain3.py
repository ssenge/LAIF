# Checks for the chain bound of centred projected shadows under a 3-design, with asserts.
# The outcome law of one global shadow X = (d+1) |phi><phi| - I under the state rho has density d <phi|rho|phi> with respect
# to a projective 3-design (here: all stabilizer states on 1 and 2 qubits). Checked exactly by enumeration:
#  (1) the exact second moments of X under rho (Lemma 5), and E_rho[X C X] <= ((3d+4)/(d+2)) tr(C) I for C >= 0, for random
#      states rho of every rank;
#  (2) E_rho|tr(X M)|^2 <= ((3d+4)/(d+2)) ||M||_2^2 for complex M;
#  (3) the chain bound E|tr(E_1 B_1 ... E_j B_j)|^2 <= 3^j prod ||B_i||_2^2 for independent E_i = P X_i P - A, A = P rho P,
#      j <= 4 for d = 2 and j <= 3 for d = 4, with random B_i and with B_i = A^{e_i};
#  (4) the order-j components zeta_{j,k} of the symmetrized trace kernel h_k (k <= 4, j <= k) against (3s)^j D^{2(k-j)},
#      D = ||A||_op, and against 3s(d+1)^{2(j-1)} D^{2(k-j)}.
# python -I chain3.py
import itertools
import math
import numpy as np

rng = np.random.default_rng(7)


def stabilizer_states(q):
    """All stabilizer states on q = 1, 2 qubits as unit vectors (up to phase)."""
    s = 1 / math.sqrt(2)
    one = [np.array(v, dtype=complex) for v in ([1, 0], [0, 1], [s, s], [s, -s], [s, 1j * s], [s, -1j * s])]
    if q == 1:
        return one
    cand = [np.kron(a, b) for a in one for b in one]
    for a, b in itertools.product(one, one):
        if abs(np.vdot(a, b)) < 1e-9:
            for w in (1, -1, 1j, -1j):
                cand.append((np.kron([1, 0], a) + w * np.kron([0, 1], b)) * s)
    seen = []
    for v in cand:
        if all(abs(abs(np.vdot(u, v)) - 1) > 1e-9 for u in seen):
            seen.append(v)
    return seen


def rand_state(d, rank):
    G = rng.normal(size=(d, rank)) + 1j * rng.normal(size=(d, rank))
    R = G @ G.conj().T
    return R / np.trace(R).real


def rand_proj(d, s):
    Q, _ = np.linalg.qr(rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)))
    return Q[:, :s] @ Q[:, :s].conj().T


def cmat(d):
    return rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))


def fro2(B):
    return np.linalg.norm(B) ** 2


for q in (1, 2):
    St = stabilizer_states(q)
    d = 2 ** q
    assert len(St) == (6 if q == 1 else 60)
    I = np.eye(d)
    Xs = [(d + 1) * np.outer(v, v.conj()) - I for v in St]
    c3 = (3 * d + 4) / (d + 2)
    worst = [0.0, 0.0]
    for trial in range(20):
        rho = rand_state(d, 1 + trial % d)
        w = np.array([d * np.vdot(v, rho @ v).real for v in St]) / len(St)
        assert abs(w.sum() - 1) < 1e-12 and np.allclose(sum(wi * X for wi, X in zip(w, Xs)), rho)
        G = cmat(d); C = G @ G.conj().T
        XCX = sum(wi * X @ C @ X for wi, X in zip(w, Xs))
        tC = np.trace(C); exact = (d + 1) / (d + 2) * (tC * (I + rho) + np.trace(C @ rho) * I) - (C + C @ rho + rho @ C) / (d + 2)
        assert np.allclose(XCX, exact)
        Ga, Gb = cmat(d), cmat(d)
        lhs = sum(wi * np.trace(X @ Ga) * np.trace(X @ Gb) for wi, X in zip(w, Xs))
        ta, tb = np.trace(Ga), np.trace(Gb); ra, rb = np.trace(Ga @ rho), np.trace(Gb @ rho)
        rhs = (d + 1) / (d + 2) * (ta * tb + np.trace(Ga @ Gb) + ta * rb + tb * ra + np.trace(Ga @ Gb @ rho)
                                   + np.trace(Gb @ Ga @ rho)) - ta * tb - ra * tb - ta * rb
        assert abs(lhs - rhs) < 1e-9
        assert np.linalg.eigvalsh(c3 * np.trace(C).real * I - XCX).min() > -1e-9
        worst[0] = max(worst[0], np.linalg.eigvalsh(XCX).max() / np.trace(C).real)
        M = cmat(d)
        val = sum(wi * abs(np.trace(X @ M)) ** 2 for wi, X in zip(w, Xs))
        assert val <= c3 * fro2(M) + 1e-9
        worst[1] = max(worst[1], val / fro2(M))
    print(f"d = {d}: E[XCX] <= {c3:.3f} tr(C) I and E|tr(XM)|^2 <= {c3:.3f} ||M||^2 (largest ratios {worst[0]:.3f}, {worst[1]:.3f})")

    # (3) chain bound, exact over all tuples of outcomes
    for s in range(1, d + 1):
        for j in (1, 2, 3) if d == 4 else (1, 2, 3, 4):
            ratio = 0.0
            for trial in range(2):
                rho = rand_state(d, 1 + trial % d); P = rand_proj(d, s); A = P @ rho @ P
                w = np.array([d * np.vdot(v, rho @ v).real for v in St]) / len(St)
                Es = [P @ X @ P - A for X in Xs]
                for kind in ("random", "powers"):
                    if kind == "random":
                        Bs = [cmat(d) for _ in range(j)]
                    else:
                        es = rng.integers(0, 3, size=j)
                        Bs = [np.linalg.matrix_power(A, int(e)) if e > 0 else P for e in es]
                    bound = 3 ** j * np.prod([fro2(B) for B in Bs])
                    tot = 0.0
                    for idx in itertools.product(range(len(St)), repeat=j):
                        Mx = np.eye(d, dtype=complex)
                        for a, B in zip(idx, Bs):
                            Mx = Mx @ Es[a] @ B
                        tot += abs(np.trace(Mx)) ** 2 * np.prod(w[list(idx)])
                    assert tot <= bound * (1 + 1e-9), (d, s, j, kind, tot, bound)
                    ratio = max(ratio, tot / bound)
            print(f"d = {d}, s = {s}, j = {j}: chain bound holds (largest ratio {ratio:.3f})")

    # (4) order-j components of the symmetrized kernel h_k
    for s in range(1, d + 1):
        rho = rand_state(d, d); P = rand_proj(d, s); A = P @ rho @ P
        D = np.linalg.eigvalsh(A).max()
        w = np.array([d * np.vdot(v, rho @ v).real for v in St]) / len(St)
        Es = [P @ X @ P - A for X in Xs]
        for k in range(1, 5):
            for j in range(1, k + 1):
                if len(St) ** j > 300000:
                    continue
                perms = list(itertools.permutations(range(k)))
                zeta = 0.0
                for idx in itertools.product(range(len(St)), repeat=j):
                    args = [Es[a] for a in idx] + [A] * (k - j)
                    h = sum(np.trace(np.linalg.multi_dot([args[p] for p in pi]) if k > 1 else args[0]).real
                            for pi in perms) / len(perms)
                    zeta += h ** 2 * np.prod(w[list(idx)])
                ours = (3 * s) ** j * D ** (2 * (k - j))
                prev = 3 * s * (d + 1) ** (2 * (j - 1)) * D ** (2 * (k - j))
                assert zeta <= ours * (1 + 1e-9), (d, s, k, j, zeta, ours)
                print(f"d = {d}, s = {s}, k = {k}, j = {j}: zeta = {zeta:.3e} <= (3s)^j D^(2(k-j)) = {ours:.3e}"
                      f" (3s(d+1)^(2(j-1)) D^(2(k-j)) = {prev:.3e})")
print("chain bound checks: ok")
