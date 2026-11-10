"""Checks for the note on the nonadaptive constant of the ternary family (README.md).

1. Lemma 3: sum_a prod_l mu_l(a_l) <psi|P_a|psi>^2 <= prod_l (sum of the two largest mu_l), for random pure states
   and weights (L <= 4), and at the vertices of the weight polytope.
2. The strategy: information I(a; 0) >= (1/2) q^L, q = 2/(3 - u), the same for every label (L = 1, 2, 3).
3. The weighted budget: sum_a pi(a) I_M(a; 0) <= q^L for random global POVMs on marker and signal (L = 1, 2).
4. L = 1: the exact constant (3 + u)/(1 + u) from the explicit strategy and the matching weighted budget.
5. A table of the bounds.
"""
import itertools

import numpy as np

rng = np.random.default_rng(5)
I2 = np.eye(2, dtype=complex)
PA = {"X": np.array([[0, 1], [1, 0]], complex), "Y": np.array([[0, -1j], [1j, 0]]), "Z": np.diag([1.0 + 0j, -1])}
LET = "XYZ"


def kron(ms):
    out = np.array([[1.0 + 0j]])
    for m in ms:
        out = np.kron(out, m)
    return out


def P(word):
    return kron([PA[c] for c in word])


def top2(m):
    return sum(sorted(m)[-2:])


def rand_state(d):
    v = rng.normal(size=d) + 1j * rng.normal(size=d)
    return v / np.linalg.norm(v)


def check_lemma():
    worst = 0
    for L in range(1, 5):
        words = ["".join(w) for w in itertools.product(LET, repeat=L)]
        mats = [P(w) for w in words]
        for _ in range(300 if L < 4 else 60):
            psi = rand_state(2 ** L)
            ev = np.array([np.vdot(psi, M @ psi).real ** 2 for M in mats])
            for _ in range(5):
                mu = rng.random((L, 3)) ** 3
                w = np.array([np.prod([mu[l][LET.index(c)] for l, c in enumerate(word)]) for word in words])
                worst = max(worst, (w @ ev) / np.prod([top2(m) for m in mu]))
            # vertices: each site one letter (weight 1) or all letters with weight 1/2
            for choice in itertools.product(range(4), repeat=L):
                mu = np.array([[1.0 if k == c else 0.0 for k in range(3)] if c < 3 else [0.5] * 3 for c in choice])
                w = np.array([np.prod([mu[l][LET.index(c)] for l, c in enumerate(word)]) for word in words])
                worst = max(worst, w @ ev)
    assert worst <= 1 + 1e-9
    print(f"1. weighted sum over the bound: largest ratio {worst:.4f} <= 1 (L <= 4, random states, weights and vertices)")


def p_marker(z, a, u):  # z = +1 or -1 (Z outcome of the marker qubit)
    return {"X": (1 - z * u) / 2, "Y": 0.5, "Z": (1 + z * u) / 2}[a]


C = {"XY": I2,
     "YZ": np.array([[1, 1], [1, -1]], complex) / np.sqrt(2),  # sign transform: Z -> X, Y -> -Y
     "XZ": (I2 - 1j * PA["X"]) / np.sqrt(2)}  # rotation about X: Z -> +-Y, X -> X


def ghz_basis(L):
    d = 2 ** L
    out = []
    for x in range(d // 2):
        xb = d - 1 - x
        for sgn in (1, -1):
            v = np.zeros(d, complex)
            v[x], v[xb] = 1 / np.sqrt(2), sgn * np.exp(1j * np.pi / 4) / np.sqrt(2)
            out.append(v)
    return out


def strategy_fisher(L, u):
    """I(a; 0) of: read marker z; per site exclude a letter (X if z = +, Z if z = -, w.p. 1 - r; Y w.p. r);
    measure the signal in the rotated cat basis C^dagger |cat_b>."""
    r = (1 - u) / (3 - u)
    words = ["".join(w) for w in itertools.product(LET, repeat=L)]
    basis = ghz_basis(L)
    cache = {}
    I = {w: 0.0 for w in words}
    for z in itertools.product((1, -1), repeat=L):
        for ex in itertools.product((0, 1), repeat=L):  # 0: exclude the letter the marker disfavours, 1: exclude Y
            pr_ex = np.prod([r if e else 1 - r for e in ex])
            pairs = tuple("XZ" if e else ("YZ" if zl == 1 else "XY") for zl, e in zip(z, ex))
            if pairs not in cache:
                U = kron([C[p] for p in pairs])
                states = [U.conj().T @ v for v in basis]
                cache[pairs] = {w: sum(np.vdot(s, P(w) @ s).real ** 2 for s in states) / 2 ** L for w in words}
            for w in words:
                pz = np.prod([p_marker(zl, c, u) for zl, c in zip(z, w)])
                I[w] += pz * pr_ex * cache[pairs][w]
    return I


def check_strategy():
    for u in (0.1, 0.3, 0.49):
        q = 2 / (3 - u)
        for L in (1, 2, 3):
            I = strategy_fisher(L, u)
            v = min(I.values())
            assert v >= 0.5 * q ** L - 1e-12 and max(I.values()) - v < 1e-12
            print(f"   u={u}, L={L}: I(a; 0) = {v:.6f} for every label, q^L/2 = {0.5 * q ** L:.6f}, q^L = {q ** L:.6f}")
    print("2. the strategy gives the same I(a; 0) >= q^L / 2 for every label (L = 1, 2, 3)")


def fisher_global(E, L, u):
    """I_M(a; 0) for a POVM {E_y} on marker (first L qubits) and signal (last L qubits)."""
    d = 2 ** L
    out = {}
    for w in ("".join(t) for t in itertools.product(LET, repeat=L)):
        tau = kron([(I2 + {"X": -u, "Y": 0, "Z": u}[c] * PA["Z"]) / 2 for c in w])
        rho0, drho = np.kron(tau, np.eye(d)) / d, np.kron(tau, P(w)) / d
        out[w] = sum(np.trace(Ey @ drho).real ** 2 / np.trace(Ey @ rho0).real for Ey in E)
    return out


def rand_povm(D, k):
    V = rng.normal(size=(k, D)) + 1j * rng.normal(size=(k, D))
    S = V.T @ V.conj()  # sum_k v_k v_k^dagger
    w, U = np.linalg.eigh(S)
    T = U @ np.diag(w ** -0.5) @ U.conj().T
    E = [np.outer(T @ v, (T @ v).conj()) for v in V]
    assert np.allclose(sum(E), np.eye(D))
    return E


def check_budget():
    worst = 0
    for u in (0.1, 0.3, 0.49):
        q, s = 2 / (3 - u), 1 / (3 - u)
        for L in (1, 2):
            for _ in range(40):
                E = rand_povm(4 ** L, 4 ** L + rng.integers(0, 8))
                I = fisher_global(E, L, u)
                tot = sum(np.prod([1 - 2 * s if c == "Y" else s for c in w]) * v for w, v in I.items())
                worst = max(worst, tot / q ** L)
    assert worst <= 1 + 1e-9
    print(f"3. random global POVMs: largest sum_a pi(a) I_M(a; 0) / q^L = {worst:.4f} <= 1 (L = 1, 2)")


def check_L1():
    for u in (0.1, 0.3, 0.49):
        z0 = 2 / (3 + u)  # z = +: measure Z w.p. z0, else Y; z = -: X w.p. z0, else Y
        I = {"X": p_marker(-1, "X", u) * z0, "Y": 1 - z0, "Z": p_marker(1, "Z", u) * z0}
        s = 1 / (3 + u)  # dual weights (s, 1 - 2s, s): budget sum_z max_a pi(a) p(z|a)
        dual = sum(max(s * p_marker(z, "X", u), (1 - 2 * s) / 2, s * p_marker(z, "Z", u)) for z in (1, -1))
        target = (1 + u) / (3 + u)
        assert all(abs(v - target) < 1e-12 for v in I.values()) and abs(dual - target) < 1e-12
    print("4. L = 1: strategy and weighted budget both give I* = (1 + u)/(3 + u), constant (3 + u)/(1 + u)")


def table():
    print("5. u, L: paper lower 1/B_L, new lower ((3-u)/2)^L, new upper 2((3-u)/2)^L, paper upper 2^L + 1")
    for u in (0.1, 0.25, 0.49):
        for L in (1, 4, 10, 20):
            B = (2 ** L - 1) * (1 + u) ** L / 3 ** L
            b = (3 - u) / 2
            print(f"   u={u:<5} L={L:<3} {1 / B:12.4g} {b ** L:12.4g} {2 * b ** L:12.4g} {2 ** L + 1:12.4g}")


if __name__ == "__main__":
    check_lemma()
    check_strategy()
    check_budget()
    check_L1()
    table()
    print("all checks passed")
