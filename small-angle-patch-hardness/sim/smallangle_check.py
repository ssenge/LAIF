"""Checks for the small-angle compilation into the RY-RZ / CZ-ring ansatz.

Ansatz on N qubits (ring), L layers (L even):
  U(theta) = E R_L ... E R_1,  R_l = prod_q exp(-i y_{l,q} Y_q) exp(-i z_{l,q} Z_q),
  E = prod_q CZ(q, q+1 mod N),  C(theta) = <0| U^dag Z_0 U |0>.
Logical qubits sit on even sites, ancillas (kept in |0>) on odd sites.
"""
import numpy as np

X = np.array([[0, 1], [1, 0]], dtype=complex)
Y = np.array([[0, -1j], [1j, 0]])
Z = np.diag([1.0 + 0j, -1.0])


def rot(P, a):
    return np.cos(a) * np.eye(2) - 1j * np.sin(a) * P


def zyz(G):
    """G = phase * rot(Z,a) rot(Y,b) rot(Z,c); returns (a, b, c)."""
    G = G / np.sqrt(np.linalg.det(G))
    b = np.arctan2(abs(G[1, 0]), abs(G[0, 0]))
    s, d = -np.angle(G[0, 0]), np.angle(G[1, 0])  # s = a + c, d = a - c
    a, c = (s + d) / 2, (s - d) / 2
    if np.allclose(rot(Z, a) @ rot(Y, b) @ rot(Z, c), G, atol=1e-9):
        return a, b, c
    a, c = a + np.pi / 2, c - np.pi / 2  # other branch of the phases
    H = rot(Z, a) @ rot(Y, b) @ rot(Z, c)
    assert np.allclose(H, G, atol=1e-9) or np.allclose(H, -G, atol=1e-9)
    return a, b, c


C_ANC = rot(X, np.pi / 4)  # C Y C^dag = s Z
S_ANC = np.real(np.trace(C_ANC @ Y @ C_ANC.conj().T @ Z)) / 2
assert abs(abs(S_ANC) - 1) < 1e-12


def primitives(gates, n):
    """Target gates -> time-ordered primitives (parity, kind, site, angle).
    parity 0: odd layers (Z_q or Y_q); parity 1: even layers (Z_q or Z Y Z centred at q)."""
    out = []

    def one(q, G):
        a, b, c = zyz(G)
        out.extend([(0, "z", q, c), (0, "y", q, b), (0, "z", q, a)])

    for g in gates:
        if g[0] == "u":
            one(2 * g[1], g[2])
        else:  # CZ between logical j and j+1 (mod n), via ancilla 2j+1
            j = g[1]
            a, b, m = 2 * j, (2 * j + 2) % (2 * n), 2 * j + 1
            one(m, C_ANC.conj().T)
            out.append((1, "zyz", m, -np.pi / 4 * S_ANC))  # exp(+i pi/4 Z_a Z_b)
            one(m, C_ANC)
            out.extend([(0, "z", a, np.pi / 4), (0, "z", b, np.pi / 4)])
    return out


def compile_angles(prims, N, sigma):
    """Spread each primitive over K = ceil(|angle|/sigma) layers of its parity, one slot per layer."""
    slots, layer = [], 0
    for par, kind, q, ang in prims:
        K = max(1, int(np.ceil(abs(ang) / sigma)))
        for _ in range(K):
            if layer % 2 != par:
                layer += 1
            slots.append((layer, kind, q, ang / K))
            layer += 1
    L = layer + (layer % 2)
    th = np.zeros((L, N, 2))  # [..., 0] = z angle, [..., 1] = y angle
    for l, kind, q, a in slots:
        th[l, q, 0 if kind == "z" else 1] += a
    return th


def apply1(psi, G, q, N):
    psi = psi.reshape([2] * N)
    psi = np.moveaxis(np.tensordot(G, psi, axes=([1], [q])), 0, q)
    return psi.reshape(-1)


def cz_ring_diag(N):
    bits = (np.arange(2**N)[:, None] >> (N - 1 - np.arange(N))) & 1
    ph = np.zeros(2**N)
    for q in range(N):
        ph += bits[:, q] * bits[:, (q + 1) % N]
    return (-1.0) ** ph


def ansatz_state(th, N):
    E = cz_ring_diag(N)
    psi = np.zeros(2**N, dtype=complex)
    psi[0] = 1
    for l in range(th.shape[0]):
        for q in range(N):
            psi = apply1(psi, rot(Y, th[l, q, 1]) @ rot(Z, th[l, q, 0]), q, N)
        psi = E * psi
    return psi


def zexp(psi, q, N):
    p = np.abs(psi.reshape([2] * N)) ** 2
    return np.sum(np.moveaxis(p, q, 0)[0]) - np.sum(np.moveaxis(p, q, 0)[1])


def cost(th, N):
    return zexp(ansatz_state(th, N), 0, N)


def target_state(gates, n):
    """The same circuit on the ring of N = 2n qubits, ancillas idle."""
    N = 2 * n
    psi = np.zeros(2**N, dtype=complex)
    psi[0] = 1
    bits = (np.arange(2**N)[:, None] >> (N - 1 - np.arange(N))) & 1
    for g in gates:
        if g[0] == "u":
            psi = apply1(psi, g[2], 2 * g[1], N)
        else:
            a, b = 2 * g[1], (2 * g[1] + 2) % N
            psi = psi * (-1.0) ** (bits[:, a] * bits[:, b])
    return psi


def random_u(rng):
    m = rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2))
    return np.linalg.qr(m)[0]


def random_circuit(n, s, rng):
    gates = []
    for _ in range(s):
        if rng.random() < 0.5:
            gates.append(("u", int(rng.integers(n)), random_u(rng)))
        else:
            gates.append(("cz", int(rng.integers(n))))
    return gates


def check_theorem1(rng):
    for n, s, sigma in [(2, 6, 0.1), (3, 8, 0.05), (3, 6, 0.02)]:
        N = 2 * n
        gates = random_circuit(n, s, rng)
        th = compile_angles(primitives(gates, n), N, sigma)
        psi_t = target_state(gates, n)
        psi_a = ansatz_state(th, N)
        fid = abs(np.vdot(psi_t, psi_a))
        c_a, c_t = zexp(psi_a, 0, N), zexp(psi_t, 0, N)
        assert np.max(np.abs(th)) <= sigma + 1e-12
        assert abs(fid - 1) < 1e-9 and abs(c_a - c_t) < 1e-9
        print(f"n = {n}, N = {N}, s = {s}, L = {th.shape[0]}, D = {th.size}, max|theta| = "
              f"{np.max(np.abs(th)):.3f} <= {sigma}: |<target|ansatz>| = {fid:.12f}, "
              f"C = {c_a:+.6f} vs {c_t:+.6f}")


def check_theorem2(rng):
    n, N, sigma = 2, 4, 0.1
    for sign in (+1, -1):
        # a circuit whose output qubit has <Z_0> = sign * 0.99
        b = np.arccos(0.99) / 2 if sign > 0 else (np.pi - np.arccos(0.99)) / 2
        gates = [("u", 0, rot(Y, b)), ("u", 1, random_u(rng)), ("cz", 1)]
        prims = primitives(gates, n) + [(0, "y", 0, np.pi / 8)]
        th = compile_angles(prims, N, sigma)
        D = th.size
        flat = th.reshape(-1)
        idx_last = [i for i in range(D) if flat[i] != 0][-int(np.ceil((np.pi / 8) / sigma)):]
        c0 = cost(th, N)

        def grad(t, idx):
            g, h = [], 1e-6
            for i in idx:
                e = np.zeros(D)
                e[i] = h
                g.append((cost((t.reshape(-1) + e).reshape(t.shape), N)
                          - cost((t.reshape(-1) - e).reshape(t.shape), N)) / (2 * h))
            return np.array(g)

        g0 = grad(th, idx_last)
        assert abs(c0) >= 0.55 and np.sign(c0) == sign and np.all(np.abs(g0) >= 1.10)
        w = 0.01 / D
        worst_c, worst_g = 0.0, 0.0
        for _ in range(20):
            d = rng.uniform(-w, w, size=D)
            t = (flat + d).reshape(th.shape)
            l1 = np.sum(np.abs(d))
            worst_c = max(worst_c, abs(cost(t, N) - c0) / l1)
            worst_g = max(worst_g, np.max(np.abs(grad(t, idx_last) - g0)) / l1)
        assert worst_c <= 2 + 1e-6 and worst_g <= 4 + 1e-4
        print(f"sign {sign:+d}: C(theta*) = {c0:+.4f}, min |dC/dtheta_k| over the last "
              f"{len(idx_last)} slots = {np.min(np.abs(g0)):.4f}; in the box of width 0.01/D: "
              f"|dC|/l1 <= {worst_c:.3f} (bound 2), |d grad|/l1 <= {worst_g:.3f} (bound 4)")


if __name__ == "__main__":
    rng = np.random.default_rng(7)
    check_theorem1(rng)
    check_theorem2(rng)
    print("small-angle compilation checks pass")
