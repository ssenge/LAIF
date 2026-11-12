"""Glued trees with uniform damping: unit masses, unit springs on the edges, walls so that K = 3I - Adj
(every vertex has K_jj = 3), x(0) = 0, x'(0) = e_ENTRANCE. Two binary trees of depth n glued at their
leaves by a random cycle, as in the classical lower bound of Babbush et al.

For each damping g, prints the largest kinetic-energy fraction at EXIT over t in [0, 4n], the time of that
maximum, g times that time, and the bound min(1, 0.2546/(g t)) of the notes at that time."""
import sys
import numpy as np
import scalar_check as sc

rng = np.random.default_rng(3)


def glued(n):
    size = 2 ** (n + 1) - 1
    edges = [(i, 2 * i + 1) for i in range(size // 2)] + [(i, 2 * i + 2) for i in range(size // 2)]
    edges += [(size + a, size + b) for a, b in edges]
    leaves = list(range(size // 2, size))
    perm = rng.permutation(len(leaves))
    L1 = leaves
    L2 = [size + leaves[p] for p in perm]
    for i in range(len(leaves)):                      # random cycle through all leaves
        edges.append((L1[i], L2[i]))
        edges.append((L2[i], L1[(i + 1) % len(leaves)]))
    N = 2 * size
    Adj = np.zeros((N, N))
    for a, b in edges:
        Adj[a, b] = Adj[b, a] = 1
    return 3 * np.eye(N) - Adj, 0, size                # K, ENTRANCE, EXIT


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    K, ent, ex = glued(n)
    lam, U = np.linalg.eigh(K)
    lam = np.clip(lam, 0, None)
    w0 = U[ent]                                         # mode coefficients of x'(0) = e_ENTRANCE
    ts = np.linspace(0.01, 4 * n, 4000)
    print(f"glued trees n = {n}, N = {K.shape[0]}, E0 = 1/2")
    print("       g     max KE_exit/E0     at t     g*t     bound at t")
    for g in [0.0, 1e-3, 3e-3, 1e-2, 3e-2, 0.1, 0.3, 1.0]:
        best, bt = 0.0, 0.0
        for t in ts:
            if g == 0:
                w = np.cos(np.sqrt(lam) * t) * w0
            else:
                _, _, Gd = sc.mode(lam / g ** 2, g * t)
                w = Gd * w0
            ke = (U[ex] @ w) ** 2                       # (1/2) v_exit^2 / (1/2)
            if ke > best:
                best, bt = ke, t
        bound = 1.0 if g == 0 else min(1.0, 0.2546 / (g * bt))
        print(f"{g:8.3f}   {best:12.4e}   {bt:8.2f} {g * bt:7.3f}   {bound:10.4e}")

    # Damping by walls: K' = K + g^2 I with damping g. Exact claim x_d = e^{-gt} x_u, v_d = e^{-gt}(v_u - g x_u);
    # the damped side is computed from the damped mode formulas, independently of the identity.
    lam_s = np.sqrt(lam)
    sinc = np.where(lam_s > 1e-12, np.sin(np.outer(ts, lam_s)) / np.where(lam_s > 1e-12, lam_s, 1), ts[:, None])
    xu = (sinc * w0) @ U[ex]
    vu = (np.cos(np.outer(ts, lam_s)) * w0) @ U[ex]
    print("walls m g^2 added: identity error, max |e^{gt}|v_d| - |v_u|| (bound g * |x_u| <= g), max KE_exit/E0")
    for g in [0.03, 0.1, 0.3, 0.5, 1.0]:
        err, dev, best = 0.0, 0.0, 0.0
        for i, t in enumerate(ts):
            _, G, Gd = sc.mode((lam + g * g) / g ** 2, g * t)
            xd, vd = U[ex] @ (G / g * w0), U[ex] @ (Gd * w0)
            e = np.exp(-g * t)
            err = max(err, abs(xd - e * xu[i]), abs(vd - e * (vu[i] - g * xu[i])))
            dev = max(dev, abs(abs(vd) / e - abs(vu[i])))
            best = max(best, vd ** 2)
        assert err < 1e-9 and dev <= g + 1e-9
        print(f"{g:8.3f}   {err:9.1e}   {dev:9.2e} <= {g:5.3f}   {best:12.4e}")
