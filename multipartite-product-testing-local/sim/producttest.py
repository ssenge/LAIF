# Two-stage product test for pure n-qudit states with single-copy local measurements. Checks with asserts:
#  (1) for the local random-basis estimator R = (1/N) sum_t ((d+1)|v_t><v_t| - I) of a pure qudit state phi,
#      E ||(R - phi) phi||^2 = 2(d-1)/N (Lemma 2), and 1 - |<v|phi>|^2 <= (16/9) ||(R - phi) phi||^2 for the top
#      eigenvector v of R whenever ||R - phi||_op <= 1/4 (Lemma 1);
#  (2) the full test with the constants of Theorem 1 accepts random product states and rejects states at trace
#      distance eps from the product states (tensor products of entangled pairs, rotated by random local unitaries),
#      each with error below 1/3 (in fact below 0.2).
# Stage 1 uses only the marginal outcomes of each qudit, which have the same law under any joint state; stage 2 is
# simulated exactly through the all-hit probability |<v_1 ... v_n|psi>|^2.
# python -I producttest.py
import sys
import numpy as np


def haar(d, rng):
    z = (rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / np.abs(np.diag(r)))


def rand_vec(d, rng):
    v = rng.standard_normal(d) + 1j * rng.standard_normal(d)
    return v / np.linalg.norm(v)


def local_estimate(rho, N, rng):
    """Measure N copies of the qudit state rho, each in a fresh uniformly random basis; return R."""
    d = rho.shape[0]
    z = (rng.standard_normal((N, d, d)) + 1j * rng.standard_normal((N, d, d))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    dg = np.diagonal(r, axis1=1, axis2=2)
    U = q * (dg / np.abs(dg))[:, None, :]                      # N uniformly random bases, columns are basis vectors
    p = np.real(np.einsum("nji,jk,nki->ni", U.conj(), rho, U)); p = np.clip(p, 0, None); p /= p.sum(axis=1, keepdims=True)
    k = (rng.random((N, 1)) > np.cumsum(p, axis=1)).sum(axis=1).clip(max=d - 1)
    V = U[np.arange(N), :, k]                                   # (N, d) measured basis vectors
    return (d + 1) * np.einsum("ni,nj->ij", V, V.conj()) / N - np.eye(d)


def top_vec(R):
    w, V = np.linalg.eigh(R)
    return V[:, -1]


def copies(n, d, eps):
    n1 = int(np.ceil(max(143 * n * (d - 1) / eps**2, 72 * d * np.log(80 * n * d / eps**2))))
    n2 = int(np.ceil(160 / eps**2))
    return n1, n2


def check_lemmas(rng):
    for d, N in ((2, 50), (2, 400), (8, 200), (8, 1600)):
        phi = rand_vec(d, rng); P = np.outer(phi, phi.conj())
        res, infid = [], []
        for _ in range(400):
            R = local_estimate(P, N, rng)
            E = R - P
            r2 = np.linalg.norm(E @ phi) ** 2
            res.append(r2)
            if np.linalg.norm(E, 2) <= 0.25:
                f = 1 - abs(np.vdot(top_vec(R), phi)) ** 2
                assert f <= 16 / 9 * r2 + 1e-12, (d, N, f, r2)
                infid.append(f)
        m, se = np.mean(res), np.std(res) / np.sqrt(len(res))
        assert abs(m - 2 * (d - 1) / N) <= 5 * se, (d, N, m, 2 * (d - 1) / N)
        print(f"d = {d}, N = {N}: E||(R - phi)phi||^2 = {m:.5f} (formula {2 * (d - 1) / N:.5f}), "
              f"mean infidelity {np.mean(infid) if infid else float('nan'):.5f} on {len(infid)} runs with ||R - phi|| <= 1/4")


def apply_local(psi, Us, n, d):
    t = psi.reshape([d] * n)
    for i, U in enumerate(Us):
        t = np.moveaxis(np.tensordot(U, t, axes=([1], [i])), 0, i)
    return t.reshape(-1)


def pair_state(n, t):
    """Tensor product of n/2 two-qubit states cos t |00> + sin t |11>; distance^2 to product = 1 - cos^n t."""
    pair = np.zeros(4, complex); pair[0] = np.cos(t); pair[3] = np.sin(t)
    psi = pair
    for _ in range(n // 2 - 1):
        psi = np.kron(psi, pair)
    return psi


def marginal(psi, i, n, d):
    t = np.moveaxis(psi.reshape([d] * n), i, 0).reshape(d, -1)
    return t @ t.conj().T


def test(psi, n, d, eps, rng):
    """Return True for accept."""
    n1, n2 = copies(n, d, eps)
    vs = [top_vec(local_estimate(marginal(psi, i, n, d), n1, rng)) for i in range(n)]
    prod = vs[0]
    for v in vs[1:]:
        prod = np.kron(prod, v)
    hit = abs(np.vdot(prod, psi)) ** 2
    misses = rng.binomial(n2, 1 - min(hit, 1.0))
    return misses < 0.75 * eps**2 * n2


def check_test(rng, n=6, d=2, eps=0.4, trials=40):
    t = np.arccos((1 - eps**2) ** (1 / n))       # n/2 pairs with cos^n t = 1 - eps^2
    acc_null = acc_alt = 0
    for _ in range(trials):
        prod = rand_vec(d, rng)
        for _ in range(n - 1):
            prod = np.kron(prod, rand_vec(d, rng))
        acc_null += test(prod, n, d, eps, rng)
        alt = apply_local(pair_state(n, t), [haar(d, rng) for _ in range(n)], n, d)
        acc_alt += test(alt, n, d, eps, rng)
    n1, n2 = copies(n, d, eps)
    print(f"test n = {n}, d = {d}, eps = {eps}: copies {n1} + {n2}; accepted {acc_null}/{trials} product states, "
          f"{acc_alt}/{trials} states at distance eps", flush=True)
    assert acc_null >= 0.8 * trials and acc_alt <= 0.2 * trials, (acc_null, acc_alt)


if __name__ == "__main__":
    rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 5)
    check_lemmas(rng)
    check_test(rng)
    check_test(rng, n=10, eps=0.3, trials=20)
    print("product test checks: ok")
