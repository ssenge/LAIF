# Pauli shadow norm of a state rho: S(rho) = max_sigma E_B sum_x <x_B|sigma|x_B> est_B(x)^2,
# est_B(x) = Tr(rho (x)_i (3|b_i x_i><b_i x_i| - I)). Search for max S(rho)/Tr(rho^2) (pure and mixed rho).
import itertools, sys
import numpy as np

H = np.array([[1, 1], [1, -1]]) / np.sqrt(2)
SH = np.array([[1, -1j], [1, 1j]]) / np.sqrt(2)      # rows: eigenvectors of Y (conjugated)
LOC = [H, SH.conj() @ np.eye(2), np.eye(2)]         # rows of U_b are <b, x|
LOC[1] = np.array([[1, -1j], [1, 1j]]) / np.sqrt(2)
F = np.array([[2.0, -1.0], [-1.0, 2.0]])


def setup(N):
    Us = []
    for bs in itertools.product(range(3), repeat=N):
        U = np.array([[1.0]])
        for b in bs:
            U = np.kron(U, LOC[b])
        Us.append(U)
    FN = np.array([[1.0]])
    for _ in range(N):
        FN = np.kron(FN, F)
    return np.array(Us), FN


def M_of(rho, Us, FN):
    """M = 3^-N sum_B U_B^dag diag(est_B^2) U_B; S(rho) = lambda_max(M)."""
    p = np.einsum('bxi,ij,bxj->bx', Us, rho, Us.conj()).real      # p_B(x) = <x|U rho U^dag|x>
    est = p @ FN.T
    return np.einsum('bxi,bx,bxj->ij', Us.conj(), est ** 2, Us) / len(Us), est


def check_basis(N, Us, FN, rng):
    # unbiasedness: sum_x p_sigma(x) est(x) averaged over B = Tr(rho sigma)
    d = 2 ** N
    a = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)); r = a @ a.conj().T; r /= np.trace(r)
    b = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)); s = b @ b.conj().T; s /= np.trace(s)
    _, est = M_of(r, Us, FN)
    ps = np.einsum('bxi,ij,bxj->bx', Us, s, Us.conj()).real
    assert abs((ps * est).sum() / len(Us) - np.trace(r @ s).real) < 1e-10


def ascend(N, Us, FN, rng, rank, iters=400):
    d = 2 ** N
    A = rng.normal(size=(d, rank)) + 1j * rng.normal(size=(d, rank))
    best = 0
    lr = 0.5
    for it in range(iters):
        rho = A @ A.conj().T; t = np.trace(rho).real; rho /= t; A /= np.sqrt(t)
        M, est = M_of(rho, Us, FN)
        w, V = np.linalg.eigh(M); phi = V[:, -1]
        pur = np.trace(rho @ rho).real
        val = w[-1] / pur
        if val > best:
            best, best_rho = val, rho.copy()
        # gradient of lambda_max(M(rho))/Tr(rho^2) in rho (self-adjoint), then chain rule to A
        q = np.abs(Us @ phi) ** 2                          # sigma distribution per basis
        wgt = (2 * est * q) @ FN / len(Us)               # d lambda / d p_B(y)
        G = np.einsum('bxi,bx,bxj->ij', Us.conj(), wgt, Us)    # d lambda / d rho
        G = G / pur - w[-1] * 2 * rho / pur ** 2
        G = G - np.trace(G @ rho).real * np.eye(d)       # keep trace direction neutral
        A = A + lr * G @ A
    return best, best_rho


if __name__ == "__main__":
    rng = np.random.default_rng(0)
    for N in [int(v) for v in sys.argv[1].split(",")]:
        Us, FN = setup(N)
        check_basis(N, Us, FN, rng)
        z = np.zeros((2 ** N, 2 ** N)); z[0, 0] = 1
        prod = np.linalg.eigvalsh(M_of(z, Us, FN)[0])[-1]
        assert abs(prod - 1.5 ** N) < 1e-9
        res = {}
        for rank in [1, 2, 4]:
            res[rank] = max(ascend(N, Us, FN, rng, rank)[0] for _ in range(int(sys.argv[2]) if len(sys.argv) > 2 else 6))
        print(f"N={N} product 1.5^N={1.5 ** N:.4f}  best ratio found: " + ", ".join(f"rank {k}: {v:.4f}" for k, v in res.items()), flush=True)
