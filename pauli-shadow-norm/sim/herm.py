# sup over self-adjoint O and states sigma of E_{B,x~sigma}[Tr(O rhohat)^2] / Tr(O^2), alternating maximization.
import itertools, sys
import numpy as np
import shadow as S

PA = [np.eye(2), np.array([[0, 1], [1, 0]]), np.array([[0, -1j], [1j, 0]]), np.diag([1.0, -1.0])]


def phi(N):
    """rows (B, x): f_B(x) = sum_P a_P 3^|P| chi_P(x) [P compatible with B] / d, columns P in {I,X,Y,Z}^N."""
    d = 2 ** N
    Ps = list(itertools.product(range(4), repeat=N))
    rows = []
    for B in itertools.product(range(1, 4), repeat=N):
        for x in itertools.product([1, -1], repeat=N):
            r = []
            for P in Ps:
                if all(p == 0 or p == b for p, b in zip(P, B)):
                    r.append(np.prod([3 * xi for p, xi in zip(P, x) if p]) / d)
                else:
                    r.append(0.0)
            rows.append(r)
    return np.array(rows), Ps


def paulis(N, Ps):
    out = []
    for P in Ps:
        m = np.array([[1.0]])
        for p in P:
            m = np.kron(m, PA[p])
        out.append(m)
    return out


def run(N, restarts, iters, rng):
    d = 2 ** N
    Ph, Ps = phi(N)
    Us, FN = S.setup(N)
    Pm = paulis(N, Ps)
    best = 0
    for _ in range(restarts):
        v = rng.normal(size=d) + 1j * rng.normal(size=d); v /= np.linalg.norm(v)
        for _ in range(iters):
            q = (np.abs(Us @ v) ** 2).reshape(-1) / 3 ** N          # weight of row (B, x)
            Gm = Ph.T @ (q[:, None] * Ph)
            w, V = np.linalg.eigh(Gm)
            a = V[:, -1]                                            # sum a^2 = 1, Tr O^2 = 1/d
            ratio = w[-1] * d
            O = sum(ai * P for ai, P in zip(a, Pm)) / d
            M, _ = S.M_of(O, Us, FN)
            ww, VV = np.linalg.eigh(M)
            v = VV[:, -1]
        best = max(best, ww[-1] / np.trace(O @ O).real)
    return best


if __name__ == "__main__":
    rng = np.random.default_rng(0)
    c1 = (2 + np.sqrt(2)) / 2
    for N in [int(v) for v in sys.argv[1].split(",")]:
        b = run(N, int(sys.argv[2]), int(sys.argv[3]), rng)
        print(f"N={N} sup ratio (self-adjoint O) >= {b:.5f}   c1^N = {c1 ** N:.5f}   per qubit {b ** (1 / N):.5f}", flush=True)
