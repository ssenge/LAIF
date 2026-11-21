"""Checks for state identity testing with every eps < 1/2.
(1) the antisymmetric projector A = (1 - SWAP)/2 on two registers has tr(A psi (x) phi) = (1 - |<psi|phi>|^2)/2
    for random pure states, so yes instances give at most eps/2 and no instances at least (1 - eps)/2;
    with threshold 1/4 and slack (1 - 2 eps)/4 both sides are separated;
(2) the hard pair: |0>, and phi_F = sqrt(F)|0> + sqrt(1 - F)|1> with F = 1 - eps (yes) or F = eps (no);
    m copies of the two candidates have trace distance sqrt(1 - (4 eps (1 - eps))^m), computed exactly on the
    symmetric subspace, and the copy bound log(1/(4 delta (1 - delta)))/log(1/(4 eps (1 - eps))) is checked
    against the smallest m with Helstrom error at most delta;
(3) the copy bound is at least 4 eps (1 - eps) log(1/(4 delta (1 - delta)))/(1 - 2 eps)^2;
(4) 1 - 2 eps >= 1 - 2 sqrt(eps), so the gap (1 - 2 eps)/4 is at least half of gamma = 1/2 - sqrt(eps)."""
import numpy as np
from math import comb, log, sqrt

rng = np.random.default_rng(7)


def rand_state(d):
    v = rng.normal(size=d) + 1j * rng.normal(size=d)
    return v / np.linalg.norm(v)


def swap(d):
    S = np.zeros((d * d, d * d))
    for i in range(d):
        for j in range(d):
            S[i * d + j, j * d + i] = 1
    return S


def sym_copies(F, m):
    """phi_F^{(x) m} in the Dicke basis of the symmetric subspace of m qubits."""
    a, b = sqrt(F), sqrt(1 - F)
    return np.array([sqrt(comb(m, k)) * a ** (m - k) * b ** k for k in range(m + 1)])


def main():
    # (1)
    for d in [2, 3, 5]:
        A = (np.eye(d * d) - swap(d)) / 2
        for _ in range(200):
            p, q = rand_state(d), rand_state(d)
            v = np.kron(p, q)
            val = np.real(v.conj() @ A @ v)
            F = abs(np.vdot(p, q)) ** 2
            assert abs(val - (1 - F) / 2) < 1e-12
    for eps in np.linspace(0, 0.499, 400):
        g = (1 - 2 * eps) / 4
        assert eps / 2 <= 0.25 - g + 1e-15 and (1 - eps) / 2 > 0.25 and g > 0
    print("antisymmetric projector: tr = (1 - F)/2; threshold 1/4 with slack (1 - 2 eps)/4 separates yes and no")
    # (2), (3)
    worst = 0.0
    for eps in [0.01, 0.1, 0.25, 0.4, 0.45, 0.49]:
        x = sym_copies(1 - eps, 1) @ sym_copies(eps, 1)
        assert abs(x ** 2 - 4 * eps * (1 - eps)) < 1e-12
        for delta in [0.3, 0.1, 0.01, 1e-4]:
            bound = log(1 / (4 * delta * (1 - delta))) / log(1 / (4 * eps * (1 - eps)))
            bound2 = 4 * eps * (1 - eps) * log(1 / (4 * delta * (1 - delta))) / (1 - 2 * eps) ** 2
            assert bound2 <= bound + 1e-12
            for mm in range(1, 41):  # exact trace distance on the symmetric subspace
                u, w = sym_copies(1 - eps, mm), sym_copies(eps, mm)
                td = 0.5 * np.abs(np.linalg.eigvalsh(np.outer(u, u) - np.outer(w, w))).sum()
                assert abs(td - sqrt(1 - (4 * eps * (1 - eps)) ** mm)) < 1e-9
            m = 1  # smallest m with Helstrom error (1 - td)/2 <= delta, td from the verified formula
            while (1 - sqrt(1 - (4 * eps * (1 - eps)) ** m)) / 2 > delta:
                m += 1
            assert m >= bound - 1e-9, (eps, delta, m, bound)
            worst = max(worst, bound / m)
    print(f"hard pair: trace distance sqrt(1 - (4 eps(1-eps))^m) exact; smallest m with error <= delta is at least"
          f" the bound (largest bound/m = {worst:.3f}); bound >= 4 eps(1-eps) log(1/(4 delta(1-delta)))/(1-2eps)^2")
    # (4)
    for eps in np.linspace(0, 1, 1001):
        assert 1 - 2 * eps >= 1 - 2 * sqrt(eps) - 1e-15
    print("1 - 2 eps >= 1 - 2 sqrt(eps) on [0, 1]")
    print("check: all asserts passed")


if __name__ == "__main__":
    main()
