"""All-Z measurement of psi_n against rho_n: exact per-copy chi-square by the binomial formula (mpmath),
ratio to (2/3)^{n/2} and times sqrt(n). Asserts agreement with the state-vector value for n <= 10
and that chi^2 <= (2/3)^{n/2} for all n checked."""
import numpy as np, mpmath as mp
mp.mp.dps = 60
r = np.ones(3) / np.sqrt(3)
X = np.array([[0, 1], [1, 0]]); Y = np.array([[0, -1j], [1j, 0]]); Z = np.diag([1., -1])
w, V = np.linalg.eigh((np.eye(2) + r[0] * X + r[1] * Y + r[2] * Z) / 2); a, b = V[:, 1], V[:, 0]
def chi_exact(n):
    s = mp.mpf(0)
    za = [mp.mpc(complex(a[i])) for i in range(2)]; zb = [mp.mpc(complex(b[i])) for i in range(2)]
    for k in range(n + 1):           # k outcomes "1"
        u = za[0] ** (n - k) * za[1] ** k; v = zb[0] ** (n - k) * zb[1] ** k
        m = (abs(u) ** 2 + abs(v) ** 2) / 2; c = mp.re(u * mp.conj(v)); s += mp.binomial(n, k) * c ** 2 / m
    return s
def chi_vec(n):
    A = a; B = b
    for _ in range(n - 1): A = np.kron(A, a); B = np.kron(B, b)
    m = (abs(A) ** 2 + abs(B) ** 2) / 2; c = (A * B.conj()).real; return np.sum(c ** 2 / m)
for n in range(1, 11): assert abs(float(chi_exact(n)) - chi_vec(n)) < 1e-10
for n in [1, 2, 4, 8, 16, 32, 64, 128, 256, 320]:
    x = chi_exact(n) / (mp.mpf(2) / 3) ** (mp.mpf(n) / 2); assert x <= 1
    print(f"n={n}: chi2/(2/3)^(n/2) = {float(x):.4f}, times sqrt(n) = {float(x * mp.sqrt(n)):.4f}")
