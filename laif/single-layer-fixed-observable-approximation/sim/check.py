"""Checks for single-layer quantum models with the fixed observable Z (x) I.
Model: f(x) = <0| W1^* S(x)^* W2^* M W2 S(x) W1 |0>, S(x) = tensor of exp(-i x_v Z / 2) over the qubits of block v,
M = Z (x) I. The construction: psi = uniform superposition of one basis vector per tuple of numbers of ones, P = dilation
of the constant-diagonal matrix G_{mn} = h^(n - m) with h = (1 + g)/2, padded to rank 2^{R-1}; W2 maps range(P) onto the
states with first qubit 0, W1 maps |0> to psi. Then f equals the arithmetic mean of the first N partial frequency sums
(per coordinate), and with a modified G it equals g exactly for trigonometric polynomials with sup |g| < 1."""
import itertools, numpy as np
from scipy.linalg import sqrtm
Z1 = np.array([1.0, -1.0])

def diag_S(x, blocks):                    # diagonal of S(x) in the computational basis
    d = np.ones(1, complex)
    for xv, R in zip(x, blocks):
        for _ in range(R):
            d = np.kron(d, np.exp(-1j * xv * Z1 / 2))
    return d

def build(blocks, coef, N):
    """coef(k) for multi-index k: the matrix entries T_k; returns W1, W2 with G_{mn} = coef(n - m)."""
    R = sum(blocks); dim = 2 ** R
    weights = [np.array([bin(b).count("1") for b in range(2 ** Rv)]) for Rv in blocks]
    reps = [[int(np.where(w == n)[0][0]) for n in range(Nv)] for w, Nv in zip(weights, N)]
    levels = list(itertools.product(*[range(Nv) for Nv in N]))
    def index(t):                         # basis index of the product of the chosen weight vectors
        i = 0
        for v, n in enumerate(t):
            i = i * 2 ** blocks[v] + reps[v][n]
        return i
    eps = [index(t) for t in levels]
    G = np.array([[coef(tuple(np.subtract(t2, t1))) for t2 in levels] for t1 in levels])
    G = (G + G.conj().T) / 2
    ev = np.linalg.eigvalsh(G); assert ev.min() > -1e-9 and ev.max() < 1 + 1e-9, (ev.min(), ev.max())
    L = len(levels); rest = [b for b in range(dim) if b not in set(eps)]
    eta, extra = rest[:L], rest[L:]
    B = sqrtm(G @ (np.eye(L) - G)); B = (B + B.conj().T) / 2
    P = np.zeros((dim, dim), complex)
    P[np.ix_(eps + eta, eps + eta)] = np.block([[G, B], [B, np.eye(L) - G]])
    need = dim // 2 - L; assert need >= 0
    for b in extra[:need]: P[b, b] = 1
    assert np.allclose(P @ P, P, atol=1e-8) and abs(np.trace(P).real - dim // 2) < 1e-8
    vals, V = np.linalg.eigh(P)
    V = V[:, np.argsort(-vals)]           # range first: maps onto the states with first qubit 0
    W2 = V.conj().T
    M = np.kron(np.diag(Z1), np.eye(dim // 2))
    assert np.allclose(W2.conj().T @ M @ W2, 2 * P - np.eye(dim), atol=1e-8)
    psi = np.zeros(dim, complex); psi[eps] = 1 / np.sqrt(L)
    W1, _ = np.linalg.qr(np.column_stack([psi, np.random.default_rng(0).normal(size=(dim, dim - 1))]))
    W1 = W1 * (np.vdot(W1[:, 0], psi) / abs(np.vdot(W1[:, 0], psi)))   # fix phase so W1|0> = psi
    assert np.allclose(W1[:, 0], psi)
    return W1, W2, M

def model(W1, W2, M, x, blocks):
    v = diag_S(x, blocks) * W1[:, 0]
    w = W2 @ v
    return np.real(np.vdot(w, M @ w))

def freq_coeffs(g, n, K=64):                  # coefficients on a K^n grid, dict k -> g^(k)
    grids = np.meshgrid(*[2 * np.pi * np.arange(K) / K] * n, indexing="ij")
    vals = g(*grids); c = np.fft.fftn(vals) / K ** n
    return lambda k: c[tuple(ki % K for ki in k)]

rng = np.random.default_rng(1)
# 1) univariate and bivariate: model equals the mean of partial sums of g, for |g| <= 1
cases = [((3,), lambda x: 0.95 * np.sign(np.sin(x))), ((5,), lambda x: np.cos(3 * x) * np.sin(x)),
         ((7,), lambda x: np.where(np.cos(x) > 0.3, 1.0, -1.0)),
         ((3, 3), lambda x, y: np.cos(x + 2 * y) * 0.9), ((3, 4), lambda x, y: np.sign(np.sin(x) * np.cos(y)))]
for blocks, g in cases:
    n = len(blocks); N = [R + 1 for R in blocks]; gh = freq_coeffs(g, n)
    hh = lambda k: (0.5 if all(ki == 0 for ki in k) else 0) + gh(k) / 2
    W1, W2, M = build(blocks, hh, N)
    worst = 0
    for _ in range(60):
        x = rng.uniform(0, 2 * np.pi, n)
        mean = sum(np.prod([(1 - abs(k[v]) / N[v]) for v in range(n)]) * gh(k) * np.exp(1j * np.dot(k, x))
                   for k in itertools.product(*[range(-Nv + 1, Nv) for Nv in N]))
        worst = max(worst, abs(model(W1, W2, M, x, blocks) - mean.real))
    assert worst < 1e-9, worst
    print(f"blocks {blocks}: model = mean of partial sums, max deviation {worst:.1e}")

# 2) exact representation: trigonometric polynomial of degree D with sup |g| <= 1 - eta, N >= D + D sqrt(2D)/eta levels
for D, eta in [(1, 0.5), (2, 0.4), (3, 0.9)]:   # R up to 11 qubits (dense 2^11 matrices)
    c = rng.normal(size=2 * D + 1) + 1j * rng.normal(size=2 * D + 1)
    ks = np.arange(-D, D + 1)
    raw = lambda x, c=c: np.real(sum(c[i] * np.exp(1j * k * x) for i, k in enumerate(ks)))
    xs = np.linspace(0, 2 * np.pi, 4001); s = (1 - eta) / np.max(np.abs(raw(xs)))
    g = lambda x: s * raw(x)
    gh = freq_coeffs(g, 1)
    Nreq = int(np.ceil(D + D * np.sqrt(2 * D) / eta)); R = max(3, Nreq - 1); N = R + 1
    coef = lambda k: (0.5 + gh(k) / 2 if k[0] == 0 else 0) + (gh(k) / 2 * N / (N - abs(k[0])) if 0 < abs(k[0]) <= D else 0)
    W1, W2, M = build((R,), coef, [N])
    worst = max(abs(model(W1, W2, M, [x], (R,)) - g(x)) for x in rng.uniform(0, 2 * np.pi, 80))
    assert worst < 1e-9, worst
    print(f"degree {D}, margin {eta}: exact representation with R = {R} qubits, max deviation {worst:.1e}")

# 3) rescaled observables c_k Z (x) I: L2 error for an unbounded-range target decreases
g = lambda x: 3 * np.cos(x) + 2 * np.sign(np.sin(2 * x))
xs = 2 * np.pi * np.arange(2048) / 2048
prev = np.inf
for R, cR in [(3, 6.0), (5, 6.0), (7, 6.0), (9, 6.0)]:
    gc = lambda x: np.clip(g(x), -cR, cR) / cR
    gh = freq_coeffs(gc, 1, K=256); N = R + 1
    hh = lambda k: (0.5 if k[0] == 0 else 0) + gh(k) / 2
    W1, W2, M = build((R,), hh, [N])
    f = np.array([cR * model(W1, W2, M, [x], (R,)) for x in xs[::8]])
    err = np.sqrt(np.mean((f - g(xs[::8])) ** 2))
    assert err < prev + 1e-12; prev = err
    print(f"rescaled observable {cR} Z (x) I, R = {R}: L2 error {err:.3f}")
print("all checks passed")
