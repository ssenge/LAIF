"""End-to-end: solve g(y*+v) = p for random small p in P_{(m-1)L}, v in T (sum v_j = 0), check y*+v >= 0 on a fine grid."""
import numpy as np
from numpy.polynomial import chebyshev as C
rng = np.random.default_rng(7)
def basis(N, x): return np.stack([np.ones_like(x)] + [f(w*x) for w in range(1, N+1) for f in (np.cos, np.sin)], 1)
def run(m, L, eps, scale):
    N = (m-1)*L; K = 2*N+1
    x = np.linspace(0, 2*np.pi, 6*K+11, endpoint=False); B = basis(L, x); BN = basis(N, x)
    ys = np.full((len(x), m), 1/m); ys[:, 0] += eps*np.cos(L*x); ys[:, 1] += eps*np.sin(L*x); ys[:, m-1] = 1 - ys[:, :m-1].sum(1)
    def g(y):
        z = y[:, :m-1] - 1/m
        G = z[:, 0]**2 + z[:, 1]**2 + sum(z[:, j]*C.chebval(z[:, 0]/eps, [0]*j + [1]) for j in range(2, m-1))
        return G - eps**2
    def Y(c):  # c: (m-1, 2L+1) coefficients of v_1..v_{m-1}; v_m = -sum
        V = B @ c.T; return ys + np.column_stack([V, -V.sum(1)])
    p = BN @ (scale*rng.standard_normal(K))
    c = np.zeros((m-1, 2*L+1))
    for it in range(30):
        r = g(Y(c)) - p
        J = np.empty((len(x), c.size)); h = 1e-7
        for k in range(c.size):
            d = np.zeros(c.size); d[k] = h; J[:, k] = (g(Y(c + d.reshape(c.shape))) - g(Y(c))) / h
        c = c - np.linalg.lstsq(J, r, rcond=None)[0].reshape(c.shape)
    r = np.abs(g(Y(c)) - p).max()
    xf = np.linspace(0, 2*np.pi, 4001); Bf = basis(L, xf); Vf = Bf @ c.T
    yf = np.full((len(xf), m), 1/m); yf[:, 0] += eps*np.cos(L*xf); yf[:, 1] += eps*np.sin(L*xf)
    yf[:, :m-1] += Vf; yf[:, m-1] = 1 - yf[:, :m-1].sum(1)
    return r, yf.min(), np.abs(c).max()
for m in range(3, 7):
    for L in (1, 2, 3):
        r, ymin, cmax = run(m, L, 0.05, 1e-4)
        assert r < 1e-9 and ymin > 0, (m, L, r, ymin)
        print(f"m={m} L={L}: residual {r:.1e}, min y {ymin:.3f}, max|v coef| {cmax:.1e}")
print("all checks passed")
