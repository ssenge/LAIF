"""||W_n||_1 = (1/2) int_0^inf e^{-x/2} |L_n(x)| dx for number states, via the stable recurrence
of the radial functions f_k = e^{-x/2} L_k on a grid in u = sqrt(x)."""
import sys, numpy as np

def l1(n, per=60):
    N = n + 0.5
    umax = np.sqrt(4 * N + 12 * N ** (1 / 3) + 40)
    M = int(umax * per * np.sqrt(N)) + 2000
    u = np.linspace(0, umax, M); x = u * u
    g0, g1, ls = np.ones_like(x), 1 - x, -x / 2          # f_k = exp(ls) * g_k, rescaled to avoid over/underflow
    for k in range(1, n):
        g0, g1 = g1, ((2 * k + 1 - x) * g1 - k * g0) / (k + 1)
        m = np.maximum(np.abs(g0), np.abs(g1)); g0 = g0 / m; g1 = g1 / m; ls = ls + np.log(m)
    f = np.exp(ls) * (g0 if n == 0 else g1)
    return 0.5 * np.trapezoid(np.abs(f) * 2 * u, u)

if __name__ == "__main__":
    assert abs(l1(0) - 1) < 1e-5 and abs(l1(1) - (4 * np.exp(-0.5) - 1)) < 1e-5
    for n in map(int, sys.argv[1:]):
        v = l1(n); print(n, v, np.log(v) - 0.5 * np.log(n), v / np.sqrt(n), flush=True)
