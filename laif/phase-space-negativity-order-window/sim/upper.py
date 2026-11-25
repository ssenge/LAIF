"""Orders a > 1/2: psi = (|0> + t|beta>)/N with beta -> infinity. Limits (README, Theorem 2):
||W||_1 -> 1 + 4t/(pi(1+t^2)),  Delta_a -> D_a(t) = ln((1+t^{2a})/(1+t^2)^a)/(1-a)  (a != 1),
Delta_1 -> binary entropy of t^2/(1+t^2), Delta_inf -> ln(1+t^2). Finds t with ln||W||_1 > Delta_a and
checks the limits on a grid at finite beta."""
import numpy as np
from scipy.optimize import brentq
Lim = lambda t: np.log1p(4 * t / (np.pi * (1 + t * t)))
def Dlim(a, t):
    p = t * t / (1 + t * t)
    if a == 1: return -p * np.log(p) - (1 - p) * np.log(1 - p)
    if a == np.inf: return np.log1p(t * t)
    return np.log((1 + t ** (2 * a)) / (1 + t * t) ** a) / (1 - a)

# a = 1/2: no violation in the limit (Lim < D_{1/2} for all t in (0, 1]), as the conjecture requires
ts = np.linspace(1e-6, 1, 20001); assert (Lim(ts) < Dlim(0.5, ts)).all()
for a in [0.55, 0.6, 0.75, 1, 2, np.inf]:
    f = lambda lt: Lim(np.exp(lt)) - Dlim(a, np.exp(lt))
    lts = np.linspace(-60, 0, 6001); v = np.array([f(x) for x in lts]); assert (v > 0).any()
    tbest = np.exp(lts[np.argmax(v)]); print(f"a={a}: violated in the limit for t = {tbest:.3g}, margin {v.max():.3g}")

# finite beta on a grid: t = 0.2, beta = 3 sqrt 2 (the example of [1]) and t = 0.05, beta = 7
def finite(t, beta, a_list, L=12.0, K=1201):
    x = np.linspace(-L, L, K) ; X, Y = np.meshgrid(x + beta / 2, x); A = X + 1j * Y; h2 = (x[1] - x[0]) ** 2
    N2 = 1 + t * t + 2 * t * np.exp(-beta ** 2 / 2)
    W = (2 / np.pi) * (np.exp(-2 * np.abs(A) ** 2) + t * t * np.exp(-2 * np.abs(A - beta) ** 2)
                       + 2 * t * np.real(np.exp(-beta ** 2 / 2 - 2 * np.abs(A) ** 2 + 2 * beta * A))) / N2
    amp = np.exp(-np.abs(A) ** 2 / 2) * (1 + t * np.exp(-beta ** 2 / 2 + beta * np.conj(A)))
    Q = np.abs(amp) ** 2 / (np.pi * N2)
    assert abs(W.sum() * h2 - 1) < 1e-6 and abs(Q.sum() * h2 - 1) < 1e-6
    out = [np.log(np.abs(W).sum() * h2)]
    for a in a_list:
        if a == 1: out.append(-(Q * np.log(np.maximum(Q, 1e-300))).sum() * h2 - (1 + np.log(np.pi)))
        elif a == np.inf: out.append(-np.log(np.pi * Q.max()))
        else: out.append(np.log(a * np.pi ** (a - 1) * (Q ** a).sum() * h2) / (1 - a))
    return out
for t, beta in [(0.2, 3 * np.sqrt(2)), (0.05, 7.0)]:
    r = finite(t, beta, [0.75, 1, 2, np.inf])
    print(f"t={t} beta={beta:.3f}: ln||W||_1={r[0]:.4f} (limit {Lim(t):.4f}); Delta_0.75,1,2,inf =",
          np.round(r[1:], 4), "limits", np.round([Dlim(a, t) for a in [0.75, 1, 2, np.inf]], 4))
    assert abs(r[0] - Lim(t)) < 0.02
