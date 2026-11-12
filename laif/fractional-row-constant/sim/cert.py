"""Certificate for the band-limited function Phi(s) = a cos(tau s) + sum_k b_k [K(s - t_k) + K(s + t_k)],
K(s) = sinc(tau s / 2)^2 with sinc(z) = sin(z)/z, t_k = k h. Every term has spectrum in [-tau, tau].
Checked in 50-digit decimal arithmetic:
  alpha = 2 / (Phi(0) - Phi(1)), beta = 1 - alpha Phi(0) (the affine map sending Phi(0), Phi(1) to 1, -1),
  M = max of |Phi(sqrt j)| (2 <= j <= J) and sup of |Phi(s)| over s >= sqrt(J) - 1, and alpha M + |beta| < 1.
The sup over [sqrt(J) - 1, S] uses grid values and |Phi''| <= tau^2 |a| + (7/12) tau^2 sum |b_k|; beyond S the bound
|Phi| <= |a| + 2 sum |b_k| (2 / (tau (S - T)))^2 (T = largest t_k)."""
import sys
from decimal import Decimal as Dm, getcontext
import numpy as np
from scipy.optimize import linprog

getcontext().prec = 50
PI = Dm("3.14159265358979323846264338327950288419716939937510582097494")
ALLOW = Dm("1e-30")                      # allowance for rounding in every value of Phi

def sincos(x):
    k = (x / (2 * PI)).to_integral_value(); r = x - 2 * k * PI
    s, c, term, n = Dm(0), Dm(0), Dm(1), 0
    while True:                          # term = r^n / n!
        if n % 4 == 0: c += term
        elif n % 4 == 1: s += term
        elif n % 4 == 2: c -= term
        else: s -= term
        n += 1; term = term * r / n
        if abs(term) < Dm("1e-45"): break
    return s, c

def K(s, tau):
    return np.sinc(tau * s / (2 * np.pi)) ** 2          # numpy sinc(x) = sin(pi x)/(pi x)

def lp(tau, h, T, J, S, delta_min=None):
    t = np.arange(0, T + 1e-9, h)
    B = lambda s: np.hstack([np.cos(tau * s)[:, None], np.array([K(s - tk, tau) + K(s + tk, tau) for tk in t]).T])
    sj = np.sqrt(np.arange(2, J + 1.0)); sc = np.arange(np.sqrt(J) - 1, S + 5, 0.01)
    A = np.vstack([B(sj), B(sc)]); Aeq = B(np.array([0.0, 1.0])); nb = A.shape[1]
    if delta_min is None:                # maximise the margin
        c = np.r_[np.zeros(nb), -1]; Aub = np.vstack([np.hstack([A, np.ones((len(A), 1))]), np.hstack([-A, np.ones((len(A), 1))])])
        r = linprog(c, A_ub=Aub, b_ub=np.ones(2 * len(A)), A_eq=np.hstack([Aeq, np.zeros((2, 1))]), b_eq=[1, -1], bounds=[(-50, 50)] * nb + [(None, 1)], method="highs")
        return r.x[-1]
    # minimise sum |coef| with margin delta_min: variables x (nb), u (nb) with |x| <= u
    I = np.eye(nb); Z = np.zeros_like(A)
    Aub = np.vstack([np.hstack([A, Z]), np.hstack([-A, Z]), np.hstack([I, -I]), np.hstack([-I, -I])])
    bub = np.r_[np.ones(2 * len(A)) * (1 - delta_min), np.zeros(2 * nb)]
    r = linprog(np.r_[np.zeros(nb), np.ones(nb)], A_ub=Aub, b_ub=bub, A_eq=np.hstack([Aeq, np.zeros((2, nb))]), b_eq=[1, -1], bounds=[(None, None)] * (2 * nb), method="highs")
    return t, r.x[:nb]

def check(tau, t, coef, J, S, eta):
    tau = Dm(repr(tau)); a = Dm(repr(float(coef[0]))); b = [Dm(repr(float(x))) for x in coef[1:]]; t = [Dm(repr(float(x))) for x in t]
    half = tau / 2; ST = [sincos(half * tk) for tk in t]
    def Phi(s):
        ss, cs = sincos(half * s); out = a * sincos(tau * s)[1]
        for bk, tk, (st, ct) in zip(b, t, ST):
            for sign in (1, -1):
                z = half * (s - sign * tk)
                if abs(z) < Dm("1e-20"): v = Dm(1)
                else: v = ((ss * ct - sign * cs * st) / z) ** 2
                out += bk * v
        return out
    P0, P1 = Phi(Dm(0)), Phi(Dm(1))
    alpha = 2 / (P0 - P1); beta = 1 - alpha * P0
    M1 = max(abs(Phi(Dm(j).sqrt())) for j in range(2, J + 1)) + ALLOW
    sb = sum(abs(x) for x in b); L2 = tau ** 2 * abs(a) + Dm(7) / 12 * tau ** 2 * sb
    s0 = Dm(J).sqrt() - 1; n = int(((Dm(S) - s0) / Dm(repr(eta))).to_integral_value(rounding="ROUND_CEILING"))
    step = (Dm(S) - s0) / n
    M2 = max(abs(Phi(s0 + i * step)) for i in range(n + 1)) + L2 * step ** 2 / 8 + ALLOW
    M3 = abs(a) + 2 * sb * (2 / (tau * (Dm(S) - max(t)))) ** 2
    M = max(M1, M2, M3); lhs = alpha * M + abs(beta)
    return dict(Phi0=P0, Phi1=P1, alpha=alpha, beta=beta, M_points=M1, M_grid=M2, M_tail=M3, sum_abs_b=sb, a=a, result=lhs)

if __name__ == "__main__":
    tau = float(sys.argv[1]) if len(sys.argv) > 1 else 2.63; h, T, J, S = 0.125, 20.0, 150, 90.0
    dmax = lp(tau, h, T, J, S); print(f"tau = {tau}: largest margin {dmax:.4f}", flush=True)
    t, coef = lp(tau, h, T, J, S, delta_min=0.6 * dmax)
    print(f"a = {coef[0]:.6f}, sum |b_k| = {np.abs(coef[1:]).sum():.4f}", flush=True)
    out = check(tau, t, coef, J, S, eta=0.02)
    for k, v in out.items(): print(f"  {k} = {float(v):.10f}")
    assert out["result"] < 1
    print(f"certified: alpha M + |beta| = {float(out['result']):.6f} < 1, so c* <= tau^2/2 = {tau**2/2:.5f}")
