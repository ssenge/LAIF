"""One mode of the uniformly damped oscillator u'' + 2 g u' + lam u = 0, in dimensionless form.

With lam = g^2 l and tau = g t, the mode propagator in energy coordinates (p = sqrt(lam) u, w = u') is
    R = [[F, sqrt(l) G], [-sqrt(l) G, Gd]],
where F, G, Gd depend only on (l, tau): G = g * (solution with u(0) = 0, u'(0) = 1), Gd = its derivative,
F = Gd + 2 G.  Heat flow replaces them by e^{-tau l / 2} (F), e^{-tau l / 2} / 2 (G) and the derivative of the
position (Gd, -l/4 e^{-tau l/2}).

Prints, as functions of tau:
  ke(tau)  = sup_l (l G^2 + Gd^2), the largest kinetic-energy fraction at time t of a unit-energy mode,
  err(tau) = sup_l ||R - R_heat||_2 (spectral norm of the 2x2 difference),
and their products with tau. Formulas are written with decaying exponentials only, so they are stable."""
import numpy as np


def mode(l, tau):
    l = np.asarray(l, dtype=float)
    F, G, Gd = np.empty_like(l), np.empty_like(l), np.empty_like(l)
    o = l < 1 - 1e-9                                    # overdamped: rho = sqrt(1 - l) in [0, 1)
    rho = np.sqrt(1 - l[o])
    a, b = np.exp(-tau * (1 - rho)), np.exp(-tau * (1 + rho))
    ch, sh = (a + b) / 2, (a - b) / 2                   # e^{-tau} cosh(tau rho), e^{-tau} sinh(tau rho)
    G[o] = sh / rho
    Gd[o] = ch - sh / rho
    c = np.abs(l - 1) <= 1e-9                           # critical
    G[c] = tau * np.exp(-tau)
    Gd[c] = (1 - tau) * np.exp(-tau)
    u = l > 1 + 1e-9                                    # underdamped: omega = sqrt(l - 1)
    om = np.sqrt(l[u] - 1)
    e = np.exp(-tau)
    G[u] = e * np.sin(tau * om) / om
    Gd[u] = e * (np.cos(tau * om) - np.sin(tau * om) / om)
    F[:] = Gd + 2 * G
    return F, G, Gd


def heat(l, tau):
    h = np.exp(-tau * l / 2)
    return h, h / 2, -l / 4 * h


def sup_over_l(tau, l):
    F, G, Gd = mode(l, tau)
    Fh, Gh, Gdh = heat(l, tau)
    q = np.sqrt(l)
    ke = np.max(l * G ** 2 + Gd ** 2)
    D = np.stack([np.stack([F - Fh, q * (G - Gh)]), np.stack([-q * (G - Gh), Gd - Gdh])])   # 2x2xL
    err = np.max(np.linalg.norm(np.moveaxis(D, -1, 0), ord=2, axis=(1, 2)))
    return ke, err


if __name__ == "__main__":
    l = np.concatenate([np.geomspace(1e-12, 0.999, 60000), np.linspace(1.001, 1e4, 200000)])
    print("   tau        ke     tau*ke        err    tau*err")
    for tau in [0.01, 0.1, 0.5, 1, 2, 3, 5, 10, 30, 100, 300, 1000, 1e4, 1e5]:
        ke, err = sup_over_l(tau, l)
        print(f"{tau:8.2f} {ke:9.3e} {tau*ke:8.4f}  {err:9.3e} {tau*err:8.4f}")
    taus = np.geomspace(0.01, 1e5, 400)
    vals = np.array([sup_over_l(t, l) for t in taus])
    print("sup_tau tau*ke  =", (taus * vals[:, 0]).max(), " sup_tau min(1, ...) check: max ke =", vals[:, 0].max())
    print("sup_tau tau*err =", (taus * vals[:, 1]).max())
    print("1/(4e) =", 1 / (4 * np.e))
