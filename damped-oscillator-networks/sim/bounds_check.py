"""Grid check of every inequality used in the proofs of Theorems A and B of the notes (not a proof).

Theorem A: l G^2 + Gd^2 <= min(1, 4/tau) for all l >= 0, tau > 0, via the three case bounds
  rho >= 1/2:  1/(e tau) + 2/(e^2 tau^2) + 4.5 e^{-3 tau}
  rho <  1/2:  (1 + 2 tau + 2 tau^2) e^{-tau}
  l > 1:       (2 + 2 tau + 2 tau^2) e^{-2 tau}
Theorem B: every entry of R - R_heat is at most C_B / tau for tau >= 1, entrywise bounds of the notes."""
import numpy as np
import scalar_check as sc

taus = np.concatenate([np.geomspace(1e-3, 1, 200), np.geomspace(1, 1e5, 600)])
ls = np.concatenate([np.geomspace(1e-14, 0.75, 20000), np.linspace(0.75, 0.999999, 5000), np.linspace(1.000001, 2, 5000), np.geomspace(2, 1e6, 20000)])
rho = np.sqrt(np.clip(1 - ls, 0, None))
worstA, worstcase, worstB = 0.0, 0.0, 0.0
for tau in taus:
    F, G, Gd = sc.mode(ls, tau)
    lhs = ls * G ** 2 + Gd ** 2
    worstA = max(worstA, np.max(lhs / min(1, 4 / tau)))
    caseA = np.where(ls > 1, (2 + 2 * tau + 2 * tau ** 2) * np.exp(-2 * tau),
                     np.where(rho >= 0.5, 1 / (np.e * tau) + 2 / (np.e * tau) ** 2 + 4.5 * np.exp(-3 * tau),
                              (1 + 2 * tau + 2 * tau ** 2) * np.exp(-tau)))
    worstcase = max(worstcase, np.max(lhs / caseA))
    if tau >= 1:
        Fh, Gh, Gdh = sc.heat(ls, tau)
        q = np.sqrt(ls)
        ent = np.max(np.abs(np.stack([F - Fh, q * (G - Gh), Gd - Gdh])))
        worstB = max(worstB, tau * ent)
print(f"Theorem A: max of (lG^2+Gd^2)/min(1,4/tau) = {worstA:.4f} (must be <= 1)")
print(f"Theorem A: max of (lG^2+Gd^2)/(case bound) = {worstcase:.4f} (must be <= 1)")
print(f"Theorem B: max over tau >= 1 of tau * max entry of R - R_heat = {worstB:.4f}")

# Theorem B, region by region, the constants of the notes (tau >= 1)
wb = {"F-h (rho>=1/2)": 0, "sqrt(l)(G-h/2) (rho>=1/2)": 0, "Gd+lh/4 (rho>=1/2)": 0, "exact (l>3/4)": 0, "heat (l>3/4)": 0}
lim = {"F-h (rho>=1/2)": 1.34, "sqrt(l)(G-h/2) (rho>=1/2)": 1.06, "Gd+lh/4 (rho>=1/2)": 2.06, "exact (l>3/4)": 2.74, "heat (l>3/4)": 0.99}
lo, hi = ls <= 0.75, ls > 0.75
for tau in taus[taus >= 1]:
    F, G, Gd = sc.mode(ls, tau)
    Fh, Gh, Gdh = sc.heat(ls, tau)
    q = np.sqrt(ls)
    wb["F-h (rho>=1/2)"] = max(wb["F-h (rho>=1/2)"], tau * np.max(np.abs(F - Fh)[lo]))
    wb["sqrt(l)(G-h/2) (rho>=1/2)"] = max(wb["sqrt(l)(G-h/2) (rho>=1/2)"], tau * np.max(np.abs(q * (G - Gh))[lo]))
    wb["Gd+lh/4 (rho>=1/2)"] = max(wb["Gd+lh/4 (rho>=1/2)"], tau * np.max(np.abs(Gd - Gdh)[lo]))
    wb["exact (l>3/4)"] = max(wb["exact (l>3/4)"], tau * np.max(np.abs(np.stack([F, q * G, Gd]))[:, hi]))
    wb["heat (l>3/4)"] = max(wb["heat (l>3/4)"], tau * np.max(np.abs(np.stack([Fh, q * Gh, Gdh]))[:, hi]))
for k in wb:
    print(f"Theorem B piece {k:28s}: max tau*|.| = {wb[k]:.4f}  claimed <= {lim[k]}  {'ok' if wb[k] <= lim[k] else 'FAIL'}")

# the intermediate bound used for l > 3/4: (1+tau) e^{-tau/2} <= 2.74/tau
tt = np.linspace(1e-3, 60, 600001)
m = np.max(tt * (1 + tt) * np.exp(-tt / 2))
print(f"max tau (1+tau) e^(-tau/2) = {m:.4f}  claimed <= 2.74  {'ok' if m <= 2.74 else 'FAIL'}")
