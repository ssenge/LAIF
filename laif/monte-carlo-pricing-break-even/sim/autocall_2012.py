"""Basket autocallable of the derivative-pricing resource study (3 underlyings, worst-of, 20 time steps of 1/20,
5 autocall dates, binary strike return 1.1 with payments p_i = 2 i, knock-in put with barrier 0.7, put strike 1,
notional 18), GBM with vols 0.1, 0.25, 0.4, correlation 0.5, r = 0. Measures the payoff standard deviation, plain MC
and RQMC RMSE, and the classical paths needed for the normalized error 2e-3 (normalization f_max + k K_put = 28)."""
import json, numpy as np
from scipy.stats import qmc, norm
d, m, dt = 3, 20, 1 / 20; vols = np.array([0.1, 0.25, 0.4]); C = np.linalg.cholesky(0.5 * np.eye(d) + 0.5)
call_dates = [4, 8, 12, 16, 20]
def payoff(u):
    z = norm.ppf(u).reshape(len(u), m, d) @ C.T                         # time-major increments
    logR = np.cumsum((-vols ** 2 / 2) * dt + vols * np.sqrt(dt) * z, axis=1)
    worst = np.exp(logR.min(2))                                          # worst-of cumulative return per date
    pay = np.zeros(len(u)); alive = np.ones(len(u), bool)
    for i, t in enumerate(call_dates):
        hit = alive & (worst[:, t - 1] >= 1.1); pay[hit] = 2 * (i + 1); alive &= ~hit
    ki = alive & (worst.min(1) < 0.7) & (worst[:, -1] < 1.0)
    pay[ki] = -18 * (1 - worst[ki, -1]); return pay
if __name__ == "__main__":
    rng = np.random.default_rng(3); x = payoff(rng.random((2 ** 20, m * d)))
    sigma = x.std(); norm_ = 10 + 18; eps = 2e-3 * norm_
    Ns = [2 ** k for k in range(10, 17)]; rq = []
    for N in Ns:
        v = [payoff(qmc.Sobol(m * d, scramble=True, seed=rng).random(N)).mean() for _ in range(16)]; rq.append(np.std(v, ddof=1))
    a, c = np.polyfit(np.log(Ns), np.log(rq), 1)
    n_mc = (sigma / eps) ** 2; n_rqmc = (np.exp(c) / eps) ** (1 / -a)
    print(json.dumps({"price": x.mean(), "sigma": sigma, "eps_abs": eps, "rqmc_exp": -a, "rqmc_c": float(np.exp(c)),
                      "paths_mc_68pct": n_mc, "paths_rqmc_rmse": n_rqmc}))
