"""Classical baseline: RMSE of plain MC and of randomized QMC (Owen-scrambled Sobol', Brownian bridge) for
standard payoffs under geometric Brownian motion. RQMC is unbiased, so its RMSE is the standard deviation over
independent scramblings. Fits RMSE ~ c N^-a on N = 2^10..2^16."""
import json, sys, numpy as np
from scipy.stats import qmc, norm
S0, r, vol, T = 100.0, 0.05, 0.2, 1.0
def bridge(z, m):
    """Brownian bridge on m = 2^k dates from standard normals z (n, m); returns W at t_i = i T/m."""
    n = z.shape[0]; W = np.zeros((n, m + 1)); W[:, m] = np.sqrt(T) * z[:, 0]; j = 1; h = m
    while h > 1:
        for left in range(0, m, h):
            mid, right = left + h // 2, left + h
            tl, tm, tr = left * T / m, mid * T / m, right * T / m
            mean = ((tr - tm) * W[:, left] + (tm - tl) * W[:, right]) / (tr - tl)
            W[:, mid] = mean + np.sqrt((tm - tl) * (tr - tm) / (tr - tl)) * z[:, j]; j += 1
        h //= 2
    return W[:, 1:]
def paths(z, m):
    W = bridge(z, m); t = np.arange(1, m + 1) * T / m
    return S0 * np.exp((r - vol ** 2 / 2) * t + vol * W)
disc = np.exp(-r * T)
def basket(u):                                    # 5 assets, correlation 0.5, terminal only
    z = norm.ppf(u); L = np.linalg.cholesky(0.5 * np.eye(5) + 0.5)
    ST = S0 * np.exp((r - vol ** 2 / 2) * T + vol * np.sqrt(T) * z @ L.T)
    return disc * (ST.mean(1) > 105)
def autocall(S):                                  # m = 4 quarterly observations, per unit notional
    pay = np.zeros(len(S)); alive = np.ones(len(S), bool)
    for i in range(4):
        hit = alive & (S[:, i] >= 100); pay[hit] = (1 + 0.05 * (i + 1)) * np.exp(-r * (i + 1) * T / 4); alive &= ~hit
    pay[alive] = np.where(S[alive, 3] < 70, S[alive, 3] / 100, 1.0) * disc
    return pay
PAY = {  # name: (dimension, payoff of uniforms)
    "european_call": (1, lambda u: disc * np.maximum(paths(norm.ppf(u), 1)[:, -1] - 100, 0)),
    "digital_call": (1, lambda u: disc * (paths(norm.ppf(u), 1)[:, -1] > 100)),
    "asian_call_16": (16, lambda u: disc * np.maximum(paths(norm.ppf(u), 16).mean(1) - 100, 0)),
    "down_out_call_16": (16, lambda u: disc * np.maximum(paths(norm.ppf(u), 16)[:, -1] - 100, 0) * (paths(norm.ppf(u), 16).min(1) > 85)),
    "basket_digital_5": (5, basket),
    "autocall_4": (4, lambda u: autocall(paths(norm.ppf(u), 4))),
}
if __name__ == "__main__":
    R = 32; Ns = [2 ** k for k in range(10, 17)]; rng = np.random.default_rng(1)
    for name, (dim, f) in PAY.items():
        mc, qm, est = [], [], []
        for N in Ns:
            v = [f(qmc.Sobol(dim, scramble=True, seed=rng).random(N)).mean() for _ in range(R)]
            qm.append(np.std(v, ddof=1)); est.append(np.mean(v))
            x = f(rng.random((N, dim))); mc.append(x.std() / np.sqrt(N))
        a_q, c_q = np.polyfit(np.log(Ns), np.log(qm), 1); a_m, c_m = np.polyfit(np.log(Ns), np.log(mc), 1)
        print(json.dumps({"payoff": name, "dim": dim, "value": est[-1], "sigma": mc[-1] * np.sqrt(Ns[-1]),
                          "rqmc_exp": -a_q, "rqmc_c": float(np.exp(c_q)), "mc_exp": -a_m,
                          "rqmc_rmse_2^16": qm[-1], "mc_rmse_2^16": mc[-1]}), flush=True)
