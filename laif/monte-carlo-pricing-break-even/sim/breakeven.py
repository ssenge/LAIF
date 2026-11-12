"""Break-even logical T rate for the basket autocallable of the derivative-pricing resource study [1]
(see autocall_2012.py). Classical: RQMC (scrambled Sobol', 16 independent scramblings) at the smallest power of two N
whose measured RMSE meets the target, timed on one CPU core in numpy (Sobol' generation included). Quantum: total
T-depth 5.4e7 at normalized error 2e-3 [1, Table 1], scaled as 1/eps (the number of oracle calls of amplitude
estimation is proportional to 1/eps at fixed confidence). R* = quantum T-depth / classical time."""
import json, time, numpy as np
from scipy.stats import qmc
from autocall_2012 import payoff
NORM, TDEPTH_2E3 = 28.0, 5.4e7
if __name__ == "__main__":
    rng = np.random.default_rng(20261112); rows = []
    for eps_n in [2e-3, 1e-3, 3e-4, 1e-4]:
        eps = eps_n * NORM
        for k in range(8, 21):
            N = 2 ** k
            v = [payoff(qmc.Sobol(60, scramble=True, seed=rng).random(N)).mean() for _ in range(16)]
            rmse = np.std(v, ddof=1)
            if rmse <= eps: break
        t0 = time.perf_counter()
        for _ in range(5): payoff(qmc.Sobol(60, scramble=True, seed=rng).random(N)).mean()
        t = (time.perf_counter() - t0) / 5
        tq = TDEPTH_2E3 * 2e-3 / eps_n
        rows.append({"eps_norm": eps_n, "eps_abs": eps, "rqmc_paths": N, "rqmc_rmse": rmse, "classical_s": t,
                     "quantum_tdepth": tq, "breakeven_T_rate_Hz": tq / t})
        print(json.dumps(rows[-1]), flush=True)
    assert all(r["rqmc_rmse"] <= r["eps_abs"] for r in rows)
