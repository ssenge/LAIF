"""Does environmental noise change the sign of the cascade? Annual two-stage model (calves J, adults A):
  G_t = max(0, 1 - a A_t) * xi_t            summer forage, weather noise xi lognormal with mean 1
  S_t = max(0, 1 - bJ J_t - bA A_t)          browsable saplings (fast variable)
  J_{t+1} = f G_t A_t + sJ (1 - k S_t) J_t   newborns plus calves that did not mature
  A_{t+1} = sA (1 - hA) A_t + sJ k S_t J_t   adults; hA = adult cull rate
Compares the sign of d E[S] / d hA (finite difference, common random numbers) at sigma = 0 and sigma > 0."""
import sys
import numpy as np

def mean_S(p, hA, Z, burn=2000):
    a, f, sJ, sA, k, bJ, bA, sig = p
    xi = np.exp(sig*Z - sig**2/2)
    J, A = 0.1, 0.1; tot = 0.0; n = 0
    for t, x in enumerate(xi):
        G = max(0.0, 1 - a*A)*x; S = max(0.0, 1 - bJ*J - bA*A)
        J, A = f*G*A + sJ*(1 - k*S)*J, sA*(1 - hA)*A + sJ*k*S*J
        if A < 1e-12: return np.nan
        if t >= burn: tot += S; n += 1
    return tot/n

if __name__ == "__main__":
    rng = np.random.default_rng(int(sys.argv[1])); M = int(sys.argv[2]); T = int(sys.argv[3])
    flips = 0; tested = 0
    for _ in range(M):
        p = [rng.uniform(0.5, 5), np.exp(rng.uniform(np.log(0.3), np.log(5))), rng.uniform(0.3, 0.9), rng.uniform(0.6, 0.95),
             rng.uniform(0.2, 1), np.exp(rng.uniform(np.log(0.2), np.log(5))), np.exp(rng.uniform(np.log(0.2), np.log(5))), 0.0]
        Z = rng.standard_normal(T)
        det = [mean_S(p, h, Z) for h in (0.0, 0.02)]
        p[7] = rng.uniform(0.3, 0.8)
        sto = [mean_S(p, h, Z) for h in (0.0, 0.02)]
        if np.any(np.isnan(det + sto)): continue
        tested += 1
        sd, ss = np.sign(det[1] - det[0]), np.sign(sto[1] - sto[0])
        if sd != ss and abs(sto[1]-sto[0]) > 1e-4 and abs(det[1]-det[0]) > 1e-4:
            flips += 1
            print(f"flip: p={np.round(p,3)}  det dS={det[1]-det[0]:+.4f}  noisy dS={sto[1]-sto[0]:+.4f}")
    print(f"tested {tested}, sign flips {flips}")
