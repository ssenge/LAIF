"""Two regulators: 3 stages, cut stage j = 2; stages 2 and 3 are fecund, stage-2 fecundity uses forage G2,
stage-3 fecundity uses forage G1. G_l = 1 - a_l.x / r_l (logistic forage at equilibrium), S = 1 - b.x / rS.
Maturation 1->2 at k1 S, 2->3 at k2 S.  Check: small cull on stage 2 lowers S iff U^b - sum_l w_l U_l > 1/E."""
import sys
import numpy as np
from scipy.optimize import fsolve

def F(y, P, h2):
    x1, x2, x3, S = y
    k1, k2, d, f2, f3, a1, a2, r1, r2, b, rS = P
    G1 = 1 - a1 @ y[:3]/r1; G2 = 1 - a2 @ y[:3]/r2
    return [f2*G2*x2 + f3*G1*x3 - (k1*S + d[0])*x1, k1*S*x1 - (k2*S + d[1] + h2)*x2, k2*S*x2 - d[2]*x3,
            S - (1 - b @ y[:3]/rS)]

def solve(P, h2, rng):
    sols = []
    for _ in range(30):
        y, _, ok, _ = fsolve(F, np.r_[np.exp(rng.uniform(-3, 0, 3)), rng.uniform(0.1, 1)], args=(P, h2), full_output=True)
        x = y[:3]; k1, k2, d, f2, f3, a1, a2, r1, r2, b, rS = P
        if ok != 1 or np.any(y <= 1e-9) or max(abs(np.array(F(y, P, h2)))) > 1e-11: continue
        if 1 - a1 @ x/r1 <= 0 or 1 - a2 @ x/r2 <= 0 or y[3] >= 1: continue
        if not any(np.allclose(y, z, rtol=1e-7) for z in sols): sols.append(y)
    return sols

rng = np.random.default_rng(int(sys.argv[1])); agree = dis = rev = unst = 0
for _ in range(int(sys.argv[2])):
    P = (np.exp(rng.uniform(-1, 1.5)), np.exp(rng.uniform(-1, 1.5)), np.exp(rng.uniform(np.log(0.02), np.log(0.4), 3)),
         np.exp(rng.uniform(0, 3)), np.exp(rng.uniform(0, 3)),
         np.r_[0, 0, 1.0], np.r_[rng.uniform(0, 2), rng.uniform(0, 2), 0], 1.0, 1.0,
         np.exp(rng.uniform(np.log(0.3), np.log(5), 3)), rng.uniform(0.5, 3))
    s0 = solve(P, 0.0, rng)
    if len(s0) != 1: continue
    y = s0[0]; x = y[:3]; S = y[3]; k1, k2, d, f2, f3, a1, a2, r1, r2, b, rS = P
    def xdot(xx):  # ODE in x with S, G algebraic
        return np.array(F(np.r_[xx, 1 - b @ xx/rS], P, 0.0)[:3])
    Jx = np.array([(xdot(x+1e-7*np.eye(3)[i]) - xdot(x-1e-7*np.eye(3)[i]))/2e-7 for i in range(3)]).T
    stable = np.max(np.linalg.eigvals(Jx).real) < -1e-9
    if not stable: unst += 1; continue
    G1 = 1 - a1 @ x/r1; G2 = 1 - a2 @ x/r2
    # fecundity shares (elasticities of R0 to G1, G2) and depletion elasticities of logistic forage
    eps = np.array([f3*G1*x[2], f2*G2*x[1]]); eps /= eps.sum()
    eta = np.array([-(1 - G1)/G1, -(1 - G2)/G2])
    E = -(eps*eta).sum(); w = eps*eta/(eps*eta).sum()
    Ub = b[0]*x[0]/(b @ x); Ua = np.array([0.0, a2[0]*x[0]/(a2 @ x)])
    pred = Ub - w @ Ua > 1/E
    s1 = solve(P, 1e-5, rng)
    if len(s1) != 1: continue
    down = s1[0][3] < S; rev += down
    agree += down == pred; dis += down != pred
    if down != pred: print(f"  margin {Ub - w @ Ua - 1/E:+.3e}  dS {s1[0][3]-S:+.3e}  eig {np.max(np.linalg.eigvals(np.array([(np.array(F(y+1e-7*np.eye(4)[i],P,0.0))-np.array(F(y-1e-7*np.eye(4)[i],P,0.0)))/2e-7 for i in range(4)]).T).real):+.3e}")
print(f"two regulators (stable equilibria): agree {agree}, disagree {dis}, reversals {rev}, unstable skipped {unst}")
assert dis == 0
