"""Generate lean/MeanEstimation/Rows.lean from data/certified.jsonl: for each certified row, the error
bound of Error.lean at sigma = 1, with eta rounded up to 14 decimals, is at most eps (exact rationals)."""
import json, math, sys
from fractions import Fraction as Fr
rows = [json.loads(l) for l in open(sys.argv[1] if len(sys.argv) > 1 else "data/certified.jsonl")]
out = ['import MeanEstimation.Error', '', '/-!', '# Error bounds of the certified rows',
       '', 'Each theorem checks, in exact rational arithmetic, that the bound of `estimator_error` for the',
       'parameters of one row (σ = 1, central band `b`, ratio `ρ`, `n` outer bands, angle width `η`',
       'rounded up, `S = 1 + 1/16`) is at most `ε`. The bound increases with `η`, so it also holds',
       'for the unrounded width.', '-/', '', 'namespace MeanEstimation', '']
for d in rows:
    D = d["design"]; b, rho, n = D["b"], D["rho"], D["L"] - 1
    eta = Fr(math.ceil(Fr(D["eta"]) * 10**14), 10**14)
    eps = Fr(1) / Fr(round(d["inv_eps"] * 3), 3) if abs(d["inv_eps"] * 3 - round(d["inv_eps"] * 3)) < 1e-6 else None
    eps = Fr(1, round(d["inv_eps"])) if abs(d["inv_eps"] - round(d["inv_eps"])) < 1e-9 else eps
    assert abs(float(eps) - 1 / d["inv_eps"]) < 1e-15
    S = Fr(17, 16); T = Fr(b) * rho ** n; A = 2 * n * rho * eta ** 2
    sq = eta ** 2 * sum(Fr(b) * rho ** (j + 1) for j in range(n))
    rest = b * eta + sq
    sqrt_branch = S <= A * T ** 2 / 4
    val = (math.sqrt(A * S) if sqrt_branch else A * T / 4 + S / T) + rest
    assert val <= eps, (d, float(val), float(eps))
    name = f"row_{str(d['delta']).replace('.', '')}_{round(d['inv_eps'])}"
    e = f"({eta.numerator} / {eta.denominator} : ℝ)"
    lhs = (f"({b} : ℝ) * {e} + B (2 * {n} * {rho} * {e} ^ 2) (17 / 16) ({b} * {rho} ^ {n}) + {e} ^ 2 * "
           f"(∑ j ∈ Finset.range {n}, ({b} : ℝ) * {rho} ^ (j + 1))")
    rhs = f"({eps.numerator} / {eps.denominator} : ℝ)"
    out.append(f"/-- δ = {d['delta']}, σ/ε = {d['inv_eps']:.4g}: margin {float(eps - val):.3g}. -/")
    out.append(f"theorem {name} :\n    {lhs} ≤\n      {rhs} := by")
    if sqrt_branch:
        out.append("  unfold B; rw [if_pos (by norm_num)]")
        out.append(f"  have h : √(2 * {n} * {rho} * {e} ^ 2 * (17 / 16)) ≤ {rhs} - (({b} : ℝ) * {e} + {e} ^ 2 * "
                   f"(∑ j ∈ Finset.range {n}, ({b} : ℝ) * {rho} ^ (j + 1))) := by")
        out.append("    rw [Real.sqrt_le_left (by simp [Finset.sum_range_succ]; norm_num)]; simp [Finset.sum_range_succ]; norm_num")
        out.append("  linarith")
    else:
        out.append("  unfold B; rw [if_neg (by norm_num)]; simp [Finset.sum_range_succ]; norm_num")
    out.append("")
out.append("end MeanEstimation")
open(sys.argv[2] if len(sys.argv) > 2 else "lean/MeanEstimation/Rows.lean", "w").write("\n".join(out) + "\n")
print(len(rows), "rows;", sum(1 for d in rows), "written")
