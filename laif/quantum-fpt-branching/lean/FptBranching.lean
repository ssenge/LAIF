import Mathlib

/-!
# Parameter bounds for walks over the vertex cover above LP search tree

The search tree for Vertex Cover above LP has size `2.3146^μ` for the excess `μ = budget − LP value`, and a walk over
it costs the square root, `1.5214^μ`, up to polynomial factors. The reductions below bound the excess by the parameter
of the source problem. This file proves the bounds on the excess and the bases.

* `matching_le_fractional`: a matching of size `m` forces every fractional vertex cover to have total weight `≥ m`.
* `transversal_excess`: the auxiliary graph of the transversal reduction (two copies of the vertex set joined by a
  perfect matching) has excess at most `k` at budget `n + k`.
* `kvd_excess`: an excess of at most half the size of a deletion set to a graph whose vertex cover number equals its
  matching number, from the two inequalities used for it; `kvd_budget`: the budget step.
* `cost_of_excess`, `half_excess_base`: the bases `1.5214^k` and `1.2335^k`.
-/

namespace FptBranching

open Finset

/-- A matching of size `m`, given by endpoint maps `a b : Fin m → V` whose `2m` endpoints are pairwise distinct,
forces every fractional vertex cover `x` (nonnegative, with `x (a i) + x (b i) ≥ 1` on each matching edge) to have
total weight at least `m`. -/
theorem matching_le_fractional {V : Type*} [Fintype V] {m : ℕ} (a b : Fin m → V)
    (hinj : Function.Injective (Sum.elim a b)) (x : V → ℝ) (hx : ∀ v, 0 ≤ x v)
    (hcov : ∀ i, 1 ≤ x (a i) + x (b i)) : (m : ℝ) ≤ ∑ v, x v := by
  classical
  have h1 : ∑ s : Fin m ⊕ Fin m, x (Sum.elim a b s) ≤ ∑ v, x v := by
    rw [← Finset.sum_image (f := x) (s := (Finset.univ : Finset (Fin m ⊕ Fin m))) (g := Sum.elim a b)
      (by intro s _ t _ h; exact hinj h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => hx v)
  have h2 : ∑ s : Fin m ⊕ Fin m, x (Sum.elim a b s) = ∑ i, (x (a i) + x (b i)) := by
    rw [Fintype.sum_sum_type, Finset.sum_add_distrib]
    simp
  have h3 : ∑ _i : Fin m, (1 : ℝ) ≤ ∑ i, (x (a i) + x (b i)) :=
    Finset.sum_le_sum (fun i _ => hcov i)
  simp at h3
  linarith

/-- The transversal reduction: the auxiliary graph has a perfect matching on its `2n` vertices, so every fractional
vertex cover has weight at least `n`, and at budget `n + k` the excess over any fractional cover is at most `k`. -/
theorem transversal_excess {V : Type*} [Fintype V] {n : ℕ} (a b : Fin n → V)
    (hinj : Function.Injective (Sum.elim a b)) (x : V → ℝ) (hx : ∀ v, 0 ≤ x v)
    (hcov : ∀ i, 1 ≤ x (a i) + x (b i)) (k : ℝ) : ((n : ℝ) + k) - ∑ v, x v ≤ k := by
  have := matching_le_fractional a b hinj x hx hcov
  linarith

/-- The excess bound for deletion to a graph whose vertex cover number equals its matching number: if the remaining
graph has a matching `M` with a vertex cover of the same size, then `vc ≤ |M| + |O|`; with an LP value of at least
`|M| + |O| / 2` the excess is at most `|O| / 2`, so at most `k / 2` for a deletion set `O` of size at most `k`. -/
theorem kvd_excess {vc lp M O k : ℝ} (hvc : vc ≤ M + O) (hlp : M + O / 2 ≤ lp) (hO : O ≤ k) :
    vc - lp ≤ k / 2 := by
  linarith

/-- The budget step: if `vc − lp ≤ k / 2`, then a budget `ℓ` either reaches the vertex cover number (and the answer is
yes) or has an excess `ℓ − lp` below `k / 2`. -/
theorem kvd_budget {ℓ lp vc k : ℝ} (h : vc - lp ≤ k / 2) : vc ≤ ℓ ∨ ℓ - lp < k / 2 := by
  by_cases hl : ℓ - lp < k / 2
  · exact Or.inr hl
  · exact Or.inl (by linarith)

/-- The walk bases:`√2.3146 < 1.5214`, and `2.3146^(1/4) < 1.2335`. -/
theorem walk_base_k : (2.3146 : ℝ) < (1.5214 : ℝ) ^ 2 := by norm_num

theorem walk_base_half : (2.3146 : ℝ) < (1.2335 : ℝ) ^ 4 := by norm_num

theorem base_half_sq : (1.5214 : ℝ) ≤ (1.2335 : ℝ) ^ 2 := by norm_num

/-- A cost bound `C · b^μ` in the excess carries over to the parameter when `μ ≤ k` and `b ≥ 1`. -/
theorem cost_of_excess {C b μ k : ℝ} (hb : 1 ≤ b) (hC : 0 ≤ C) (hμ : μ ≤ k) :
    C * b ^ μ ≤ C * b ^ k :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hb hμ) hC

/-- An excess of at most `k / 2` turns the base `1.5214` into `1.2335` per unit of `k`. -/
theorem half_excess_base {k : ℝ} (hk : 0 ≤ k) : (1.5214 : ℝ) ^ (k / 2) ≤ (1.2335 : ℝ) ^ k := by
  have h1 : (1.5214 : ℝ) ^ (k / 2) ≤ ((1.2335 : ℝ) ^ (2 : ℝ)) ^ (k / 2) := by
    apply Real.rpow_le_rpow (by norm_num) _ (by linarith)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  rw [← Real.rpow_mul (by norm_num)] at h1
  have h2 : (2 : ℝ) * (k / 2) = k := by ring
  rwa [h2] at h1

/-- The full chain for the transversal problems: a walk cost `C · 1.5214^μ` in the excess of the auxiliary graph is at
most `C · 1.5214^k`. -/
theorem transversal_cost {V : Type*} [Fintype V] {n : ℕ} (a b : Fin n → V)
    (hinj : Function.Injective (Sum.elim a b)) (x : V → ℝ) (hx : ∀ v, 0 ≤ x v)
    (hcov : ∀ i, 1 ≤ x (a i) + x (b i)) {C k : ℝ} (hC : 0 ≤ C) :
    C * (1.5214 : ℝ) ^ (((n : ℝ) + k) - ∑ v, x v) ≤ C * (1.5214 : ℝ) ^ k :=
  cost_of_excess (by norm_num) hC (transversal_excess a b hinj x hx hcov k)

/-- The full chain for the half-excess problems: a walk cost `C · 1.5214^μ` with `μ ≤ k / 2` is at most
`C · 1.2335^k`. -/
theorem half_cost {C μ k : ℝ} (hC : 0 ≤ C) (hk : 0 ≤ k) (hμ : μ ≤ k / 2) :
    C * (1.5214 : ℝ) ^ μ ≤ C * (1.2335 : ℝ) ^ k :=
  (cost_of_excess (by norm_num) hC hμ).trans (mul_le_mul_of_nonneg_left (half_excess_base hk) hC)

end FptBranching
