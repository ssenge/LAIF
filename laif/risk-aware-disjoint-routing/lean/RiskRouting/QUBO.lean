import Mathlib

/-!
# A QUBO for risk-aware disjoint routing

- `no_quadratic_parity`: at a vertex with at least three incident links, no quadratic function of
  the link variables vanishes on the sets of size 0 and 2 and is positive on the sets of size 1
  and 3. So the condition "degree 0 or 2" needs a slack variable there.
- `slack_pen_zero_iff`, `pair_pen_zero_iff`, `single_pen_zero_iff`, `end_pen_zero_iff`,
  `disj_pen_zero_iff`: each local penalty term is a nonnegative integer, and it vanishes, for the
  best slack, exactly when the local condition holds.
- `obj_le_U`: a pair of link sets without a common link has objective at most
  `U = c(E) + B Σ_{e ≠ f, unordered} p(e, f)`, for symmetric `p ≥ 0`.
- `qubo_minimizer`, `qubo_minimizer_strict`, `qubo_infeasible`: with a penalty weight `A > U`,
  every minimizer has penalty zero and reduces to an optimal feasible pair with the same objective;
  if every assignment of penalty zero that is not feasible can be strictly improved, minimizers are
  feasible; and if no assignment has penalty zero, the minimum exceeds `U`. The reduction step
  (`hred`) is the decomposition of a link set with degrees 1 at the ends and 0 or 2 elsewhere into
  a path and disjoint cycles, which is taken as a hypothesis of these statements.
-/

namespace RiskRouting.QUBO

open Finset

/-! ## No quadratic penalty at a vertex of degree at least three -/

/-- A quadratic function of `k` binary variables, evaluated at the indicator vector of `S`. -/
def quad {k : ℕ} (c : ℚ) (a : Fin k → ℚ) (b : Fin k → Fin k → ℚ) (S : Finset (Fin k)) : ℚ :=
  c + ∑ i ∈ S, a i + ∑ i ∈ S, ∑ j ∈ S, b i j

/-- `quad` is the polynomial `c + Σ a_i x_i + Σ b_ij x_i x_j` at the indicator vector of `S`. -/
theorem quad_eq_eval {k : ℕ} (c : ℚ) (a : Fin k → ℚ) (b : Fin k → Fin k → ℚ) (S : Finset (Fin k)) :
    quad c a b S = c + ∑ i, a i * (if i ∈ S then 1 else 0) +
      ∑ i, ∑ j, b i j * (if i ∈ S then 1 else 0) * (if j ∈ S then 1 else 0) := by
  unfold quad
  congr 1
  · congr 1
    simp [Finset.sum_ite_mem]
  · rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S)]
    have h1 : ∀ i ∈ Finset.univ.filter (· ∉ S),
        (∑ j, b i j * (if i ∈ S then (1 : ℚ) else 0) * (if j ∈ S then 1 else 0)) = 0 := by
      intro i hi; simp at hi; simp [hi]
    rw [Finset.sum_eq_zero h1, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp [hi, Finset.sum_ite_mem]

/-- **Lemma.** With at least three link variables at a vertex, no quadratic function is zero at
the sets of size 0 and 2 and positive at the sets of size 1 and 3. -/
theorem no_quadratic_parity {k : ℕ} (hk : 3 ≤ k) (c : ℚ) (a : Fin k → ℚ)
    (b : Fin k → Fin k → ℚ) :
    ¬ ∀ S : Finset (Fin k), (S.card = 0 ∨ S.card = 2 → quad c a b S = 0) ∧
        (S.card = 1 ∨ S.card = 3 → 0 < quad c a b S) := by
  intro h
  set p : Fin k := ⟨0, by omega⟩
  set q : Fin k := ⟨1, by omega⟩
  set r : Fin k := ⟨2, by omega⟩
  have hpq : p ≠ q := by simp [p, q, Fin.ext_iff]
  have hpr : p ≠ r := by simp [p, r, Fin.ext_iff]
  have hqr : q ≠ r := by simp [q, r, Fin.ext_iff]
  have h0 := (h ∅).1 (Or.inl rfl)
  have hp := (h {p}).2 (Or.inl (by simp))
  have hq := (h {q}).2 (Or.inl (by simp))
  have hr := (h {r}).2 (Or.inl (by simp))
  have hpq2 := (h {p, q}).1 (Or.inr (by simp [hpq]))
  have hpr2 := (h {p, r}).1 (Or.inr (by simp [hpr]))
  have hqr2 := (h {q, r}).1 (Or.inr (by simp [hqr]))
  have hpqr := (h {p, q, r}).2 (Or.inr (by simp [hpq, hpr, hqr]))
  simp [quad, Finset.sum_insert, hpq, hpr, hqr] at h0 hp hq hr hpq2 hpr2 hqr2 hpqr
  linarith

/-! ## Local penalty terms -/

/-- Slack penalty `(d - 2z)²` at a vertex of degree at least three: some slack `z ∈ {0, 1}`
makes it zero iff the degree is 0 or 2, and it is a nonnegative integer. -/
theorem slack_pen_zero_iff (d : ℕ) :
    (∃ z : ℕ, z ≤ 1 ∧ ((d : ℤ) - 2 * z) ^ 2 = 0) ↔ d = 0 ∨ d = 2 := by
  constructor
  · rintro ⟨z, hz, h⟩
    have : (d : ℤ) = 2 * z := by nlinarith [sq_nonneg ((d : ℤ) - 2 * z)]
    interval_cases z <;> omega
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, by norm_num⟩
    · exact ⟨1, le_rfl, by norm_num⟩

/-- At a vertex with two links `e, f`, the penalty `(x_e - x_f)²` is zero iff the degree
`x_e + x_f` is 0 or 2. -/
theorem pair_pen_zero_iff (xe xf : ℕ) (he : xe ≤ 1) (hf : xf ≤ 1) :
    ((xe : ℤ) - xf) ^ 2 = 0 ↔ xe + xf = 0 ∨ xe + xf = 2 := by
  interval_cases xe <;> interval_cases xf <;> simp

/-- At a vertex with one link `e`, the penalty `x_e` is zero iff the degree is 0. -/
theorem single_pen_zero_iff (xe : ℕ) : (xe : ℤ) = 0 ↔ xe = 0 := by simp

/-- At an end vertex, `(d - 1)²` is zero iff the degree is 1. -/
theorem end_pen_zero_iff (d : ℕ) : ((d : ℤ) - 1) ^ 2 = 0 ↔ d = 1 := by
  constructor
  · intro h
    have : (d : ℤ) = 1 := by nlinarith [sq_nonneg ((d : ℤ) - 1)]
    omega
  · rintro rfl; norm_num

/-- The disjointness term `Σ_v deg_x(v) deg_y(v)` vanishes iff no vertex carries links of both
paths. -/
theorem disj_pen_zero_iff {V : Type*} (T : Finset V) (dx dy : V → ℕ) :
    ∑ v ∈ T, dx v * dy v = 0 ↔ ∀ v ∈ T, dx v = 0 ∨ dy v = 0 := by
  rw [Finset.sum_eq_zero_iff]
  simp

/-! ## The objective of a pair without a common link is at most `U` -/

theorem obj_le_U {L : Type*} [Fintype L] [DecidableEq L] (c : L → ℚ) (p : L → L → ℚ) {B : ℚ}
    (hc : ∀ e, 0 ≤ c e) (hp : ∀ e f, 0 ≤ p e f) (hsym : ∀ e f, p e f = p f e) (hB : 0 ≤ B)
    (X Y : Finset L) (hXY : Disjoint X Y) :
    ∑ e ∈ X, c e + ∑ e ∈ Y, c e + B * ∑ e ∈ X, ∑ f ∈ Y, p e f ≤
      ∑ e, c e + B * ((1 / 2) * ∑ ef ∈ (Finset.univ : Finset L).offDiag, p ef.1 ef.2) := by
  have h1 : ∑ e ∈ X, c e + ∑ e ∈ Y, c e ≤ ∑ e, c e := by
    rw [← Finset.sum_union hXY]
    exact Finset.sum_le_univ_sum_of_nonneg hc
  have hXY' : Disjoint (X ×ˢ Y) (Y ×ˢ X) := by
    rw [Finset.disjoint_left]
    rintro ⟨e, f⟩ h1 h2
    simp at h1 h2
    exact Finset.disjoint_left.mp hXY h1.1 h2.1
  have hsub : X ×ˢ Y ∪ Y ×ˢ X ⊆ (Finset.univ : Finset L).offDiag := by
    rintro ⟨e, f⟩ h
    simp only [Finset.mem_union, Finset.mem_product] at h
    simp only [Finset.mem_offDiag, Finset.mem_univ, true_and]
    rintro rfl
    rcases h with h | h
    · exact Finset.disjoint_left.mp hXY h.1 h.2
    · exact Finset.disjoint_left.mp hXY h.2 h.1
  have h2 : ∑ ef ∈ X ×ˢ Y, p ef.1 ef.2 = ∑ ef ∈ Y ×ˢ X, p ef.1 ef.2 := by
    rw [Finset.sum_product, Finset.sum_product, Finset.sum_comm]
    exact Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun e _ => hsym e f
  have h3 : ∑ ef ∈ X ×ˢ Y ∪ Y ×ˢ X, p ef.1 ef.2 ≤
      ∑ ef ∈ (Finset.univ : Finset L).offDiag, p ef.1 ef.2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun ef _ _ => hp _ _
  rw [Finset.sum_union hXY', ← h2] at h3
  have h4 : ∑ e ∈ X, ∑ f ∈ Y, p e f = ∑ ef ∈ X ×ˢ Y, p ef.1 ef.2 := by
    rw [Finset.sum_product]
  rw [h4]
  have := mul_le_mul_of_nonneg_left (show ∑ ef ∈ X ×ˢ Y, p ef.1 ef.2 ≤
    (1 / 2) * ∑ ef ∈ (Finset.univ : Finset L).offDiag, p ef.1 ef.2 by linarith) hB
  linarith

/-! ## Minimizers of the penalized cost -/

section Abstract

variable {X : Type*} (obj : X → ℚ) (pen : X → ℕ) (Feas : X → Prop) (U A : ℚ)

/-- **Theorem (sufficiency of `A > U`).** If a feasible assignment exists, every minimizer of
`obj + A · pen` has penalty zero, and reduces to a feasible assignment of the same objective that
is optimal among feasible assignments. -/
theorem qubo_minimizer (hobj : ∀ x, 0 ≤ obj x) (hFpen : ∀ x, Feas x → pen x = 0)
    (hFU : ∀ x, Feas x → obj x ≤ U) (hA : U < A)
    (hred : ∀ x, pen x = 0 → ∃ y, Feas y ∧ obj y ≤ obj x)
    (x : X) (hmin : ∀ z, obj x + A * pen x ≤ obj z + A * pen z) (hex : ∃ z, Feas z) :
    pen x = 0 ∧ ∃ y, Feas y ∧ obj y = obj x ∧ ∀ z, Feas z → obj y ≤ obj z := by
  obtain ⟨z, hz⟩ := hex
  have hpx : pen x = 0 := by
    by_contra h
    have h1 : (1 : ℚ) ≤ pen x := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    have hz' := hmin z
    rw [hFpen z hz] at hz'
    push_cast at hz'
    have hA0 : 0 < A := by linarith [hobj z, hFU z hz]
    have : A * 1 ≤ A * pen x := mul_le_mul_of_nonneg_left h1 hA0.le
    linarith [hobj x, hFU z hz]
  refine ⟨hpx, ?_⟩
  obtain ⟨y, hy, hle⟩ := hred x hpx
  have hxy := hmin y
  rw [hpx, hFpen y hy] at hxy
  refine ⟨y, hy, by push_cast at hxy; linarith, fun w hw => ?_⟩
  have := hmin w
  rw [hpx, hFpen w hw] at this
  push_cast at this
  linarith

/-- With strict improvement of every non-feasible assignment of penalty zero (for instance, all
latencies positive, so that dropping a cycle lowers the objective), minimizers are feasible. -/
theorem qubo_minimizer_strict (hobj : ∀ x, 0 ≤ obj x) (hFpen : ∀ x, Feas x → pen x = 0)
    (hFU : ∀ x, Feas x → obj x ≤ U) (hA : U < A)
    (hred : ∀ x, pen x = 0 → ∃ y, Feas y ∧ obj y ≤ obj x)
    (hstrict : ∀ x, pen x = 0 → ¬ Feas x → ∃ y, Feas y ∧ obj y < obj x)
    (x : X) (hmin : ∀ z, obj x + A * pen x ≤ obj z + A * pen z) (hex : ∃ z, Feas z) :
    Feas x := by
  obtain ⟨hpx, -⟩ := qubo_minimizer obj pen Feas U A hobj hFpen hFU hA hred x hmin hex
  by_contra hF
  obtain ⟨y, hy, hlt⟩ := hstrict x hpx hF
  have := hmin y
  rw [hpx, hFpen y hy] at this
  push_cast at this
  linarith

/-- If no assignment has penalty zero, the penalized cost `obj + A pen` exceeds `U` everywhere. -/
theorem qubo_infeasible (hobj : ∀ x, 0 ≤ obj x) (hA : U < A) (hU : 0 ≤ U)
    (hnone : ∀ x, pen x ≠ 0) (x : X) : U < obj x + A * pen x := by
  have h1 : (1 : ℚ) ≤ pen x := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hnone x)
  have : A * 1 ≤ A * pen x := mul_le_mul_of_nonneg_left h1 (by linarith)
  linarith [hobj x]

end Abstract

end RiskRouting.QUBO
