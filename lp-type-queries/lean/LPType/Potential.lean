import LPType.Sampling
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The potential argument, deterministic part

A history is the list of samples so far, newest first. The weight of `h` after a history is `2` to
the number of samples in the history that `h` violates. If every sample has a violator in a basis
`B` of `H`, then by pigeonhole some `b ∈ B` is counted at least `T / δ` times.
-/

open Finset

namespace LPType

variable {H R : Type*} [DecidableEq H] [Fintype H] [PartialOrder R] (P : Problem H R)

namespace Problem

open scoped Classical in
/-- The number of samples in the history that `h` violates. -/
noncomputable def violCount (hist : List (Finset H)) (h : H) : ℕ :=
  hist.countP fun S => decide (P.Violates h S)

/-- The weight of `h` after a history. -/
noncomputable def histWeight (hist : List (Finset H)) (h : H) : ℝ := 2 ^ P.violCount hist h

/-- The total weight after a history. -/
noncomputable def histTotal (hist : List (Finset H)) : ℝ := ∑ h, P.histWeight hist h

omit [Fintype H] in
theorem histWeight_pos (hist : List (Finset H)) (h : H) : 0 < P.histWeight hist h :=
  pow_pos (by norm_num) _

@[simp] theorem histTotal_nil : P.histTotal [] = Fintype.card H := by
  simp [histTotal, histWeight, violCount]

/-- `W_{t+1} = W_t + w_t(V_t)`. -/
theorem histTotal_cons (S : Finset H) (hist : List (Finset H)) :
    P.histTotal (S :: hist) = P.histTotal hist + ∑ h ∈ P.violators S, P.histWeight hist h := by
  classical
  have h1 : ∀ h, P.histWeight (S :: hist) h
      = P.histWeight hist h + if h ∈ P.violators S then P.histWeight hist h else 0 := by
    intro h
    by_cases hv : P.Violates h S
    · simp [histWeight, violCount, hv, pow_succ, mul_two]
    · simp [histWeight, violCount, hv]
  simp only [histTotal, h1, sum_add_distrib, sum_ite_mem, univ_inter]

/-- `W_t ≤ W_{t+1}`. -/
theorem histTotal_le_cons (S : Finset H) (hist : List (Finset H)) :
    P.histTotal hist ≤ P.histTotal (S :: hist) := by
  rw [histTotal_cons]
  have : 0 ≤ ∑ h ∈ P.violators S, P.histWeight hist h :=
    sum_nonneg fun h _ => (P.histWeight_pos hist h).le
  linarith

/-- `W_{t+1} ≤ 2 W_t`. -/
theorem histTotal_cons_le (S : Finset H) (hist : List (Finset H)) :
    P.histTotal (S :: hist) ≤ 2 * P.histTotal hist := by
  rw [histTotal_cons, two_mul]
  have : ∑ h ∈ P.violators S, P.histWeight hist h ≤ P.histTotal hist :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun h _ _ => (P.histWeight_pos hist h).le
  linarith

omit [Fintype H] in
/-- Double counting: each sample with a violator in `B` contributes at least one count. -/
theorem length_le_sum_violCount {B : Finset H} {hist : List (Finset H)}
    (h : ∀ S ∈ hist, ∃ b ∈ B, P.Violates b S) :
    hist.length ≤ ∑ b ∈ B, P.violCount hist b := by
  classical
  induction hist with
  | nil => simp
  | cons S hist ih =>
    have ih' := ih fun S' hS' => h S' (List.mem_cons_of_mem _ hS')
    obtain ⟨b₀, hb₀, hv₀⟩ := h S List.mem_cons_self
    have hstep : ∀ b, P.violCount (S :: hist) b
        = P.violCount hist b + if P.Violates b S then 1 else 0 := by
      intro b
      simp only [violCount, List.countP_cons, decide_eq_true_eq]
    simp only [hstep, sum_add_distrib, List.length_cons]
    have : 1 ≤ ∑ b ∈ B, (if P.Violates b S then 1 else 0 : ℕ) :=
      (by simp [hv₀] : 1 = if P.Violates b₀ S then 1 else 0).le.trans
        (single_le_sum (f := fun b => if P.Violates b S then 1 else 0)
          (fun _ _ => Nat.zero_le _) hb₀)
    omega

omit [Fintype H] in
/-- **Pigeonhole.** If every one of `T ≥ 1` samples has a violator in `B`, some `b ∈ B` violates at
least `T / |B|` of them. -/
theorem pigeonhole {B : Finset H} {hist : List (Finset H)} (hne : hist ≠ [])
    (h : ∀ S ∈ hist, ∃ b ∈ B, P.Violates b S) :
    ∃ b ∈ B, hist.length ≤ #B * P.violCount hist b := by
  have hsum := P.length_le_sum_violCount h
  by_contra hno
  push Not at hno
  have hBne : B.Nonempty := by
    obtain ⟨S, hS⟩ := List.exists_mem_of_ne_nil hist hne
    obtain ⟨b, hb, -⟩ := h S hS
    exact ⟨b, hb⟩
  have hpos : 0 < #B := card_pos.2 hBne
  have h1 : #B * ∑ b ∈ B, P.violCount hist b < #B * hist.length := by
    rw [mul_sum]
    calc ∑ b ∈ B, #B * P.violCount hist b
        < ∑ _b ∈ B, hist.length := sum_lt_sum_of_nonempty hBne hno
      _ = #B * hist.length := by simp
  exact absurd (Nat.mul_le_mul_left #B hsum) (not_le.2 h1)

/-- If all samples have value below `f H`, some element of a basis of `H` violates at least `T / δ`
of them. -/
theorem exists_many_violations {B : Finset H} {hist : List (Finset H)} (hne : hist ≠ [])
    (hB : P.IsBasis B univ) (h : ∀ S ∈ hist, P.f S < P.f univ) :
    ∃ b ∈ B, hist.length ≤ P.combDim * P.violCount hist b := by
  obtain ⟨b, hb, hc⟩ := P.pigeonhole hne fun S hS => fact4 (h S hS) hB
  exact ⟨b, hb, hc.trans (Nat.mul_le_mul_right _ hB.card_le)⟩

/-- **The deterministic part of Theorem 1.** If all `T` samples have value below `f H`, then
`W_T ≥ 2^{T/δ}`. The cases `T = 0` and `δ = 0` are separated by `Nonempty H` and `1 ≤ δ`. -/
theorem two_rpow_le_histTotal [Nonempty H] (hδ : 1 ≤ P.combDim) {hist : List (Finset H)}
    (h : ∀ S ∈ hist, P.f S < P.f univ) :
    (2 : ℝ) ^ ((hist.length : ℝ) / P.combDim) ≤ P.histTotal hist := by
  have hδ' : (0 : ℝ) < P.combDim := by exact_mod_cast hδ
  rcases eq_or_ne hist [] with rfl | hne
  · simp only [List.length_nil, Nat.cast_zero, zero_div, Real.rpow_zero, histTotal_nil]
    exact_mod_cast Fintype.card_pos
  · obtain ⟨B, hB⟩ := exists_isBasis (P := P) (univ : Finset H)
    obtain ⟨b, -, hc⟩ := P.exists_many_violations hne hB h
    have h1 : (hist.length : ℝ) / P.combDim ≤ P.violCount hist b := by
      rw [div_le_iff₀ hδ']
      have : (hist.length : ℝ) ≤ P.combDim * P.violCount hist b := by exact_mod_cast hc
      linarith
    calc (2 : ℝ) ^ ((hist.length : ℝ) / P.combDim)
        ≤ (2 : ℝ) ^ (P.violCount hist b : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      _ = P.histWeight hist b := by simp [histWeight]
      _ ≤ P.histTotal hist :=
        single_le_sum (f := P.histWeight hist) (fun i _ => (P.histWeight_pos hist i).le) (mem_univ b)

end Problem

end LPType
