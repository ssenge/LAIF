import CutQuery.QReduction
import CutQuery.ClassicalBound
import CutQuery.UpperBound

/-!
# Explicit constants, the separation scale, and satisfiable premises

* `quantum_bound_24`, `classical_bound_23`: the two bounds with the constant in the statement;
* `classical_at_quantum_scale`: the classical bound at the weight scale of the quantum bound;
* `readAll_errAt`, `quantum_premise_holds`: for every `n` a quantum algorithm with `n` queries computes the
  minimum degree with error `0`, so the premise of `quantum_bound` can be met.
-/

open Finset

namespace CutQuery

local notation "ω" => ZMod.stdAddChar

section Explicit

theorem classicalWeight_le (n : ℕ) (hn : 0 < n) : classicalWeight n 23 ≤ (quantumWeight n 24 : ℤ) := by
  unfold classicalWeight quantumWeight
  push_cast
  apply pow_le_pow_right₀ (by norm_num)
  have h : 23 * n ≤ 24 * n ^ 2 := by nlinarith
  exact Nat.mul_le_mul_right _ h

/-- `classical_bound` with `C = 23` in the statement. -/
theorem classical_bound_23 (n : ℕ) [NeZero n] (T : ℕ) (Ω : Type) [Fintype Ω] (r : RandAlg n Ω)
    (herr : ∀ A : Weights n, InClass (classicalWeight n 23) A → r.err T A ≤ 1 / 3) :
    (n : ℝ) / 7 - 2 ≤ T := by
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  by_cases hn : n < 3
  · have : (n : ℝ) ≤ 3 := by exact_mod_cast hn.le
    linarith
  by_cases hT : n ≤ T
  · have : (n : ℝ) ≤ T := by exact_mod_cast hT
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  exact classical_bound_aux (by omega) Ω r herr

/-- Theorem 6 at the weight scale of Theorem 1. -/
theorem classical_at_quantum_scale (n : ℕ) [NeZero n] (T : ℕ) (Ω : Type) [Fintype Ω] (r : RandAlg n Ω)
    (herr : ∀ A : Weights n, InClass (quantumWeight n 24 : ℤ) A → r.err T A ≤ 1 / 3) :
    (n : ℝ) / 7 - 2 ≤ T :=
  classical_bound_23 n T Ω r fun A hA => herr A fun e =>
    ⟨(hA e).1, (hA e).2.trans (classicalWeight_le n (Nat.pos_of_ne_zero (NeZero.ne n)))⟩

/-- `quantum_bound` with `C = 24` in the statement. -/
theorem quantum_bound_24 (hA : AndApproxDegree) : ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) [NeZero n] (T : ℕ) (S : Type) [Fintype S] [DecidableEq S] (q : QAlg n T S),
    (∀ A : Weights n, InClass (quantumWeight n 24 : ℤ) A →
      q.errAt (n ^ 2 * quantumWeight n 24) A (minDegree A) ≤ 1 / 3) →
    c * Real.sqrt n ≤ T + 1 := by
  obtain ⟨c₀, hc₀, hdeg⟩ := hA
  refine ⟨min (c₀ / 36) (1 / 2), by positivity, ?_⟩
  intro n _ T S _ _ q herr
  have hT : (0 : ℝ) ≤ T := by positivity
  have hsq0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  by_cases hn : n < 3
  · have h1 : Real.sqrt n ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      have : (n : ℝ) ≤ 2 := by exact_mod_cast (by omega : n ≤ 2)
      linarith
    have h2 : min (c₀ / 36) (1 / 2) * Real.sqrt n ≤ (1 / 2) * 2 :=
      mul_le_mul (min_le_right _ _) h1 hsq0 (by norm_num)
    linarith
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    obtain ⟨m, L, W₀, hm, hL, hmN, hclass, hδ, hε⟩ := params k
    have : NeZero ((k + 3) ^ 2 * quantumWeight (k + 3) 24) := ⟨by
      unfold quantumWeight
      positivity⟩
    obtain ⟨r, hrd, hr⟩ := exists_and_approx q ((k + 3) ^ 2 * quantumWeight (k + 3) 24)
      (quantumWeight (k + 3) 24 : ℤ) W₀ (k + 3).factorial m L
      (fun d hd1 hd2 => Nat.dvd_factorial hd1 hd2) (Nat.factorial_pos _) hm hmN hL hclass herr hδ hε
    have h1 := hdeg (k + 3) r hr
    have h2 : (r.totalDegree : ℝ) ≤ 3 * (12 * T + 6) := by exact_mod_cast hrd
    have h3 : min (c₀ / 36) (1 / 2) * Real.sqrt ((k + 3 : ℕ) : ℝ)
        ≤ (c₀ / 36) * Real.sqrt ((k + 3 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hsq0
    linarith

end Explicit

section Witness

variable {n N : ℕ} [NeZero N]

/-- The normalization `1 / √(N^n)`. -/
noncomputable def kappa (n N : ℕ) : ℂ := rootInv N ^ n

omit [NeZero N] in
theorem kappa_mul_self : kappa n N * kappa n N = ((N : ℂ) ^ n)⁻¹ := by
  rw [kappa, ← mul_pow, rootInv_mul_self, inv_pow]

omit [NeZero N] in
theorem star_kappa : star (kappa n N) = kappa n N := by
  unfold kappa rootInv
  rw [star_pow]
  simp

theorem map_sum_eq_prod_char (y d : Fin n → ZMod N) : ω (∑ j, y j * d j) = ∏ j, ω (y j * d j) := by
  classical
  induction (univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [sum_insert hj, prod_insert hj, AddChar.map_add_eq_mul, ih]

theorem sum_char_pi (d : Fin n → ZMod N) :
    ∑ y : Fin n → ZMod N, ω (∑ j, y j * d j) = if d = 0 then (N : ℂ) ^ n else 0 := by
  have h : ∀ y : Fin n → ZMod N, ω (∑ j, y j * d j) = ∏ j, ω (y j * d j) := fun y =>
    map_sum_eq_prod_char y d
  simp_rw [h]
  have hp := Finset.prod_univ_sum (fun _ : Fin n => (univ : Finset (ZMod N))) (fun j a => ω (a * d j))
  rw [Fintype.piFinset_univ] at hp
  rw [← hp]
  simp_rw [sum_char_mul]
  split_ifs with hd
  · subst hd
    simp
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp hd
    exact prod_eq_zero (mem_univ j) (if_neg hj)

/-- Pointer and answer registers. -/
abbrev Reg (n N : ℕ) := Fin n × (Fin n → ZMod N)

/-- The Fourier transform of the answer registers, with the pointer unchanged. -/
noncomputable def qft (n N : ℕ) [NeZero N] : Matrix (Reg n N) (Reg n N) ℂ :=
  Matrix.of fun s s' => if s.1 = s'.1 then kappa n N * ω (∑ j, s.2 j * s'.2 j) else 0

theorem star_qft_apply (s s' : Reg n N) :
    star (qft n N) s s' = if s.1 = s'.1 then kappa n N * ω (-∑ j, s'.2 j * s.2 j) else 0 := by
  rw [Matrix.star_apply]
  simp only [qft, Matrix.of_apply]
  by_cases h : s.1 = s'.1
  · rw [if_pos h, if_pos h.symm, star_mul', star_kappa, AddChar.map_neg_eq_conj, Complex.star_def]
  · rw [if_neg h, if_neg fun h' => h h'.symm, star_zero]

theorem qft_mem : qft n N ∈ Matrix.unitaryGroup (Reg n N) ℂ := by
  have hN : ((N : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne N)
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type]
  have h : ∀ (i : Fin n) (y : Fin n → ZMod N),
      qft n N a (i, y) * star (qft n N) (i, y) b
        = if a.1 = i ∧ i = b.1 then ((N : ℂ) ^ n)⁻¹ * ω (∑ j, y j * (a.2 j - b.2 j)) else 0 := by
    intro i y
    rw [star_qft_apply]
    simp only [qft, Matrix.of_apply]
    by_cases h1 : a.1 = i
    · by_cases h2 : i = b.1
      · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩, mul_mul_mul_comm, kappa_mul_self,
          ← AddChar.map_add_eq_mul]
        congr 2
        rw [← sum_neg_distrib, ← sum_add_distrib]
        exact sum_congr rfl fun j _ => by ring
      · rw [if_neg h2, mul_zero, if_neg fun h => h2 h.2]
    · rw [if_neg h1, zero_mul, if_neg fun h => h1 h.1]
  simp_rw [h]
  have h2 : ∀ i : Fin n, ∑ y : Fin n → ZMod N,
      (if a.1 = i ∧ i = b.1 then ((N : ℂ) ^ n)⁻¹ * ω (∑ j, y j * (a.2 j - b.2 j)) else 0)
        = if i = a.1 ∧ a.1 = b.1 then (if a.2 = b.2 then 1 else 0) else 0 := by
    intro i
    by_cases h1 : i = a.1 ∧ a.1 = b.1
    · obtain ⟨rfl, h3⟩ := h1
      simp only [h3, and_self, if_true]
      have hz : (fun j => a.2 j - b.2 j) = 0 ↔ a.2 = b.2 :=
        ⟨fun h => funext fun j => sub_eq_zero.mp (congrFun h j), fun h => funext fun j => by simp [h]⟩
      rw [← mul_sum, sum_char_pi]
      by_cases h4 : a.2 = b.2
      · rw [if_pos (hz.mpr h4), if_pos h4]
        exact inv_mul_cancel₀ hN
      · rw [if_neg fun h => h4 (hz.mp h), if_neg h4, mul_zero]
    · rw [if_neg h1]
      refine sum_eq_zero fun y _ => if_neg fun h => h1 ⟨h.1.symm, h.1.trans h.2⟩
  simp_rw [h2]
  by_cases h3 : a.1 = b.1
  · by_cases h4 : a.2 = b.2
    · rw [if_pos (Prod.ext h3 h4)]
      simp [h3, h4]
    · rw [if_neg fun h => h4 (congrArg Prod.snd h)]
      simp [h3, h4]
  · rw [if_neg fun h => h3 (congrArg Prod.fst h)]
    simp [h3]

variable [NeZero n]

/-- Move the pointer by one, as a permutation matrix. -/
noncomputable def stepM (n N : ℕ) [NeZero n] [NeZero N] : Matrix (Reg n N) (Reg n N) ℂ :=
  Matrix.of fun s s' => if s' = (s.1 - 1, s.2) then 1 else 0

theorem stepM_mem : stepM n N ∈ Matrix.unitaryGroup (Reg n N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [stepM, Matrix.star_apply, Matrix.of_apply]
  rw [sum_eq_single (a.1 - 1, a.2)]
  · by_cases h : a = b
    · simp [h]
    · rw [if_neg h, if_pos rfl, one_mul, if_neg, star_zero]
      intro h'
      have h1 : a.1 - 1 = b.1 - 1 := congrArg Prod.fst h'
      exact h (Prod.ext (sub_left_injective h1) (Prod.mk.inj h').2)
  · intro s _ hs
    rw [if_neg hs, zero_mul]
  · simp

/-- Fourier transform, then a query per vertex with the pointer moved in between, then the inverse. -/
noncomputable def readAll (n N : ℕ) [NeZero n] [NeZero N] : QAlg n n (Reg n N) where
  x s := singleton s.1
  z s := ((s.2 s.1).val : ℤ)
  U t := if (t : ℕ) = n then star ⟨qft n N, qft_mem⟩
    else if (t : ℕ) = 0 then ⟨qft n N, qft_mem⟩ else ⟨stepM n N, stepM_mem⟩
  init := (0, 0)
  out s := univ.inf' ⟨0, mem_univ _⟩ fun v => ((s.2 v).val : ℤ)

/-- The degree of `v` modulo `N`. -/
noncomputable def degMod (N : ℕ) (A : Weights n) (v : Fin n) : ZMod N := ((degree A v : ℤ) : ZMod N)

theorem readAll_phase (A : Weights n) (i : Fin n) (y : Fin n → ZMod N) :
    (readAll n N).phase N A (i, y) = ω (y i * degMod N A i) := by
  rw [QAlg.phase_eq_char]
  congr 1
  simp [readAll, degMod, cut_singleton]

theorem ofNat_add_one (t : ℕ) : Fin.ofNat n t + 1 = Fin.ofNat n (t + 1) := by
  apply Fin.ext
  simp [Fin.val_add, Fin.ofNat, Nat.add_mod]

theorem sum_lt_succ (f : Fin n → ZMod N) (t : ℕ) (ht : t < n) :
    (∑ j : Fin n, if (j : ℕ) < t + 1 then f j else 0)
      = (∑ j : Fin n, if (j : ℕ) < t then f j else 0) + f (Fin.ofNat n t) := by
  have hp : ((Fin.ofNat n t : Fin n) : ℕ) = t := by simp [Fin.ofNat, Nat.mod_eq_of_lt ht]
  have h : ∀ j : Fin n, (if (j : ℕ) < t + 1 then f j else 0)
      = (if (j : ℕ) < t then f j else 0) + if j = Fin.ofNat n t then f j else 0 := by
    intro j
    by_cases h1 : j = Fin.ofNat n t
    · have h2 : (j : ℕ) = t := by rw [h1, hp]
      rw [if_pos (by omega), if_neg (by omega), if_pos h1, zero_add]
    · have h2 : (j : ℕ) ≠ t := fun h => h1 (Fin.ext (by rw [h, hp]))
      by_cases h3 : (j : ℕ) < t
      · rw [if_pos (by omega), if_pos h3, if_neg h1, add_zero]
      · rw [if_neg (by omega), if_neg h3, if_neg h1, add_zero]
  simp_rw [h]
  rw [sum_add_distrib, sum_ite_eq' univ]
  simp

/-- Before the last unitary, the pointer holds the round and the answer registers hold the phases so far. -/
theorem readAll_state (A : Weights n) (t : ℕ) (ht : t < n) (i : Fin n) (y : Fin n → ZMod N) :
    (readAll n N).state N A t ht.le (i, y) = if i = Fin.ofNat n t then
      kappa n N * ω (∑ j : Fin n, if (j : ℕ) < t then y j * degMod N A j else 0) else 0 := by
  induction t generalizing i y with
  | zero =>
    have hU : ((readAll n N).U ⟨0, Nat.succ_pos n⟩ : Matrix (Reg n N) (Reg n N) ℂ) = qft n N := by
      have h : (0 : ℕ) ≠ n := (NeZero.ne n).symm
      simp [readAll, h]
    rw [QAlg.state, hU, Matrix.mulVec, dotProduct, sum_eq_single (readAll n N).init]
    · have h0 : (readAll n N).init = (0, 0) := rfl
      simp only [Pi.single_eq_same, mul_one, h0, qft, Matrix.of_apply]
      simp
    · intro s _ hs
      rw [Pi.single_eq_of_ne hs, mul_zero]
    · simp
  | succ t ih =>
    have hU : ((readAll n N).U ⟨t + 1, Nat.succ_lt_succ ht.le⟩ : Matrix (Reg n N) (Reg n N) ℂ)
        = stepM n N := by
      have h : t + 1 ≠ n := ht.ne
      simp [readAll, h]
    rw [QAlg.state, hU, Matrix.mulVec, dotProduct, sum_eq_single (i - 1, y)]
    · simp only [stepM, Matrix.of_apply, if_true, one_mul]
      rw [ih (by omega), readAll_phase]
      have hi : i - 1 = Fin.ofNat n t ↔ i = Fin.ofNat n (t + 1) := by
        rw [sub_eq_iff_eq_add, ofNat_add_one]
      by_cases h : i = Fin.ofNat n (t + 1)
      · rw [if_pos (hi.mpr h), if_pos h, hi.mpr h, mul_left_comm, ← AddChar.map_add_eq_mul,
          sum_lt_succ _ t (by omega), add_comm]
      · rw [if_neg fun h' => h (hi.mp h'), if_neg h, mul_zero]
    · intro s _ hs
      simp only [stepM, Matrix.of_apply]
      rw [if_neg hs, zero_mul]
    · simp

/-- The final state vanishes unless the answer registers hold the degrees. -/
theorem readAll_final (A : Weights n) (i : Fin n) (y : Fin n → ZMod N) (hy : y ≠ degMod N A) :
    (readAll n N).state N A n le_rfl (i, y) = 0 := by
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := NeZero.pos n; omega⟩
  have hU : ∀ h, ((readAll n N).U ⟨n, h⟩ : Matrix (Reg n N) (Reg n N) ℂ) = star (qft n N) := by
    intro h
    simp [readAll]
  have hstate : ∀ h : m + 1 ≤ n, (readAll n N).state N A (m + 1) h (i, y)
      = ∑ s, star (qft n N) (i, y) s
        * ((readAll n N).phase N A s * (readAll n N).state N A m (by omega) s) := by
    intro h
    rw [QAlg.state]
    have h1 : (⟨m + 1, Nat.succ_lt_succ h⟩ : Fin (n + 1)) = ⟨n, Nat.lt_succ_self n⟩ :=
      Fin.ext hm.symm
    rw [h1, hU]
    rfl
  have hfin : (readAll n N).state N A n le_rfl (i, y) = (readAll n N).state N A (m + 1) hm.ge (i, y) := by
    congr 1
  rw [hfin, hstate, Fintype.sum_prod_type]
  have hN : ((N : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne N)
  have hm' : m < n := by omega
  have hterm : ∀ (i' : Fin n) (y' : Fin n → ZMod N), star (qft n N) (i, y) (i', y')
      * ((readAll n N).phase N A (i', y') * (readAll n N).state N A m (by omega) (i', y'))
        = if i = i' ∧ i' = Fin.ofNat n m then
          ((N : ℂ) ^ n)⁻¹ * ω (∑ j, y' j * (degMod N A j - y j)) else 0 := by
    intro i' y'
    rw [star_qft_apply, readAll_phase, readAll_state A m hm']
    simp only
    by_cases h1 : i = i'
    · by_cases h2 : i' = Fin.ofNat n m
      · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩, h2]
        have hall : ∑ j, y' j * (degMod N A j - y j)
            = -(∑ j, y' j * y j) + ((∑ j : Fin n, if (j : ℕ) < m then y' j * degMod N A j else 0)
              + y' (Fin.ofNat n m) * degMod N A (Fin.ofNat n m)) := by
          rw [← sum_lt_succ _ m hm']
          have : ∀ j : Fin n, (if (j : ℕ) < m + 1 then y' j * degMod N A j else 0)
              = y' j * degMod N A j := fun j => if_pos (by have := j.2; omega)
          simp_rw [this]
          rw [← sum_neg_distrib, ← sum_add_distrib]
          exact sum_congr rfl fun j _ => by ring
        rw [hall, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, ← kappa_mul_self]
        ring
      · rw [if_neg h2, mul_zero, mul_zero, if_neg fun h => h2 h.2]
    · rw [if_neg h1, zero_mul, if_neg fun h => h1 h.1]
  simp_rw [hterm]
  refine sum_eq_zero fun i' _ => ?_
  by_cases h : i = i' ∧ i' = Fin.ofNat n m
  · simp only [h, and_self, if_true]
    rw [← mul_sum, sum_char_pi, if_neg, mul_zero]
    intro h'
    exact hy (funext fun j => (sub_eq_zero.mp (congrFun h' j)).symm)
  · exact sum_eq_zero fun y' _ => if_neg h

/-- `n` phase queries compute the minimum degree with error `0`, when the degrees lie in `[0, N)`. -/
theorem readAll_errAt (A : Weights n) (hdeg : ∀ v, 0 ≤ degree A v ∧ degree A v < N) :
    (readAll n N).errAt N A (minDegree A) = 0 := by
  unfold QAlg.errAt
  refine sum_eq_zero fun s _ => ?_
  obtain ⟨i, y⟩ := s
  by_cases hy : y = degMod N A
  · have hval : ∀ v, ((y v).val : ℤ) = degree A v := by
      intro v
      rw [hy, degMod, ZMod.val_intCast]
      exact Int.emod_eq_of_lt (hdeg v).1 (hdeg v).2
    have hout : (readAll n N).out (i, y) = minDegree A := by
      change univ.inf' ⟨0, mem_univ _⟩ (fun v => ((y v).val : ℤ)) = _
      simp_rw [hval]
      rfl
    rw [if_pos hout]
  · simp [readAll_final A i y hy]

/-- The premise of `quantum_bound` can be met for every `n` and `C`, with `T = n` and error `0`. -/
theorem quantum_premise_holds (n : ℕ) [NeZero n] (C : ℕ) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (q : QAlg n n S),
      ∀ A : Weights n, InClass (quantumWeight n C : ℤ) A →
        q.errAt (n ^ 2 * quantumWeight n C) A (minDegree A) ≤ 1 / 3 := by
  have hW : 0 < quantumWeight n C := by
    unfold quantumWeight
    positivity
  have : NeZero (n ^ 2 * quantumWeight n C) := ⟨by
    have := NeZero.pos n
    positivity⟩
  refine ⟨Reg n (n ^ 2 * quantumWeight n C), inferInstance, inferInstance, readAll n _, fun A hA => ?_⟩
  rw [readAll_errAt]
  · norm_num
  · intro v
    have h := cut_mem_of_inClass hW hA (singleton v)
    rw [cut_singleton] at h
    exact h

end Witness

end CutQuery
