import CutQuery.Model
import CutQuery.Fejer

/-!
# Path expansion of a quantum query algorithm

Write `ω` for `ZMod.stdAddChar`. The state of a `T`-query algorithm on input `A` is a sum over paths
`p : Fin t → S` of an amplitude that does not depend on `A` times `ω (∑_i z (p i) cut A (x (p i)))`. The
acceptance probability is the corresponding sum over pairs of paths with a common accepting end point.
-/

open Finset

namespace CutQuery

variable {n T : ℕ} {S : Type*} [Fintype S] [DecidableEq S]

/-- The integer phase accumulated along a path. -/
def QAlg.pathPhase (q : QAlg n T S) (A : Weights n) {t : ℕ} (p : Fin t → S) : ℤ :=
  ∑ i, q.z (p i) * cut A (q.x (p i))

theorem QAlg.phase_eq_char (q : QAlg n T S) (N : ℕ) [NeZero N] (A : Weights n) (s : S) :
    q.phase N A s = ZMod.stdAddChar ((q.z s * cut A (q.x s) : ℤ) : ZMod N) :=
  (ZMod.stdAddChar_coe _).symm

/-- The path expansion of the state, with amplitudes independent of the input. -/
theorem QAlg.exists_path_expansion (q : QAlg n T S) (N : ℕ) [NeZero N] :
    ∀ (t : ℕ) (ht : t ≤ T), ∃ amp : (Fin t → S) → S → ℂ, ∀ (A : Weights n) (s : S),
      q.state N A t ht s
        = ∑ p, amp p s * ZMod.stdAddChar ((q.pathPhase A p : ℤ) : ZMod N) := by
  intro t
  induction t with
  | zero =>
    intro ht
    refine ⟨fun _ s => (q.U ⟨0, Nat.succ_pos T⟩ : Matrix S S ℂ).mulVec (Pi.single q.init 1) s, ?_⟩
    intro A s
    simp [QAlg.state, QAlg.pathPhase]
  | succ t ih =>
    intro ht
    obtain ⟨amp, hamp⟩ := ih (Nat.le_of_succ_le ht)
    refine ⟨fun p s => (q.U ⟨t + 1, Nat.succ_lt_succ ht⟩ : Matrix S S ℂ) s (p (Fin.last t))
      * amp (Fin.init p) (p (Fin.last t)), ?_⟩
    intro A s
    have hL : q.state N A (t + 1) ht s = ∑ s', (q.U ⟨t + 1, Nat.succ_lt_succ ht⟩ : Matrix S S ℂ) s s'
        * (q.phase N A s' * q.state N A t (Nat.le_of_succ_le ht) s') := rfl
    rw [hL, ← (Fin.snocEquiv fun _ : Fin (t + 1) => S).sum_comp, Fintype.sum_prod_type]
    refine sum_congr rfl fun s' _ => ?_
    rw [hamp A s', q.phase_eq_char, mul_sum, mul_sum]
    refine sum_congr rfl fun p₀ _ => ?_
    have hphase : q.pathPhase A ((Fin.snocEquiv fun _ : Fin (t + 1) => S) (s', p₀))
        = q.pathPhase A p₀ + q.z s' * cut A (q.x s') := by
      simp [QAlg.pathPhase, Fin.sum_univ_castSucc, Fin.snocEquiv]
    have hinit : Fin.init ((Fin.snocEquiv fun _ : Fin (t + 1) => S) (s', p₀)) = p₀ := by
      simp [Fin.snocEquiv]
    have hlast : ((Fin.snocEquiv fun _ : Fin (t + 1) => S) (s', p₀)) (Fin.last t) = s' := by
      simp [Fin.snocEquiv]
    simp only [hphase, hinit, hlast]
    push_cast
    rw [AddChar.map_add_eq_mul]
    ring

/-- A unitary matrix preserves the sum of squared moduli. -/
theorem sum_normSq_mulVec (U : Matrix.unitaryGroup S ℂ) (v : S → ℂ) :
    ∑ s, Complex.normSq ((U : Matrix S S ℂ).mulVec v s) = ∑ s, Complex.normSq (v s) := by
  have hstar : star (U : Matrix S S ℂ) * (U : Matrix S S ℂ) = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  have h : star ((U : Matrix S S ℂ).mulVec v) ⬝ᵥ (U : Matrix S S ℂ).mulVec v = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.star_eq_conjTranspose,
      hstar, Matrix.vecMul_one]
  have hconv : ∀ w : S → ℂ, star w ⬝ᵥ w = ((∑ s, Complex.normSq (w s) : ℝ) : ℂ) := by
    intro w
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.ofReal_sum]
    exact sum_congr rfl fun s _ => (Complex.normSq_eq_conj_mul_self).symm
  rw [hconv, hconv] at h
  exact_mod_cast h

/-- The state has unit norm at every step, for every integer input. -/
theorem QAlg.sum_normSq_state (q : QAlg n T S) (N : ℕ) [NeZero N] (A : Weights n) :
    ∀ (t : ℕ) (ht : t ≤ T), ∑ s, Complex.normSq (q.state N A t ht s) = 1 := by
  intro t
  induction t with
  | zero =>
    intro ht
    have h0 : q.state N A 0 ht = (q.U ⟨0, Nat.succ_pos T⟩ : Matrix S S ℂ).mulVec (Pi.single q.init 1) := rfl
    rw [h0, sum_normSq_mulVec]
    rw [Finset.sum_eq_single q.init]
    · simp
    · intro s _ hs
      simp [Pi.single_eq_of_ne hs]
    · simp
  | succ t ih =>
    intro ht
    have h1 : q.state N A (t + 1) ht = (q.U ⟨t + 1, Nat.succ_lt_succ ht⟩ : Matrix S S ℂ).mulVec
        fun s => q.phase N A s * q.state N A t (Nat.le_of_succ_le ht) s := rfl
    rw [h1, sum_normSq_mulVec]
    rw [← ih (Nat.le_of_succ_le ht)]
    refine sum_congr rfl fun s _ => ?_
    rw [map_mul, q.phase_eq_char, Complex.normSq_eq_norm_sq (ZMod.stdAddChar _), norm_char]
    simp

/-- The probability that the final measurement reports the value `d`. -/
noncomputable def QAlg.acc (q : QAlg n T S) (N : ℕ) (A : Weights n) (d : ℤ) : ℝ :=
  ∑ s, if q.out s = d then Complex.normSq (q.state N A T le_rfl s) else 0

theorem QAlg.acc_add_errAt (q : QAlg n T S) (N : ℕ) [NeZero N] (A : Weights n) (d : ℤ) :
    q.acc N A d + q.errAt N A d = 1 := by
  unfold QAlg.acc QAlg.errAt
  rw [← sum_add_distrib, ← q.sum_normSq_state N A T le_rfl]
  refine sum_congr rfl fun s _ => ?_
  split_ifs <;> simp

theorem QAlg.acc_nonneg (q : QAlg n T S) (N : ℕ) (A : Weights n) (d : ℤ) : 0 ≤ q.acc N A d := by
  unfold QAlg.acc
  refine sum_nonneg fun s _ => ?_
  split_ifs
  · exact Complex.normSq_nonneg _
  · exact le_rfl

theorem QAlg.errAt_nonneg (q : QAlg n T S) (N : ℕ) (A : Weights n) (d : ℤ) : 0 ≤ q.errAt N A d := by
  unfold QAlg.errAt
  refine sum_nonneg fun s _ => ?_
  split_ifs
  · exact le_rfl
  · exact Complex.normSq_nonneg _

theorem QAlg.acc_le_one (q : QAlg n T S) (N : ℕ) [NeZero N] (A : Weights n) (d : ℤ) : q.acc N A d ≤ 1 := by
  have h := q.acc_add_errAt N A d
  have h2 := q.errAt_nonneg N A d
  linarith

/-- If `d ≠ d'`, acceptance of `d` is an error for `d'`. -/
theorem QAlg.acc_le_errAt (q : QAlg n T S) (N : ℕ) (A : Weights n) {d d' : ℤ} (h : d ≠ d') :
    q.acc N A d ≤ q.errAt N A d' := by
  unfold QAlg.acc QAlg.errAt
  refine sum_le_sum fun s _ => ?_
  by_cases hs : q.out s = d
  · have : q.out s ≠ d' := hs ▸ h
    simp only [hs, ↓reduceIte, h, le_refl]
  · simp only [hs, ↓reduceIte]
    split_ifs
    · exact le_rfl
    · exact Complex.normSq_nonneg _

/-- The expansion of the acceptance probability over pairs of paths with a common end point. -/
theorem QAlg.exists_acc_expansion (q : QAlg n T S) (N : ℕ) [NeZero N] (d : ℤ) :
    ∃ α : (Fin T → S) × (Fin T → S) × S → ℂ, ∀ A : Weights n,
      (q.acc N A d : ℂ) = ∑ i, α i * ZMod.stdAddChar
        ((q.pathPhase A i.1 - q.pathPhase A i.2.1 : ℤ) : ZMod N) := by
  obtain ⟨amp, hamp⟩ := q.exists_path_expansion N T le_rfl
  refine ⟨fun i => if q.out i.2.2 = d then amp i.1 i.2.2 * (starRingEnd ℂ) (amp i.2.1 i.2.2) else 0, ?_⟩
  intro A
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  unfold QAlg.acc
  have hs : ∀ s, (((if q.out s = d then Complex.normSq (q.state N A T le_rfl s) else 0 : ℝ)) : ℂ)
      = ∑ p, ∑ p', (if q.out s = d then amp p s * (starRingEnd ℂ) (amp p' s) else 0)
          * ZMod.stdAddChar ((q.pathPhase A p - q.pathPhase A p' : ℤ) : ZMod N) := by
    intro s
    by_cases h : q.out s = d
    · simp only [h, ↓reduceIte]
      rw [Complex.normSq_eq_conj_mul_self, hamp A s, map_sum, mul_comm, sum_mul_sum]
      refine sum_congr rfl fun p _ => sum_congr rfl fun p' _ => ?_
      push_cast
      rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj, map_mul]
      ring
    · simp [h]
  rw [Complex.ofReal_sum]
  simp_rw [hs]
  rw [sum_comm]
  refine sum_congr rfl fun p _ => ?_
  rw [sum_comm]

end CutQuery
