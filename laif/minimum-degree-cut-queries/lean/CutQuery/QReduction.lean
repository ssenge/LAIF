import CutQuery.QuantumBound

/-!
# Queries with an arbitrary phase function

`GenAlg` is a query algorithm whose query acts as `|s⟩ ↦ f s (cut A (x s)) |s⟩`, where `f : S → ℤ → ℂ` has unit
modulus. This covers an answer register read in any Fourier basis and any other modulus, for example
`f s y = e(z_s y / M)`.

On inputs whose cuts lie in `[0, N)` one such query is simulated by two phase queries on `S × ZMod N`, with `F` the
Fourier transform on the second register and `D` the diagonal of `f` on the value register. The value register holds
the uniform vector between simulated queries, and a query block maps

  `ψ ⊗ u  ↦(O)  ∑_s ψ_s |s⟩ F|c_s⟩  ↦(F⁻¹)  ∑_s ψ_s |s, c_s⟩  ↦(D)  ∑_s f_s ψ_s |s, c_s⟩
    ↦(F⁻¹)  ∑_s f_s ψ_s |s⟩ F⁻¹|c_s⟩  ↦(O)  (f ψ) ⊗ u`.

`GenAlg.errAt_sim` shows that the error probabilities agree and `quantum_bound_general` carries the bound over.
-/

open Finset
open scoped Kronecker

namespace CutQuery

local notation "ω" => ZMod.stdAddChar

/-- A `T`-query algorithm whose query multiplies `|s⟩` by `f s (cut A (x s))`. -/
structure GenAlg (n T : ℕ) (S : Type*) [Fintype S] [DecidableEq S] where
  x : S → Fin n → Bool
  f : S → ℤ → ℂ
  norm_f : ∀ s y, ‖f s y‖ = 1
  U : Fin (T + 1) → Matrix.unitaryGroup S ℂ
  init : S
  out : S → ℤ

variable {n T : ℕ} {S : Type*} [Fintype S] [DecidableEq S]

/-- The state after `U_t O U_{t-1} ⋯ O U_0` applied to the initial basis state. -/
noncomputable def GenAlg.state (g : GenAlg n T S) (A : Weights n) : (t : ℕ) → t ≤ T → S → ℂ
  | 0, _ => (g.U ⟨0, Nat.succ_pos T⟩ : Matrix S S ℂ).mulVec (Pi.single g.init 1)
  | t + 1, h => (g.U ⟨t + 1, Nat.succ_lt_succ h⟩ : Matrix S S ℂ).mulVec
      fun s => g.f s (cut A (g.x s)) * g.state A t (Nat.le_of_succ_le h) s

/-- The probability that the final measurement reports a value other than `d`. -/
noncomputable def GenAlg.errAt (g : GenAlg n T S) (A : Weights n) (d : ℤ) : ℝ :=
  ∑ s, if g.out s = d then 0 else Complex.normSq (g.state A T le_rfl s)

section Fourier

variable {N : ℕ} [NeZero N]

/-- The normalization `1 / √N`. -/
noncomputable def rootInv (N : ℕ) : ℂ := (((Real.sqrt N)⁻¹ : ℝ) : ℂ)

omit [NeZero N] in
theorem rootInv_mul_self : rootInv N * rootInv N = (N : ℂ)⁻¹ := by
  have hN : (0 : ℝ) ≤ N := by positivity
  unfold rootInv
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hN]
  push_cast
  rfl

/-- `∑_v ω (v b) = N` if `b = 0`, else `0`. -/
theorem sum_char_mul (b : ZMod N) : ∑ v : ZMod N, ω (v * b) = if b = 0 then (N : ℂ) else 0 := by
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar N), ZMod.card]
  split_ifs <;> simp

/-- The Fourier matrix on `ZMod N`. -/
noncomputable def fourier (N : ℕ) [NeZero N] : Matrix (ZMod N) (ZMod N) ℂ :=
  Matrix.of fun y w => rootInv N * ω (y * w)

theorem star_fourier_apply (y w : ZMod N) : (star (fourier N)) y w = rootInv N * ω (-(y * w)) := by
  rw [Matrix.star_apply]
  simp only [fourier, Matrix.of_apply]
  rw [star_mul', AddChar.map_neg_eq_conj]
  have h : star (rootInv N) = rootInv N := by
    unfold rootInv
    simp
  rw [h, Complex.star_def, mul_comm w y]

theorem fourier_mem : fourier N ∈ Matrix.unitaryGroup (ZMod N) ℂ := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [Matrix.mem_unitaryGroup_iff]
  ext y w
  rw [Matrix.mul_apply, Matrix.one_apply]
  have h : ∀ v, fourier N y v * (star (fourier N)) v w
      = (N : ℂ)⁻¹ * ω (v * (y - w)) := by
    intro v
    rw [star_fourier_apply]
    simp only [fourier, Matrix.of_apply]
    rw [mul_mul_mul_comm, rootInv_mul_self, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [h]
  rw [← mul_sum, sum_char_mul]
  by_cases hyw : y = w
  · simp [hyw, hN]
  · simp [hyw, sub_eq_zero]

/-- The Fourier inversion on the second register. -/
theorem star_fourier_mulVec_char (c w : ZMod N) (τ : ℂ) :
    ∑ y, (star (fourier N)) w y * (ω (y * c) * (τ * rootInv N)) = if w = c then τ else 0 := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have h : ∀ y, (star (fourier N)) w y * (ω (y * c) * (τ * rootInv N))
      = τ * ((N : ℂ)⁻¹ * ω (y * (c - w))) := by
    intro y
    rw [star_fourier_apply, ← rootInv_mul_self]
    have : ω (y * (c - w)) = ω (-(w * y)) * ω (y * c) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    rw [this]
    ring
  simp_rw [h]
  rw [← mul_sum, ← mul_sum, sum_char_mul]
  by_cases hc : w = c
  · simp [hc, hN]
  · have : c - w ≠ 0 := sub_ne_zero.mpr fun h => hc h.symm
    simp [hc, this]

/-- The Fourier transform of a delta on the second register. -/
theorem star_fourier_mulVec_delta (c y : ZMod N) (τ : ℂ) :
    ∑ w, (star (fourier N)) y w * (if w = c then τ else 0) = rootInv N * ω (-(y * c)) * τ := by
  rw [Finset.sum_eq_single c]
  · simp only [↓reduceIte]
    rw [star_fourier_apply]
  · intro w _ hw
    simp [hw]
  · intro hc
    exact absurd (mem_univ c) hc

end Fourier

section Gates

variable {κ κ' : Type*} [Fintype κ] [Fintype κ'] [DecidableEq κ] [DecidableEq κ']

theorem kron_mem {A : Matrix κ κ ℂ} {B : Matrix κ' κ' ℂ} (hA : A ∈ Matrix.unitaryGroup κ ℂ)
    (hB : B ∈ Matrix.unitaryGroup κ' ℂ) : A ⊗ₖ B ∈ Matrix.unitaryGroup (κ × κ') ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at *
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, hA, hB, Matrix.one_kronecker_one]

omit [DecidableEq κ] in
theorem kron_left_apply (V : Matrix κ κ ℂ) (v : κ × κ' → ℂ) (s : κ) (y : κ') :
    ((V ⊗ₖ (1 : Matrix κ' κ' ℂ)).mulVec v) (s, y) = ∑ s', V s s' * v (s', y) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply]
  refine sum_congr rfl fun s' _ => ?_
  rw [Finset.sum_eq_single y]
  · simp
  · intro w _ hw
    simp [hw.symm]
  · intro hy
    exact absurd (mem_univ y) hy

omit [DecidableEq κ'] in
theorem kron_right_apply (Φ : Matrix κ' κ' ℂ) (v : κ × κ' → ℂ) (s : κ) (y : κ') :
    (((1 : Matrix κ κ ℂ) ⊗ₖ Φ).mulVec v) (s, y) = ∑ w, Φ y w * v (s, w) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single s]
  · simp
  · intro s' _ hs
    simp [hs.symm]
  · intro hs
    exact absurd (mem_univ s) hs

end Gates

section Simulation

variable {N : ℕ} [NeZero N]

/-- `V ⊗ 1`. -/
noncomputable def liftGate (V : Matrix.unitaryGroup S ℂ) : Matrix.unitaryGroup (S × ZMod N) ℂ :=
  ⟨(V : Matrix S S ℂ) ⊗ₖ (1 : Matrix (ZMod N) (ZMod N) ℂ), kron_mem V.2 (one_mem _)⟩

/-- `1 ⊗ F`. -/
noncomputable def fourierGate : Matrix.unitaryGroup (S × ZMod N) ℂ :=
  ⟨(1 : Matrix S S ℂ) ⊗ₖ fourier N, kron_mem (one_mem _) fourier_mem⟩

/-- The diagonal of `f`, reading the value register as an element of `[0, N)`. -/
noncomputable def GenAlg.valueGate (g : GenAlg n T S) (N : ℕ) [NeZero N] :
    Matrix.unitaryGroup (S × ZMod N) ℂ :=
  ⟨Matrix.diagonal fun p => g.f p.1 (p.2.val : ℤ), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext p
    simp only [Pi.star_apply, Complex.star_def, Complex.mul_conj]
    rw [Complex.normSq_eq_norm_sq, g.norm_f]
    simp⟩

/-- The algorithm with phase queries that simulates `g`. -/
noncomputable def GenAlg.sim (g : GenAlg n T S) (N : ℕ) [NeZero N] : QAlg n (2 * T) (S × ZMod N) where
  x p := g.x p.1
  z p := (p.2.val : ℤ)
  U i :=
    if (i : ℕ) = 0 then liftGate (g.U ⟨0, Nat.succ_pos T⟩) * fourierGate
    else if (i : ℕ) % 2 = 1 then star fourierGate * g.valueGate N * star fourierGate
    else liftGate (g.U ⟨(i : ℕ) / 2, by have := i.2; omega⟩)
  init := (g.init, 0)
  out p := g.out p.1

theorem GenAlg.sim_phase (g : GenAlg n T S) (A : Weights n) (s : S) (y : ZMod N) :
    (g.sim N).phase N A (s, y) = ω (y * ((cut A (g.x s) : ℤ) : ZMod N)) := by
  rw [QAlg.phase_eq_char]
  congr 1
  simp [GenAlg.sim]

theorem star_fourierGate_apply (v : S × ZMod N → ℂ) (s : S) (y : ZMod N) :
    (((star (fourierGate : Matrix.unitaryGroup (S × ZMod N) ℂ) :
      Matrix.unitaryGroup (S × ZMod N) ℂ) : Matrix (S × ZMod N) (S × ZMod N) ℂ).mulVec v) (s, y)
      = ∑ w, (star (fourier N)) y w * v (s, w) := by
  have h : ((star (fourierGate : Matrix.unitaryGroup (S × ZMod N) ℂ) :
      Matrix.unitaryGroup (S × ZMod N) ℂ) : Matrix (S × ZMod N) (S × ZMod N) ℂ)
      = (1 : Matrix S S ℂ) ⊗ₖ star (fourier N) := by
    change star ((1 : Matrix S S ℂ) ⊗ₖ fourier N) = _
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      Matrix.star_eq_conjTranspose]
  rw [h, kron_right_apply]

/-- One query block: two phase queries around the gates `F⁻¹ D F⁻¹`. -/
theorem GenAlg.query_block (g : GenAlg n T S) (A : Weights n) (hcut : ∀ s, 0 ≤ cut A (g.x s) ∧ cut A (g.x s) < N)
    (ψ : S → ℂ) (p : S × ZMod N) :
    (g.sim N).phase N A p * (((star fourierGate * g.valueGate N * star fourierGate :
        Matrix.unitaryGroup (S × ZMod N) ℂ) : Matrix (S × ZMod N) (S × ZMod N) ℂ).mulVec
        fun p' => (g.sim N).phase N A p' * (ψ p'.1 * rootInv N)) p
      = g.f p.1 (cut A (g.x p.1)) * ψ p.1 * rootInv N := by
  obtain ⟨s, y⟩ := p
  have hval : ∀ s', ((((cut A (g.x s') : ℤ) : ZMod N).val : ℕ) : ℤ) = cut A (g.x s') := by
    intro s'
    rw [ZMod.val_intCast]
    exact Int.emod_eq_of_lt (hcut s').1 (hcut s').2
  have h1 : ∀ (s' : S) (w : ZMod N), ((star fourierGate : Matrix.unitaryGroup (S × ZMod N) ℂ) :
      Matrix (S × ZMod N) (S × ZMod N) ℂ).mulVec
      (fun p' => (g.sim N).phase N A p' * (ψ p'.1 * rootInv N)) (s', w)
      = if w = ((cut A (g.x s') : ℤ) : ZMod N) then ψ s' else 0 := by
    intro s' w
    rw [star_fourierGate_apply]
    simp only [g.sim_phase]
    exact star_fourier_mulVec_char _ w (ψ s')
  have hmul : ((star fourierGate * g.valueGate N * star fourierGate :
      Matrix.unitaryGroup (S × ZMod N) ℂ) : Matrix (S × ZMod N) (S × ZMod N) ℂ)
      = ((star fourierGate : Matrix.unitaryGroup (S × ZMod N) ℂ) : Matrix (S × ZMod N) (S × ZMod N) ℂ)
        * ((g.valueGate N : Matrix.unitaryGroup (S × ZMod N) ℂ) : Matrix (S × ZMod N) (S × ZMod N) ℂ)
        * ((star fourierGate : Matrix.unitaryGroup (S × ZMod N) ℂ) : Matrix (S × ZMod N) (S × ZMod N) ℂ) := rfl
  rw [hmul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, star_fourierGate_apply]
  have h2 : ∀ w : ZMod N, ((g.valueGate N : Matrix.unitaryGroup (S × ZMod N) ℂ) :
      Matrix (S × ZMod N) (S × ZMod N) ℂ).mulVec (((star fourierGate :
        Matrix.unitaryGroup (S × ZMod N) ℂ) : Matrix (S × ZMod N) (S × ZMod N) ℂ).mulVec
        fun p' => (g.sim N).phase N A p' * (ψ p'.1 * rootInv N)) (s, w)
      = if w = ((cut A (g.x s) : ℤ) : ZMod N) then g.f s (cut A (g.x s)) * ψ s else 0 := by
    intro w
    have hd : ((g.valueGate N : Matrix.unitaryGroup (S × ZMod N) ℂ) :
        Matrix (S × ZMod N) (S × ZMod N) ℂ) = Matrix.diagonal fun p => g.f p.1 (p.2.val : ℤ) := rfl
    rw [hd, Matrix.mulVec_diagonal, h1]
    by_cases hw : w = ((cut A (g.x s) : ℤ) : ZMod N)
    · simp only [hw, ↓reduceIte, hval]
    · simp [hw]
  simp_rw [h2]
  rw [star_fourier_mulVec_delta, g.sim_phase]
  have h3 : ω (y * ((cut A (g.x s) : ℤ) : ZMod N)) * ω (-(y * ((cut A (g.x s) : ℤ) : ZMod N))) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  calc _ = (ω (y * ((cut A (g.x s) : ℤ) : ZMod N)) * ω (-(y * ((cut A (g.x s) : ℤ) : ZMod N))))
        * (g.f s (cut A (g.x s)) * ψ s * rootInv N) := by ring
    _ = _ := by rw [h3, one_mul]

/-- The invariant: after `2 t` queries the state is `ψ_t ⊗ u`, with `u` the uniform vector. -/
theorem GenAlg.sim_state (g : GenAlg n T S) (A : Weights n) (hcut : ∀ s, 0 ≤ cut A (g.x s) ∧ cut A (g.x s) < N) :
    ∀ (t : ℕ) (ht : t ≤ T), ∀ p, (g.sim N).state N A (2 * t) (by omega) p
      = g.state A t ht p.1 * rootInv N := by
  intro t
  induction t with
  | zero =>
    intro ht p
    obtain ⟨s, y⟩ := p
    have h0 : (g.sim N).state N A (2 * 0) (by omega)
        = ((g.sim N).U ⟨0, Nat.succ_pos _⟩ : Matrix (S × ZMod N) (S × ZMod N) ℂ).mulVec
            (Pi.single (g.sim N).init 1) := rfl
    have hU : ((g.sim N).U ⟨0, Nat.succ_pos _⟩ : Matrix (S × ZMod N) (S × ZMod N) ℂ)
        = ((liftGate (g.U ⟨0, Nat.succ_pos T⟩) : Matrix.unitaryGroup (S × ZMod N) ℂ) :
            Matrix (S × ZMod N) (S × ZMod N) ℂ)
          * ((fourierGate : Matrix.unitaryGroup (S × ZMod N) ℂ) : Matrix (S × ZMod N) (S × ZMod N) ℂ) := by
      simp only [GenAlg.sim, ↓reduceIte]
      rfl
    have hsimp : (g.sim N).init = (g.init, 0) := rfl
    rw [h0, hU, ← Matrix.mulVec_mulVec]
    have hF : ∀ (s' : S) (w : ZMod N),
        (((fourierGate : Matrix.unitaryGroup (S × ZMod N) ℂ) : Matrix (S × ZMod N) (S × ZMod N) ℂ).mulVec
          (Pi.single (g.init, (0 : ZMod N)) 1)) (s', w)
        = (Pi.single g.init (1 : ℂ) : S → ℂ) s' * rootInv N := by
      intro s' w
      change (((1 : Matrix S S ℂ) ⊗ₖ fourier N).mulVec _) (s', w) = _
      rw [kron_right_apply, Finset.sum_eq_single 0]
      · by_cases hs : s' = g.init
        · subst hs
          simp [fourier]
        · simp [hs]
      · intro w' _ hw'
        simp [hw']
      · intro h0
        exact absurd (mem_univ _) h0
    rw [hsimp]
    change ((g.U ⟨0, Nat.succ_pos T⟩ : Matrix S S ℂ) ⊗ₖ (1 : Matrix (ZMod N) (ZMod N) ℂ)).mulVec _ (s, y) = _
    rw [kron_left_apply]
    simp_rw [hF]
    have hst : g.state A 0 ht s
        = ∑ s', (g.U ⟨0, Nat.succ_pos T⟩ : Matrix S S ℂ) s s' * (Pi.single g.init (1 : ℂ) : S → ℂ) s' := rfl
    rw [hst, sum_mul]
    exact sum_congr rfl fun s' _ => by ring
  | succ t ih =>
    intro ht p
    obtain ⟨s, y⟩ := p
    have hst : (g.sim N).state N A (2 * (t + 1)) (by omega)
        = ((g.sim N).U ⟨2 * t + 2, by omega⟩ : Matrix (S × ZMod N) (S × ZMod N) ℂ).mulVec
          fun p' => (g.sim N).phase N A p' * ((g.sim N).U ⟨2 * t + 1, by omega⟩ :
            Matrix (S × ZMod N) (S × ZMod N) ℂ).mulVec
            (fun p'' => (g.sim N).phase N A p'' * (g.sim N).state N A (2 * t) (by omega) p'') p' := rfl
    have hU2 : ((g.sim N).U ⟨2 * t + 2, by omega⟩ : Matrix (S × ZMod N) (S × ZMod N) ℂ)
        = ((liftGate (g.U ⟨t + 1, by omega⟩) : Matrix.unitaryGroup (S × ZMod N) ℂ) :
            Matrix (S × ZMod N) (S × ZMod N) ℂ) := by
      have h1 : (2 * t + 2) ≠ 0 := by omega
      have h2 : ¬ ((2 * t + 2) % 2 = 1) := by omega
      have h3 : (⟨(2 * t + 2) / 2, by omega⟩ : Fin (T + 1)) = ⟨t + 1, by omega⟩ := by
        apply Fin.ext
        change (2 * t + 2) / 2 = t + 1
        omega
      simp only [GenAlg.sim, h1, h2, ↓reduceIte, h3]
    have hU1 : (g.sim N).U ⟨2 * t + 1, by omega⟩
        = star fourierGate * g.valueGate N * star fourierGate := by
      have h1 : (2 * t + 1) ≠ 0 := by omega
      have h2 : (2 * t + 1) % 2 = 1 := by omega
      simp only [GenAlg.sim, h1, h2, ↓reduceIte]
    have hih : (fun p'' => (g.sim N).phase N A p'' * (g.sim N).state N A (2 * t) (by omega) p'')
        = fun p'' => (g.sim N).phase N A p'' * (g.state A t (Nat.le_of_succ_le ht) p''.1 * rootInv N) := by
      funext p''
      rw [ih (Nat.le_of_succ_le ht) p'']
    rw [hst, hU2, hU1, hih]
    simp_rw [g.query_block A hcut]
    change ((g.U ⟨t + 1, by omega⟩ : Matrix S S ℂ) ⊗ₖ (1 : Matrix (ZMod N) (ZMod N) ℂ)).mulVec _ (s, y) = _
    rw [kron_left_apply]
    have hg : g.state A (t + 1) ht s = ∑ s', (g.U ⟨t + 1, Nat.succ_lt_succ ht⟩ : Matrix S S ℂ) s s'
        * (g.f s' (cut A (g.x s')) * g.state A t (Nat.le_of_succ_le ht) s') := rfl
    rw [hg, sum_mul]
    exact sum_congr rfl fun s' _ => by ring

/-- The simulation has the same error probabilities, on inputs whose cuts lie in `[0, N)`. -/
theorem GenAlg.errAt_sim (g : GenAlg n T S) (A : Weights n) (hcut : ∀ s, 0 ≤ cut A (g.x s) ∧ cut A (g.x s) < N)
    (d : ℤ) : (g.sim N).errAt N A d = g.errAt A d := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hnorm : Complex.normSq (rootInv N) = (N : ℝ)⁻¹ := by
    rw [rootInv, Complex.normSq_ofReal, ← mul_inv, Real.mul_self_sqrt (by positivity)]
  unfold QAlg.errAt GenAlg.errAt
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun s _ => ?_
  have hout : ∀ y : ZMod N, (g.sim N).out (s, y) = g.out s := fun _ => rfl
  simp only [hout]
  by_cases hs : g.out s = d
  · simp [hs]
  · simp only [hs, ↓reduceIte]
    have hT : ∀ y : ZMod N, (g.sim N).state N A (2 * T) le_rfl (s, y) = g.state A T le_rfl s * rootInv N :=
      fun y => g.sim_state A hcut T le_rfl (s, y)
    simp_rw [hT, map_mul, hnorm]
    rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
    field_simp

end Simulation

/-- Cuts of graphs in the class lie in `[0, n² W)`. -/
theorem cut_mem_of_inClass [NeZero n] {W : ℕ} (hW : 0 < W) {A : Weights n} (hA : InClass (W : ℤ) A)
    (x : Fin n → Bool) : 0 ≤ cut A x ∧ cut A x < ((n ^ 2 * W : ℕ) : ℤ) := by
  have hcross : ∀ e : Edge n, 0 ≤ crosses x e ∧ crosses x e ≤ 1 := by
    intro e
    unfold crosses
    split_ifs <;> simp
  constructor
  · exact sum_nonneg fun e _ => mul_nonneg (hA e).1 (hcross e).1
  · have hle : cut A x ≤ ∑ _e : Edge n, (W : ℤ) := sum_le_sum fun e _ => by
      have h1 := hA e
      have h2 := hcross e
      nlinarith
    have hcard : Fintype.card (Edge n) < n ^ 2 := by
      have hz := Fintype.card_subtype_lt (p := fun p : Fin n × Fin n => p.1 < p.2)
        (x := ((⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n), (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n)))
        (lt_irrefl _)
      rw [Fintype.card_prod, Fintype.card_fin] at hz
      rwa [sq]
    have hW' : (0 : ℤ) < W := by exact_mod_cast hW
    have hc' : ((Fintype.card (Edge n) : ℕ) : ℤ) < ((n ^ 2 : ℕ) : ℤ) := by exact_mod_cast hcard
    rw [sum_const, card_univ, nsmul_eq_mul] at hle
    push_cast at hc' ⊢
    nlinarith

/-- The quantum bound for queries with an arbitrary phase function of the cut value. -/
theorem quantum_bound_general (hA : AndApproxDegree) : ∃ (C : ℕ) (c : ℝ), 0 < c ∧
    ∀ (n : ℕ) [NeZero n] (T : ℕ) (S : Type) [Fintype S] [DecidableEq S] (g : GenAlg n T S),
    (∀ A : Weights n, InClass (quantumWeight n C : ℤ) A → g.errAt A (minDegree A) ≤ 1 / 3) →
    c * Real.sqrt n ≤ 2 * T + 1 := by
  obtain ⟨C, c, hc, hb⟩ := quantum_bound hA
  refine ⟨C, c, hc, ?_⟩
  intro n _ T S _ _ g herr
  have hW : 0 < quantumWeight n C := by
    unfold quantumWeight
    positivity
  have hN : NeZero (n ^ 2 * quantumWeight n C) := ⟨by
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    positivity⟩
  have h := hb n (2 * T) (S × ZMod (n ^ 2 * quantumWeight n C)) (g.sim (n ^ 2 * quantumWeight n C)) (by
    intro A hA'
    rw [g.errAt_sim A (fun s => cut_mem_of_inClass hW hA' (g.x s))]
    exact herr A hA')
  push_cast at h
  exact h

end CutQuery
