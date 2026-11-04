import Monge.TotallyMonotone
import Monge.Factorization
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The quantum model and the quantum facts taken as hypotheses

Bounded-error quantum query complexity `Q` over a finite alphabet, the general adversary bound
`Adv±`, and three named hypotheses: the two theorems of arXiv:1011.3020
and maximum finding. These three are not proved. They are `Prop`s passed
as arguments, and `Axioms.lean` confirms no axiom is added. The two theorems at the end only chain
them together.

Only the three hypotheses connect `Q` and `Adv±` to the rest, so the proofs never unfold their
definitions. The definitions are here so that the hypotheses are statements about the real objects.
The vectors in `Monge.Factorization` are real. Complex vectors give the same `γ` on a real target,
by taking real parts of the inner products and doubling the dimension.
-/

open scoped Matrix.Norms.L2Operator

namespace Monge

/-! ## Quantum query algorithms -/

/-- Basis states: a query index, an answer register, and a workspace. -/
abbrev QBasis (J : Type) (k w : ℕ) := J × Fin k × Fin w

/-- A `T`-query algorithm with a workspace of size `w`. The unitaries do not depend on the input. -/
structure QAlg (J : Type) [Fintype J] [DecidableEq J] (k w T : ℕ) (E : Type) where
  U : Fin (T + 1) → Matrix.unitaryGroup (QBasis J k w) ℂ
  init : QBasis J k w
  out : QBasis J k w → E

variable {J : Type} [Fintype J] [DecidableEq J] {k w T : ℕ} {E : Type}

/-- The query `|j, b, z⟩ ↦ |j, b + x_j, z⟩` as a permutation matrix, with addition in `Fin k`. -/
def queryMatrix (x : J → Fin k) : Matrix (QBasis J k w) (QBasis J k w) ℂ :=
  Matrix.of fun s' s => if s' = (s.1, s.2.1 + x s.1, s.2.2) then 1 else 0

/-- The amplitudes after `U_t O_x U_{t-1} ⋯ O_x U_0` on the initial basis state. -/
noncomputable def QAlg.state (A : QAlg J k w T E) (x : J → Fin k) :
    (t : ℕ) → t ≤ T → QBasis J k w → ℂ
  | 0, _ => (A.U ⟨0, Nat.succ_pos T⟩ : Matrix _ _ ℂ).mulVec (Pi.single A.init 1)
  | t + 1, h => (A.U ⟨t + 1, Nat.succ_lt_succ h⟩ : Matrix _ _ ℂ).mulVec
      ((queryMatrix x).mulVec (A.state x t (Nat.le_of_succ_le h)))

/-- The probability that the final measurement reports a value other than `e`. -/
noncomputable def QAlg.errAt [DecidableEq E] (A : QAlg J k w T E) (x : J → Fin k) (e : E) : ℝ :=
  ∑ s, if A.out s = e then 0 else Complex.normSq (A.state x T le_rfl s)

/-- `A` computes `f` on `D` with error at most `1/3`. -/
def QAlg.Computes [DecidableEq E] (A : QAlg J k w T E) (D : Set (J → Fin k))
    (f : (J → Fin k) → E) : Prop :=
  ∀ x ∈ D, A.errAt x (f x) ≤ 1 / 3

/-- Bounded-error quantum query complexity of `f` on `D`. -/
noncomputable def queryQ [DecidableEq E] (D : Set (J → Fin k)) (f : (J → Fin k) → E) : ℕ :=
  sInf {T | ∃ (w : ℕ) (A : QAlg J k w T E), A.Computes D f}

/-! ## The general adversary bound -/

open scoped Classical in
/-- `Γ ∘ Δ_j`. -/
noncomputable def adversaryMask (D : Set (J → Fin k)) (Γ : Matrix D D ℝ) (j : J) : Matrix D D ℝ :=
  Matrix.of fun x y => Γ x y * delta j x.1 y.1

/-- An adversary matrix for `f`: real symmetric, with zeros on pairs with equal values. Hermitian
matrices give the same value here, since the target is real and the bound is linear in `Γ` in its
dual form. -/
def IsAdversary (D : Set (J → Fin k)) (f : (J → Fin k) → E) (Γ : Matrix D D ℝ) : Prop :=
  Γ.IsSymm ∧ ∀ x y : D, f x.1 = f y.1 → Γ x y = 0

open scoped Classical in
/-- `Adv±(f) = max_Γ ‖Γ‖ / max_j ‖Γ ∘ Δ_j‖`, with the spectral norm. -/
noncomputable def advPM (D : Set (J → Fin k)) (f : (J → Fin k) → E) : ℝ :=
  sSup {ρ | ∃ Γ : Matrix D D ℝ, IsAdversary D f Γ ∧
    ρ = ‖Γ‖ / ⨆ j, ‖adversaryMask D Γ j‖}

/-! ## The hypotheses -/

/-- **arXiv:1011.3020, Theorem 1.1.** `Q(f) = Θ(Adv±(f))`, with a constant `C` that is universal over
index sets, alphabets, domains and functions. -/
def LeeQueryAdv (C : ℝ) : Prop :=
  ∀ (J : Type) [Fintype J] [DecidableEq J] (k : ℕ) (E : Type) [Fintype E] [DecidableEq E]
    (D : Set (J → Fin k)) (f : (J → Fin k) → E),
    (queryQ D f : ℝ) ≤ C * advPM D f ∧ advPM D f ≤ C * (queryQ D f : ℝ)

/-- **arXiv:1011.3020, Theorem 3.4.** `Adv±(f) ≤ γ(f) ≤ 2 Adv±(f)`, where `γ` is the filtered `γ₂` with
constraints on all pairs. -/
def LeeAdvGamma : Prop :=
  ∀ (J : Type) [Fintype J] [DecidableEq J] (k : ℕ) (E : Type) [Fintype E] [DecidableEq E]
    (D : Set (J → Fin k)) (f : (J → Fin k) → E),
    advPM D f ≤ gam D f ∧ gam D f ≤ 2 * advPM D f

/-- **Maximum finding**, on the pairs (value, minus index) so that it returns the
leftmost maximum: for `c` positions `w` of the input, the leftmost maximum costs at most `κ √c`
queries, with `κ` universal. The bound does not depend on the alphabet. -/
def DurrHoyer (κ : ℝ) : Prop :=
  ∀ (J : Type) [Fintype J] [DecidableEq J] (k c : ℕ) [NeZero c] (D : Set (J → Fin k))
    (w : Fin c → J),
    (queryQ D (fun x => leftmost fun a => x (w a)) : ℝ) ≤ κ * √(c : ℝ)

/-- From the three hypotheses: `γ` of a window maximum is `O(√c)`. -/
theorem gam_leftmost_le {C κ : ℝ} (hC : 0 ≤ C) (hLQ : LeeQueryAdv C) (hLG : LeeAdvGamma)
    (hDH : DurrHoyer κ) {J : Type} [Fintype J] [DecidableEq J] {k c : ℕ} [NeZero c]
    (D : Set (J → Fin k)) (w : Fin c → J) :
    gam D (fun x => leftmost fun a => x (w a)) ≤ (2 * C * κ) * √(c : ℝ) := by
  have h1 := (hLG J k (Fin c) D (fun x => leftmost fun a => x (w a))).2
  have h2 := (hLQ J k (Fin c) D (fun x => leftmost fun a => x (w a))).2
  have h3 := hDH J k c D w
  have h4 := mul_le_mul_of_nonneg_left h3 hC
  calc gam D (fun x => leftmost fun a => x (w a))
      ≤ 2 * advPM D (fun x => leftmost fun a => x (w a)) := h1
    _ ≤ 2 * (C * (queryQ D (fun x => leftmost fun a => x (w a)) : ℝ)) := by linarith
    _ ≤ 2 * (C * (κ * √(c : ℝ))) := by linarith
    _ = (2 * C * κ) * √(c : ℝ) := by ring

/-- From the hypotheses: `Q(f) = O(γ(f))`. -/
theorem queryQ_le_gam {C : ℝ} (hC : 0 ≤ C) (hLQ : LeeQueryAdv C) (hLG : LeeAdvGamma)
    {J : Type} [Fintype J] [DecidableEq J] {k : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (D : Set (J → Fin k)) (f : (J → Fin k) → E) :
    (queryQ D f : ℝ) ≤ C * gam D f :=
  (hLQ J k E D f).1.trans (mul_le_mul_of_nonneg_left (hLG J k E D f).1 hC)

end Monge
