import SsspFlow.LabelHypothesis

/-!
# One oracle of the Exact SSSP bound

The Exact SSSP bound gives, for every bound `K` on the lengths, every number of nodes `n` and every
diameter `D`, an algorithm whose outputs meet the specification of the oracle. One fixed choice of
it is used by every algorithm built on the oracle, so two runs of it on the same network with the
same inputs give the same outputs, parents included.

* `ExactSsspBound.cC`, `ExactSsspBound.cc`: the constants of the bound.
* `ExactSsspBound.alg`, `ExactSsspBound.out`: the algorithm and its output.
* `ExactSsspBound.alg_spec`: its outputs meet the specification of the oracle.
* `ExactSsspBound.oracleRun`: its outputs on a network after `cC · log^cc n · D` rounds.
-/

set_option autoImplicit false

namespace SsspFlow

namespace Congest

open Cslib.Congest Cslib.Congest.Algorithm
open scoped ENNReal

namespace ExactSsspBound

variable (hE : ExactSsspBound) (K : ℕ)

/-- The constant factor of the rounds of the oracle. -/
noncomputable def cC : ℕ := (hE K).choose

/-- The exponent of the logarithm in the rounds of the oracle. -/
noncomputable def cc : ℕ := (hE K).choose_spec.choose

theorem spec_cc (n D : ℕ) (hD : 1 ≤ D) :
    ∃ (σ : Type) (A : Algorithm (Fin n) (OracleIn (Fin n)) σ (hE.cC K * logN n ^ hE.cc K))
      (out : Fin n → σ → ℕ∞ × Option (Fin n)),
      ∀ (N : Net (Fin n)) (ℓ : Fin n → Fin n → ℕ∞) (φ : Fin n → ℕ∞),
        N.toRot.Planar → N.DiamLE D → OracleValid N 0 ((n + 2) ^ K) ℓ φ →
        N.ExactSpec ℓ φ (fun v =>
          out v (A.run N.G (N.oracleIn ℓ φ) (hE.cC K * logN n ^ hE.cc K * D) v)) :=
  (hE K).choose_spec.choose_spec n D hD

/-- The states of the oracle. -/
noncomputable def st (n D : ℕ) (hD : 1 ≤ D) : Type := (hE.spec_cc K n D hD).choose

/-- The algorithm of the oracle. -/
noncomputable def alg (n D : ℕ) (hD : 1 ≤ D) :
    Algorithm (Fin n) (OracleIn (Fin n)) (hE.st K n D hD) (hE.cC K * logN n ^ hE.cc K) :=
  (hE.spec_cc K n D hD).choose_spec.choose

/-- The output of the oracle, read from a state. -/
noncomputable def out (n D : ℕ) (hD : 1 ≤ D) : Fin n → hE.st K n D hD → ℕ∞ × Option (Fin n) :=
  (hE.spec_cc K n D hD).choose_spec.choose_spec.choose

/-- The outputs of the oracle on a network of diameter at most `D`. -/
noncomputable def oracleRun {n : ℕ} (D : ℕ) (hD : 1 ≤ D) (N : Net (Fin n)) (ℓ : Fin n → Fin n → ℕ∞)
    (φ : Fin n → ℕ∞) : Fin n → ℕ∞ × Option (Fin n) :=
  fun v => hE.out K n D hD v ((hE.alg K n D hD).run N.G (N.oracleIn ℓ φ) (hE.cC K * logN n ^ hE.cc K * D) v)

/-- **The chosen oracle.** On a planar network of diameter at most `D` with valid lengths and offsets,
the outputs of the chosen algorithm meet the specification of the oracle. -/
theorem alg_spec (n D : ℕ) (hD : 1 ≤ D) (N : Net (Fin n)) (ℓ : Fin n → Fin n → ℕ∞) (φ : Fin n → ℕ∞)
    (hP : N.toRot.Planar) (hDi : N.DiamLE D) (hval : OracleValid N 0 ((n + 2) ^ K) ℓ φ) :
    N.ExactSpec ℓ φ (hE.oracleRun K D hD N ℓ φ) :=
  (hE.spec_cc K n D hD).choose_spec.choose_spec.choose_spec N ℓ φ hP hDi hval

end ExactSsspBound

end Congest

end SsspFlow
