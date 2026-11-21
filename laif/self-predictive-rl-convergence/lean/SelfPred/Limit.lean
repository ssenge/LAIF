import SelfPred.Flow

/-!
# Linear self-predictive learning: the limit

The dynamics is the gradient flow of `tr(Q²)/4` on the Stiefel manifold, a real-analytic function on a compact
real-analytic manifold, so by the Łojasiewicz gradient inequality every solution converges to a single critical
point. This enters as the named hypothesis `LojasiewiczLimit`. With it, `limit_of_flow` (Theorem 2) states that from
a nonsingular predictor the limit has a nonsingular predictor and a `T`-invariant span.
-/

open Matrix Filter Topology

namespace SelfPred

variable {n k : Type*} [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]

/-- Convergence of the flow to a critical point: the solution `Φ` converges as `t → ∞` to some `Φ∞` with
`V(Φ∞) = 0`. For the gradient flow of the real-analytic function `tr(Q²)/4` on the compact Stiefel manifold this is
the Łojasiewicz theorem (S. Łojasiewicz, Sur les trajectoires du gradient d'une fonction analytique, Seminari di
Geometria, Bologna, 1984). -/
def LojasiewiczLimit (T : Matrix n n ℝ) (Φ : ℝ → Matrix n k ℝ) : Prop :=
  ∃ Φinf : Matrix n k ℝ, Tendsto Φ atTop (𝓝 Φinf) ∧ vf T Φinf = 0

/-- **Theorem 2.** From a nonsingular `Q(s)`, the limit of the flow has a nonsingular predictor and a
`T`-invariant span: `T Φ∞ = Φ∞ Q∞`. -/
theorem limit_of_flow (hlin : LinearODEGlobal k) (host : OstrowskiCongruence k) {T : Matrix n n ℝ}
    (hT : Tᵀ = T) {Φ : ℝ → Matrix n k ℝ} (hΦ : IsFlow T Φ) (hloj : LojasiewiczLimit T Φ) {s : ℝ}
    (hs : (Φ s)ᵀ * Φ s = 1) (hdet : (Qm T (Φ s)).det ≠ 0) :
    ∃ Φinf : Matrix n k ℝ, Tendsto Φ atTop (𝓝 Φinf) ∧ (Qm T Φinf).det ≠ 0 ∧ T * Φinf = Φinf * Qm T Φinf := by
  obtain ⟨Φinf, hlim, hcrit⟩ := hloj
  exact ⟨Φinf, hlim, limit_invariant hlin host hT hΦ hs hdet hlim hcrit⟩

end SelfPred
