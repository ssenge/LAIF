import SsspFlow.GHatLevelRoots
import SsspFlow.GHatChainOut

/-!
# The chains of the targets of a level do not meet

Every node of the parent chain of a target of distance below `M` has its copy in the component of
`Ĝ_ℓ[E_R ∪ E_C]` of the target. So if the targets of a level lie in different components, their
chains do not meet. For the targets of a list of annuli of a level of a run, one per annulus, this
is the condition on the targets of `RData.chain_step_out`.

* `RData.chains_eq_of_meet`: targets of distance below `M` whose copies are joined by E_R and E_C
  edges only when they are equal have chains that do not meet.
* `RData.tgtFlag_chains`: the chains of the targets of a list of annuli of a level of a run, each
  with one index and `λ_t < M`, do not meet.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)

/-- **Chains of targets in different components do not meet.** For an output of the oracle on the
network of a level, let every two targets be copy nodes of distance below `M` whose copies are joined
by E_R and E_C edges only when they are equal. Then two targets whose chains meet are equal. -/
theorem chains_eq_of_meet (lam : S.Tok → ℕ) (M : ℕ) (ψ : Fin (n * (n * 21)) → ℕ∞)
    (r : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (hr : (S.levelNet hN).ExactSpec (S.levelLen hN lam M) ψ r) (isT : Fin (n * (n * 21)) → Bool)
    (hU : ∀ t t', isT t = true → isT t' = true → ∃ w w' : S.hRot.Vertex,
      t = (S.levelPad hN).ι (.inl w) ∧ t' = (S.levelPad hN).ι (.inl w') ∧
      ((r t).1 : ℝ≥0∞) < M ∧ ((r t').1 : ℝ≥0∞) < M ∧
      (Relation.ReflTransGen S.ERC (S.vcopy w) (S.vcopy w') → w = w')) :
    ∀ t t' i i', isT t = true → isT t' = true → Net.ParSteps r t i → Net.ParSteps r t' i' →
      (Net.parOf r)^[i] t = (Net.parOf r)^[i'] t' → t = t' := by
  intro t t' i i' ht ht' _ _ he
  obtain ⟨w, w', rfl, rfl, hw, hw', hu⟩ := hU t t' ht ht'
  have h1 := (S.chain_erc hN lam M ψ r hr hw ⟨i, rfl⟩).1
  have h2 := (S.chain_erc hN lam M ψ r hr hw' ⟨i', he.symm⟩).1
  rw [hu (Relation.ReflTransGen.trans (S.erc_symm h1) h2)]

variable {C : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞} {hR : N.toRot.dual.Planar}
  {hC : N.toRot.dual.Connected} {hg : ∀ x, g (N.toRot.dual.rev x) = g x}
  {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : C.Live g Γ₀} {j k : ℕ}
  (r : CutPath.Run hR hC hg Γ₀ L₀ j k) (ℓ : ℕ)

/-- **The chains of the targets of a level do not meet.** For an output of the oracle on the
network of a level from the sources of a list `Q` of annuli of a level of a run, each with one index
and `λ_t < M`, two targets of `Q` whose chains meet are equal. -/
theorem tgtFlag_chains (lam : S.Tok → ℕ) (M : ℕ) (c : N.G.Dart → ℕ)
    (hcr : ∀ d, c (N.toRot.rev d) = c d) (hlam : ∀ x, lam x = c x.1.1) (hgc : ∀ d, g d = c d)
    (hΓ : S.Γ = Γ₀ ∪ r.steps ℓ) (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ))
    (hQ : ∀ q ∈ Q, q.1 ∈ r.nodes ℓ ∧ q.1.2.xa ≤ q.2 ∧ q.1.2.ya ≤ q.2 ∧ q.2 ≤ q.1.2.xb ∧
      q.2 ≤ q.1.2.yb ∧ C.lamD g q.2 < M)
    (hQu : ∀ q ∈ Q, ∀ q' ∈ Q, q.1 = q'.1 → q.2 = q'.2)
    (R : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (hr : (S.levelNet hN).ExactSpec (S.levelLen hN lam M) (S.srcOff hN Q) R) :
    ∀ t t' i i', S.tgtFlag hN Q t = true → S.tgtFlag hN Q t' = true → Net.ParSteps R t i →
      Net.ParSteps R t' i' → (Net.parOf R)^[i] t = (Net.parOf R)^[i'] t' → t = t' := by
  classical
  have upper := S.tgt_dist_le hN r ℓ lam M c hcr hlam hgc hΓ Q hQ R hr
  have mem : ∀ t, S.tgtFlag hN Q t = true →
      ∃ q ∈ Q, t = (S.levelPad hN).ι (.inl (S.endV (q.1.2.κ1 q.2))) := fun t ht => by
    simpa [tgtFlag] using ht
  refine S.chains_eq_of_meet hN lam M _ R hr _ fun t t' ht ht' => ?_
  obtain ⟨q, hq, rfl⟩ := mem t ht
  obtain ⟨q', hq', rfl⟩ := mem t' ht'
  obtain ⟨-, -, k2, -, k4, hM⟩ := hQ q hq
  obtain ⟨-, -, -, -, -, hM'⟩ := hQ q' hq'
  refine ⟨_, _, rfl, rfl, (upper q hq).trans_lt hM, (upper q' hq').trans_lt hM', fun he => ?_⟩
  rw [S.tgt_same r ℓ M hΓ Q hQ hQu q hq q' hq' _ (q.1.2.gcomp_κ1 k2 k4) he]

end RData

end RotSystem

end SsspFlow
