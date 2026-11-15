import SsspFlow.GHatLevelRoots
import SsspFlow.RunKappa

/-!
# The region of an annulus in the network of a level

The corners of the component of an annulus of a level in the cut along its own corners reach no other
corner of the level. So walks from them are walks of the cut along all the corners of the level, and
the copies at the ends of the tokens at any two corners of the component are joined by E_R and E_C
edges. With `RData.annulus_eq`, the component of the E_R and E_C edges of the target of an annulus
holds exactly the copies of the corners of the annulus.

* `RotSystem.exists_walk_of_gcomp`: two darts of one component are joined by a walk.
* `RData.region_erc`: the copies at the corners of the component of an annulus of a level are joined
  by E_R and E_C edges.
* `RData.region_erc_mid`: in particular the copies at the corners `κ0(t)` and `κ1(t)` of the top
  annulus at an index strictly inside the ranges of an annulus are joined to its target.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

/-- **Two darts of one component are joined by a walk.** -/
theorem exists_walk_of_gcomp {E : Type*} [Fintype E] [DecidableEq E] {M : RotSystem E} {a b : E}
    (h : M.toHypermap.gcomp a b) : ∃ p, M.IsWalk (M.tail a) p (M.tail b) := by
  induction h with
  | refl => exact ⟨[], rfl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨p, hp⟩ := ih
    have hone : M.IsWalk (M.tail b) [b] (M.head b) := ⟨rfl, rfl⟩
    rcases hbc with h | h | h
    · refine ⟨p ++ [b], hp.append ?_⟩
      rw [← h]
      exact hone
    · refine ⟨p, ?_⟩
      rw [← h, toHypermap_node, M.tail_rot]
      exact hp
    · refine ⟨p ++ [b], hp.append ?_⟩
      rw [← h, toHypermap_face, M.tail_rot_symm]
      exact hone

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData)

section Level

variable {C : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞} {hR : N.toRot.dual.Planar}
  {hC : N.toRot.dual.Connected} {hg : ∀ x, g (N.toRot.dual.rev x) = g x}
  {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : C.Live g Γ₀} {j k : ℕ}
  (r : CutPath.Run hR hC hg Γ₀ L₀ j k) (ℓ : ℕ)

/-- A walk of the cut along the corners of an annulus from its corner `κ0(x_a)` is a walk of the cut
along the corners of the level. -/
theorem region_walk (hΓ : S.Γ = Γ₀ ∪ r.steps ℓ) {A : Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ'}
    (hA : A ∈ r.nodes ℓ) {z : N.G.Dart × Bool}
    (hz : (N.toRot.dual.double.split A.1).toHypermap.gcomp (A.2.κ0 A.2.xa) z) :
    ∃ p, S.dualSplit.IsWalk (S.dualSplit.tail (A.2.κ0 A.2.xa)) p (S.dualSplit.tail z) := by
  obtain ⟨p, hp⟩ := exists_walk_of_gcomp hz
  have hsub : A.1 ⊆ S.Γ := hΓ ▸ r.subset_level ℓ hA
  have hun : ∀ w ∈ S.Γ, w ∉ A.1 → ∀ q, ¬ (N.toRot.dual.double.split A.1).IsWalk
      ((N.toRot.dual.double.split A.1).tail (A.2.κ0 A.2.xa)) q ((N.toRot.dual.double.split A.1).tail w) :=
    fun w hw hwA q => r.unreach_level ℓ hA (hΓ ▸ hw) hwA le_rfl A.2.le_x q
  exact ⟨p, (N.toRot.dual.double.isWalk_split_split_iff hsub hun p ⟨[], rfl⟩ z).2 hp⟩

/-- **The region of an annulus is joined by E_R and E_C edges.** -/
theorem region_erc (hΓ : S.Γ = Γ₀ ∪ r.steps ℓ) {A : Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ'}
    (hA : A ∈ r.nodes ℓ) {z z' : N.G.Dart × Bool}
    (hz : (N.toRot.dual.double.split A.1).toHypermap.gcomp (A.2.κ0 A.2.xa) z)
    (hz' : (N.toRot.dual.double.split A.1).toHypermap.gcomp (A.2.κ0 A.2.xa) z') :
    Relation.ReflTransGen S.ERC (S.vcopy (S.endV z)) (S.vcopy (S.endV z')) := by
  have key : ∀ {y : N.G.Dart × Bool},
      (N.toRot.dual.double.split A.1).toHypermap.gcomp (A.2.κ0 A.2.xa) y →
      Relation.ReflTransGen S.ERC (S.vcopy (S.endV (A.2.κ0 A.2.xa))) (S.vcopy (S.endV y)) := by
    intro y hy
    obtain ⟨p, hp⟩ := S.region_walk r ℓ hΓ hA hy
    have ht : Relation.ReflTransGen S.TG (S.pieceAt (A.2.κ0 A.2.xa)) (S.pieceAt y) :=
      (S.tg_comp_iff _ _).2 ⟨p, by rw [S.vertexEquiv_pieceAt, S.vertexEquiv_pieceAt]; exact hp⟩
    rw [← S.pieceOf_endV, ← S.pieceOf_endV] at ht
    exact (S.erc_comp_iff ⟨_, S.endV_end _⟩ ⟨_, S.endV_end _⟩).2 ht
  exact (S.erc_symm (key hz)).trans (key hz')

/-- **The corners of the top annulus inside an annulus.** For an annulus of a level and indices `t`,
`t'` strictly inside its ranges, the copies at the corners `κ0(t)` and `κ1(t')` of the top annulus are
joined by E_R and E_C edges to the copy at the corner `κ1(t'')` of the annulus, for any `t''` in its
ranges. -/
theorem region_erc_mid (hΓ : S.Γ = Γ₀ ∪ r.steps ℓ) {A : Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ'}
    (hA : A ∈ r.nodes ℓ) {t t'' : ℕ} (h1 : A.2.ya ≤ t'') (h2 : t'' ≤ A.2.yb) (σ : Fin 2)
    (ht : if σ = 0 then A.2.xa < t ∧ t < A.2.xb else A.2.ya < t ∧ t < A.2.yb) :
    Relation.ReflTransGen S.ERC
      (S.vcopy (S.endV (if σ = 0 then L₀.κ0 t else L₀.κ1 t))) (S.vcopy (S.endV (A.2.κ1 t''))) := by
  obtain ⟨-, -, -, -, e0, e1⟩ := r.below_nodes ℓ A hA
  refine S.region_erc r ℓ hΓ hA ?_ (A.2.gcomp_κ1 h1 h2)
  split_ifs at ht ⊢ with hσ
  · rw [← e0 t ht.1 ht.2]
    exact A.2.gcomp_κ0 ht.1.le ht.2.le
  · rw [← e1 t ht.1 ht.2]
    exact A.2.gcomp_κ1 ht.1.le ht.2.le

end Level

end RData

end RotSystem

end SsspFlow
