import SsspFlow.GHatChainVisits
import SsspFlow.SideCorners
import SsspFlow.OracleChainCount

/-!
# The corners of the sides on the chain of a target

A node of the network of a level is flagged for a choice `P` of corners of the annuli of a list `Q`
when the piece of its copy is the vertex of such a corner of an annulus of `Q`. The flags are local:
they depend on the copy of the node only. On the chain of the target of an annulus of `Q` they detect
exactly the corners of that annulus, since a walk of an annulus of a level visits no corner of the
sides of another annulus of the same level.

* `Net.ExactSpec.chain_any`: a flag on a chain, read at its root after a counting run.
* `RData.cornerFlag`: the flag of a node for a choice of corners.
* `RData.chain_corner`: the walk of the chain of a target visits a chosen corner of its annulus
  exactly when a node of the chain is flagged.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace Congest

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **A flag on a chain, read at its root.** For targets whose valid chains do not meet, let a chain of
`k` valid steps from a target end at a root. After a counting run with the indicator of a flag `f` as
lengths on the arcs to the parents, some node of the chain is flagged exactly when the count at the
root is not `0` or the root is flagged. -/
theorem Net.ExactSpec.chain_any {N : Net V} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞} {r : V → ℕ∞ × Option V}
    (h : N.ExactSpec ℓ φ r) (f isT : V → Bool) {r₂ : V → ℕ∞ × Option V}
    (h₂ : N.ExactSpec (Net.markLenW r fun a => ((f a).toNat : ℕ∞)) (Net.markOffB isT) r₂)
    (hT : ∀ t t' i i', isT t = true → isT t' = true → Net.ParSteps r t i → Net.ParSteps r t' i' →
      (Net.parOf r)^[i] t = (Net.parOf r)^[i'] t' → t = t')
    {t : V} {k : ℕ} (ht : isT t = true) (hs : Net.ParSteps r t k)
    (hnone : (r ((Net.parOf r)^[k] t)).2 = none) :
    (∃ y, (∃ i, (Net.parOf r)^[i] t = y) ∧ f y = true) ↔
      (r₂ ((Net.parOf r)^[k] t)).1 ≠ 0 ∨ f ((Net.parOf r)^[k] t) = true := by
  classical
  have e : (Net.markLenW r fun a => ((f a).toNat : ℕ∞)) =
      Net.markLenW r fun a => if f a = true then 1 else 0 := by
    congr 1
    funext a
    cases f a <;> simp
  rw [e] at h₂
  have key : (r₂ ((Net.parOf r)^[k] t)).1 = 0 ↔ ∀ i < k, ¬ f ((Net.parOf r)^[i] t) = true := by
    rw [← ENat.toENNReal_eq_zero, h₂.dist_eq]
    convert h.dsrcTop_flag_eq_zero (fun a => f a = true) isT hT ht hs
  have hfx : Net.parOf r ((Net.parOf r)^[k] t) = (Net.parOf r)^[k] t := by
    simp [Net.parOf, hnone]
  rw [Ne, key]
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, hy⟩
    by_cases hi : i < k
    · exact .inl fun hall => hall i hi hy
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hi)
      rw [Nat.add_comm, Function.iterate_add_apply, Function.iterate_fixed hfx] at hy
      exact .inr hy
  · rintro (hn | hn)
    · push_neg at hn
      obtain ⟨i, -, hi⟩ := hn
      exact ⟨_, ⟨i, rfl⟩, hi⟩
    · exact ⟨_, ⟨k, rfl⟩, hn⟩

end Congest

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)

variable {C : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞}

/-- A node of the network of a level is flagged for a choice `P` of corners of the annuli of `Q` when
the piece of its copy is the vertex of a chosen corner of an annulus of `Q`. -/
def cornerFlag (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ))
    (P : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') → N.G.Dart × Bool → Prop)
    (a : Fin (n * (n * 21))) : Prop :=
  ∃ q ∈ Q, ∃ c, P q.1 c ∧ ∃ hy : (∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN a)),
    S.vertexEquiv (S.pieceOf ⟨S.copyAt hN a, hy⟩) = S.dualSplit.tail c

variable {hR : N.toRot.dual.Planar} {hC : N.toRot.dual.Connected} {hg : ∀ x, g (N.toRot.dual.rev x) = g x}
  {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : C.Live g Γ₀} {j k : ℕ}

/-- **The chosen corners on the chain of a target.** Let `Q` list annuli of a level `ℓ` of a run with
one index `t` each in their ranges, and let `P` choose corners of the sides. For an annulus of `Q`
with a walk `p` from `κ0(t)` that visits a corner exactly when the piece of the copy of a node of the
chain of `v` is its vertex, the walk visits a chosen corner of the annulus exactly when a node of the
chain is flagged for `P`. -/
theorem chain_corner (r : CutPath.Run hR hC hg Γ₀ L₀ j k) (ℓ : ℕ)
    (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ))
    (hQ : ∀ q ∈ Q, q.1 ∈ r.nodes ℓ ∧ q.1.2.xa ≤ q.2 ∧ q.1.2.ya ≤ q.2 ∧ q.2 ≤ q.1.2.xb ∧ q.2 ≤ q.1.2.yb)
    (P : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') → N.G.Dart × Bool → Prop)
    (hP : ∀ A c, P A c → A.2.CornerA c ∨ A.2.CornerB c)
    {At : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ} (hAt : At ∈ Q) {p : List (N.G.Dart × Bool)}
    {b : (N.toRot.dual.double.split At.1.1).Vertex}
    (hp : (N.toRot.dual.double.split At.1.1).IsWalk
      ((N.toRot.dual.double.split At.1.1).tail (At.1.2.κ0 At.2)) p b)
    (R : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21)))) (v : Fin (n * (n * 21)))
    (hvc : ∀ c, At.1.2.Visits At.2 p c ↔ ∃ y, (∃ i, (Net.parOf R)^[i] v = y) ∧
      ∃ hy : (∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN y)),
        S.vertexEquiv (S.pieceOf ⟨S.copyAt hN y, hy⟩) = S.dualSplit.tail c) :
    (∃ c, P At.1 c ∧ At.1.2.Visits At.2 p c) ↔
      ∃ y, (∃ i, (Net.parOf R)^[i] v = y) ∧ S.cornerFlag hN Q P y := by
  constructor
  · rintro ⟨c, hc, hv⟩
    obtain ⟨y, hy, hcy, he⟩ := (hvc c).1 hv
    exact ⟨y, hy, At, hAt, c, hc, hcy, he⟩
  · rintro ⟨y, hy, q, hq, c, hc, hcy, he⟩
    have hv := (hvc c).2 ⟨y, hy, hcy, he⟩
    have e := r.corner_eq ℓ (hQ At hAt).1 (hQ q hq).1 (hQ At hAt).2.1 (hQ At hAt).2.2.2.1 hp hv
      (hP _ _ hc)
    exact ⟨c, e ▸ hc, hv⟩

end RData

end RotSystem

end SsspFlow
