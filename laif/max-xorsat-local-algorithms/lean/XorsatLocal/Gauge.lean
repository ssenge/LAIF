import Mathlib

/-!
# Random gauge signs make clause signs uniform

Signs ±1 are written additively in `ZMod 2`. A clause k has vertex set `e k`, and the vertex signs
`τ` shift its sign by `∑ j ∈ e k, τ j`. If every clause k has a vertex `v k ∈ e k` that lies in no
earlier clause (an elimination order, as on a hypertree ordered by distance from the root), then
for any fixed signs `J` the shifted signs `J + gauge e τ` are uniform over all sign patterns when
`τ` is uniform: every target pattern is hit by the same number of `τ`.
-/

open Finset

namespace XorsatLocal

variable {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}

/-- The sign shift of each clause caused by the vertex signs `τ`. -/
def gauge (e : Fin m → Finset V) : (V → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) where
  toFun τ k := ∑ j ∈ e k, τ j
  map_add' τ σ := by ext k; simp [Finset.sum_add_distrib]
  map_smul' c τ := by ext k; simp [Finset.mul_sum]

/-- Vertex signs supported on the private vertices `v k`. -/
def lift (v : Fin m → V) : (Fin m → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) where
  toFun x j := ∑ k, if v k = j then x k else 0
  map_add' x y := by ext j; simp [← Finset.sum_add_distrib, ite_add_zero]
  map_smul' c x := by ext j; simp [Finset.mul_sum]

lemma gauge_lift_apply (e : Fin m → Finset V) (v : Fin m → V) (x : Fin m → ZMod 2) (l : Fin m) :
    gauge e (lift v x) l = ∑ k, if v k ∈ e l then x k else 0 := by
  show ∑ j ∈ e l, ∑ k, (if v k = j then x k else 0) = _
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_ite_eq (e l) (v k) (fun _ => x k)

lemma gauge_lift_injective (e : Fin m → Finset V) (v : Fin m → V)
    (hv : ∀ k, v k ∈ e k) (hord : ∀ k l, l < k → v k ∉ e l) :
    Function.Injective ((gauge e).comp (lift v)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  by_contra hne
  have hex : ∃ k, x k ≠ 0 := by
    by_contra h; push Not at h; exact hne (funext h)
  classical
  let k0 := Finset.min' (univ.filter fun k => x k ≠ 0) (by
    obtain ⟨k, hk⟩ := hex; exact ⟨k, by simp [hk]⟩)
  have hk0 : x k0 ≠ 0 := by
    have := Finset.min'_mem (univ.filter fun k => x k ≠ 0) (by
      obtain ⟨k, hk⟩ := hex; exact ⟨k, by simp [hk]⟩)
    simpa using this
  have hmin : ∀ k, k < k0 → x k = 0 := by
    intro k hk; by_contra h
    exact absurd (Finset.min'_le _ k (by simp [h])) (not_le.mpr hk)
  have h0 := congrFun hx k0
  simp only [LinearMap.coe_comp, Function.comp_apply, Pi.zero_apply] at h0
  rw [gauge_lift_apply, Finset.sum_eq_single k0] at h0
  · simp [hv k0] at h0; exact hk0 h0
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · simp [hmin k hlt]
    · simp [hord k k0 hgt]
  · simp

/-- Under an elimination order the sign shift reaches every sign pattern. -/
theorem gauge_surjective (e : Fin m → Finset V) (v : Fin m → V)
    (hv : ∀ k, v k ∈ e k) (hord : ∀ k l, l < k → v k ∉ e l) :
    Function.Surjective (gauge e) := by
  have hs : Function.Surjective ((gauge e).comp (lift v)) :=
    LinearMap.injective_iff_surjective.mp (gauge_lift_injective e v hv hord)
  intro y; obtain ⟨x, hx⟩ := hs y; exact ⟨lift v x, hx⟩

/-- For any fixed clause signs `J` and any target pattern `J'`, the number of vertex sign
patterns `τ` with `J + gauge e τ = J'` does not depend on `J` or `J'`. So with uniform `τ` the
shifted signs are uniform. -/
theorem gauge_uniform (e : Fin m → Finset V) (v : Fin m → V)
    (hv : ∀ k, v k ∈ e k) (hord : ∀ k l, l < k → v k ∉ e l) (J J' : Fin m → ZMod 2) :
    (univ.filter fun τ : V → ZMod 2 => J + gauge e τ = J').card =
      (univ.filter fun τ : V → ZMod 2 => gauge e τ = 0).card := by
  obtain ⟨τ0, h0⟩ := gauge_surjective e v hv hord (J' - J)
  refine Finset.card_bij (fun τ _ => τ - τ0) ?_ ?_ ?_
  · intro τ hτ; simp only [mem_filter, mem_univ, true_and] at hτ ⊢
    rw [map_sub, h0, ← hτ]; abel
  · intro a _ b _ h; simpa using h
  · intro σ hσ; refine ⟨σ + τ0, ?_, by simp⟩
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    rw [map_add, hσ, h0]; abel

end XorsatLocal
