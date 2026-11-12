import SsspFlow.Run

/-!
# Shortest walks are simple for positive costs

For costs at least `1` on every dart, a shortest walk of a live annulus visits no vertex twice and
reaches the vertex of `κ1(i)` only at its end, since dropping a loop makes it shorter. So the step of
`CutPath.Live.exists_step_sel` exists on every shortest walk, not only on a chosen one.

* `CutPath.Live.sum_add_length_le`: for costs at least `1`, a sublist costs at least the number of
  dropped entries less.
* `CutPath.Live.shortest_simple`: for costs at least `1`, a shortest walk is simple.
* `CutPath.Live.exists_step_of_shortest`: every shortest walk contains the step of its last vertex at a
  copy `p_x^0` and the first vertex at a copy `p_y^1` after it.
-/

set_option autoImplicit false

universe u

namespace SsspFlow

open FourColor SimpleGraph
open scoped ENNReal

namespace RotSystem

namespace CutPath

namespace Live

/-- For costs at least `1`, a sublist costs at least the number of dropped entries less. -/
theorem sum_add_length_le {α : Type*} {f : α → ℕ} (hf : ∀ a, 1 ≤ f a) {l₁ l₂ : List α}
    (h : l₁.Sublist l₂) : (l₁.map f).sum + l₂.length ≤ (l₂.map f).sum + l₁.length := by
  induction h with
  | slnil => simp
  | cons a _ ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := hf a
    omega
  | cons_cons a _ ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

variable {D : Type u} [Fintype D] [DecidableEq D] {R : RotSystem D} {C : R.CutPath} {g₀ : D → ℕ}
  {Γ : Finset (D × Bool)} (L : C.Live (Nat.cast ∘ g₀) Γ)

/-- **Shortest walks are simple.** For costs at least `1`, a shortest walk of a live annulus visits no
vertex twice and reaches the vertex of `κ1(i)` only at its end. -/
theorem shortest_simple (hg : ∀ d, 1 ≤ g₀ d) {i : ℕ} {p : List (D × Bool)} (hp : L.Shortest i p) :
    (p.map (R.double.split Γ).tail).Nodup ∧
      ∀ z ∈ p, (R.double.split Γ).tail z ≠ (R.double.split Γ).tail (L.κ1 i) := by
  obtain ⟨q, hq, hnd, hne, hsub⟩ := hp.1.exists_simple
  have h1 := hp.2.1 q hq
  rw [sum_cast_fst, sum_cast_fst] at h1
  have h1' : (p.map (g₀ ∘ Prod.fst)).sum ≤ (q.map (g₀ ∘ Prod.fst)).sum := by exact_mod_cast h1
  have h2 := sum_add_length_le (f := g₀ ∘ Prod.fst) (fun a => hg a.1) hsub
  obtain rfl := hsub.eq_of_length (le_antisymm hsub.length_le (by omega))
  exact ⟨hnd, hne⟩

/-- **The step of every shortest walk.** For costs at least `1`, a shortest walk of a live annulus from
the vertex of `κ0(i)` to the vertex of `κ1(i)` contains the step from its last vertex at a copy
`p_x^0` to the first vertex at a copy `p_y^1` after it. -/
theorem exists_step_of_shortest (hR : R.Planar) (hC : R.Connected) (hg : ∀ d, 1 ≤ g₀ d) {i : ℕ}
    (h1 : L.xa ≤ i) (h2 : i ≤ L.xb) (h3 : L.ya ≤ i) (h4 : i ≤ L.yb) {p : List (D × Bool)}
    (hp : L.Shortest i p) :
    ∃ S : L.Step, ∃ p₁ p₃, p = p₁ ++ (List.range S.n).map S.q ++ p₃ ∧
      (∀ z ∈ (List.range S.n).map S.q ++ p₃, ¬ C.atCopy Γ 0 ((R.double.split Γ).head z)) ∧
      ∀ z ∈ (List.range S.n).map S.q, ¬ C.atCopy Γ 1 ((R.double.split Γ).tail z) := by
  obtain ⟨hnd, hne⟩ := L.shortest_simple hg hp
  exact L.exists_step_sel hR hC h1 h2 h3 h4 hp.1 hnd hne hp.2.1 hp.2.2

end Live

end CutPath

end RotSystem

end SsspFlow
