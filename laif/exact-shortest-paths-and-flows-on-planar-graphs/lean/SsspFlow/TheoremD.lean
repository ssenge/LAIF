import SsspFlow.Run

/-!
# Theorem D: the least computed length is the minimum cut

`G` is the planar network and `C` a path of its dual map `G.dual` from a face at `s` to a face at
`t`, with end corners `cs` at `s` and `ct` at `t`. The recursion runs with the lengths
`w = K c + 1` of the capacities `c`, which are positive, as the recursion needs on the path.

* `cutVal`, `cutVals`: the capacity of the cut of a vertex set, and the capacities of the
  `st`-cuts. `exists_isLeast_cutVals`: a minimum `st`-cut exists for `s ≠ t`.
* `isLeast_scale`: for `K` larger than the number of darts, a minimum cut for `K c + 1` divided by
  `K` is a minimum cut for `c`.
* `CutDuality`: the classical duality of planar minimum cuts and shortest paths in the cut along a
  shortest dual path, taken as a hypothesis.
* `theoremD_correct`: given the duality, every run of the recursion computes as its least length a
  value whose quotient by `K` is the minimum `st`-cut for `c`.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor
open scoped ENNReal

noncomputable section

namespace RotSystem

variable {E : Type*} [Fintype E] [DecidableEq E] (G : RotSystem E)

open Classical in
/-- The darts from a vertex set `S` to its complement. Each edge across the cut has exactly one
of them. -/
def cutDarts (S : Set G.Vertex) : Finset E :=
  Finset.univ.filter fun x => G.tail x ∈ S ∧ G.head x ∉ S

/-- The capacity of the cut of `S` for the lengths `w`. -/
def cutVal (w : E → ℕ) (S : Set G.Vertex) : ℕ := ∑ x ∈ G.cutDarts S, w x

/-- The capacities of the `st`-cuts. -/
def cutVals (w : E → ℕ) (s t : G.Vertex) : Set ℕ :=
  {v | ∃ S : Set G.Vertex, s ∈ S ∧ t ∉ S ∧ G.cutVal w S = v}

/-- A minimum `st`-cut exists when `s ≠ t`. -/
theorem exists_isLeast_cutVals (w : E → ℕ) {s t : G.Vertex} (h : s ≠ t) :
    ∃ v, IsLeast (G.cutVals w s t) v := by
  have hne : (G.cutVals w s t).Nonempty :=
    ⟨_, {s}, rfl, fun ht => h (Set.mem_singleton_iff.1 ht).symm, rfl⟩
  exact ⟨_, Nat.sInf_mem hne, fun _ hv => Nat.sInf_le hv⟩

theorem cutVal_scale (K : ℕ) (c : E → ℕ) (S : Set G.Vertex) :
    G.cutVal (fun x => K * c x + 1) S = K * G.cutVal c S + (G.cutDarts S).card := by
  unfold cutVal
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.card_eq_sum_ones]

/-- **Scaling.** If `K` exceeds the number of darts, a minimum `st`-cut `v` for the lengths
`K c + 1` gives the minimum `st`-cut `v / K` for `c`. -/
theorem isLeast_scale (c : E → ℕ) {K : ℕ} (hK : Fintype.card E < K) {s t : G.Vertex} {v : ℕ}
    (h : IsLeast (G.cutVals (fun x => K * c x + 1) s t) v) : IsLeast (G.cutVals c s t) (v / K) := by
  obtain ⟨⟨S₀, hs₀, ht₀, rfl⟩, hmin⟩ := h
  have hn : ∀ S, (G.cutDarts S).card < K := fun S => (Finset.card_le_univ _).trans_lt hK
  have hK0 : 0 < K := (Nat.zero_le _).trans_lt hK
  rw [cutVal_scale, Nat.mul_add_div hK0, Nat.div_eq_of_lt (hn S₀), add_zero]
  refine ⟨⟨S₀, hs₀, ht₀, rfl⟩, ?_⟩
  rintro _ ⟨S, hs, ht, rfl⟩
  by_contra hlt
  have hle := hmin ⟨S, hs, ht, rfl⟩
  rw [cutVal_scale, cutVal_scale] at hle
  have h2 : K * (G.cutVal c S + 1) ≤ K * G.cutVal c S₀ := Nat.mul_le_mul_left K (by omega)
  have h3 := hn S
  rw [mul_add, mul_one] at h2
  omega

variable {G}

variable (E) in
/-- **Cut duality along a shortest dual path** ([21], [22] of the README):
let the dual map of `H` be planar and connected, the lengths `w ≥ 0` agree on the two darts of an
edge, and `C` be a shortest path of the dual map from a face at `s` to a face at `t`, with end
corners `cs` at `s` and `ct` at `t`. Then the minimum `st`-cut is the least distance `λ_t` in the
cut along the path between the two copies of a vertex `p_t` of the path. -/
def CutDuality : Prop :=
  ∀ (H : RotSystem E), H.dual.Planar → H.dual.Connected → ∀ (C : H.dual.CutPath) (w : E → ℕ),
    (∀ x, w (H.rev x) = w x) →
    (∀ q, H.dual.IsWalk (C.v 0) q (C.v C.m) → C.pos w C.m ≤ (q.map w).sum) →
    ∀ v, IsLeast (H.cutVals w (H.tail C.cs) (H.tail C.ct)) v →
      ∃ t ≤ C.m, C.lamD (Nat.cast ∘ w) t = v ∧ ∀ q ≤ C.m, (v : ℝ≥0∞) ≤ C.lamD (Nat.cast ∘ w) q

/-- The two end corners of a cut path lie at different vertices of the network. -/
theorem CutPath.tail_cs_ne (C : G.dual.CutPath) : G.tail C.cs ≠ G.tail C.ct := by
  intro h
  apply C.faces
  rw [← G.dual_faceOf_eq_iff, faceOf_eq_iff] at h
  exact (fconnect_congr G.dual.facePerm_apply).2 h

variable (hR : G.dual.Planar) (hC : G.dual.Connected) (C : G.dual.CutPath) (c : E → ℕ) {K : ℕ}
  (hgc : ∀ x, (Nat.cast ∘ (fun x => K * c x + 1) : E → ℝ≥0∞) (G.dual.rev x) =
    (Nat.cast ∘ (fun x => K * c x + 1) : E → ℝ≥0∞) x)

include hgc in
/-- **Theorem D, correctness.** Let the dual map be planar and connected, the capacities `c` agree
on the two darts of an edge, `K` exceed the number of darts, and the path `C` be shortest for the
lengths `K c + 1`. Given the cut duality, a run of the recursion on the cut
exists, and for every run the least computed length `v` gives the minimum `st`-cut `v / K` for `c`. -/
theorem theoremD_correct (hc : ∀ x, c (G.rev x) = c x) (hK : Fintype.card E < K)
    (hP : ∀ q, G.dual.IsWalk (C.v 0) q (C.v C.m) →
      C.pos (fun x => K * c x + 1) C.m ≤ (q.map fun x => K * c x + 1).sum)
    (hD : CutDuality E) :
    Nonempty (CutPath.Run hR hC hgc C.Γ (C.liveOne (Nat.cast ∘ fun x => K * c x + 1)) 0 C.m) ∧
      ∀ r : CutPath.Run hR hC hgc C.Γ (C.liveOne (Nat.cast ∘ fun x => K * c x + 1)) 0 C.m,
        ∃ v : ℕ, IsLeast (Prod.snd '' r.vals) (v : ℝ≥0∞) ∧
          IsLeast (G.cutVals c (G.tail C.cs) (G.tail C.ct)) (v / K) := by
  have hg₀ : ∀ x, K * c (G.dual.rev x) + 1 = K * c x + 1 := fun x => by
    rw [dual_rev, hc]
  have hpos : ∀ t, t < C.m → 1 ≤ K * c (C.e t) + 1 := fun _ _ => Nat.le_add_left 1 _
  obtain ⟨hne, hrun⟩ := CutPath.recursion_cut (C := C) hR hC hgc hg₀ hpos hP
  refine ⟨hne, fun r => ?_⟩
  obtain ⟨v, hv⟩ := G.exists_isLeast_cutVals (fun x => K * c x + 1) C.tail_cs_ne
  obtain ⟨t₁, ht₁m, ht₁, hall⟩ := hD G hR hC C _ (fun x => by rw [hc]) hP v hv
  obtain ⟨-, t, ht, hmin, hleast⟩ := hrun r
  have heq : C.lamD (Nat.cast ∘ fun x => K * c x + 1) t = v :=
    le_antisymm ((hmin t₁ ht₁m).trans ht₁.le) (hall t ht)
  exact ⟨v, heq ▸ hleast, G.isLeast_scale c hK hv⟩

end RotSystem

end

end SsspFlow
