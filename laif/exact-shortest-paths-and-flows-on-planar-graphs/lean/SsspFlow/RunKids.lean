import SsspFlow.RunPick
import SsspFlow.SideCorners

/-!
# The ranges of the subruns of the next level

A node with a walk `q` at the middle index of `[j, k]`, least and greatest index `i1`, `i2` of the cut
path on `q`, calls the side of `κ0(x_a)` on `[j, i1]` unless the walk visits a corner of that side or
the range is empty, and the side of `κ0(x_b)` on `[i2, k]` likewise. So the ranges of the subruns of
the next level of the runs of the levels are given by the walks, indices and corners of the nodes of
the level above.

* `CutPath.Live.kids`: the ranges of the two sides of a node.
* `CutPath.Live.pickNode_kids`: the ranges of the subruns below a node with given data.
* `CutPath.pickF_kids`, `CutPath.pickF_kids_leaf`: the same after the picking graft.
* `CutPath.Run.seq_kids`: the ranges at the next depth of the runs of the levels.
-/

set_option autoImplicit false

universe u

namespace SsspFlow

open FourColor
open scoped ENNReal

namespace RotSystem

variable {D : Type u} [Fintype D] [DecidableEq D] {R : RotSystem D}

namespace CutPath

open Classical in
/-- The ranges of the two sides of a node with walk `q` and indices `i1`, `i2` on the range `[j, k]`. -/
noncomputable def Live.kids {g : D → ℝ≥0∞} {C : R.CutPath} {Γ : Finset (D × Bool)} (L : C.Live g Γ)
    (j k : ℕ) (q : List (D × Bool)) (i1 i2 : ℕ) : List (ℕ × ℕ) :=
  (if (∃ c, L.CornerA c ∧ L.Visits ((j + k) / 2) q c) ∨ i1 < j then [] else [(j, i1)]) ++
    (if (∃ c, L.CornerB c ∧ L.Visits ((j + k) / 2) q c) ∨ k < i2 then [] else [(i2, k)])

variable {C : R.CutPath} {g₀ : D → ℕ} (hR : R.Planar) (hC : R.Connected)
  (hgc : ∀ x, (Nat.cast ∘ g₀ : D → ℝ≥0∞) (R.rev x) = (Nat.cast ∘ g₀ : D → ℝ≥0∞) x)

namespace Live

variable {Γ : Finset (D × Bool)} (L : C.Live (Nat.cast ∘ g₀) Γ) {j k : ℕ} (hjk : j + 2 ≤ k)
  (hxa : L.xa ≤ j) (hya : L.ya ≤ j) (hxb : k ≤ L.xb) (hyb : k ≤ L.yb)
  {q : List (D × Bool)} (hq : L.Shortest ((j + k) / 2) q) {i1 i2 : ℕ}
  (hI1 : IsLeast (C.idx (L.κ0 ((j + k) / 2)) q) i1) (hI2 : IsGreatest (C.idx (L.κ0 ((j + k) / 2)) q) i2)
  (S : L.Step) (hsub : ∃ p₁ p₃, q = p₁ ++ (List.range S.n).map S.q ++ p₃)

/-- **The ranges below a node with given data.** -/
theorem pickNode_kids :
    ((L.pickNode hR hC hgc hjk hxa hya hxb hyb hq hI1 hI2 S hsub).subs 1).map (fun s => s.2.1) =
      L.kids j k q i1 i2 := by
  unfold pickNode Live.kids
  simp only [Run.subs, List.map_append]
  congr 1
  · by_cases hA : ∃ c, (c = L.κ0 L.xa ∨ c ∈ L.La ∨ c = L.κ1 L.ya) ∧ L.Visits ((j + k) / 2) q c
    · have e : ∀ x : {s : SideA hR hC hgc Γ L q ((j + k) / 2) S j i1 // s.IsOverlap hR hC hgc},
          x.1.subs 0 = [] := fun x => SideA.subs_of_isOverlap hR hC hgc x.2 0
      rw [dif_pos hA, e, List.map_nil]
      exact (if_pos (Or.inl hA)).symm
    · rw [dif_neg hA]
      by_cases hj : j ≤ i1
      · rw [dif_pos hj, if_neg (by rintro (h | h); exacts [hA h, by omega])]
        simp only [SideA.subs, Run.subs_zero, List.map_cons, List.map_nil]
      · rw [dif_neg hj, if_pos (Or.inr (by omega))]
        rfl
  · by_cases hB : ∃ c, (c = L.κ0 L.xb ∨ c ∈ L.Lb ∨ c = L.κ1 L.yb) ∧ L.Visits ((j + k) / 2) q c
    · have e : ∀ x : {s : SideB hR hC hgc Γ L q ((j + k) / 2) S i2 k // s.IsOverlap hR hC hgc},
          x.1.subs 0 = [] := fun x => SideB.subs_of_isOverlap hR hC hgc x.2 0
      rw [dif_pos hB, e, List.map_nil]
      exact (if_pos (Or.inl hB)).symm
    · rw [dif_neg hB]
      by_cases hj : i2 ≤ k
      · rw [dif_pos hj, if_neg (by rintro (h | h); exacts [hB h, by omega])]
        simp only [SideB.subs, Run.subs_zero, List.map_cons, List.map_nil]
      · rw [dif_neg hj, if_pos (Or.inr (by omega))]
        rfl

end Live

variable (P : (Σ Γ' : Finset (D × Bool), C.Live (Nat.cast ∘ g₀) Γ') → ℕ → List (D × Bool) →
  List (D × Bool) → Prop)

/-- **The ranges below a picked node.** If there are data whose walk and step darts satisfy `P`, the
picking graft gives a node whose walk and step darts satisfy `P` and whose subruns have the ranges of
the two sides for the walk. -/
theorem pickF_kids {Γ : Finset (D × Bool)} {L : C.Live (Nat.cast ∘ g₀) Γ} {j k : ℕ}
    (r : Run hR hC hgc Γ L j k)
    (h : Nonempty {d : NodeData L j k // P ⟨Γ, L⟩ ((j + k) / 2) d.q d.S.darts}) :
    ∃ q sd, (pickF hR hC hgc P r).top = some (q, sd) ∧ P ⟨Γ, L⟩ ((j + k) / 2) q sd ∧
      ∀ i1 i2, IsLeast (C.idx (L.κ0 ((j + k) / 2)) q) i1 →
        IsGreatest (C.idx (L.κ0 ((j + k) / 2)) q) i2 →
          ((pickF hR hC hgc P r).subs 1).map (fun s => s.2.1) = L.kids j k q i1 i2 := by
  unfold pickF
  rw [dif_pos h]
  refine ⟨(Classical.choice h).1.q, _, rfl, (Classical.choice h).2, fun i1 i2 h1 h2 => ?_⟩
  obtain rfl := h1.unique (Classical.choice h).1.hI1
  obtain rfl := h2.unique (Classical.choice h).1.hI2
  exact L.pickNode_kids hR hC hgc _ _ _ _ _ _ _ _ _ _

/-- A leaf has no subruns below it, also after the picking graft. -/
theorem pickF_kids_leaf {Γ : Finset (D × Bool)} {L : C.Live (Nat.cast ∘ g₀) Γ} {j k : ℕ}
    (r : Run hR hC hgc Γ L j k) (hk : k < j + 2) : (pickF hR hC hgc P r).subs 1 = [] := by
  unfold pickF
  split_ifs with h
  · exact absurd (Classical.choice h).1.hjk (by omega)
  · cases r with
    | leaf => rfl
    | node hjk => omega

section Seq

variable {Γ : Finset (D × Bool)} {L : C.Live (Nat.cast ∘ g₀) Γ} {j k : ℕ}
  (Pof : ℕ → Run hR hC hgc Γ L j k → (Σ Γ' : Finset (D × Bool), C.Live (Nat.cast ∘ g₀) Γ') → ℕ →
    List (D × Bool) → List (D × Bool) → Prop)
  (r₀ : Run hR hC hgc Γ L j k)

/-- **The ranges at the next depth.** The subruns at depth `ℓ + 1` of the run of level `ℓ + 1` are
those below the picked subruns at depth `ℓ`. -/
theorem Run.seq_kids (ℓ : ℕ) :
    ((r₀.seq hR hC hgc Pof (ℓ + 1)).subs (ℓ + 1)).map (fun s => (s.1, s.2.1)) =
      ((r₀.seq hR hC hgc Pof ℓ).subs ℓ).flatMap
        (fun s => ((pickF hR hC hgc (Pof ℓ (r₀.seq hR hC hgc Pof ℓ)) s.2.2).subs 1).map
          (fun s => (s.1, s.2.1))) := by
  show (((r₀.seq hR hC hgc Pof ℓ).graft _ ℓ).subs (ℓ + 1)).map _ = _
  rw [Run.subs_graft, List.map_flatMap]

end Seq

end CutPath

end RotSystem

end SsspFlow
