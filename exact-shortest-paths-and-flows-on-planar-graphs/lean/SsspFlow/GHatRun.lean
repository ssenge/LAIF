import SsspFlow.Annuli
import SsspFlow.GHatPlanar

/-!
# The levels of a run have no conflict

The planarity of the repaired graph (`RData.gRot_planar`) needs that no incised dart has its tail
corner cut in mode R and its head corner cut in mode L (`RData.NoConflict`). These two corners are
consecutive at one vertex of the dual, so a conflict needs two distinct cut corners at one vertex
of the dual (`RData.noConflict_of_cut`). The cut corners of every level of a run of the recursion
are the corners at `s` and `t` (`CutPath.Run.cut_data`), which lie at the vertices `p_0` and `p_m`
of the dual path. For `m ≥ 1` these differ, and for `m = 0` nothing is incised. So every level of a
run has no conflict, for any modes and any hosts (`CutPath.Run.noConflict`), and its repaired graph
is planar (`CutPath.Run.planar_data`).
-/

set_option autoImplicit false

universe u

namespace SsspFlow

open FourColor
open scoped ENNReal

noncomputable section

namespace RotSystem

namespace RData

variable {E : Type u} [Fintype E] [DecidableEq E] {G : RotSystem E} (S : G.RData)

/-- A conflict needs two distinct cut corners at one vertex of the dual. -/
theorem noConflict_of_cut
    (h : ∀ c₁ ∈ S.cut, ∀ c₂ ∈ S.cut, G.dual.tail c₁ = G.dual.tail c₂ → c₁ = c₂) :
    S.NoConflict := by
  rintro d - ⟨⟨h1, m1⟩, ⟨h2, m2⟩⟩
  have hrot : G.dual.rot (G.tailCorner d) = G.rev d := by
    simp [tailCorner]
  have ht : G.dual.tail (G.tailCorner d) = G.dual.tail (G.rev d) := by
    rw [← hrot, G.dual.tail_rot]
  have he := h _ h1 _ h2 ht
  rw [he] at m1
  rw [m1] at m2
  exact absurd m2 (by decide)

/-- Without incised darts there is no conflict. -/
theorem noConflict_of_inc (h : S.inc = ∅) : S.NoConflict := by
  intro d hd
  simp [h] at hd

end RData

variable {D : Type u} [Fintype D] [DecidableEq D] {R : RotSystem D}

namespace CutPath

variable {C : R.CutPath} {g : D → ℝ≥0∞}
variable {hR : R.Planar} {hC : R.Connected} {hg : ∀ x, g (R.rev x) = g x}

mutual
/-- The incisions of a run are digon corners. -/
theorem Run.not_true_steps : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k) (ℓ : ℕ) (c : D), (c, true) ∉ r.steps ℓ
  | _, _, _, _, .leaf .., _, _, h => by simp [Run.steps] at h
  | _, _, _, _, .node .., 0, _, h => by simp [Run.steps] at h
  | _, _, _, _, .node _ _ _ _ _ _ _ _ _ _ _ S _ left right, ℓ + 1, c, h => by
    simp only [Run.steps, Finset.mem_union] at h
    rcases h with (h | h) | h
    · obtain ⟨j, -, e | e⟩ := S.mem_corners.1 h <;> simp at e
    · exact SideA.not_true_steps left ℓ c h
    · exact SideB.not_true_steps right ℓ c h
theorem SideA.not_true_steps : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)}
    {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideA hR hC hg Γ L p i S lo hi) (ℓ : ℕ) (c : D),
      (c, true) ∉ s.steps ℓ
  | _, _, _, _, _, _, _, .overlap .., _, _, h => by simp [SideA.steps] at h
  | _, _, _, _, _, _, _, .child _ _ r, ℓ, c, h => by
    simp only [SideA.steps] at h
    exact Run.not_true_steps r ℓ c h
  | _, _, _, _, _, _, _, .empty _, _, _, h => by simp [SideA.steps] at h
theorem SideB.not_true_steps : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)}
    {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideB hR hC hg Γ L p i S lo hi) (ℓ : ℕ) (c : D),
      (c, true) ∉ s.steps ℓ
  | _, _, _, _, _, _, _, .overlap .., _, _, h => by simp [SideB.steps] at h
  | _, _, _, _, _, _, _, .child _ _ r, ℓ, c, h => by
    simp only [SideB.steps] at h
    exact Run.not_true_steps r ℓ c h
  | _, _, _, _, _, _, _, .empty _, _, _, h => by simp [SideB.steps] at h
end

/-- A run over at most one index makes no incision. -/
theorem Run.steps_eq_empty {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k) (hk : k ≤ j + 1) (ℓ : ℕ) : r.steps ℓ = ∅ := by
  cases r with
  | leaf => simp [Run.steps]
  | node hjk => omega

/-- The corners of the cut at `s` and `t` are the only corners of the cut that are not digon
corners. -/
theorem mem_Γ_true {c : D} (h : (c, true) ∈ C.Γ) : c = C.cs ∨ c = C.ct := by
  simp only [Γ, Recursion.copyCorners, List.mem_toFinset, List.mem_append, List.mem_map,
    List.mem_range, List.mem_reverse] at h
  rcases h with ⟨t, -, ht⟩ | ⟨t, -, ht⟩
  · simp only [k, k0, if_true] at ht
    split_ifs at ht <;> simp_all
  · simp only [k, k1, Fin.one_eq_zero_iff, if_false] at ht
    split_ifs at ht <;> simp_all

/-- For `m = 0` the cut has no digon corners. -/
theorem not_mem_Γ_false (hm : C.m = 0) (d : D) : (d, false) ∉ C.Γ := by
  simp only [Γ, Recursion.copyCorners, List.mem_toFinset, List.mem_append, List.mem_map,
    List.mem_range, List.mem_reverse, hm]
  rintro (⟨t, ht, h⟩ | ⟨t, ht, h⟩)
  · have : t = 0 := by omega
    subst this
    simp [k, k0, hm] at h
  · have : t = 0 := by omega
    subst this
    simp [k, k1] at h

end CutPath

section Tokens

variable {E : Type u} [Fintype E] [DecidableEq E] {G : RotSystem E} {C : G.dual.CutPath}
  {g : E → ℝ≥0∞} {hR : G.dual.Planar} {hC : G.dual.Connected} {hg : ∀ x, g (G.dual.rev x) = g x}

namespace CutPath

variable (r : Run hR hC hg C.Γ (C.liveOne g) 0 C.m) (ℓ : ℕ) (modeL hostT : E → Bool)
  (hhost : ∀ d, (d, false) ∉ C.Γ ∪ r.steps ℓ → hostT (G.rev d) = !hostT d)

/-- The cut corners of a level are corners of the cut at `s` and `t`. -/
theorem Run.cut_data {c : E} (hc : c ∈ (r.data ℓ modeL hostT hhost).cut) : c = C.cs ∨ c = C.ct := by
  simp only [Run.data, RData.ofCorners, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union] at hc
  rcases hc with h | h
  · exact mem_Γ_true h
  · exact absurd h (r.not_true_steps ℓ c)

/-- **Every level of a run has no conflict**, for any modes and any hosts. -/
theorem Run.noConflict : (r.data ℓ modeL hostT hhost).NoConflict := by
  by_cases hm : C.m = 0
  · apply RData.noConflict_of_inc
    rw [Finset.eq_empty_iff_forall_notMem]
    intro d hd
    simp only [Run.data, RData.ofCorners, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, r.steps_eq_empty (by omega)] at hd
    simpa [C.not_mem_Γ_false hm d] using hd
  · apply RData.noConflict_of_cut
    have hst : G.dual.tail C.cs ≠ G.dual.tail C.ct := by
      rw [C.tail_cs, C.tail_ct]
      intro h
      exact hm (C.inj 0 C.m (Nat.zero_le _) le_rfl h).symm
    intro c₁ h₁ c₂ h₂ he
    rcases r.cut_data ℓ modeL hostT hhost h₁ with rfl | rfl <;>
      rcases r.cut_data ℓ modeL hostT hhost h₂ with rfl | rfl
    · rfl
    · exact absurd he hst
    · exact absurd he.symm hst
    · rfl

/-- **The repaired graph of every level of a run is planar**, for a connected planar network. -/
theorem Run.planar_data (hP : G.Planar) (hc : G.Connected) :
    (r.data ℓ modeL hostT hhost).gRot.Planar :=
  RData.gRot_planar _ hP hc (r.noConflict ℓ modeL hostT hhost)

end CutPath

end Tokens

end RotSystem

end

end SsspFlow
