import SsspFlow.Annuli

/-!
# The depth of a run

An annulus with the index range `[j, k]` that is not a leaf calls its sides on the ranges `[j, i₁]` and
`[i₂, k]` with `i₁ ≤ ⌊(j + k)/2⌋ ≤ i₂`, so each range at most halves. A run on `[j, k]` has an annulus
at depth `ℓ + 1` only if `2 ^ ℓ < k - j` (`CutPath.Run.nodes_width`), so all its annuli lie at depth
at most `log₂ (k - j) + 1` (`CutPath.Run.nodes_eq_nil`): a run on the cut has at most `log₂ m + 2` levels.
-/

set_option autoImplicit false

universe u

namespace SsspFlow

open FourColor
open scoped ENNReal

noncomputable section

namespace RotSystem

variable {D : Type u} [Fintype D] [DecidableEq D] {R : RotSystem D}

namespace CutPath

variable {C : R.CutPath} {g : D → ℝ≥0∞}
variable {hR : R.Planar} {hC : R.Connected} {hg : ∀ x, g (R.rev x) = g x}

mutual
/-- **Depth and width.** A run on `[j, k]` with an annulus at depth `ℓ + 1` has `2 ^ ℓ < k - j`. -/
theorem Run.nodes_width : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k) (ℓ : ℕ), r.nodes (ℓ + 1) ≠ [] → 2 ^ ℓ < k - j
  | _, _, _, _, .leaf .., _, h => by simp [Run.nodes] at h
  | _, L, j, k, .node hjk hxa _ hxb _ p _ i1 i2 h1 h2 _ _ left right, ℓ, h => by
    have hm := L.mem_idx (i := (j + k) / 2) (by omega) (by omega) p
    have hi1 := h1.2 hm
    have hi2 := h2.2 hm
    cases ℓ with
    | zero => simp only [pow_zero]; omega
    | succ ℓ =>
      simp only [Run.nodes, ne_eq, List.append_eq_nil_iff, not_and_or] at h
      rcases h with h | h
      · have := SideA.nodes_width left ℓ h
        rw [pow_succ]
        omega
      · have := SideB.nodes_width right ℓ h
        rw [pow_succ]
        omega
theorem SideA.nodes_width : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)}
    {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideA hR hC hg Γ L p i S lo hi) (ℓ : ℕ),
      s.nodes (ℓ + 1) ≠ [] → 2 ^ ℓ < hi - lo
  | _, _, _, _, _, _, _, .overlap .., _, h => by simp [SideA.nodes] at h
  | _, _, _, _, _, _, _, .child _ _ r, ℓ, h => Run.nodes_width r ℓ h
  | _, _, _, _, _, _, _, .empty _, _, h => by simp [SideA.nodes] at h
theorem SideB.nodes_width : ∀ {Γ : Finset (D × Bool)} {L : C.Live g Γ} {p : List (D × Bool)}
    {i : ℕ} {S : L.Step} {lo hi : ℕ} (s : SideB hR hC hg Γ L p i S lo hi) (ℓ : ℕ),
      s.nodes (ℓ + 1) ≠ [] → 2 ^ ℓ < hi - lo
  | _, _, _, _, _, _, _, .overlap .., _, h => by simp [SideB.nodes] at h
  | _, _, _, _, _, _, _, .child _ _ r, ℓ, h => Run.nodes_width r ℓ h
  | _, _, _, _, _, _, _, .empty _, _, h => by simp [SideB.nodes] at h
end

/-- **The depth of a run.** A run on `[j, k]` has no annulus below depth `log₂ (k - j) + 1`. -/
theorem Run.nodes_eq_nil {Γ : Finset (D × Bool)} {L : C.Live g Γ} {j k : ℕ}
    (r : Run hR hC hg Γ L j k) {ℓ : ℕ} (hℓ : Nat.log 2 (k - j) + 1 < ℓ) : r.nodes ℓ = [] := by
  cases ℓ with
  | zero => exact absurd hℓ (by omega)
  | succ ℓ =>
    by_contra h
    have h2 : ℓ ≤ Nat.log 2 (k - j) := Nat.le_log_of_pow_le (by norm_num) (r.nodes_width ℓ h).le
    omega

end CutPath

end RotSystem

end

end SsspFlow
