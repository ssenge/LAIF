import SubsetBalancing.Accounting
import SubsetBalancing.Concavity

/-!
# Proposition 2: the total exponent on a box

The total exponent is the maximum of four terms, each concave in the profile for a fixed kernel and a
fixed `σ`. So a bound on the tangents of the four terms at the corners of a box bounds `L` on the box.
-/

open Finset

namespace SubsetBalancing

variable {κ Lab β γ : Type*} [Fintype κ] [Fintype Lab] [Fintype β] [Fintype γ] [DecidableEq γ]
  {W : κ → Lab → β → ℝ}

/-- **Proposition 2.** Fix the kernel and `σ`. Let each of the four terms of the total exponent have a
derivative at a centre `x` of the profiles, and let the tangent of each term be at most `B` at the
corner of its derivative. Then `L ≤ B` on the box. -/
theorem exponent_box_bound [DecidableEq κ] (hW : ∀ c l b, 0 ≤ W c l b) (fx fy : β → γ) (σ : ℝ)
    {lo hi x : κ → ℝ} (hbox : Set.Icc lo hi ⊆ profiles κ) (hx : x ∈ profiles κ)
    {g₁ g₂ g₃ g₄ : (κ → ℝ) →L[ℝ] ℝ} {B : ℝ}
    (h₁ : HasFDerivAt (fun π => aExp W π / 2 + a₀Exp W π + σ) g₁ x)
    (h₂ : HasFDerivAt
      (fun π => aExp W π / 2 + σ / 2 + (2 / 3) * (listEnt W fx π - a₀Exp W π - σ)) g₂ x)
    (h₃ : HasFDerivAt
      (fun π => aExp W π / 2 + σ / 2 + (2 / 3) * (listEnt W fy π - a₀Exp W π - σ)) g₃ x)
    (h₄ : HasFDerivAt (fun π => aExp W π / 2 + σ / 2) g₄ x)
    (hB₁ : aExp W x / 2 + a₀Exp W x + σ
      + g₁ (corner (coeffs (g₁ : (κ → ℝ) →ₗ[ℝ] ℝ)) lo hi - x) ≤ B)
    (hB₂ : aExp W x / 2 + σ / 2 + (2 / 3) * (listEnt W fx x - a₀Exp W x - σ)
      + g₂ (corner (coeffs (g₂ : (κ → ℝ) →ₗ[ℝ] ℝ)) lo hi - x) ≤ B)
    (hB₃ : aExp W x / 2 + σ / 2 + (2 / 3) * (listEnt W fy x - a₀Exp W x - σ)
      + g₃ (corner (coeffs (g₃ : (κ → ℝ) →ₗ[ℝ] ℝ)) lo hi - x) ≤ B)
    (hB₄ : aExp W x / 2 + σ / 2 + g₄ (corner (coeffs (g₄ : (κ → ℝ) →ₗ[ℝ] ℝ)) lo hi - x) ≤ B)
    {π : κ → ℝ} (hπ : π ∈ Set.Icc lo hi) :
    totalExp (aExp W π) (max (listEnt W fx π) (listEnt W fy π)) (a₀Exp W π) σ ≤ B := by
  rw [totalExp_eq_terms]
  refine max_le ?_ (max_le ?_ (max_le ?_ ?_))
  · exact (concave_le_corner (term_table_concave hW σ) hbox hx h₁ hπ).trans hB₁
  · exact (concave_le_corner (term_search_concave hW fx σ) hbox hx h₂ hπ).trans hB₂
  · exact (concave_le_corner (term_search_concave hW fy σ) hbox hx h₃ hπ).trans hB₃
  · exact (concave_le_corner (term_half_concave hW σ) hbox hx h₄ hπ).trans hB₄

end SubsetBalancing
