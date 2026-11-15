import SsspFlow.GHatLevelOff

/-!
# A value for every node of a component

With token lengths `0`, the distance between two copies in `Ĝ_ℓ` is `0` inside a component of the
E_R and E_C edges and at least `M` between components. So one run of the oracle from offsets that are
finite only at sources gives every copy the offset of the source of its component, if that source is
the only one there and its offset is at most `M`.

* `RData.bcast_eq`: the least offset plus distance with token lengths `0` is the offset of the source.
* `RData.levelBcast_local`: one algorithm of the message model that gives every copy the value of the
  source of its component.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)

/-- **The value of the source of a component.** With token lengths `0`, let the copy of `u₁` reach the
copy of `v` by E_R and E_C edges, let `u₁` be the only vertex with a finite offset whose copy does so,
and let its offset be at most `M`. Then the least offset plus distance at the copy of `v` is the offset
of `u₁`. -/
theorem bcast_eq (M : ℕ) (hM : 1 ≤ M) (ψ : Fin (n * (n * 21)) → ℕ∞) {v u₁ : S.hRot.Vertex}
    (h1 : Relation.ReflTransGen S.ERC (S.vcopy u₁) (S.vcopy v))
    (huniq : ∀ u, ψ ((S.levelPad hN).ι (.inl u)) ≠ ⊤ →
      Relation.ReflTransGen S.ERC (S.vcopy u) (S.vcopy v) → u = u₁)
    (hle : (ψ ((S.levelPad hN).ι (.inl u₁)) : ℝ≥0∞) ≤ M) :
    ⨅ u, (ψ ((S.levelPad hN).ι (.inl u)) : ℝ≥0∞) + S.arcDist (fun _ => 0) M (S.vcopy u) (S.vcopy v) =
      ψ ((S.levelPad hN).ι (.inl u₁)) := by
  apply le_antisymm
  · refine iInf_le_of_le u₁ ?_
    rw [(S.arcDist_eq_zero_iff_rtg (fun _ => 0) M (fun _ => .inl rfl) hM).2 (by rw [zr_zero]; exact h1),
      add_zero]
  · refine le_iInf fun u => ?_
    by_cases hu : ψ ((S.levelPad hN).ι (.inl u)) = ⊤
    · simp [hu]
    by_cases hc : Relation.ReflTransGen S.ERC (S.vcopy u) (S.vcopy v)
    · rw [huniq u hu hc]
      exact le_self_add
    · exact hle.trans ((S.le_arcDist (fun _ => 0) M (fun _ => .inl rfl) (by rwa [zr_zero])).trans
        le_add_self)

open Cslib.Congest.Algorithm in
/-- **A value for every node of a component, from local inputs.** Assuming the Exact SSSP bound, one
algorithm of the message model on `N`, fixed before the network, starts from the inputs of a level
with token lengths `0` and, at each node, offsets that agree with `ψ` at the identifiers it hosts.
After `1 + C log^c n' · (12 D + 16)` rounds, every copy of a vertex `v` whose component of E_R and E_C
edges holds exactly one vertex `u₁` with a finite offset, at most `M`, holds the offset of `u₁`. -/
theorem levelBcast_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n) (LevelIn n × (Fin (n * (n * 21)) → ℕ∞)) σ
      (4 * (C * logN (n * (n * 21)) ^ c) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (out : Fin (n * (n * 21)) → σ → ℕ∞),
    ∀ (N : Net (Fin n)) (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w) (M : ℕ)
      (u₀ : S.hRot.Vertex) (ψ : Fin (n * (n * 21)) → ℕ∞) (off : Fin n → Fin (n * (n * 21)) → ℕ∞),
      N.toRot.Planar → N.toRot.Connected → S.NoConflict → S.cut.card ≤ 3 → N.DiamLE D →
      1 ≤ M → M ≤ (n * (n * 21) + 2) ^ K →
      (∀ z, (∀ u, z ≠ (S.levelPad hN).ι (.inl u)) → ψ z = ⊤) →
      (∀ z, ψ z = ⊤ ∨ ψ z ≤ (n * (n * 21) + 2) ^ K) →
      (∀ a, off (hostOf a) a = ψ a) →
      ∀ v u₁ : S.hRot.Vertex, Relation.ReflTransGen S.ERC (S.vcopy u₁) (S.vcopy v) →
        (∀ u, ψ ((S.levelPad hN).ι (.inl u)) ≠ ⊤ →
          Relation.ReflTransGen S.ERC (S.vcopy u) (S.vcopy v) → u = u₁) →
        (ψ ((S.levelPad hN).ι (.inl u₁)) : ℝ≥0∞) ≤ M →
        out ((S.levelPad hN).ι (.inl v))
          (A.run N.G (fun w => (S.levelIn hN (fun _ => 0) M u₀ w, off w))
            (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16)) (hostOf ((S.levelPad hN).ι (.inl v)))) =
          ψ ((S.levelPad hN).ι (.inl u₁)) := by
  obtain ⟨C, c, hC⟩ := levelSsspOff_local hE K
  refine ⟨C, c, fun n D => ?_⟩
  obtain ⟨σ, A, out, hA⟩ := hC n D
  refine ⟨σ, A, out, ?_⟩
  intro N S hN M u₀ ψ off hP hc hS hcut hD hM1 hM hψ hψW hoff v u₁ h1 huniq hle
  have key := hA N S hN (fun _ => 0) M u₀ ψ off hP hc hS hcut hD (fun _ => Nat.zero_le _) hM hψ hψW hoff v
  rw [S.bcast_eq hN M hM1 ψ h1 huniq hle] at key
  exact_mod_cast key

end RData

end RotSystem

end SsspFlow
