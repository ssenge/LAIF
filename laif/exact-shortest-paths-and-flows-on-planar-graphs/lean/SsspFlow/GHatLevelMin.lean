import SsspFlow.GHatLevelMark

/-!
# Least offsets in the components of a level

With token lengths `0`, a run from offsets `ψ` at the copies gives, below `M`, the least offset in
the component of `Ĝ_ℓ[E_R ∪ E_C]` of each copy. With the index on the cut path as offset at the
marked copies this gives the least index on the marked walk of each annulus, and with the index
subtracted from a bound, the greatest.

* `RData.zmin_cap`: for token lengths `0` or at least `M`, the least offset plus distance, capped at
  `M`, is the least offset among the copies joined by zero arcs, capped at `M`.
* `RData.levelMin_local`: assuming the Exact SSSP bound, one algorithm of the message model, fixed
  before the network, starts from the local inputs of a level with token lengths `0` and the offsets
  at the identifiers of each node, and after `C log^c n' · (12 D + 16) + 1` rounds holds at every copy
  the least offset of its component of `Ĝ_ℓ[E_R ∪ E_C]`, capped at `M`.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

section Cap

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (lam : S.Tok → ℕ) (M : ℕ)

/-- **Capped least offsets.** For token lengths `0` or at least `M`, the least offset plus distance,
capped at `M`, is the least offset of the copies joined by zero arcs, capped at `M`. -/
theorem zmin_cap (hlam : ∀ x, lam x = 0 ∨ M ≤ lam x) (ψ : S.hRot.Vertex → ℕ∞) (v : S.hRot.Vertex) :
    min (⨅ u, (ψ u : ℝ≥0∞) + S.arcDist lam M (S.vcopy u) (S.vcopy v)) M =
      min (⨅ u, ⨅ (_ : Relation.ReflTransGen (S.ZR lam) (S.vcopy u) (S.vcopy v)), (ψ u : ℝ≥0∞)) M := by
  apply le_antisymm
  · rcases Nat.eq_zero_or_pos M with h0 | hM
    · subst h0
      simp
    · refine min_le_min_right _ (le_iInf fun u => le_iInf fun hu => iInf_le_of_le u ?_)
      rw [(S.arcDist_eq_zero_iff_rtg lam M hlam hM).2 hu, add_zero]
  · refine le_min (le_iInf fun u => ?_) (min_le_right _ _)
    by_cases hu : Relation.ReflTransGen (S.ZR lam) (S.vcopy u) (S.vcopy v)
    · exact (min_le_left _ _).trans ((iInf_le_of_le u (iInf_le_of_le hu le_rfl)).trans le_self_add)
    · exact (min_le_right _ _).trans ((S.le_arcDist lam M hlam hu).trans le_add_self)

end Cap

/-- **Least offsets of the components, from local inputs.** Assuming the Exact SSSP bound, one algorithm
of the message model on `N`, fixed before the network, starts from the inputs of a level with token
lengths `0` and, at each node, offsets that agree with `ψ` at the identifiers it hosts. After
`C log^c n' · (12 D + 16) + 1` rounds it holds at every copy the least offset of the copies of its
component of `Ĝ_ℓ[E_R ∪ E_C]`, capped at `M`. -/
theorem levelMin_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n) (LevelIn n × (Fin (n * (n * 21)) → ℕ∞)) σ
      (4 * (C * logN (n * (n * 21)) ^ c) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (out : Fin (n * (n * 21)) → σ → ℕ∞),
    ∀ (N : Net (Fin n)) (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w) (M : ℕ)
      (u₀ : S.hRot.Vertex) (ψ : Fin (n * (n * 21)) → ℕ∞) (off : Fin n → Fin (n * (n * 21)) → ℕ∞),
      N.toRot.Planar → N.toRot.Connected → S.NoConflict → S.cut.card ≤ 3 → N.DiamLE D →
      M ≤ (n * (n * 21) + 2) ^ K →
      (∀ z, (∀ u, z ≠ (S.levelPad hN).ι (.inl u)) → ψ z = ⊤) →
      (∀ z, ψ z = ⊤ ∨ ψ z ≤ (n * (n * 21) + 2) ^ K) →
      (∀ a, off (hostOf a) a = ψ a) →
      ∀ v : S.hRot.Vertex,
        min (out ((S.levelPad hN).ι (.inl v))
          (A.run N.G (fun w => (S.levelIn hN (fun _ => 0) M u₀ w, off w))
            (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16)) (hostOf ((S.levelPad hN).ι (.inl v)))) : ℝ≥0∞) M =
          min (⨅ u, ⨅ (_ : Relation.ReflTransGen S.ERC (S.vcopy u) (S.vcopy v)),
            (ψ ((S.levelPad hN).ι (.inl u)) : ℝ≥0∞)) M := by
  obtain ⟨C, c, hC⟩ := levelSsspOff_local hE K
  refine ⟨C, c, fun n D => ?_⟩
  obtain ⟨σ, A, out, hA⟩ := hC n D
  refine ⟨σ, A, out, fun N S hN M u₀ ψ off hP hc hS hcut hD hM hψ hψW hoff v => ?_⟩
  rw [hA N S hN (fun _ => 0) M u₀ ψ off hP hc hS hcut hD (fun _ => Nat.zero_le _) hM hψ hψW hoff v,
    S.zmin_cap (fun _ => 0) M (fun _ => Or.inl rfl) (fun u => ψ ((S.levelPad hN).ι (.inl u))) v, zr_zero]

end RData

end RotSystem

end SsspFlow
