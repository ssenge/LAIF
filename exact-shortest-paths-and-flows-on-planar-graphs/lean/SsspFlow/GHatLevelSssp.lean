import SsspFlow.GHatLevelDist

/-!
# Distances of a level in polylogarithmic times diameter rounds

The source of a level is one copy: offset `0` at its identifier and `∞` elsewhere
(`RData.levelOff`). Then the distance from the virtual source of the network of a level is the
distance in `Ĝ_ℓ` from that copy (`RData.dsrcTop_levelOff`), and with lengths at most `W` the input
is valid for an oracle with lengths in `[0, W]` (`RData.oracleValid_level`).

* `RData.levelSssp`: given the Exact SSSP bound, one algorithm on the identifiers of the levels of
  networks on `n` nodes computes, at the identifier of every copy, its distance in `Ĝ_ℓ` from the
  source copy, in `C log^c n · (12 D + 16)` rounds on the network of the level.
* `RData.levelSssp_sim`: the nodes of the network compute the same distances in the same number of
  rounds, with messages of four times the width, if each node knows the edges and inputs at its own
  identifiers.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

section Sssp

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  (lam : S.Tok → ℕ) (M : ℕ)

open Classical in
/-- The offset of a level: `0` at the identifier of the source copy, `∞` elsewhere. -/
noncomputable def levelOff (u₀ : S.hRot.Vertex) (z : Fin (n * (n * 21))) : ℕ∞ :=
  if z = (S.levelPad hN).ι (.inl u₀) then 0 else ⊤

/-- **The distance from the virtual source is the distance in `Ĝ_ℓ` from the source copy.** -/
theorem dsrcTop_levelOff (u₀ v : S.hRot.Vertex) :
    (S.levelNet hN).dsrcTop (S.levelLen hN lam M) (S.levelOff hN u₀) ((S.levelPad hN).ι (.inl v)) =
      S.arcDist lam M (S.vcopy u₀) (S.vcopy v) := by
  classical
  rw [← S.levelNet_dist hN lam M u₀ v]
  apply le_antisymm
  · refine iInf_le_of_le ((S.levelPad hN).ι (.inl u₀)) ?_
    simp [offTop, levelOff]
  · refine le_iInf fun a => ?_
    by_cases ha : a = (S.levelPad hN).ι (.inl u₀)
    · subst ha
      exact le_add_self
    · simp [offTop, levelOff, ha]

theorem dartW_le {W : ℕ} (hlam : ∀ x, lam x ≤ W) (hM : M ≤ W) (d : S.HD) : S.dartW lam M d ≤ W := by
  unfold dartW
  split
  · exact Nat.zero_le _
  · exact hlam _
  · exact hlam _
  · exact hM

/-- With lengths at most `W`, the input of a level is valid for an oracle on `[0, W]`. -/
theorem oracleValid_level {W : ℕ} (hlam : ∀ x, lam x ≤ W) (hM : M ≤ W) (u₀ : S.hRot.Vertex) :
    OracleValid (S.levelNet hN) 0 W (S.levelLen hN lam M) (S.levelOff hN u₀) := by
  classical
  refine ⟨fun x y _ => ?_, fun z => ?_⟩
  · unfold levelLen
    split_ifs with h
    · split
      · split_ifs
        · exact .inr ⟨zero_le, by exact_mod_cast S.dartW_le lam M hlam hM _⟩
        · exact .inl rfl
      · exact .inr ⟨le_rfl, zero_le⟩
      · exact .inr ⟨le_rfl, zero_le⟩
      · exact .inl rfl
    · exact .inl rfl
  · unfold levelOff
    split_ifs
    · exact .inr (zero_le)
    · exact .inl rfl

end Sssp

/-- **Distances of a level.** Given the Exact SSSP bound, one algorithm, fixed for `n` and `D`,
computes on the network of every level of every connected plane network on `n` nodes of diameter at
most `D` the distance in `Ĝ_ℓ` from a source copy to every copy, in `C log^c n' · (12 D + 16)` rounds
with `n' = 21 n²`, for lengths at most `(n' + 2) ^ K`. -/
theorem levelSssp (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin (n * (n * 21))) (OracleIn (Fin (n * (n * 21)))) σ
      (C * logN (n * (n * 21)) ^ c)) (out : Fin (n * (n * 21)) → σ → ℕ∞ × Option (Fin (n * (n * 21)))),
    ∀ (N : Net (Fin n)) (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w) (lam : S.Tok → ℕ) (M : ℕ)
      (u₀ : S.hRot.Vertex),
      N.toRot.Planar → N.toRot.Connected → S.NoConflict → S.cut.card ≤ 3 → N.DiamLE D →
      (∀ x, lam x ≤ (n * (n * 21) + 2) ^ K) → M ≤ (n * (n * 21) + 2) ^ K →
      ∀ v : S.hRot.Vertex,
        ((out ((S.levelPad hN).ι (.inl v)) (A.run (S.levelNet hN).G
          ((S.levelNet hN).oracleIn (S.levelLen hN lam M) (S.levelOff hN u₀))
          (C * logN (n * (n * 21)) ^ c * (12 * D + 16)) ((S.levelPad hN).ι (.inl v)))).1 : ℝ≥0∞) =
          S.arcDist lam M (S.vcopy u₀) (S.vcopy v) := by
  obtain ⟨C, c, hC⟩ := hE K
  refine ⟨C, c, fun n D => ?_⟩
  obtain ⟨σ, A, out, hA⟩ := hC (n * (n * 21)) (12 * D + 16) (by omega)
  refine ⟨σ, A, out, fun N S hN lam M u₀ hP hc hS hcut hD hlam hM v => ?_⟩
  have h := (hA (S.levelNet hN) (S.levelLen hN lam M) (S.levelOff hN u₀)
    (S.levelNet_planar hN hP hc hS hcut hD) (S.levelNet_diam hN hcut hD)
    (S.oracleValid_level hN lam M hlam hM u₀)).dist_eq ((S.levelPad hN).ι (.inl v))
  rw [h, S.dsrcTop_levelOff]

/-- **The nodes compute the distances of a level.** The nodes of the network run the algorithm of
`levelSssp` on the network of a level, round for round with messages of four times the width, if
each node knows the edges and the inputs at its own identifiers. -/
theorem levelSssp_sim (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin (n * (n * 21))) (OracleIn (Fin (n * (n * 21)))) σ
      (C * logN (n * (n * 21)) ^ c)) (out : Fin (n * (n * 21)) → σ → ℕ∞ × Option (Fin (n * (n * 21)))),
    ∀ (I : Type) (view : I → Fin (n * (n * 21)) → Fin (n * (n * 21)) → Prop)
      (vin : Fin n → I → Fin (n * (n * 21)) → OracleIn (Fin (n * (n * 21)))),
    ∀ (N : Net (Fin n)) (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w) (lam : S.Tok → ℕ) (M : ℕ)
      (u₀ : S.hRot.Vertex) (inp : Fin n → I),
      N.toRot.Planar → N.toRot.Connected → S.NoConflict → S.cut.card ≤ 3 → N.DiamLE D →
      (∀ x, lam x ≤ (n * (n * 21) + 2) ^ K) → M ≤ (n * (n * 21) + 2) ^ K →
      (∀ a, (S.levelNet hN).oracleIn (S.levelLen hN lam M) (S.levelOff hN u₀) a =
        vin (hostOf a) (inp (hostOf a)) a) →
      (∀ w b a, (hostOf b = w ∨ hostOf a = w) → (view (inp w) b a ↔ (S.levelNet hN).G.Adj b a)) →
      ∀ v : S.hRot.Vertex,
        ((out ((S.levelPad hN).ι (.inl v))
          (((Cslib.Congest.Algorithm.simulateView (k := 4) A hostOf view vin).run N.G inp
            (C * logN (n * (n * 21)) ^ c * (12 * D + 16)) (hostOf ((S.levelPad hN).ι (.inl v)))).2
              ((S.levelPad hN).ι (.inl v)))).1 : ℝ≥0∞) =
          S.arcDist lam M (S.vcopy u₀) (S.vcopy v) := by
  obtain ⟨C, c, hC⟩ := levelSssp hE K
  refine ⟨C, c, fun n D => ?_⟩
  obtain ⟨σ, A, out, hA⟩ := hC n D
  refine ⟨σ, A, out, fun I view vin N S hN lam M u₀ inp hP hc hS hcut hD hlam hM hin hview v => ?_⟩
  rw [S.run_levelSim hN A view vin inp _ hin hview _ _ _ rfl]
  exact hA N S hN lam M u₀ hP hc hS hcut hD hlam hM v

end RData

end RotSystem

end SsspFlow
