import SsspFlow.GHatCornerLocal
import SsspFlow.MinFlood

/-!
# A common copy of a level, known to every node

The inputs of a level name one copy of a vertex of `Ĝ_ℓ` by its identifier. For a fixed corner `z₀`,
the copy at the first end of its token is hosted at the head of its dart, which recognizes its
identifier from local data. A flood of the least number then tells every node this identifier in `D`
rounds.

* `RData.flag0`: the value `0` at `z₀` and `⊤` elsewhere.
* `RData.onCopies_flag0`: the least value of `flag0 z₀` at the first ends of the tokens at an
  identifier is `0` exactly at the identifier of the copy `endV z₀`.
* `RData.seedOf`: the least identifier with the value `0` among the identifiers that a node hosts.
* `RData.run_u0`: after `D` rounds of the flood of `seedOf`, every node holds the identifier of the copy
  `endV z₀`.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest Cslib.Congest.Algorithm
open scoped ENNReal

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)

open Classical in
/-- The value `0` at `z₀` and `⊤` at every other corner. -/
noncomputable def flag0 (z₀ : N.G.Dart × Bool) (z : N.G.Dart × Bool) : ℕ∞ := if z = z₀ then 0 else ⊤

/-- **The copy of a fixed corner by local values.** -/
theorem onCopies_flag0 (z₀ : N.G.Dart × Bool) (a : Fin (n * (n * 21))) :
    S.onCopies hN (fun u => S.copyVal0 (flag0 z₀) (S.vcopy u)) a = 0 ↔
      a = (S.levelPad hN).ι (.inl (S.endV z₀)) := by
  have hf : ∀ z, flag0 z₀ z = 0 ∨ flag0 z₀ z = ⊤ := fun z => by
    unfold flag0; split_ifs <;> simp
  by_cases ha : ∃ u, a = (S.levelPad hN).ι (.inl u)
  · obtain ⟨u, rfl⟩ := ha
    rw [S.onCopies_copy, S.copyVal0_flag _ hf]
    have hinj : (S.levelPad hN).ι (.inl u) = (S.levelPad hN).ι (.inl (S.endV z₀)) ↔ S.endV z₀ = u :=
      ⟨fun h => (Sum.inl_injective ((S.levelPad hN).ι_injective h)).symm, fun h => by rw [h]⟩
    rw [hinj]
    split_ifs with h
    · obtain ⟨z, hz, h0⟩ := h
      have : z = z₀ := by
        by_contra hne
        simp [flag0, hne] at h0
      subst this
      exact ⟨fun _ => hz, fun _ => rfl⟩
    · refine ⟨fun h0 => absurd h0 ENat.top_ne_zero, fun hz => absurd ⟨z₀, hz, ?_⟩ h⟩
      simp [flag0]
  · rw [S.onCopies_other hN _ _ fun u e => ha ⟨u, e⟩]
    exact ⟨fun h => absurd h ENat.top_ne_zero, fun h => absurd ⟨_, h⟩ ha⟩

open Classical in
/-- The least identifier hosted at `w` with the value `0`, or `n * (n * 21)` if there is none. -/
noncomputable def seedOf (test : Fin n → Fin (n * (n * 21)) → ℕ∞) (w : Fin n) : ℕ :=
  Finset.univ.fold min (n * (n * 21)) fun a => if hostOf a = w ∧ test w a = 0 then a.val else n * (n * 21)

/-- **Every node learns the identifier of the copy of `z₀`.** If the value `test (hostOf a) a`
computed at the host of each identifier `a` is the least value of `flag0 z₀` at the first ends of the
tokens at `a`, then after `D` rounds of the flood of `seedOf test`, with `B` bits per message for
`n (21 n) < 2 ^ B`, on a network of diameter at most `D`, every node holds the identifier of the copy
`endV z₀`. -/
theorem run_u0 (z₀ : N.G.Dart × Bool) (test : Fin n → Fin (n * (n * 21)) → ℕ∞)
    (htest : ∀ a, test (hostOf a) a = S.onCopies hN (fun u => S.copyVal0 (flag0 z₀) (S.vcopy u)) a)
    {B D : ℕ} (hB : n * (n * 21) < 2 ^ B) (hD : N.DiamLE D) (w : Fin n) :
    ((minFlood B).run N.G (seedOf test) D w).1 = ((S.levelPad hN).ι (.inl (S.endV z₀))).val := by
  set a₀ := (S.levelPad hN).ι (.inl (S.endV z₀))
  have hseed : ∀ w a, (if hostOf a = w ∧ test w a = 0 then a.val else n * (n * 21)) =
      if hostOf a = w ∧ a = a₀ then a.val else n * (n * 21) := by
    intro w a
    by_cases h : hostOf a = w
    · subst h
      have e : test (hostOf a) a = 0 ↔ a = a₀ := by rw [htest]; exact S.onCopies_flag0 hN z₀ a
      simp only [true_and, e]
    · simp [h]
  refine run_minFlood N.G (seedOf test) (fun v => ?_) hD (fun v => ?_) ⟨hostOf a₀, ?_⟩ w
  · exact lt_of_le_of_lt ((Finset.fold_min_le _).2 (.inl le_rfl)) hB
  · refine (Finset.le_fold_min _).2 ⟨a₀.isLt.le, fun a _ => ?_⟩
    rw [hseed]
    split_ifs with h
    · rw [h.2]
    · exact a₀.isLt.le
  · refine le_antisymm ((Finset.fold_min_le _).2 (.inr ⟨a₀, Finset.mem_univ _, ?_⟩))
      ((Finset.le_fold_min _).2 ⟨a₀.isLt.le, fun a _ => ?_⟩)
    · rw [hseed]; simp
    · rw [hseed]
      split_ifs with h
      · rw [h.2]
      · exact a₀.isLt.le

end RData

end RotSystem

end SsspFlow
