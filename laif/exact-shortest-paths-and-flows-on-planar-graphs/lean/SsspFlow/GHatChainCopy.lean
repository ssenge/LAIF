import Mathlib.Data.ENat.BigOperators
import SsspFlow.GHatLevelMinIdx

/-!
# Copies on the parent chains of a level

An edge of finite length of the network of a level at a dart node joins it to the copy node of its
tail or to the node of its reverse dart. The ranks of the oracle fall strictly along a parent chain,
so the two neighbours of a dart node inside a chain are different, and one of them is the copy node
of its tail. The ends of a chain from a target copy are copy nodes when the sources are. So the copies
of the nodes of the chains of the targets are the copies whose own nodes lie on these chains.

* `RData.levelLen_real`: an edge of finite length joins two real nodes.
* `RData.dart_nbr_in`, `RData.dart_nbr_out`: the neighbours of a dart node across edges of finite
  length.
* `RData.chain_copy_node`: the copy of a node of the parent chain of a copy is the copy of a copy node
  of that chain.
* `RData.marked_copy_iff`: a copy is the copy of a node of the chain of a target exactly when its own
  node lies on the chain of a target.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  (lam : S.Tok → ℕ) (M : ℕ)

theorem levelLen_real {x y : Fin (n * (n * 21))} (h : S.levelLen hN lam M x y ≠ ⊤) :
    (S.levelPad hN).IsReal x ∧ (S.levelPad hN).IsReal y := by
  by_contra hc
  apply h
  unfold levelLen
  exact ite_eq_right_iff.2 (fun h' => absurd h' hc)

theorem dart_nbr_in {b : Fin (n * (n * 21))} {d : S.HD}
    (h : (S.levelNet hN).G.Adj b ((S.levelPad hN).ι (.inr d)))
    (hf : S.levelLen hN lam M b ((S.levelPad hN).ι (.inr d)) ≠ ⊤) :
    b = (S.levelPad hN).ι (.inl (S.hRot.tail d)) ∨ b = (S.levelPad hN).ι (.inr (S.hrev d)) := by
  rcases padNet_adj_cases h with ⟨x, y, rfl, hy, hxy⟩ | ⟨hb, -⟩ | ⟨ha, -⟩
  · obtain rfl := (S.levelPad hN).ι_injective hy
    rcases x with w | d₀
    · obtain rfl : S.hRot.tail d = w := hxy
      exact .inl rfl
    · have e : d = S.hRot.rev d₀ := hxy
      refine .inr ?_
      have : d₀ = S.hrev d := by
        rw [e]
        obtain ⟨d₁, b₁⟩ := d₀
        simp [show S.hRot.rev (d₁, b₁) = S.hrev (d₁, b₁) from rfl, hrev]
      rw [this]
  · exact absurd (S.levelLen_real hN lam M hf).1 hb
  · exact absurd (S.levelLen_real hN lam M hf).2 ha

theorem dart_nbr_out {a : Fin (n * (n * 21))} {d : S.HD}
    (h : (S.levelNet hN).G.Adj ((S.levelPad hN).ι (.inr d)) a)
    (hf : S.levelLen hN lam M ((S.levelPad hN).ι (.inr d)) a ≠ ⊤) :
    a = (S.levelPad hN).ι (.inl (S.hRot.tail d)) ∨ a = (S.levelPad hN).ι (.inr (S.hrev d)) := by
  rcases padNet_adj_cases h with ⟨x, y, hx, rfl, hxy⟩ | ⟨hb, -⟩ | ⟨ha, -⟩
  · obtain rfl := (S.levelPad hN).ι_injective hx
    rcases y with w | d'
    · obtain rfl : S.hRot.tail d = w := hxy
      exact .inl rfl
    · obtain rfl : d' = S.hRot.rev d := hxy
      exact .inr rfl
  · exact absurd (S.levelLen_real hN lam M hf).1 hb
  · exact absurd (S.levelLen_real hN lam M hf).2 ha

/-- **Chains through copy nodes.** For an output of the oracle on the network of a level whose
sources are copy nodes, the copy of a node of the parent chain of a copy node of finite distance is
the copy of a copy node of that chain. -/
theorem chain_copy_node (ψ : Fin (n * (n * 21)) → ℕ∞)
    (r : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (hr : (S.levelNet hN).ExactSpec (S.levelLen hN lam M) ψ r)
    (hroot : ∀ z, ψ z ≠ ⊤ → ∃ u, z = (S.levelPad hN).ι (.inl u)) {w : S.hRot.Vertex}
    (hfin : (r ((S.levelPad hN).ι (.inl w))).1 ≠ ⊤) {y : Fin (n * (n * 21))}
    (hy : ∃ i, (Net.parOf r)^[i] ((S.levelPad hN).ι (.inl w)) = y) :
    ∃ u, (∃ i, (Net.parOf r)^[i] ((S.levelPad hN).ι (.inl w)) = (S.levelPad hN).ι (.inl u)) ∧
      S.copyAt hN y = S.vcopy u := by
  obtain ⟨k, h1, h2, h3, h4⟩ := hr.chain _ hfin
  obtain ⟨rank, hrank⟩ := hr.parent
  have hrk : ∀ i < k, rank ((Net.parOf r)^[i + 1] ((S.levelPad hN).ι (.inl w))) <
      rank ((Net.parOf r)^[i] ((S.levelPad hN).ι (.inl w))) := fun i hi => by
    rcases hrank ((Net.parOf r)^[i] ((S.levelPad hN).ι (.inl w))) with ⟨p, hp, -, -, -, hlt⟩ | ⟨hn, -⟩
    · rw [(h3 i hi).1, Option.some.injEq] at hp
      subst hp
      exact hlt
    · rw [(h3 i hi).1] at hn
      cases hn
  have hsum : (∑ i ∈ Finset.range k, S.levelLen hN lam M ((Net.parOf r)^[i + 1] ((S.levelPad hN).ι (.inl w)))
      ((Net.parOf r)^[i] ((S.levelPad hN).ι (.inl w)))) ≠ ⊤ := fun e => hfin (by rw [← h4, e, add_top])
  have hfe : ∀ i < k, S.levelLen hN lam M ((Net.parOf r)^[i + 1] ((S.levelPad hN).ι (.inl w)))
      ((Net.parOf r)^[i] ((S.levelPad hN).ι (.inl w))) ≠ ⊤ := fun i hi =>
    ENat.sum_ne_top.1 hsum i (Finset.mem_range.2 hi)
  have hψ : ψ ((Net.parOf r)^[k] ((S.levelPad hN).ι (.inl w))) ≠ ⊤ := fun e =>
    hfin (by rw [← h4, e, top_add])
  have key : ∀ i ≤ k, ∃ u, (∃ j, (Net.parOf r)^[j] ((S.levelPad hN).ι (.inl w)) = (S.levelPad hN).ι (.inl u)) ∧
      S.copyAt hN ((Net.parOf r)^[i] ((S.levelPad hN).ι (.inl w))) = S.vcopy u := by
    intro i hik
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact ⟨w, ⟨0, rfl⟩, S.copyAt_ι hN _⟩
    rcases Nat.lt_or_ge i k with hik' | hik'
    · have hreal := (S.levelLen_real hN lam M (hfe i hik')).2
      generalize hyy : (Net.parOf r)^[i] ((S.levelPad hN).ι (.inl w)) = y at hreal ⊢
      rcases hb : (S.levelPad hN).back y with u | d
      · have hy' : y = (S.levelPad hN).ι (.inl u) := hb ▸ hreal
        refine ⟨u, ⟨i, hyy.trans hy'⟩, ?_⟩
        rw [hy', S.copyAt_ι]
        rfl
      · have hy' : y = (S.levelPad hN).ι (.inr d) := hb ▸ hreal
        have ei : i - 1 + 1 = i := by omega
        have hin := S.dart_nbr_in hN lam M (b := (Net.parOf r)^[i + 1] ((S.levelPad hN).ι (.inl w)))
          (d := d) (by rw [← hy', ← hyy]; exact (h3 i hik').2) (by rw [← hy', ← hyy]; exact hfe i hik')
        have hadj := (h3 (i - 1) (by omega)).2
        have hfo := hfe (i - 1) (by omega)
        rw [ei, hyy, hy'] at hadj hfo
        have hout := S.dart_nbr_out hN lam M hadj hfo
        have hr1 := hrk i hik'
        have hr2 := hrk (i - 1) (by omega)
        rw [ei] at hr2
        have hct : S.copyAt hN y = S.vcopy (S.hRot.tail d) := by
          rw [hy', S.copyAt_ι]
          exact (S.vcopy_tail d).symm
        rcases hin with h | h
        · exact ⟨_, ⟨i + 1, h⟩, hct⟩
        rcases hout with h' | h'
        · exact ⟨_, ⟨i - 1, h'⟩, hct⟩
        · exfalso
          rw [h.trans h'.symm] at hr1
          omega
    · obtain rfl : i = k := by omega
      obtain ⟨u, hu⟩ := hroot _ hψ
      refine ⟨u, ⟨i, hu⟩, ?_⟩
      rw [hu, S.copyAt_ι]
      rfl
  obtain ⟨i, rfl⟩ := hy
  rcases Nat.lt_or_ge i k with hik | hik
  · exact key i hik.le
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hik
    rw [Net.parOf_iterate_root h1 m]
    exact key k le_rfl

/-- **Marked copies.** For an output of the oracle on the network of a level whose sources are copy
nodes, and targets that are copy nodes of finite distance, a copy is the copy of a node of the chain
of a target exactly when its own node lies on the chain of a target. -/
theorem marked_copy_iff (ψ : Fin (n * (n * 21)) → ℕ∞)
    (r : Fin (n * (n * 21)) → ℕ∞ × Option (Fin (n * (n * 21))))
    (hr : (S.levelNet hN).ExactSpec (S.levelLen hN lam M) ψ r)
    (hroot : ∀ z, ψ z ≠ ⊤ → ∃ u, z = (S.levelPad hN).ι (.inl u)) (isT : Fin (n * (n * 21)) → Bool)
    (hT : ∀ t, isT t = true → (r t).1 ≠ ⊤ ∧ ∃ w, t = (S.levelPad hN).ι (.inl w)) (u : S.hRot.Vertex) :
    (∃ y, (∃ t i, isT t = true ∧ (Net.parOf r)^[i] t = y) ∧ S.copyAt hN y = S.vcopy u) ↔
      ∃ t i, isT t = true ∧ (Net.parOf r)^[i] t = (S.levelPad hN).ι (.inl u) := by
  constructor
  · rintro ⟨y, ⟨t, i, ht, rfl⟩, hyu⟩
    obtain ⟨hf, w, rfl⟩ := hT t ht
    obtain ⟨u', ⟨j, hj⟩, hc⟩ := S.chain_copy_node hN lam M ψ r hr hroot hf ⟨i, rfl⟩
    obtain rfl : u' = u := S.vcopy_injective (hc.symm.trans hyu)
    exact ⟨_, j, ht, hj⟩
  · rintro h
    exact ⟨_, h, S.copyAt_ι hN _⟩

end RData

end RotSystem

end SsspFlow
