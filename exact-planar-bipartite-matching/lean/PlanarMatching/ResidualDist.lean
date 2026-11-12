import PlanarMatching.ResidualPath

/-!
# The dual update from distances

`notes/MATCHING.md`, Section 5. The arcs of the residual digraph have the lengths `rlen`: `y a + z b - w (a, b)` on an
arc `a → b` off the matching and `0` on an arc `b → a` of the matching. Let `d` be distances from `h`: they satisfy the
inequality of every arc, and every vertex other than `h` with `d < C` has an in-arc that attains its value. The update
uses `d` capped at `C`, and `δ ≤ C` is at most every `d b` for a free `b` and every `d a + y a`.

* `insertion_dist`: the capped distances satisfy the hypotheses of the update; along a simple path from `h` whose
  arcs are shortest, every vertex has `d ≤ δ` and every arc off the matching is tight after the update; so, if the path
  ends where `δ` is attained, the flip along it gives a matching of largest weight.
-/

namespace PlanarMatching

open Finset

variable {A B : Type*}

/-- The lengths of the residual arcs. -/
def rlen (w : A × B → ℤ) (y : A → ℤ) (z : B → ℤ) : A ⊕ B → A ⊕ B → ℤ
  | Sum.inl a, Sum.inr b => y a + z b - w (a, b)
  | Sum.inl _, Sum.inl _ => 0
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr _, Sum.inr _ => 0

theorem rlen_nonneg {E : Set (A × B)} {w : A × B → ℤ} {y : A → ℤ} {z : B → ℤ} {M : Finset (A × B)}
    (hF : Feasible E w y z) : ∀ {u v : A ⊕ B}, Res M (· ∈ E) u v → 0 ≤ rlen w y z u v
  | Sum.inl a, Sum.inr b, h => by
    have := hF.cover (a, b) h.2
    dsimp only at this
    simp only [rlen]
    omega
  | Sum.inl _, Sum.inl _, _ => le_rfl
  | Sum.inr _, Sum.inl _, _ => le_rfl
  | Sum.inr _, Sum.inr _, _ => le_rfl

theorem chain_le_last {α : Type*} {f : α → ℤ} : ∀ {l : List α}, l.IsChain (fun u v => f u ≤ f v) →
    ∀ x ∈ l, ∀ t ∈ l.getLast?, f x ≤ f t
  | [], _, x, hx, _, _ => by simp at hx
  | [a], _, x, hx, t, ht => by
    simp only [List.mem_singleton] at hx
    simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at ht
    rw [hx, ht]
  | a :: b :: l, h, x, hx, t, ht => by
    rw [List.isChain_cons_cons] at h
    rw [List.getLast?_cons_cons] at ht
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1.trans (chain_le_last h.2 b List.mem_cons_self t ht)
    · exact chain_le_last h.2 x hx t ht

theorem chain_and {α : Type*} {R : α → α → Prop} {p : α → Prop} : ∀ {l : List α}, l.IsChain R →
    (∀ x ∈ l, p x) → l.IsChain (fun u v => R u v ∧ p u ∧ p v)
  | [], _, _ => by simp
  | [_], _, _ => by simp
  | a :: b :: l, h, hp => by
    rw [List.isChain_cons_cons] at h ⊢
    exact ⟨⟨h.1, hp a List.mem_cons_self, hp b (List.mem_cons_of_mem _ List.mem_cons_self)⟩,
      chain_and h.2 fun x hx => hp x (List.mem_cons_of_mem _ hx)⟩

variable [DecidableEq A] [DecidableEq B]

/-- One insertion from distances: capped distances give the update, a simple path from `h` of shortest arcs that
ends where `δ` is attained gives the flip, and the result is a matching of largest weight. -/
theorem insertion_dist [Fintype A] [Fintype B] {E : Set (A × B)} {w : A × B → ℤ} {y : A → ℤ} {z : B → ℤ}
    {M : Finset (A × B)} {h : A} (hF : Feasible E w y z) (hsub : ∀ e ∈ M, e ∈ E) (hM : IsMatching M) (hh : FreeA M h)
    (htight : ∀ e ∈ M, y e.1 + z e.2 = w e) (hfreeA : ∀ a, a ≠ h → FreeA M a → y a = 0)
    (hfreeB : ∀ b, FreeB M b → z b = 0)
    {d : A ⊕ B → ℤ} {C δ : ℤ}
    (hdarc : ∀ u v, Res M (· ∈ E) u v → d v ≤ d u + rlen w y z u v)
    (hdbell : ∀ v, v ≠ Sum.inl h → d v < C → ∃ u, Res M (· ∈ E) u v ∧ d u + rlen w y z u v ≤ d v)
    (hδC : δ ≤ C) (hδA : ∀ a, δ ≤ d (Sum.inl a) + y a) (hδB : ∀ b, FreeB M b → δ ≤ d (Sum.inr b))
    (P : List (A ⊕ B)) (hP : P.Nodup) (h0 : P.head? = some (Sum.inl h))
    (hch : P.IsChain fun u v => Res M (· ∈ E) u v ∧ d v = d u + rlen w y z u v)
    (hend : (∃ e, P.getLast? = some (Sum.inl e) ∧ δ = d (Sum.inl e) + y e) ∨
      ∃ b, P.getLast? = some (Sum.inr b) ∧ FreeB M b ∧ d (Sum.inr b) ≤ δ) :
    ∃ M', IsMatching M' ∧ (∀ e ∈ M', e ∈ E) ∧ ∀ N : Finset (A × B), IsMatching N → (∀ e ∈ N, e ∈ E) →
      ∑ e ∈ N, w e ≤ ∑ e ∈ M', w e := by
  -- the hypotheses of the update, for the capped distances
  have harc : ∀ e ∈ E, e ∉ M →
      min (d (Sum.inr e.2)) C ≤ min (d (Sum.inl e.1)) C + (y e.1 + z e.2 - w e) := by
    intro e he hm
    have h1 := hdarc (Sum.inl e.1) (Sum.inr e.2) ⟨hm, he⟩
    have h2 := hF.cover e he
    simp only [rlen, Prod.mk.eta] at h1
    omega
  have hmatched : ∀ e ∈ M, min (d (Sum.inl e.1)) C = min (d (Sum.inr e.2)) C := by
    intro e he
    have h1 := hdarc (Sum.inr e.2) (Sum.inl e.1) he
    simp only [rlen] at h1
    by_cases hc : d (Sum.inl e.1) < C
    · have hne : (Sum.inl e.1 : A ⊕ B) ≠ Sum.inl h := fun hx => hh e he (Sum.inl_injective hx)
      obtain ⟨u, hu, hle⟩ := hdbell _ hne hc
      cases u with
      | inl _ => simp [Res] at hu
      | inr b' =>
        simp only [Res] at hu
        have hb : b' = e.2 := congrArg Prod.snd (hM.1 _ hu _ he rfl)
        subst hb
        simp only [rlen] at hle
        omega
    · omega
  have hδA' : ∀ a, δ ≤ min (d (Sum.inl a)) C + y a := fun a => by
    have := hδA a
    have := hF.nonnegA a
    omega
  have hδB' : ∀ b, FreeB M b → δ ≤ min (d (Sum.inr b)) C := fun b hb => by
    have := hδB b hb
    omega
  -- every vertex of the path has `d ≤ δ`
  have hmono : P.IsChain (fun u v => d u ≤ d v) := hch.imp fun u v ⟨hr, he⟩ => by
    have := rlen_nonneg hF hr
    omega
  have hlast : ∀ t ∈ P.getLast?, d t ≤ δ := by
    intro t ht
    rcases hend with ⟨e, he, hδ⟩ | ⟨b, hb, -, hbd⟩
    · rw [he, Option.mem_some_iff] at ht
      subst ht
      have := hF.nonnegA e
      omega
    · rw [hb, Option.mem_some_iff] at ht
      subst ht
      exact hbd
  have hall : ∀ x ∈ P, d x ≤ δ := by
    intro x hx
    cases hq : P.getLast? with
    | none =>
      rw [List.getLast?_eq_none_iff] at hq
      subst hq
      simp at hx
    | some t =>
      exact (chain_le_last hmono x hx t (by rw [hq]; rfl)).trans (hlast t (by rw [hq]; rfl))
  -- the arcs of the path are arcs of tight edges after the update
  have hch' : P.IsChain (Res M fun e => e ∈ E ∧
      (y e.1 - max 0 (δ - min (d (Sum.inl e.1)) C)) + (z e.2 + max 0 (δ - min (d (Sum.inr e.2)) C)) = w e) :=
    (chain_and hch hall).imp fun u v ⟨⟨hr, he⟩, hu, hv⟩ => by
      cases u with
      | inr b =>
        cases v with
        | inl _ => exact hr
        | inr _ => simp [Res] at hr
      | inl a =>
        cases v with
        | inl _ => simp [Res] at hr
        | inr b =>
          obtain ⟨hm, hE⟩ := hr
          refine ⟨hm, hE, ?_⟩
          simp only [rlen] at he
          exact tight_after (w := w) (y := y) (z := z) (da := fun a => min (d (Sum.inl a)) C)
            (db := fun b => min (d (Sum.inr b)) C) (δ := δ) (e := (a, b))
            (by show min (d (Sum.inr b)) C = min (d (Sum.inl a)) C + (y a + z b - w (a, b)); omega)
            (by show min (d (Sum.inl a)) C ≤ δ; omega) (by show min (d (Sum.inr b)) C ≤ δ; omega)
  refine insertion_path (da := fun a => min (d (Sum.inl a)) C) (db := fun b => min (d (Sum.inr b)) C) (δ := δ)
    hF hsub hM hh htight hfreeA hfreeB harc hmatched hδA' hδB' P hP h0 hch' ?_
  rcases hend with ⟨e, he, hδ⟩ | ⟨b, hb, hfree, -⟩
  · left
    refine ⟨e, he, ?_⟩
    have := hF.nonnegA e
    show y e - max 0 (δ - min (d (Sum.inl e)) C) = 0
    omega
  · exact Or.inr ⟨b, hb, hfree⟩

end PlanarMatching
