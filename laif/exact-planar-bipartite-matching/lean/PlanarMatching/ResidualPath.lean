import PlanarMatching.Hungarian

/-!
# From a path of the residual digraph to the flip

`notes/MATCHING.md`, Section 5. The residual digraph on `A ⊕ B` has an arc from `a` to `b` for an edge `(a, b)` off
the matching that satisfies `T` (in use: an edge that is tight for the updated duals), and an arc from `b` to `a` for an
edge `(a, b)` of the matching. A path from `h` alternates `h, b₁, a₁, b₂, a₂, …`, and `pairsOf` reads off the matched
pairs `(aᵢ, bᵢ)` in order.

* `pairsOf_spec`, `pairsOf_nodup`: the pairs are matched, consecutive pairs and the start satisfy `T` across, and a
  simple path gives distinct pairs: the hypotheses of `flip`.
* `end_inl`, `end_inr`: the path ends at the last `a` of the pairs, or at a vertex `b` joined to it by an arc.
* `insertion_path`: the insertion of `insertion`, with the list `L` replaced by a simple path of the residual digraph
  from `h` that ends at a vertex of `A` with updated dual zero or at a free vertex of `B`.
-/

namespace PlanarMatching

open Finset

variable {A B : Type*}

/-- The residual digraph of the matching `M` for the edge condition `T`. -/
def Res (M : Finset (A × B)) (T : A × B → Prop) : A ⊕ B → A ⊕ B → Prop
  | Sum.inl a, Sum.inr b => (a, b) ∉ M ∧ T (a, b)
  | Sum.inr b, Sum.inl a => (a, b) ∈ M
  | Sum.inl _, Sum.inl _ => False
  | Sum.inr _, Sum.inr _ => False

/-- The matched pairs of an alternating sequence `b₁, a₁, b₂, a₂, …`. -/
def pairsOf : List (A ⊕ B) → List (A × B)
  | [] => []
  | [_] => []
  | Sum.inl _ :: _ :: _ => []
  | Sum.inr _ :: Sum.inr _ :: _ => []
  | Sum.inr b :: Sum.inl a :: rest => (a, b) :: pairsOf rest

/-- The last vertex of `A` of an alternating sequence that follows `c`. -/
def lastA (c : A) : List (A ⊕ B) → A
  | [] => c
  | [_] => c
  | Sum.inl _ :: _ :: _ => c
  | Sum.inr _ :: Sum.inr _ :: _ => c
  | Sum.inr _ :: Sum.inl a :: rest => lastA a rest

theorem pairsOf_mem : ∀ {Q : List (A ⊕ B)} {p : A × B}, p ∈ pairsOf Q → Sum.inl p.1 ∈ Q
  | [], _, h => by simp [pairsOf] at h
  | [_], _, h => by simp [pairsOf] at h
  | Sum.inl _ :: _ :: _, _, h => by simp [pairsOf] at h
  | Sum.inr _ :: Sum.inr _ :: _, _, h => by simp [pairsOf] at h
  | Sum.inr _ :: Sum.inl a :: rest, p, h => by
    simp only [pairsOf, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (pairsOf_mem h))

theorem pairsOf_nodup : ∀ {Q : List (A ⊕ B)}, Q.Nodup → (pairsOf Q).Nodup
  | [], _ => by simp [pairsOf]
  | [_], _ => by simp [pairsOf]
  | Sum.inl _ :: _ :: _, _ => by simp [pairsOf]
  | Sum.inr _ :: Sum.inr _ :: _, _ => by simp [pairsOf]
  | Sum.inr _ :: Sum.inl a :: rest, h => by
    rw [List.nodup_cons, List.nodup_cons] at h
    simp only [pairsOf, List.nodup_cons]
    exact ⟨fun hm => h.2.1 (pairsOf_mem hm), pairsOf_nodup h.2.2⟩

/-- The pairs of a path of the residual digraph that follows `c` are matched, and consecutive pairs, as well as `c` and
the first pair, satisfy `T` across. -/
theorem pairsOf_spec {M : Finset (A × B)} {T : A × B → Prop} :
    ∀ (c : A) (Q : List (A ⊕ B)), (Sum.inl c :: Q).IsChain (Res M T) →
      (∀ p ∈ pairsOf Q, p ∈ M) ∧ (pairsOf Q).IsChain (fun p q => T (p.1, q.2)) ∧
        ∀ p ∈ (pairsOf Q).head?, T (c, p.2)
  | _, [], _ => by simp [pairsOf]
  | _, [_], _ => by simp [pairsOf]
  | _, Sum.inl _ :: _ :: _, _ => by simp [pairsOf]
  | _, Sum.inr _ :: Sum.inr _ :: _, _ => by simp [pairsOf]
  | c, Sum.inr b :: Sum.inl a :: rest, h => by
    rw [List.isChain_cons_cons, List.isChain_cons_cons] at h
    obtain ⟨h1, h2, h3⟩ := h
    simp only [Res] at h1 h2
    obtain ⟨i1, i2, i3⟩ := pairsOf_spec a rest h3
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      simp only [pairsOf, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact h2
      · exact i1 p hp
    · simp only [pairsOf]
      cases hq : pairsOf rest with
      | nil => simp
      | cons q t =>
        rw [hq] at i2 i3
        rw [List.isChain_cons_cons]
        exact ⟨i3 q (by simp), i2⟩
    · intro p hp
      simp only [pairsOf, List.head?_cons, Option.mem_def, Option.some.injEq] at hp
      subst hp
      exact h1.2

theorem lastA_eq : ∀ (c : A) (Q : List (A ⊕ B)), lastA c Q = ((pairsOf Q).getLast?.map Prod.fst).getD c
  | _, [] => rfl
  | _, [_] => rfl
  | _, Sum.inl _ :: _ :: _ => rfl
  | _, Sum.inr _ :: Sum.inr _ :: _ => rfl
  | c, Sum.inr b :: Sum.inl a :: rest => by
    simp only [lastA, pairsOf]
    rw [lastA_eq a rest]
    cases hq : pairsOf rest with
    | nil => rfl
    | cons q t =>
      rw [List.getLast?_cons_cons, List.getLast?_eq_some_getLast (List.cons_ne_nil q t)]
      rfl

/-- A path of the residual digraph that ends in `A` ends at the last `a` of its pairs. -/
theorem end_inl {M : Finset (A × B)} {T : A × B → Prop} :
    ∀ (c : A) (Q : List (A ⊕ B)), (Sum.inl c :: Q).IsChain (Res M T) → ∀ e,
      (Sum.inl c :: Q).getLast? = some (Sum.inl e) → e = lastA c Q
  | c, [], _, e, h => by simp at h; simp [lastA, h]
  | c, [x], hc, e, h => by
    simp at h
    subst h
    simp [Res] at hc
  | c, Sum.inl _ :: _ :: _, hc, _, _ => by simp [List.isChain_cons_cons, Res] at hc
  | c, Sum.inr _ :: Sum.inr _ :: _, hc, _, _ => by simp [List.isChain_cons_cons, Res] at hc
  | c, Sum.inr b :: Sum.inl a :: rest, hc, e, h => by
    rw [List.isChain_cons_cons, List.isChain_cons_cons] at hc
    simp only [lastA]
    apply end_inl a rest hc.2.2 e
    rwa [List.getLast?_cons_cons, List.getLast?_cons_cons] at h

/-- A path of the residual digraph that ends in `B` ends at a vertex joined to the last `a` of its pairs by an arc. -/
theorem end_inr {M : Finset (A × B)} {T : A × B → Prop} :
    ∀ (c : A) (Q : List (A ⊕ B)), (Sum.inl c :: Q).IsChain (Res M T) → ∀ b,
      (Sum.inl c :: Q).getLast? = some (Sum.inr b) → (lastA c Q, b) ∉ M ∧ T (lastA c Q, b)
  | c, [], _, b, h => by simp at h
  | c, [x], hc, b, h => by
    simp at h
    subst h
    simpa [Res, lastA] using hc
  | c, Sum.inl _ :: _ :: _, hc, _, _ => by simp [List.isChain_cons_cons, Res] at hc
  | c, Sum.inr _ :: Sum.inr _ :: _, hc, _, _ => by simp [List.isChain_cons_cons, Res] at hc
  | c, Sum.inr b' :: Sum.inl a :: rest, hc, b, h => by
    rw [List.isChain_cons_cons, List.isChain_cons_cons] at hc
    simp only [lastA]
    apply end_inr a rest hc.2.2 b
    rwa [List.getLast?_cons_cons, List.getLast?_cons_cons] at h

variable [DecidableEq A] [DecidableEq B]

/-- One insertion along a simple path of the residual digraph from `h`, whose arcs off the matching are tight for the
updated duals, and which ends at a vertex of `A` with updated dual zero or at a free vertex of `B`. -/
theorem insertion_path [Fintype A] [Fintype B] {E : Set (A × B)} {w : A × B → ℤ} {y : A → ℤ} {z : B → ℤ}
    {M : Finset (A × B)} {h : A} (hF : Feasible E w y z) (hsub : ∀ e ∈ M, e ∈ E) (hM : IsMatching M) (hh : FreeA M h)
    (htight : ∀ e ∈ M, y e.1 + z e.2 = w e) (hfreeA : ∀ a, a ≠ h → FreeA M a → y a = 0)
    (hfreeB : ∀ b, FreeB M b → z b = 0)
    {da : A → ℤ} {db : B → ℤ} {δ : ℤ}
    (harc : ∀ e ∈ E, e ∉ M → db e.2 ≤ da e.1 + (y e.1 + z e.2 - w e))
    (hmatched : ∀ e ∈ M, da e.1 = db e.2)
    (hδA : ∀ a, δ ≤ da a + y a) (hδB : ∀ b, FreeB M b → δ ≤ db b)
    (P : List (A ⊕ B)) (hP : P.Nodup) (h0 : P.head? = some (Sum.inl h))
    (hch : P.IsChain (Res M fun e => e ∈ E ∧
      (y e.1 - max 0 (δ - da e.1)) + (z e.2 + max 0 (δ - db e.2)) = w e))
    (hend : (∃ e, P.getLast? = some (Sum.inl e) ∧ y e - max 0 (δ - da e) = 0) ∨
      ∃ b, P.getLast? = some (Sum.inr b) ∧ FreeB M b) :
    ∃ M', IsMatching M' ∧ (∀ e ∈ M', e ∈ E) ∧ ∀ N : Finset (A × B), IsMatching N → (∀ e ∈ N, e ∈ E) →
      ∑ e ∈ N, w e ≤ ∑ e ∈ M', w e := by
  obtain ⟨Q, rfl⟩ : ∃ Q, P = Sum.inl h :: Q := by
    cases P with
    | nil => simp at h0
    | cons x Q =>
      simp only [List.head?_cons, Option.some.injEq] at h0
      exact ⟨Q, by rw [h0]⟩
  obtain ⟨s1, s2, s3⟩ := pairsOf_spec h Q hch
  refine insertion hF hsub hM hh htight hfreeA hfreeB harc hmatched hδA hδB (pairsOf Q)
    (pairsOf_nodup (List.nodup_cons.mp hP).2) s1 s2 s3 ?_
  rw [← lastA_eq h Q]
  rcases hend with ⟨e, he, hy⟩ | ⟨b, hb, hfree⟩
  · left
    rw [← end_inl h Q hch e he]
    exact hy
  · right
    obtain ⟨-, hT⟩ := end_inr h Q hch b hb
    exact ⟨b, hfree, hT.1, hT.2⟩

end PlanarMatching
