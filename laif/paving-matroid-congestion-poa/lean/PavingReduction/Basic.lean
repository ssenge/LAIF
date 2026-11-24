import Mathlib

/-!
# Reduction of rank-2 paving matroid congestion games to finitely many types

A loopless matroid of rank 2 on a finite set R of resources is given by its parallel classes `cls : R → ℕ`: the
bases are the pairs of resources from different classes. For rank 2 these are exactly the paving matroids. Each of
N players picks a basis, written as an ordered pair. Resource e has the delay a e * x + b e under load x, and the
social cost of a profile is the sum of load times delay over all resources.

* `reduction`: if a bound cost F ≤ r * cost H holds at every equilibrium F and every profile H of every game in
  which each resource is used by F or H and each two classes are joined by a basis of F or H, then it holds for
  every game.
* `card_le`: such a game has at most 4N resources. `choose_classes_le`: with k classes, C(k, 2) ≤ 2N.
  `classes_le_four`: k ≤ 4 for N = 3.
-/

open Finset

namespace PavingReduction

section Game

variable {R : Type} [Fintype R] [DecidableEq R] {N : ℕ}

/-- How often the strategy s uses resource e. -/
def uses (s : R × R) (e : R) : ℕ := (if s.1 = e then 1 else 0) + (if s.2 = e then 1 else 0)

/-- Number of players on resource e. -/
def load (P : Fin N → R × R) (e : R) : ℕ := ∑ i, uses (P i) e

/-- Affine delay of resource e under load x. -/
def delay (a b : R → ℚ) (e : R) (x : ℕ) : ℚ := a e * x + b e

/-- Social cost: the sum of load times delay over all resources. -/
def cost (a b : R → ℚ) (P : Fin N → R × R) : ℚ := ∑ e, (load P e : ℚ) * delay a b e (load P e)

/-- Cost of player i. -/
def own (a b : R → ℚ) (P : Fin N → R × R) (i : Fin N) : ℚ :=
  delay a b (P i).1 (load P (P i).1) + delay a b (P i).2 (load P (P i).2)

/-- Cost of player i after switching alone to the basis (g, h). -/
def dev (a b : R → ℚ) (P : Fin N → R × R) (i : Fin N) (g h : R) : ℚ :=
  delay a b g (load P g + 1 - uses (P i) g) + delay a b h (load P h + 1 - uses (P i) h)

/-- Every player picks a basis: two resources from different classes. -/
def Valid (cls : R → ℕ) (P : Fin N → R × R) : Prop := ∀ i, cls (P i).1 ≠ cls (P i).2

/-- Pure equilibrium: no player lowers its cost by switching alone to another basis. -/
def IsNE (cls : R → ℕ) (a b : R → ℚ) (P : Fin N → R × R) : Prop :=
  ∀ i g h, cls g ≠ cls h → own a b P i ≤ dev a b P i g h

/-- Resource e is used by F or by H. -/
def Used (F H : Fin N → R × R) (e : R) : Prop :=
  ∃ i, (F i).1 = e ∨ (F i).2 = e ∨ (H i).1 = e ∨ (H i).2 = e

/-- The basis s joins the classes A and B. -/
def JoinsC (cls : R → ℕ) (s : R × R) (A B : ℕ) : Prop :=
  (cls s.1 = A ∧ cls s.2 = B) ∨ (cls s.1 = B ∧ cls s.2 = A)

/-- Every two classes are joined by a basis of F or H. -/
def Joined (cls : R → ℕ) (F H : Fin N → R × R) : Prop :=
  ∀ e f, cls e ≠ cls f → ∃ i, JoinsC cls (F i) (cls e) (cls f) ∨ JoinsC cls (H i) (cls e) (cls f)

end Game

/-- The bound r holds at every equilibrium F, against every profile H, of every game with N players. -/
def Bound (N : ℕ) (r : ℚ) : Prop :=
  ∀ (R : Type) [Fintype R] [DecidableEq R] (cls : R → ℕ) (a b : R → ℚ) (F H : Fin N → R × R),
    (∀ e, 0 ≤ a e) → (∀ e, 0 ≤ b e) → Valid cls F → Valid cls H → IsNE cls a b F →
    cost a b F ≤ r * cost a b H

/-- The bound r holds in every reduced game: each resource is used by F or H, and each two classes are joined by a
basis of F or H. -/
def ReducedBound (N : ℕ) (r : ℚ) : Prop :=
  ∀ (R : Type) [Fintype R] [DecidableEq R] (cls : R → ℕ) (a b : R → ℚ) (F H : Fin N → R × R),
    (∀ e, 0 ≤ a e) → (∀ e, 0 ≤ b e) → Valid cls F → Valid cls H → IsNE cls a b F →
    (∀ e, Used F H e) → Joined cls F H → cost a b F ≤ r * cost a b H

section Merge

variable {R : Type} [Fintype R] [DecidableEq R] {N : ℕ}

/-- Merge class B into class A. -/
def merge (cls : R → ℕ) (A B : ℕ) : R → ℕ := fun x => if cls x = B then A else cls x

/-- A profile with no basis joining A and B stays a profile after merging. -/
theorem valid_merge (cls : R → ℕ) (A B : ℕ) (P : Fin N → R × R) (hv : Valid cls P)
    (hno : ∀ i, ¬ JoinsC cls (P i) A B) : Valid (merge cls A B) P := by
  intro i
  have h1 := hv i
  have h2 := hno i
  unfold JoinsC at h2
  unfold merge
  split_ifs <;> omega

/-- Merging only removes bases, so an equilibrium stays an equilibrium. -/
theorem ne_merge (cls : R → ℕ) (A B : ℕ) (a b : R → ℚ) (P : Fin N → R × R) (h : IsNE cls a b P) :
    IsNE (merge cls A B) a b P := by
  intro i g k hgk
  apply h i g k
  intro heq
  apply hgk
  simp only [merge, heq]

/-- Merging two classes lowers the number of classes. -/
theorem card_merge (cls : R → ℕ) (e f : R) (hef : cls e ≠ cls f) :
    (univ.image (merge cls (cls e) (cls f))).card < (univ.image cls).card := by
  have hsub : univ.image (merge cls (cls e) (cls f)) ⊆ (univ.image cls).erase (cls f) := by
    intro x hx
    rw [mem_image] at hx
    obtain ⟨y, -, rfl⟩ := hx
    rw [mem_erase, mem_image]
    unfold merge
    split_ifs with hy
    · exact ⟨hef, e, mem_univ _, rfl⟩
    · exact ⟨hy, y, mem_univ _, rfl⟩
  have hf : cls f ∈ univ.image cls := mem_image.2 ⟨f, mem_univ _, rfl⟩
  calc (univ.image (merge cls (cls e) (cls f))).card ≤ ((univ.image cls).erase (cls f)).card :=
        card_le_card hsub
    _ < (univ.image cls).card := card_erase_lt_of_mem hf

end Merge

/-- Step 2: merging classes reduces games that use every resource to reduced games. -/
theorem used_bound {N : ℕ} {r : ℚ} (hred : ReducedBound N r) (R : Type) [Fintype R] [DecidableEq R] :
    ∀ (k : ℕ) (cls : R → ℕ) (a b : R → ℚ) (F H : Fin N → R × R), (univ.image cls).card ≤ k →
      (∀ e, 0 ≤ a e) → (∀ e, 0 ≤ b e) → Valid cls F → Valid cls H → IsNE cls a b F →
      (∀ e, Used F H e) → cost a b F ≤ r * cost a b H := by
  intro k
  induction k with
  | zero =>
    intro cls a b F H hk ha hb hF hH hNE hU
    apply hred R cls a b F H ha hb hF hH hNE hU
    intro e
    have hm : cls e ∈ univ.image cls := mem_image.2 ⟨e, mem_univ _, rfl⟩
    have := card_pos.2 ⟨_, hm⟩
    omega
  | succ k ih =>
    intro cls a b F H hk ha hb hF hH hNE hU
    by_cases hJ : Joined cls F H
    · exact hred R cls a b F H ha hb hF hH hNE hU hJ
    · unfold Joined at hJ
      push_neg at hJ
      obtain ⟨e, f, hef, hno⟩ := hJ
      have hlt := card_merge cls e f hef
      exact ih (merge cls (cls e) (cls f)) a b F H (by omega) ha hb
        (valid_merge cls _ _ F hF fun i => (hno i).1) (valid_merge cls _ _ H hH fun i => (hno i).2)
        (ne_merge cls _ _ a b F hNE) hU

section Delete

variable {R : Type} [Fintype R] [DecidableEq R] {N : ℕ} {p : R → Prop}

theorem uses_val (s : Subtype p × Subtype p) (e : Subtype p) :
    uses s e = uses ((s.1 : R), (s.2 : R)) (e : R) := by
  simp only [uses, Subtype.ext_iff]

/-- A profile that only uses resources satisfying p, as a profile of the restricted game. -/
def res (P : Fin N → R × R) (hp : ∀ i, p (P i).1 ∧ p (P i).2) : Fin N → Subtype p × Subtype p :=
  fun i => (⟨(P i).1, (hp i).1⟩, ⟨(P i).2, (hp i).2⟩)

theorem load_res (P : Fin N → R × R) (hp : ∀ i, p (P i).1 ∧ p (P i).2) (e : Subtype p) :
    load (res P hp) e = load P e := by
  unfold load
  exact sum_congr rfl fun i _ => uses_val (res P hp i) e

/-- Deleting unused resources keeps the social cost. -/
theorem cost_res [DecidablePred p] (a b : R → ℚ) (P : Fin N → R × R) (hp : ∀ i, p (P i).1 ∧ p (P i).2)
    (h0 : ∀ e, ¬ p e → load P e = 0) :
    cost (fun e : Subtype p => a e) (fun e => b e) (res P hp) = cost a b P := by
  unfold cost
  set f : R → ℚ := fun e => (load P e : ℚ) * delay a b e (load P e) with hf
  have h1 : ∑ e ∈ univ.filter p, f e = ∑ e, f e := sum_filter_of_ne fun e _ hne => by
    by_contra hpe
    exact hne (by simp only [hf, h0 e hpe, Nat.cast_zero, zero_mul])
  have h2 : ∑ e ∈ univ.filter p, f e = ∑ e : Subtype p, f e := sum_subtype _ (fun x => by simp) f
  rw [← h1, h2]
  apply sum_congr rfl
  intro e _
  simp only [hf, load_res]
  rfl

/-- An equilibrium stays an equilibrium after deleting resources it does not use. -/
theorem ne_res (cls : R → ℕ) (a b : R → ℚ) (F : Fin N → R × R) (hp : ∀ i, p (F i).1 ∧ p (F i).2)
    (h : IsNE cls a b F) : IsNE (fun e : Subtype p => cls e) (fun e => a e) (fun e => b e) (res F hp) := by
  intro i g k hgk
  have := h i g k hgk
  unfold own dev at this ⊢
  simp only [load_res, uses_val]
  exact this

end Delete

/-- Steps 1 and 2: a bound for all reduced games is a bound for all games. -/
theorem reduction (N : ℕ) (r : ℚ) (hred : ReducedBound N r) : Bound N r := by
  intro R _ _ cls a b F H ha hb hF hH hNE
  classical
  have hpF : ∀ i, Used F H (F i).1 ∧ Used F H (F i).2 := fun i => ⟨⟨i, Or.inl rfl⟩, ⟨i, Or.inr (Or.inl rfl)⟩⟩
  have hpH : ∀ i, Used F H (H i).1 ∧ Used F H (H i).2 :=
    fun i => ⟨⟨i, Or.inr (Or.inr (Or.inl rfl))⟩, ⟨i, Or.inr (Or.inr (Or.inr rfl))⟩⟩
  have h0 : ∀ P : Fin N → R × R, (∀ i e, ((P i).1 = e ∨ (P i).2 = e) → Used F H e) →
      ∀ e, ¬ Used F H e → load P e = 0 := by
    intro P hP e he
    unfold load
    apply sum_eq_zero
    intro i _
    unfold uses
    have h1 : ¬ (P i).1 = e := fun h => he (hP i e (Or.inl h))
    have h2 : ¬ (P i).2 = e := fun h => he (hP i e (Or.inr h))
    simp [h1, h2]
  have h0F := h0 F fun i e h => by
    rcases h with h | h
    · exact ⟨i, Or.inl h⟩
    · exact ⟨i, Or.inr (Or.inl h)⟩
  have h0H := h0 H fun i e h => by
    rcases h with h | h
    · exact ⟨i, Or.inr (Or.inr (Or.inl h))⟩
    · exact ⟨i, Or.inr (Or.inr (Or.inr h))⟩
  have hU : ∀ e : Subtype (Used F H), Used (res F hpF) (res H hpH) e := by
    intro e
    obtain ⟨i, hi⟩ := e.2
    refine ⟨i, ?_⟩
    simp only [res, Subtype.ext_iff]
    exact hi
  have key := used_bound hred (Subtype (Used F H)) _ (fun e => cls e) (fun e => a e) (fun e => b e)
    (res F hpF) (res H hpH) le_rfl (fun e => ha e) (fun e => hb e) (fun i => hF i) (fun i => hH i)
    (ne_res cls a b F hpF hNE) hU
  rwa [cost_res a b F hpF h0F, cost_res a b H hpH h0H] at key

section Count

variable {R : Type} [Fintype R] [DecidableEq R] {N : ℕ}

/-- A game in which every resource is used by F or H has at most 4N resources. -/
theorem card_le (F H : Fin N → R × R) (hU : ∀ e, Used F H e) : Fintype.card R ≤ 4 * N := by
  have hsub : (univ : Finset R) ⊆
      (univ : Finset (Fin N)).biUnion fun i => {(F i).1, (F i).2, (H i).1, (H i).2} := by
    intro e _
    obtain ⟨i, hi⟩ := hU e
    rw [mem_biUnion]
    refine ⟨i, mem_univ _, ?_⟩
    simp only [mem_insert, mem_singleton]
    rcases hi with h | h | h | h <;> simp [h]
  calc Fintype.card R = (univ : Finset R).card := card_univ.symm
    _ ≤ _ := card_le_card hsub
    _ ≤ ∑ i : Fin N, ({(F i).1, (F i).2, (H i).1, (H i).2} : Finset R).card := card_biUnion_le
    _ ≤ ∑ _i : Fin N, 4 := sum_le_sum fun i _ => card_le_four
    _ = 4 * N := by simp [mul_comm]

/-- If every two of the k classes are joined by one of the 2N bases of F and H, then C(k, 2) ≤ 2N. -/
theorem choose_classes_le (cls : R → ℕ) (F H : Fin N → R × R) (hJ : Joined cls F H) :
    ((univ.image cls).card).choose 2 ≤ 2 * N := by
  set T : Finset (Finset ℕ) := (univ.image fun i => ({cls (F i).1, cls (F i).2} : Finset ℕ)) ∪
    (univ.image fun i => ({cls (H i).1, cls (H i).2} : Finset ℕ)) with hT
  have hsub : (univ.image cls).powersetCard 2 ⊆ T := by
    intro s hs
    rw [mem_powersetCard] at hs
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.1 hs.2
    have hx : x ∈ univ.image cls := hs.1 (mem_insert_self x {y})
    have hy : y ∈ univ.image cls := hs.1 (mem_insert_of_mem (mem_singleton_self y))
    obtain ⟨e, -, rfl⟩ := mem_image.1 hx
    obtain ⟨f, -, rfl⟩ := mem_image.1 hy
    obtain ⟨i, hi⟩ := hJ e f hxy
    rw [hT, mem_union, mem_image, mem_image]
    rcases hi with h | h
    · left
      refine ⟨i, mem_univ _, ?_⟩
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, pair_comm]
    · right
      refine ⟨i, mem_univ _, ?_⟩
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, pair_comm]
  calc ((univ.image cls).card).choose 2 = ((univ.image cls).powersetCard 2).card :=
        (card_powersetCard 2 _).symm
    _ ≤ T.card := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ N + N := add_le_add (card_image_le.trans (by simp)) (card_image_le.trans (by simp))
    _ = 2 * N := by ring

/-- For three players at most four classes remain. -/
theorem classes_le_four (k : ℕ) (h : k.choose 2 ≤ 2 * 3) : k ≤ 4 := by
  by_contra hk
  have h5 := Nat.choose_le_choose 2 (show 5 ≤ k by omega)
  have e5 : (5 : ℕ).choose 2 = 10 := by decide
  omega

end Count

end PavingReduction
