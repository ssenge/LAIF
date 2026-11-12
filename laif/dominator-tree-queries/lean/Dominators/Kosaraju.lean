import Dominators.DFS

/-!
# The two-pass components algorithm, with the search as a parameter

The first round is a search over all roots. The second round searches the reverse graph, with roots in
decreasing finish time, and each of its trees is a component. Main result: `kosaraju_correct`.
-/

open Finset

namespace Dominators

universe u

variable {V : Type u} [DecidableEq V] {E : V → V → Prop}

/-! ## The first round -/

/-- What the first round needs. `back`: a finished vertex that reaches an unfinished one is in the same
component as some stack vertex. `order`: if `y` reaches `t` but not conversely, then the component of `y` has a
vertex that is unfinished or finished after `t`. -/
structure KInv (E : V → V → Prop) (s : St V) : Prop where
  back : ∀ x ∈ s.finished, ∀ w, Reach E x w → w ∉ s.finished → ∃ z ∈ s.stack, Reach E x z ∧ Reach E z x
  order : ∀ y t, t ∈ s.finished → Reach E y t → ¬ Reach E t y →
    ∃ z, Mutual E y z ∧ (z ∉ s.finished ∨ ∃ A B, s.finished = A ++ t :: B ∧ z ∈ A)

omit [DecidableEq V] in
theorem KInv.init : KInv E (St.init : St V) := ⟨by simp [St.init], by simp [St.init]⟩

omit [DecidableEq V] in
/-- From the popped vertex, a walk that leaves the finished part must meet the rest of the stack. -/
theorem exit_rest {s : St V} (h : Inv E s) {v : V} {rest : List V} (hst : s.stack = v :: rest)
    (hn : ∀ w, E v w → w ∈ s.visited) {a w : V} (p : Walk E a w) (ha : a = v ∨ a ∈ s.finished)
    (hva : Reach E v a) (hw : w ≠ v) (hwf : w ∉ s.finished) : ∃ z ∈ rest, Reach E v z := by
  induction p with
  | nil a =>
    rcases ha with rfl | ha
    · exact absurd rfl hw
    · exact absurd ha hwf
  | @cons a b w hab p ih =>
    have hb : b ∈ s.visited := by
      rcases ha with rfl | ha
      · exact hn b hab
      · exact h.closed a ha b hab
    rw [h.mem_visited, hst, List.mem_cons] at hb
    rcases hb with (rfl | hb) | hb
    · exact ih (Or.inl rfl) (Reach.refl _ _) hw hwf
    · exact ⟨b, hb, hva.tail hab⟩
    · exact ih (Or.inr hb) (hva.tail hab) hw hwf

theorem KInv.push {s : St V} (h : KInv E s) (w : V) (p : Option V) (c : ℕ) :
    KInv E { s.push w p with searches := c } := by
  constructor
  · intro x hx t hxt ht
    obtain ⟨z, hz, h1, h2⟩ := h.back x hx t hxt ht
    exact ⟨z, by simp [St.push, hz], h1, h2⟩
  · exact h.order

theorem KInv.pop {s : St V} (hI : Inv E s) (h : KInv E s) {v : V} {rest : List V}
    (hst : s.stack = v :: rest) (hn : ∀ w, E v w → w ∈ s.visited) :
    KInv E { s with stack := rest, finished := v :: s.finished, searches := s.searches + 1 } := by
  have hnd := hI.nodup
  rw [hst] at hnd
  have hv : v ∉ s.finished := by
    intro hv
    simp only [List.cons_append, List.nodup_cons, List.mem_append, not_or] at hnd
    exact hnd.1.2 hv
  have hr : ∀ z ∈ rest, z ∉ v :: s.finished := by
    intro z hz hz'
    simp only [List.cons_append, List.nodup_cons, List.mem_append, not_or] at hnd
    rcases List.mem_cons.mp hz' with rfl | hz'
    · exact hnd.1.1 hz
    · exact (List.nodup_append.mp hnd.2).2.2 z hz z hz' rfl
  have hch := hI.chain
  rw [hst] at hch
  have hback : ∀ z ∈ rest, Reach E z v := (List.pairwise_cons.mp hch).1
  constructor
  · intro x hx w hxw hw
    simp only [List.mem_cons, not_or] at hx hw
    rcases hx with rfl | hx
    · obtain ⟨p⟩ := hxw
      obtain ⟨z, hz, h1⟩ := exit_rest hI hst hn p (Or.inl rfl) (Reach.refl _ _) hw.1 hw.2
      exact ⟨z, hz, h1, hback z hz⟩
    · obtain ⟨z, hz, h1, h2⟩ := h.back x hx w hxw hw.2
      rw [hst] at hz
      rcases List.mem_cons.mp hz with rfl | hz
      · obtain ⟨p⟩ := h2.trans hxw
        obtain ⟨z', hz', h3⟩ := exit_rest hI hst hn p (Or.inl rfl) (Reach.refl _ _) hw.1 hw.2
        exact ⟨z', hz', h1.trans h3, (hback z' hz').trans h2⟩
      · exact ⟨z, hz, h1, h2⟩
  · intro y t ht hyt hty
    simp only [List.mem_cons] at ht
    by_cases htv : t = v
    · subst htv
      by_cases hy : y ∈ s.finished
      · obtain ⟨z, hz, h1, h2⟩ := h.back y hy t hyt hv
        rw [hst] at hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact absurd h2 hty
        · exact ⟨z, ⟨h1, h2⟩, Or.inl (hr z hz)⟩
      · refine ⟨y, ⟨Reach.refl _ _, Reach.refl _ _⟩, Or.inl ?_⟩
        simp only [List.mem_cons, not_or]
        exact ⟨fun e => hty (e ▸ Reach.refl _ _), hy⟩
    · have ht' : t ∈ s.finished := ht.resolve_left htv
      obtain ⟨z, hz, h1⟩ := h.order y t ht' hyt hty
      refine ⟨z, hz, ?_⟩
      rcases h1 with h1 | ⟨A, B, hAB, hzA⟩
      · by_cases hzv : z = v
        · right
          obtain ⟨A, B, hAB⟩ := List.append_of_mem ht'
          refine ⟨v :: A, B, ?_, by simp [hzv]⟩
          simp [hAB]
        · left
          simp only [List.mem_cons, not_or]
          exact ⟨hzv, h1⟩
      · right
        refine ⟨v :: A, B, ?_, List.mem_cons_of_mem _ hzA⟩
        simp [hAB]

theorem KInv.step {search : V → Finset V → Option V} (hS : IsSearch E search) {s : St V} (hI : Inv E s)
    (h : KInv E s) : KInv E (step search s) := by
  cases hst : s.stack with
  | nil => rwa [step_nil hst]
  | cons v rest =>
    cases hq : search v s.visited with
    | none =>
      rw [step_none hst hq]
      exact h.pop hI hst (hS.none hq)
    | some w =>
      rw [step_found hst hq]
      exact h.push w (some v) _

theorem KInv.push_root {s : St V} (h : KInv E s) (r : V) : KInv E (s.push r none) :=
  h.push r none s.searches

/-- The first-round invariants survive a tree. -/
theorem KInv.visit {search : V → Finset V → Option V} (hS : IsSearch E search) {fuel : ℕ} {s : St V}
    (hI : Inv E s) (hst : s.stack = []) (h : KInv E s) (r : V) : KInv E (visit search fuel s r) := by
  unfold Dominators.visit
  split_ifs with hr
  · exact h
  · have := run_induct (search := search) (fun t => Inv E t ∧ KInv E t)
      (fun _ h' => ⟨h'.1.step hS, h'.2.step hS h'.1⟩) fuel _ ⟨hI.push_root hst hr, h.push_root r⟩
    exact this.2

section Rounds

variable [Fintype V]

/-- The output of the first round. -/
def round1 (search : V → Finset V → Option V) (fuel : ℕ) (roots : List V) : St V :=
  forest search fuel roots St.init

/-- The property of the finish order: if `y` reaches `t` but not conversely, then the component of `y` has a
vertex finished after `t`. The list has every vertex exactly once. -/
theorem round1_order {search : V → Finset V → Option V} (hS : IsSearch E search) {fuel : ℕ}
    (hf : 2 * Fintype.card V ≤ fuel) {roots : List V} (hroots : ∀ x, x ∈ roots) :
    let L := (round1 search fuel roots).finished
    L.Nodup ∧ (∀ x, x ∈ L) ∧ ∀ y t, Reach E y t → ¬ Reach E t y →
      ∃ z, Mutual E y z ∧ ∃ A B, L = A ++ t :: B ∧ z ∈ A := by
  intro L
  have hgood : Good E (round1 search fuel roots) := (Good.init (E := E)).forest hS hf roots
  have hK : KInv E (round1 search fuel roots) := by
    have : ∀ (rs : List V) (s : St V), Good E s → KInv E s → KInv E (forest search fuel rs s) := by
      intro rs
      induction rs with
      | nil => exact fun _ _ h => h
      | cons r rs ih =>
        intro s hg hk
        exact ih _ (hg.visit hS hf r) (hk.visit hS hg.inv hg.nil r)
    exact this roots _ Good.init KInv.init
  have hall : ∀ x, x ∈ L := by
    intro x
    have hx : x ∈ (round1 search fuel roots).visited := mem_forest_of_mem _ (hroots x)
    rw [hgood.inv.mem_visited, hgood.nil] at hx
    simpa using hx
  refine ⟨?_, hall, ?_⟩
  · have := hgood.inv.nodup
    rw [hgood.nil] at this
    simpa using this
  · intro y t hyt hty
    obtain ⟨z, hz, h⟩ := hK.order y t (hall t) hyt hty
    refine ⟨z, hz, ?_⟩
    rcases h with h | h
    · exact absurd (hall z) h
    · exact h

/-! ## The second round -/

/-- Search the graph with roots in the given order. Each new tree, as a set of vertices, is added to `acc`. -/
def round2 (search : V → Finset V → Option V) (fuel : ℕ) :
    List V → St V → List (Finset V) → St V × List (Finset V)
  | [], s, acc => (s, acc)
  | t :: ts, s, acc =>
    if t ∈ s.visited then round2 search fuel ts s acc
    else
      let s' := visit search fuel s t
      round2 search fuel ts s' ((s'.visited \ s.visited) :: acc)

/-- The two-pass algorithm. The second search is for the reverse graph. It returns the components and the total
number of searches. -/
def kosaraju (searchG searchR : V → Finset V → Option V) (fuel : ℕ) (roots : List V) :
    List (Finset V) × ℕ :=
  let s₁ := round1 searchG fuel roots
  let r₂ := round2 searchR fuel s₁.finished St.init []
  (r₂.2, s₁.searches + r₂.1.searches)

/-- A set is the component of some vertex. -/
def IsComponent (E : V → V → Prop) (C : Finset V) : Prop := ∃ t, ∀ x, x ∈ C ↔ Mutual E t x

/-- The invariant of the second round. -/
structure RInv (E : V → V → Prop) (s : St V) (acc : List (Finset V)) : Prop where
  comp : ∀ C ∈ acc, C ⊆ s.visited ∧ IsComponent E C
  disj : acc.Pairwise Disjoint
  cover : ∀ x ∈ s.visited, ∃ C ∈ acc, x ∈ C

theorem round2_spec {searchR : V → Finset V → Option V} (hR : IsSearch (rev E) searchR) {fuel : ℕ}
    (hf : 2 * Fintype.card V ≤ fuel) (L : List V) (hLnd : L.Nodup)
    (horder : ∀ y t, Reach E y t → ¬ Reach E t y → ∃ z, Mutual E y z ∧ ∃ A B, L = A ++ t :: B ∧ z ∈ A)
    (A ts : List V) (s : St V) (acc : List (Finset V)) (hL : L = A ++ ts)
    (hg : Good (rev E) s) (hA : ∀ a ∈ A, a ∈ s.visited) (hr : RInv E s acc) :
    let out := round2 searchR fuel ts s acc
    Good (rev E) out.1 ∧ RInv E out.1 out.2 ∧ ∀ a ∈ L, a ∈ out.1.visited := by
  induction ts generalizing A s acc with
  | nil =>
    refine ⟨hg, hr, ?_⟩
    intro a ha
    rw [hL, List.append_nil] at ha
    exact hA a ha
  | cons t ts ih =>
    simp only [round2]
    split_ifs with ht
    · refine ih (A ++ [t]) s acc (by simp [hL]) hg ?_ hr
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hA a ha
      · rw [List.mem_singleton.mp ha]
        exact ht
    · have hg' := hg.visit hR hf t
      set s' := visit searchR fuel s t with hs'
      have hsub : s.visited ⊆ s'.visited := visited_visit_subset fuel s t
      have htmem : t ∈ s'.visited := mem_visit_self fuel s t
      have hT : ∀ x, x ∈ s'.visited \ s.visited ↔ Mutual E t x := by
        intro x
        rw [Finset.mem_sdiff]
        constructor
        · rintro ⟨hx, hxn⟩
          have hxt : Reach E x t := by
            rcases visit_reach hR fuel t hg.nil hx with h | h
            · exact absurd h hxn
            · exact reach_rev.mp h
          refine ⟨?_, hxt⟩
          by_contra htx
          obtain ⟨z, hz, A', B', hAB, hzA⟩ := horder x t hxt htx
          have htA : t ∉ A := by
            intro htA
            rw [hL] at hLnd
            exact (List.nodup_append.mp hLnd).2.2 t htA t (by simp) rfl
          have heq : A' = A := by
            have h1 : A ++ t :: ts = A' ++ t :: B' := by rw [← hL, hAB]
            have hts : t ∉ ts := by
              rw [hL] at hLnd
              exact (List.nodup_cons.mp (List.nodup_append.mp hLnd).2.1).1
            exact ((List.append_cons_inj_of_notMem htA hts).mp h1).1.symm
          rw [heq] at hzA
          have hzv : z ∈ s.visited := hA z hzA
          exact hxn (hg.inv.reach_of_nil hg.nil hzv (reach_rev.mpr hz.1))
        · intro hm
          refine ⟨hg'.inv.reach_of_nil hg'.nil htmem (reach_rev.mpr hm.2), fun hx => ht ?_⟩
          exact hg.inv.reach_of_nil hg.nil hx (reach_rev.mpr hm.1)
      refine ih (A ++ [t]) s' _ (by simp [hL]) hg' ?_ ?_
      · intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hsub (hA a ha)
        · rw [List.mem_singleton.mp ha]
          exact htmem
      · refine ⟨?_, ?_, ?_⟩
        · intro C hC
          rcases List.mem_cons.mp hC with rfl | hC
          · exact ⟨Finset.sdiff_subset, t, hT⟩
          · exact ⟨(hr.comp C hC).1.trans hsub, (hr.comp C hC).2⟩
        · refine List.pairwise_cons.mpr ⟨?_, hr.disj⟩
          intro C hC
          exact Finset.disjoint_of_subset_right (hr.comp C hC).1 Finset.sdiff_disjoint
        · intro x hx
          by_cases hxs : x ∈ s.visited
          · obtain ⟨C, hC, hxC⟩ := hr.cover x hxs
            exact ⟨C, List.mem_cons_of_mem _ hC, hxC⟩
          · exact ⟨_, List.mem_cons_self, Finset.mem_sdiff.mpr ⟨hx, hxs⟩⟩

/-- **Correctness of the two-pass algorithm.** With searches meeting their specification on the graph and on its reverse, all
vertices as roots and `2n` fuel: every output set is a component, the sets are pairwise disjoint, they cover all
vertices, and the algorithm makes at most `4n` searches. -/
theorem kosaraju_correct {searchG searchR : V → Finset V → Option V} (hG : IsSearch E searchG)
    (hR : IsSearch (rev E) searchR) {fuel : ℕ} (hf : 2 * Fintype.card V ≤ fuel) {roots : List V}
    (hroots : ∀ x, x ∈ roots) :
    let out := kosaraju searchG searchR fuel roots
    (∀ C ∈ out.1, IsComponent E C) ∧ out.1.Pairwise Disjoint ∧ (∀ x, ∃ C ∈ out.1, x ∈ C) ∧
      out.2 ≤ 4 * Fintype.card V := by
  intro out
  obtain ⟨hnd, hall, hord⟩ := round1_order hG hf hroots
  have hspec := round2_spec (E := E) hR hf _ hnd hord [] _ St.init [] rfl Good.init (by simp)
    ⟨by simp, by simp, by simp [St.init]⟩
  obtain ⟨hg, hr, hL⟩ := hspec
  refine ⟨fun C hC => (hr.comp C hC).2, hr.disj, fun x => hr.cover x (hL x (hall x)), ?_⟩
  have h1 : (round1 searchG fuel roots).searches ≤ 2 * Fintype.card V := forest_searches_le hG fuel roots
  have h2 : (round2 searchR fuel (round1 searchG fuel roots).finished St.init []).1.searches ≤
      2 * Fintype.card V := hg.budget.searches_le
  have hout : out.2 = (round1 searchG fuel roots).searches +
      (round2 searchR fuel (round1 searchG fuel roots).finished St.init []).1.searches := rfl
  rw [hout]
  omega

/-- Two vertices lie in the same output set iff they are in the same strongly connected component. -/
theorem kosaraju_same_iff {searchG searchR : V → Finset V → Option V} (hG : IsSearch E searchG)
    (hR : IsSearch (rev E) searchR) {fuel : ℕ} (hf : 2 * Fintype.card V ≤ fuel) {roots : List V}
    (hroots : ∀ x, x ∈ roots) (x y : V) :
    (∃ C ∈ (kosaraju searchG searchR fuel roots).1, x ∈ C ∧ y ∈ C) ↔ Mutual E x y := by
  obtain ⟨hc, _, hcov, _⟩ := kosaraju_correct hG hR hf hroots
  constructor
  · rintro ⟨C, hC, hx, hy⟩
    obtain ⟨t, ht⟩ := hc C hC
    have h1 := (ht x).mp hx
    have h2 := (ht y).mp hy
    exact ⟨h1.2.trans h2.1, h2.2.trans h1.1⟩
  · intro hm
    obtain ⟨C, hC, hx⟩ := hcov x
    refine ⟨C, hC, hx, ?_⟩
    obtain ⟨t, ht⟩ := hc C hC
    have h1 := (ht x).mp hx
    exact (ht y).mpr ⟨h1.1.trans hm.1, hm.2.trans h1.2⟩

end Rounds

end Dominators
