import Dominators.Lemma2

/-!
# An executable depth-first search

The search is a parameter, `search v S`, which returns an out-neighbour of `v` outside `S`, or `none` if there
is no such neighbour. `IsSearch` is its specification, so a theorem here holds for every choice of neighbour.
It is the contract that the quantum search must meet with high probability; failure of a search is not modelled
in this file. `searches` counts the calls of `search`. The function `run` takes fuel, and `run_stack_nil` shows
that `2n` fuel is enough.

Main results: `dfs_visited_iff`, `dfs_searches_le`, `forest_searches_le`.
-/

open Finset

namespace Dominators

universe u

variable {V : Type u}

/-- The search specification: a found vertex is an out-neighbour outside `S`; if none is found, all
out-neighbours are in `S`. -/
structure IsSearch (E : V → V → Prop) (search : V → Finset V → Option V) : Prop where
  found : ∀ {v S w}, search v S = some w → E v w ∧ w ∉ S
  none : ∀ {v S}, search v S = none → ∀ w, E v w → w ∈ S

/-- The state of a depth-first search. -/
structure St (V : Type u) where
  /-- The stack, top first. -/
  stack : List V
  /-- The vertices pushed so far. -/
  visited : Finset V
  /-- The vertices popped so far, most recent first: decreasing finish time. -/
  finished : List V
  /-- The vertices pushed so far, most recent first: decreasing preorder. -/
  order : List V
  /-- The preorder number of a visited vertex. -/
  pre : V → ℕ
  /-- The tree parent of a visited vertex. -/
  parent : V → Option V
  /-- The number of calls of `search` so far. -/
  searches : ℕ

/-- The state before any search. -/
def St.init : St V := ⟨[], ∅, [], [], fun _ => 0, fun _ => none, 0⟩

variable [DecidableEq V]

/-- Push the unvisited vertex `w`, with tree parent `p`. -/
def St.push (s : St V) (w : V) (p : Option V) : St V :=
  { s with
    stack := w :: s.stack
    visited := insert w s.visited
    order := w :: s.order
    pre := Function.update s.pre w s.visited.card
    parent := Function.update s.parent w p }

/-- One step: search at the top of the stack, then push what was found, or pop the top. -/
def step (search : V → Finset V → Option V) (s : St V) : St V :=
  match s.stack with
  | [] => s
  | v :: rest =>
    match search v s.visited with
    | some w => { s.push w (some v) with searches := s.searches + 1 }
    | none => { s with stack := rest, finished := v :: s.finished, searches := s.searches + 1 }

/-- Run with fuel. A step on the empty stack does nothing. -/
def run (search : V → Finset V → Option V) : ℕ → St V → St V
  | 0, s => s
  | k + 1, s => run search k (step search s)

/-- Start a tree at `r`, unless `r` is already visited. -/
def visit (search : V → Finset V → Option V) (fuel : ℕ) (s : St V) (r : V) : St V :=
  if r ∈ s.visited then s else run search fuel (s.push r none)

/-- Depth-first search over a list of roots. -/
def forest (search : V → Finset V → Option V) (fuel : ℕ) (roots : List V) (s : St V) : St V :=
  roots.foldl (visit search fuel) s

/-- Depth-first search from `r`. -/
def dfs (search : V → Finset V → Option V) (fuel : ℕ) (r : V) : St V :=
  visit search fuel St.init r

/-! ## Basic facts on steps -/

section Steps

variable {search : V → Finset V → Option V} {s : St V} {v w : V} {rest : List V}

theorem step_nil (h : s.stack = []) : step search s = s := by
  simp [step, h]

theorem step_found (h : s.stack = v :: rest) (hq : search v s.visited = some w) :
    step search s = { s.push w (some v) with searches := s.searches + 1 } := by
  simp [step, h, hq]

theorem step_none (h : s.stack = v :: rest) (hq : search v s.visited = none) :
    step search s = { s with stack := rest, finished := v :: s.finished, searches := s.searches + 1 } := by
  simp [step, h, hq]

theorem run_of_nil (h : s.stack = []) (k : ℕ) : run search k s = s := by
  induction k with
  | zero => rfl
  | succ k ih => rw [run, step_nil h, ih]

/-- What holds at every step holds after a run. -/
theorem run_induct (P : St V → Prop) (hP : ∀ s, P s → P (step search s)) (k : ℕ) (s : St V) (hs : P s) :
    P (run search k s) := by
  induction k generalizing s with
  | zero => exact hs
  | succ k ih => exact ih _ (hP _ hs)

/-- A relation that every step respects, and that is reflexive and transitive, holds along a run. -/
theorem run_rel (R : St V → St V → Prop) (hrefl : ∀ s, R s s) (htrans : ∀ a b c, R a b → R b c → R a c)
    (hP : ∀ s, R s (step search s)) (k : ℕ) (s : St V) : R s (run search k s) := by
  induction k generalizing s with
  | zero => exact hrefl s
  | succ k ih => exact htrans _ _ _ (hP s) (ih _)

end Steps

/-! ## The invariant -/

variable {E : V → V → Prop}

/-- The invariant of a search. The stack is a path, the finished vertices have only visited out-neighbours,
and each vertex is on the stack or finished exactly once. -/
structure Inv (E : V → V → Prop) (s : St V) : Prop where
  mem_visited : ∀ x, x ∈ s.visited ↔ x ∈ s.stack ∨ x ∈ s.finished
  nodup : (s.stack ++ s.finished).Nodup
  closed : ∀ x ∈ s.finished, ∀ y, E x y → y ∈ s.visited
  chain : s.stack.Pairwise (fun a b => Reach E b a)

omit [DecidableEq V] in
theorem Inv.init : Inv E (St.init : St V) where
  mem_visited := by simp [St.init]
  nodup := by simp [St.init]
  closed := by simp [St.init]
  chain := by simp [St.init]

omit [DecidableEq V] in
theorem Inv.not_mem_of_not_visited {s : St V} (h : Inv E s) {w : V} (hw : w ∉ s.visited) :
    w ∉ s.stack ∧ w ∉ s.finished := by
  rw [h.mem_visited] at hw
  simpa [not_or] using hw

theorem Inv.push_found {s : St V} (h : Inv E s) {v w : V} {rest : List V} (hst : s.stack = v :: rest)
    (he : E v w) (hw : w ∉ s.visited) :
    Inv E { s.push w (some v) with searches := s.searches + 1 } := by
  obtain ⟨h1, h2⟩ := h.not_mem_of_not_visited hw
  have hch := h.chain
  rw [hst] at hch
  have hnd := h.nodup
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    simp only [St.push, Finset.mem_insert, List.mem_cons, h.mem_visited]
    tauto
  · simp only [St.push, List.cons_append, List.nodup_cons, List.mem_append, not_or]
    exact ⟨⟨h1, h2⟩, hnd⟩
  · intro x hx y hy
    simp only [St.push, Finset.mem_insert]
    exact Or.inr (h.closed x hx y hy)
  · simp only [St.push, hst]
    refine List.pairwise_cons.mpr ⟨?_, hch⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Reach.edge he
    · exact ((List.pairwise_cons.mp hch).1 b hb).tail he

omit [DecidableEq V] in
theorem Inv.pop {s : St V} (h : Inv E s) {v : V} {rest : List V} (hst : s.stack = v :: rest)
    (hn : ∀ w, E v w → w ∈ s.visited) :
    Inv E { s with stack := rest, finished := v :: s.finished, searches := s.searches + 1 } := by
  have hnd := h.nodup
  rw [hst] at hnd
  have hch := h.chain
  rw [hst] at hch
  refine ⟨?_, ?_, ?_, (List.pairwise_cons.mp hch).2⟩
  · intro x
    simp only [h.mem_visited, hst, List.mem_cons]
    tauto
  · simp only [List.cons_append, List.nodup_cons, List.mem_append, not_or] at hnd
    simp only [List.nodup_append, List.nodup_cons, List.mem_cons] at hnd ⊢
    grind
  · intro x hx y hy
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hn y hy
    · exact h.closed x hx y hy

/-- A step keeps the invariant. -/
theorem Inv.step {search : V → Finset V → Option V} (hS : IsSearch E search) {s : St V} (h : Inv E s) :
    Inv E (step search s) := by
  cases hst : s.stack with
  | nil => rwa [step_nil hst]
  | cons v rest =>
    cases hq : search v s.visited with
    | none =>
      rw [step_none hst hq]
      exact h.pop hst (hS.none hq)
    | some w =>
      rw [step_found hst hq]
      obtain ⟨he, hw⟩ := hS.found hq
      exact h.push_found hst he hw

/-- Starting a tree on the empty stack keeps the invariant. -/
theorem Inv.push_root {s : St V} (h : Inv E s) (hst : s.stack = []) {r : V} (hr : r ∉ s.visited) :
    Inv E (s.push r none) := by
  obtain ⟨h1, h2⟩ := h.not_mem_of_not_visited hr
  have hnd := h.nodup
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    simp only [St.push, Finset.mem_insert, List.mem_cons, h.mem_visited]
    tauto
  · simp only [St.push, List.cons_append, List.nodup_cons, List.mem_append, not_or]
    exact ⟨⟨h1, h2⟩, hnd⟩
  · intro x hx y hy
    simp only [St.push, Finset.mem_insert]
    exact Or.inr (h.closed x hx y hy)
  · simp [St.push, hst]

omit [DecidableEq V] in
/-- With the stack empty, the visited set is closed under out-neighbours. -/
theorem Inv.closed_of_nil {s : St V} (h : Inv E s) (hst : s.stack = []) {x y : V} (hx : x ∈ s.visited)
    (he : E x y) : y ∈ s.visited := by
  rw [h.mem_visited, hst] at hx
  simp only [List.not_mem_nil, false_or] at hx
  exact h.closed x hx y he

omit [DecidableEq V] in
/-- With the stack empty, the visited set contains everything reachable from it. -/
theorem Inv.reach_of_nil {s : St V} (h : Inv E s) (hst : s.stack = []) {x y : V} (hx : x ∈ s.visited)
    (hr : Reach E x y) : y ∈ s.visited :=
  Reach.mem_of_closed (S := fun t => t ∈ s.visited) (fun _ _ ha he => h.closed_of_nil hst ha he) hr hx

/-! ## The search count and the fuel -/

section Budget

variable [Fintype V]

/-- The potential: two per unvisited vertex and one per stack entry. -/
def pot (s : St V) : ℕ := 2 * (Fintype.card V - s.visited.card) + s.stack.length

theorem pot_step {search : V → Finset V → Option V} (hS : IsSearch E search) {s : St V}
    (hst : s.stack ≠ []) : pot (step search s) + 1 = pot s := by
  cases hstk : s.stack with
  | nil => exact absurd hstk hst
  | cons v rest =>
    cases hq : search v s.visited with
    | none =>
      rw [step_none hstk hq]
      simp [pot, hstk]
      omega
    | some w =>
      rw [step_found hstk hq]
      have hw := (hS.found hq).2
      have hc := Finset.card_le_univ (insert w s.visited)
      rw [Finset.card_insert_of_notMem hw] at hc
      simp only [pot, St.push, hstk, Finset.card_insert_of_notMem hw, List.length_cons]
      omega

omit [Fintype V] in
theorem searches_step {search : V → Finset V → Option V} {s : St V} (hst : s.stack ≠ []) :
    (step search s).searches = s.searches + 1 := by
  cases hstk : s.stack with
  | nil => exact absurd hstk hst
  | cons v rest =>
    cases hq : search v s.visited with
    | none => rw [step_none hstk hq]
    | some w => rw [step_found hstk hq]

/-- `pot s` is enough fuel: the stack ends empty. -/
theorem run_stack_nil {search : V → Finset V → Option V} (hS : IsSearch E search) (k : ℕ) (s : St V)
    (hk : pot s ≤ k) : (run search k s).stack = [] := by
  induction k generalizing s with
  | zero =>
    simp only [pot, Nat.le_zero, Nat.add_eq_zero_iff, List.length_eq_zero_iff] at hk
    exact hk.2
  | succ k ih =>
    by_cases hst : s.stack = []
    · rw [run_of_nil hst]
      exact hst
    · rw [run]
      apply ih
      have := pot_step (search := search) hS hst
      omega

/-- The budget: searches made plus the potential never exceed `2n`. -/
def Budget (s : St V) : Prop := s.searches + pot s ≤ 2 * Fintype.card V

omit [DecidableEq V] in
theorem Budget.init : Budget (St.init : St V) := by
  simp [Budget, pot, St.init]

theorem Budget.step {search : V → Finset V → Option V} (hS : IsSearch E search) {s : St V}
    (h : Budget s) : Budget (step search s) := by
  by_cases hst : s.stack = []
  · rwa [step_nil hst]
  · have h1 := pot_step (search := search) hS hst
    have h2 := searches_step (search := search) hst
    unfold Budget at *
    omega

theorem Budget.push {s : St V} (h : Budget s) {r : V} (hr : r ∉ s.visited) (p : Option V) :
    Budget (s.push r p) := by
  have hc := Finset.card_le_univ (insert r s.visited)
  rw [Finset.card_insert_of_notMem hr] at hc
  unfold Budget pot at *
  simp only [St.push, Finset.card_insert_of_notMem hr, List.length_cons]
  omega

/-- The stack is no longer than the unvisited part allows: enough fuel for a whole tree. -/
theorem pot_push_le {s : St V} (h : Budget s) {r : V} (hr : r ∉ s.visited) (p : Option V) :
    pot (s.push r p) ≤ 2 * Fintype.card V := by
  have := Budget.push h hr p
  unfold Budget at this
  omega

theorem Budget.visit {search : V → Finset V → Option V} (hS : IsSearch E search) {fuel : ℕ} {s : St V}
    (h : Budget s) (r : V) : Budget (visit search fuel s r) := by
  unfold Dominators.visit
  split_ifs with hr
  · exact h
  · exact run_induct Budget (fun _ h' => h'.step hS) fuel _ (h.push hr none)

theorem Budget.forest {search : V → Finset V → Option V} (hS : IsSearch E search) {fuel : ℕ}
    (roots : List V) {s : St V} (h : Budget s) : Budget (forest search fuel roots s) := by
  induction roots generalizing s with
  | nil => exact h
  | cons r rs ih =>
    exact ih (h.visit hS r)

omit [DecidableEq V] in
theorem Budget.searches_le {s : St V} (h : Budget s) : s.searches ≤ 2 * Fintype.card V := by
  unfold Budget at h
  omega

/-- The state of a search with an empty stack at its boundaries. -/
structure Good (E : V → V → Prop) (s : St V) : Prop where
  inv : Inv E s
  nil : s.stack = []
  budget : Budget s

omit [DecidableEq V] in
theorem Good.init : Good E (St.init : St V) := ⟨Inv.init, rfl, Budget.init⟩

/-- Visiting one root, with `2n` fuel. -/
theorem Good.visit {search : V → Finset V → Option V} (hS : IsSearch E search) {fuel : ℕ}
    (hf : 2 * Fintype.card V ≤ fuel) {s : St V} (h : Good E s) (r : V) :
    Good E (visit search fuel s r) := by
  refine ⟨?_, ?_, h.budget.visit hS r⟩
  · unfold Dominators.visit
    split_ifs with hr
    · exact h.inv
    · exact run_induct (Inv E) (fun _ h' => h'.step hS) fuel _ (h.inv.push_root h.nil hr)
  · unfold Dominators.visit
    split_ifs with hr
    · exact h.nil
    · exact run_stack_nil hS fuel _ ((pot_push_le h.budget hr none).trans hf)

omit [Fintype V] in
theorem visited_step_subset {search : V → Finset V → Option V} (s : St V) :
    s.visited ⊆ (step search s).visited := by
  cases hstk : s.stack with
  | nil => rw [step_nil hstk]
  | cons v rest =>
    cases hq : search v s.visited with
    | none => rw [step_none hstk hq]
    | some w =>
      rw [step_found hstk hq]
      exact Finset.subset_insert _ _

omit [Fintype V] in
theorem visited_run_subset {search : V → Finset V → Option V} (k : ℕ) (s : St V) :
    s.visited ⊆ (run search k s).visited :=
  run_rel (fun a b => a.visited ⊆ b.visited) (fun _ => Finset.Subset.refl _)
    (fun _ _ _ h1 h2 => h1.trans h2) (fun s => visited_step_subset s) k s

theorem mem_visit_self {search : V → Finset V → Option V} (fuel : ℕ) (s : St V) (r : V) :
    r ∈ (visit search fuel s r).visited := by
  unfold visit
  split_ifs with hr
  · exact hr
  · apply visited_run_subset
    simp [St.push]

theorem visited_visit_subset {search : V → Finset V → Option V} (fuel : ℕ) (s : St V) (r : V) :
    s.visited ⊆ (visit search fuel s r).visited := by
  unfold visit
  split_ifs with hr
  · exact Finset.Subset.refl _
  · refine Finset.Subset.trans ?_ (visited_run_subset _ _)
    simp [St.push, Finset.subset_insert]

omit [Fintype V] in
/-- Everything newly visited by a tree from `r` is reachable from `r`. -/
theorem visit_reach {search : V → Finset V → Option V} (hS : IsSearch E search) (fuel : ℕ) {s : St V} (r : V)
    (hst : s.stack = []) {x : V} (hx : x ∈ (visit search fuel s r).visited) : x ∈ s.visited ∨ Reach E r x := by
  unfold visit at hx
  split_ifs at hx with hr
  · exact Or.inl hx
  · let P : St V → Prop := fun t =>
      (∀ y ∈ t.stack, Reach E r y) ∧ ∀ y ∈ t.visited, y ∈ s.visited ∨ Reach E r y
    have hP0 : P (s.push r none) := by
      constructor
      · intro y hy
        simp only [St.push, hst, List.mem_singleton] at hy
        rw [hy]
        exact Reach.refl _ _
      · intro y hy
        simp only [St.push, Finset.mem_insert] at hy
        rcases hy with rfl | hy
        · exact Or.inr (Reach.refl _ _)
        · exact Or.inl hy
    have hstep : ∀ t, P t → P (step search t) := by
      rintro t ⟨h1, h2⟩
      cases hstk : t.stack with
      | nil => rw [step_nil hstk]; exact ⟨h1, h2⟩
      | cons v rest =>
        cases hq : search v t.visited with
        | none =>
          rw [step_none hstk hq]
          refine ⟨fun y hy => h1 y ?_, h2⟩
          simp only [hstk, List.mem_cons]
          exact Or.inr hy
        | some w =>
          rw [step_found hstk hq]
          have hvw := (hS.found hq).1
          have hrv : Reach E r v := h1 v (by simp [hstk])
          constructor
          · intro y hy
            simp only [St.push, List.mem_cons] at hy
            rcases hy with rfl | hy
            · exact hrv.tail hvw
            · exact h1 y hy
          · intro y hy
            simp only [St.push, Finset.mem_insert] at hy
            rcases hy with rfl | hy
            · exact Or.inr (hrv.tail hvw)
            · exact h2 y hy
    exact (run_induct P hstep fuel _ hP0).2 x hx

/-! ## The visited set and the search count -/

/-- **DFS correctness.** With `2n` fuel, the visited set of a search from `r` is exactly the reachable set. -/
theorem dfs_visited_iff {search : V → Finset V → Option V} (hS : IsSearch E search) {fuel : ℕ}
    (hf : 2 * Fintype.card V ≤ fuel) (r x : V) : x ∈ (dfs search fuel r).visited ↔ Reach E r x := by
  have hg : Good E (dfs search fuel r) := (Good.init (E := E)).visit hS hf r
  constructor
  · intro hx
    rcases visit_reach hS fuel r rfl hx with h | h
    · simp [St.init] at h
    · exact h
  · intro hr
    exact hg.inv.reach_of_nil hg.nil (mem_visit_self fuel _ r) hr

/-- **DFS cost.** A search from `r` calls `search` at most `2n` times, whatever the fuel. -/
theorem dfs_searches_le {search : V → Finset V → Option V} (hS : IsSearch E search) (fuel : ℕ) (r : V) :
    (dfs search fuel r).searches ≤ 2 * Fintype.card V :=
  (Budget.init.visit hS r).searches_le

/-- With `2n` fuel, the stack ends empty. -/
theorem dfs_stack_nil {search : V → Finset V → Option V} (hS : IsSearch E search) {fuel : ℕ}
    (hf : 2 * Fintype.card V ≤ fuel) (r : V) : (dfs search fuel r).stack = [] :=
  ((Good.init (E := E)).visit hS hf r).nil

/-- Over any list of roots, the searches are at most `2n` in total. -/
theorem forest_searches_le {search : V → Finset V → Option V} (hS : IsSearch E search) (fuel : ℕ)
    (roots : List V) : (forest search fuel roots St.init).searches ≤ 2 * Fintype.card V :=
  (Budget.init.forest hS roots).searches_le

theorem Good.forest {search : V → Finset V → Option V} (hS : IsSearch E search) {fuel : ℕ}
    (hf : 2 * Fintype.card V ≤ fuel) (roots : List V) {s : St V} (h : Good E s) :
    Good E (forest search fuel roots s) := by
  induction roots generalizing s with
  | nil => exact h
  | cons r rs ih => exact ih (h.visit hS hf r)

theorem visited_forest_subset {search : V → Finset V → Option V} {fuel : ℕ} (roots : List V) (s : St V) :
    s.visited ⊆ (forest search fuel roots s).visited := by
  induction roots generalizing s with
  | nil => exact Finset.Subset.refl _
  | cons r rs ih => exact (visited_visit_subset fuel s r).trans (ih _)

/-- Every root is visited. -/
theorem mem_forest_of_mem {search : V → Finset V → Option V} {fuel : ℕ} {roots : List V} (s : St V) {r : V}
    (hr : r ∈ roots) : r ∈ (forest search fuel roots s).visited := by
  induction roots generalizing s with
  | nil => simp at hr
  | cons a rs ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · exact visited_forest_subset rs _ (mem_visit_self fuel s r)
    · exact ih _ hr

end Budget

end Dominators
