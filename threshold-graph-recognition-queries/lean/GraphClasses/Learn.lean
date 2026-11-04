import GraphClasses.Split

/-!
# The learner: Search, Holding, Trim, Learn

The search is a parameter with a specification: it returns a marked item if one exists, none otherwise. BBHT provides
this with high probability, which is a separate matter (see `Model.lean`, `Cost.lean`). The pivots are a parameter as
well: all correctness theorems hold for every choice of pivots, and so for every outcome of the random choices.
-/

open Finset

namespace GraphClasses

variable {R C : Type*}

/-- A search routine: given candidates and a predicate, an item or nothing. -/
abbrev Search (α : Type*) := Finset α → (α → Bool) → Option α

/-- A correct search: an item returned is a marked candidate, and "none" means there is no marked candidate. -/
def SearchSpec {α : Type*} (s : Search α) : Prop :=
  ∀ S f, (∀ a, s S f = some a → a ∈ S ∧ f a = true) ∧ (s S f = none → ∀ a ∈ S, f a = false)

/-- The specification can be met. -/
theorem exists_searchSpec (α : Type*) : ∃ s : Search α, SearchSpec s := by
  classical
  refine ⟨fun S f => if h : ∃ a ∈ S, f a = true then some h.choose else none, fun S f => ⟨fun a ha => ?_, fun h a ha => ?_⟩⟩
  · by_cases h : ∃ a ∈ S, f a = true
    · simp only [h, dif_pos, Option.some.injEq] at ha
      rw [← ha]
      exact h.choose_spec
    · simp [h] at ha
  · by_cases h' : ∃ a ∈ S, f a = true
    · simp [h'] at h
    · cases hf : f a
      · rfl
      · exact absurd ⟨a, ha, hf⟩ h'

/-- The columns of the block having an entry `val`. -/
def holdingSet (M : R → C → Bool) (A : Finset R) (B : Finset C) (val : Bool) : Finset C :=
  B.filter fun c => ∃ r ∈ A, M r c = val

section Holding

variable [DecidableEq C]

/-- **Holding(R, C, val)**, with fuel. Search `A × (B \ K)` for an entry equal to `val`. If none, return `K`. If
`(r, c)` is found, read row `r` on `B`, and add its `val`-entries to `K`. -/
def holding (s : Search (R × C)) (M : R → C → Bool) (A : Finset R) (B : Finset C) (val : Bool) :
    ℕ → Finset C → Finset C
  | 0, K => K
  | n + 1, K =>
    match s (A ×ˢ (B \ K)) (fun e => M e.1 e.2 == val) with
    | none => K
    | some e => holding s M A B val n (K ∪ B.filter fun c => M e.1 c == val)

/-- The invariant of Holding: `K` holds only columns having `val`. With enough fuel the result is exact. -/
theorem holding_eq {s : Search (R × C)} (hs : SearchSpec s) (M : R → C → Bool) (A : Finset R) (B : Finset C)
    (val : Bool) : ∀ (n : ℕ) (K : Finset C), K ⊆ holdingSet M A B val → (B \ K).card < n →
      holding s M A B val n K = holdingSet M A B val := by
  intro n
  induction n with
  | zero => intro K _ h; omega
  | succ n ih =>
    intro K hK hn
    rw [holding]
    have hsp := hs (A ×ˢ (B \ K)) (fun e => M e.1 e.2 == val)
    cases hse : s (A ×ˢ (B \ K)) (fun e => M e.1 e.2 == val) with
    | none =>
      refine Subset.antisymm hK fun c hc => ?_
      obtain ⟨hcB, r, hr, hrc⟩ := mem_filter.1 hc
      by_contra hcK
      have := hsp.2 hse (r, c) (mem_product.2 ⟨hr, mem_sdiff.2 ⟨hcB, hcK⟩⟩)
      simp [hrc] at this
    | some e =>
      obtain ⟨he, hf⟩ := hsp.1 e hse
      obtain ⟨he1, he2⟩ := mem_product.1 he
      obtain ⟨he2B, he2K⟩ := mem_sdiff.1 he2
      have hf' : M e.1 e.2 = val := by simpa using hf
      refine ih _ (union_subset hK fun c hc => ?_) ?_
      · obtain ⟨hcB, hm⟩ := mem_filter.1 hc
        exact mem_filter.2 ⟨hcB, e.1, he1, by simpa using hm⟩
      · have hlt : (B \ (K ∪ B.filter fun c => M e.1 c == val)).card < (B \ K).card := by
          refine card_lt_card ⟨fun c hc => ?_, fun hsub => ?_⟩
          · obtain ⟨h1, h2⟩ := mem_sdiff.1 hc
            exact mem_sdiff.2 ⟨h1, fun h3 => h2 (mem_union_left _ h3)⟩
          · have := hsub (mem_sdiff.2 ⟨he2B, he2K⟩)
            exact (mem_sdiff.1 this).2 (mem_union_right _ (mem_filter.2 ⟨he2B, by simpa using hf'⟩))
        omega

/-- **Lemma 2, the set.** With a correct search, Holding returns exactly the columns having `val`. No nestedness is
needed for this part; nestedness only bounds the number of rounds (`Rounds.lean`). -/
theorem holding_correct {s : Search (R × C)} (hs : SearchSpec s) (M : R → C → Bool) (A : Finset R) (B : Finset C)
    (val : Bool) : holding s M A B val (B.card + 1) ∅ = holdingSet M A B val := by
  refine holding_eq hs M A B val _ _ (empty_subset _) ?_
  simp

end Holding

section Learn

variable [DecidableEq R] [DecidableEq C]

/-- A learned table: a finite set of triples (row, column, value). -/
abbrev Table (R C : Type*) := Finset (R × C × Bool)

/-- The true table of a block. -/
def graphOn (M : R → C → Bool) (A : Finset R) (B : Finset C) : Table R C :=
  (A ×ˢ B).image fun e => (e.1, e.2, M e.1 e.2)

/-- A block recorded as constant `v`, without reading it. -/
def recConst (A : Finset R) (B : Finset C) (v : Bool) : Table R C :=
  (A ×ˢ B).image fun e => (e.1, e.2, v)

theorem mem_graphOn {M : R → C → Bool} {A : Finset R} {B : Finset C} {r : R} {c : C} {v : Bool} :
    (r, c, v) ∈ graphOn M A B ↔ r ∈ A ∧ c ∈ B ∧ M r c = v := by
  simp only [graphOn, mem_image, mem_product, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨h1, h2⟩, rfl, rfl, rfl⟩
    exact ⟨h1, h2, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨r, c, ⟨h1, h2⟩, rfl, rfl, h3⟩

theorem mem_recConst {A : Finset R} {B : Finset C} {v : Bool} {r : R} {c : C} {u : Bool} :
    (r, c, u) ∈ recConst A B v ↔ r ∈ A ∧ c ∈ B ∧ v = u := by
  simp only [recConst, mem_image, mem_product, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨h1, h2⟩, rfl, rfl, rfl⟩
    exact ⟨h1, h2, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨r, c, ⟨h1, h2⟩, rfl, rfl, h3⟩

/-- The result of Trim: the surviving rows and columns, and the entries recorded for the others. -/
structure Trimmed (R C : Type*) where
  rows : Finset R
  cols : Finset C
  table : Table R C

/-- **Trim(R, C).** Holding on columns and, on the transpose, on rows, for `val = 0` and `val = 1`, all on this same
block. A row or column missing from the `val`-list is constant `1 - val`: record those entries and remove it. -/
def trim (s : Search (R × C)) (t : Search (C × R)) (M : R → C → Bool) (A : Finset R) (B : Finset C) : Trimmed R C :=
  let C0 := holding s M A B false (B.card + 1) ∅
  let C1 := holding s M A B true (B.card + 1) ∅
  let R0 := holding t (fun c r => M r c) B A false (A.card + 1) ∅
  let R1 := holding t (fun c r => M r c) B A true (A.card + 1) ∅
  { rows := R0 ∩ R1
    cols := C0 ∩ C1
    table := recConst (A \ R0) B true ∪ recConst (A \ R1) B false ∪
      recConst A (B \ C0) true ∪ recConst A (B \ C1) false }

variable {s : Search (R × C)} {t : Search (C × R)}

theorem trim_rows (hs : SearchSpec t) (M : R → C → Bool) (A : Finset R) (B : Finset C) :
    (trim s t M A B).rows = survR M A B := by
  ext r
  simp only [trim, holding_correct hs, holdingSet, survR, mem_inter, mem_filter]
  tauto

theorem trim_cols (hs : SearchSpec s) (M : R → C → Bool) (A : Finset R) (B : Finset C) :
    (trim s t M A B).cols = survC M A B := by
  ext c
  simp only [trim, holding_correct hs, holdingSet, survC, mem_inter, mem_filter]
  tauto

/-- **Trim is right.** The recorded entries together with the true table of the surviving block are exactly the true
table of the block given. -/
theorem trim_table (hs : SearchSpec s) (ht : SearchSpec t) (M : R → C → Bool) (A : Finset R) (B : Finset C) :
    (trim s t M A B).table ∪ graphOn M (survR M A B) (survC M A B) = graphOn M A B := by
  ext ⟨r, c, v⟩
  simp only [trim, holding_correct hs, holding_correct ht, holdingSet, mem_union, mem_recConst, mem_sdiff,
    mem_filter, mem_graphOn, survR, survC]
  cases hm : M r c <;> cases v <;> simp only [Bool.true_eq_false, Bool.false_eq_true, false_and, and_false,
    or_false, true_and, and_true, reduceCtorEq, not_and, not_exists] <;> grind

/-- Recording a block that is learned by `rec`: Trim it, keep the record, and recurse on the survivors. -/
def goBlock (s : Search (R × C)) (t : Search (C × R)) (M : R → C → Bool) (rec : Finset R → Finset C → Table R C)
    (A : Finset R) (B : Finset C) : Table R C :=
  (trim s t M A B).table ∪ rec (trim s t M A B).rows (trim s t M A B).cols

/-- The node of Learn after reading row `x` and column `w`. -/
def learnNode (s : Search (R × C)) (t : Search (C × R)) (M : R → C → Bool) (rec : Finset R → Finset C → Table R C)
    (A : Finset R) (B : Finset C) (x : R) (w : C) : Table R C :=
  if M x w = true then
    recConst (rowsAt M A w false) (colsAt M B x false) false ∪
      goBlock s t M rec (rowsAt M A w false) (colsAt M B x true) ∪
      goBlock s t M rec (rowsAt M A w true) (colsAt M B x true) ∪
      goBlock s t M rec (rowsAt M A w true) (colsAt M B x false)
  else
    recConst (rowsAt M A w true) (colsAt M B x true) true ∪
      goBlock s t M rec (rowsAt M A w false) (colsAt M B x true) ∪
      goBlock s t M rec (rowsAt M A w false) (colsAt M B x false) ∪
      goBlock s t M rec (rowsAt M A w true) (colsAt M B x false)

/-- The base case of Learn: read everything. -/
def IsBase (A : Finset R) (B : Finset C) : Prop := A.card * B.card ≤ 4 * (A.card + B.card)

instance (A : Finset R) (B : Finset C) : Decidable (IsBase A B) := by unfold IsBase; infer_instance

/-- **Learn(R, C)**, with fuel. If the fuel runs out, nothing is recorded. `pick` chooses the pivots. -/
def learn (s : Search (R × C)) (t : Search (C × R)) (pick : Finset R → Finset C → Option (R × C))
    (M : R → C → Bool) : ℕ → Finset R → Finset C → Table R C
  | 0, _, _ => ∅
  | n + 1, A, B =>
    if IsBase A B then graphOn M A B
    else
      match pick A B with
      | none => ∅
      | some e => learnNode s t M (learn s t pick M n) A B e.1 e.2

/-- A correct choice of pivots: on a block with rows and columns, a row and a column of the block. -/
def PickSpec (pick : Finset R → Finset C → Option (R × C)) : Prop :=
  ∀ A B, A.Nonempty → B.Nonempty → ∃ x ∈ A, ∃ w ∈ B, pick A B = some (x, w)

/-- A non-base block has rows and columns. -/
theorem IsBase.nonempty_of_not {A : Finset R} {B : Finset C} (h : ¬ IsBase A B) : A.Nonempty ∧ B.Nonempty := by
  constructor
  · by_contra hA
    rw [not_nonempty_iff_eq_empty] at hA
    exact h (by simp [IsBase, hA])
  · by_contra hB
    rw [not_nonempty_iff_eq_empty] at hB
    exact h (by simp [IsBase, hB])

private theorem graphOn_mono_card {M : R → C → Bool} {A A' : Finset R} {B B' : Finset C}
    (hx : A' ⊆ A) (hy : B' ⊆ B) : graphOn M A' B' ⊆ graphOn M A B := by
  rintro ⟨r, c, v⟩ h
  obtain ⟨h1, h2, h3⟩ := mem_graphOn.1 h
  exact mem_graphOn.2 ⟨hx h1, hy h2, h3⟩

/-- A trimmed sub-block with a pivot removed is smaller, so it fits in the remaining fuel. -/
private theorem surv_size_lt {M : R → C → Bool} {A A' : Finset R} {B B' : Finset C} {x : R} {w : C}
    (hA : A' ⊆ A) (hB : B' ⊆ B) (hx : x ∈ A) (hw : w ∈ B)
    (h : x ∉ survR M A' B' ∨ w ∉ survC M A' B') :
    (survR M A' B').card + (survC M A' B').card < A.card + B.card := by
  have h1 : survR M A' B' ⊆ A := (survR_subset M A' B').trans hA
  have h2 : survC M A' B' ⊆ B := (survC_subset M A' B').trans hB
  rcases h with h | h
  · have h3 : (survR M A' B').card < A.card := card_lt_card ⟨h1, fun h4 => h (h4 hx)⟩
    have h4 := card_le_card h2
    omega
  · have h3 : (survC M A' B').card < B.card := card_lt_card ⟨h2, fun h4 => h (h4 hw)⟩
    have h4 := card_le_card h1
    omega

/-- One block handled by `goBlock`, given that recursion is right on its trimmed part. -/
private theorem goBlock_eq (hs : SearchSpec s) (ht : SearchSpec t) (M : R → C → Bool)
    {rec : Finset R → Finset C → Table R C} (A : Finset R) (B : Finset C)
    (h : rec (survR M A B) (survC M A B) = graphOn M (survR M A B) (survC M A B)) :
    goBlock s t M rec A B = graphOn M A B := by
  rw [goBlock, trim_rows ht, trim_cols hs, h, trim_table hs ht]

/-- A constant block is its true table. -/
private theorem recConst_eq {M : R → C → Bool} {A : Finset R} {B : Finset C} {v : Bool}
    (h : ∀ r ∈ A, ∀ c ∈ B, M r c = v) : recConst A B v = graphOn M A B := by
  ext ⟨r, c, u⟩
  simp only [mem_recConst, mem_graphOn]
  constructor
  · rintro ⟨h1, h2, rfl⟩
    exact ⟨h1, h2, h r h1 c h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by rw [← h r h1 c h2, h3]⟩

/-- The four sub-blocks cover the block. -/
private theorem graphOn_split (M : R → C → Bool) (A : Finset R) (B : Finset C) (x : R) (w : C) (r : R) (c : C) (v : Bool) :
    (r, c, v) ∈ graphOn M A B ↔
      (r, c, v) ∈ graphOn M (rowsAt M A w false) (colsAt M B x false) ∨
      (r, c, v) ∈ graphOn M (rowsAt M A w false) (colsAt M B x true) ∨
      (r, c, v) ∈ graphOn M (rowsAt M A w true) (colsAt M B x true) ∨
      (r, c, v) ∈ graphOn M (rowsAt M A w true) (colsAt M B x false) := by
  simp only [mem_graphOn, rowsAt, colsAt, mem_filter]
  cases M r w <;> cases M x c <;> simp

private theorem graphOn_cover_pos (M : R → C → Bool) (A : Finset R) (B : Finset C) (x : R) (w : C) :
    graphOn M (rowsAt M A w false) (colsAt M B x false) ∪ graphOn M (rowsAt M A w false) (colsAt M B x true) ∪
      graphOn M (rowsAt M A w true) (colsAt M B x true) ∪ graphOn M (rowsAt M A w true) (colsAt M B x false) =
    graphOn M A B := by
  ext ⟨r, c, v⟩
  rw [graphOn_split M A B x w r c v]
  simp only [mem_union]
  tauto

private theorem graphOn_cover_neg (M : R → C → Bool) (A : Finset R) (B : Finset C) (x : R) (w : C) :
    graphOn M (rowsAt M A w true) (colsAt M B x true) ∪ graphOn M (rowsAt M A w false) (colsAt M B x true) ∪
      graphOn M (rowsAt M A w false) (colsAt M B x false) ∪ graphOn M (rowsAt M A w true) (colsAt M B x false) =
    graphOn M A B := by
  ext ⟨r, c, v⟩
  rw [graphOn_split M A B x w r c v]
  simp only [mem_union]
  tauto

/-- **Learn is right.** On every nested block, with correct searches, correct pivots and fuel at least the number of
rows and columns, Learn records exactly the true table of the block: every entry, each with its true value, and
nothing else. -/
theorem learn_correct (hs : SearchSpec s) (ht : SearchSpec t) {pick : Finset R → Finset C → Option (R × C)}
    (hp : PickSpec pick) (M : R → C → Bool) :
    ∀ (n : ℕ) (A : Finset R) (B : Finset C), NestedOn M A B → A.card + B.card ≤ n →
      learn s t pick M n A B = graphOn M A B := by
  intro n
  induction n with
  | zero =>
    intro A B _ h
    have hA : A = ∅ := card_eq_zero.1 (by omega)
    have hB : B = ∅ := card_eq_zero.1 (by omega)
    subst hA hB
    simp [learn, graphOn]
  | succ n ih =>
    intro A B hN hn
    rw [learn]
    by_cases hb : IsBase A B
    · rw [if_pos hb]
    rw [if_neg hb]
    obtain ⟨hA, hB⟩ := IsBase.nonempty_of_not hb
    obtain ⟨x, hx, w, hw, hpick⟩ := hp A B hA hB
    rw [hpick]
    obtain ⟨p, q, hpq⟩ := (nestedOn_iff_positions M A B).1 hN
    -- recursion on a trimmed sub-block
    have rec_ok : ∀ {A' : Finset R} {B' : Finset C}, A' ⊆ A → B' ⊆ B →
        (x ∉ survR M A' B' ∨ w ∉ survC M A' B') →
        goBlock s t M (learn s t pick M n) A' B' = graphOn M A' B' := by
      intro A' B' hA' hB' hne
      refine goBlock_eq hs ht M A' B' (ih _ _ ?_ ?_)
      · exact hN.mono ((survR_subset M A' B').trans hA') ((survC_subset M A' B').trans hB')
      · have := surv_size_lt hA' hB' hx hw hne
        omega
    have hRA := rowsAt_subset M A w
    have hCB := colsAt_subset M B x
    obtain ⟨d1, d2, d3, d4, d5, d6, x1, x2, x3, w1, w2, w3⟩ := split_disjoint hpq hx hw
    show learnNode s t M (learn s t pick M n) A B x w = graphOn M A B
    unfold learnNode
    cases hm : M x w
    · simp only [splitBlocks, hm, reduceCtorEq, if_false] at x1 x2 x3 w1 w2 w3
      rw [if_neg (by simp), rec_ok (hRA _) (hCB _) (Or.inl x1), rec_ok (hRA _) (hCB _) (Or.inl x2),
        rec_ok (hRA _) (hCB _) (Or.inl x3)]
      rw [recConst_eq (lemma3_neg hpq hx hw hm).1]
      exact graphOn_cover_neg M A B x w
    · simp only [splitBlocks, hm, if_true] at x1 x2 x3 w1 w2 w3
      rw [if_pos rfl, rec_ok (hRA _) (hCB _) (Or.inl x1), rec_ok (hRA _) (hCB _) (Or.inl x2),
        rec_ok (hRA _) (hCB _) (Or.inl x3)]
      rw [recConst_eq (lemma3_pos hpq hx hw hm).1]
      exact graphOn_cover_pos M A B x w

end Learn

end GraphClasses
