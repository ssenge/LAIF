import GraphClasses.Learn

/-!
# Lemma 2, the rounds

The expected number of rounds of Holding when each search returns a uniformly random marked entry. The expectation is
written out as the finite recursion it is: one round, plus the average over the marked entries of what remains.
-/

open Finset

namespace GraphClasses

/-! ## The chain lemma, for weights -/

section Weights

variable {α : Type*} [DecidableEq α]

/-- The elements strictly heavier than `a`. -/
def heavier (w : α → ℕ) (U : Finset α) (a : α) : Finset α := U.filter fun b => w a < w b

/-- The elements whose reading at least halves `U`. -/
def halving (w : α → ℕ) (U : Finset α) : Finset α := U.filter fun a => 2 * (heavier w U a).card ≤ U.card

/-- **The upper half holds at least half the weight.** The elements with at most half of `U` strictly heavier carry
at least as much weight as the others. -/
theorem weight_halving (w : α → ℕ) (U : Finset α) :
    ∑ a ∈ U.filter (fun a => a ∉ halving w U), w a ≤ ∑ a ∈ halving w U, w a := by
  set B := U.filter (fun a => a ∉ halving w U) with hB
  rcases B.eq_empty_or_nonempty with he | hne
  · rw [he]; simp
  obtain ⟨r, hr, hmax⟩ := exists_max_image B w hne
  obtain ⟨hrU, hrT⟩ := mem_filter.1 hr
  have hrbad : U.card < 2 * (heavier w U r).card := by
    by_contra hc
    exact hrT (mem_filter.2 ⟨hrU, by omega⟩)
  -- Everything strictly heavier than `r` halves.
  have hsub : heavier w U r ⊆ halving w U := by
    intro b hb
    obtain ⟨hbU, hbw⟩ := mem_filter.1 hb
    by_contra hbT
    have := hmax b (mem_filter.2 ⟨hbU, hbT⟩)
    omega
  have hcardB : B.card ≤ (halving w U).card := by
    have hdis : Disjoint B (heavier w U r) := by
      refine disjoint_left.2 fun a ha hb => ?_
      have h1 := hmax a ha
      have h2 := (mem_filter.1 hb).2
      omega
    have hu : (B ∪ heavier w U r).card ≤ U.card :=
      card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
    rw [card_union_of_disjoint hdis] at hu
    have := card_le_card hsub
    omega
  -- Everything that halves is at least as heavy as `r`.
  have hheavy : ∀ a ∈ halving w U, w r ≤ w a := by
    intro a ha
    obtain ⟨haU, hac⟩ := mem_filter.1 ha
    by_contra hlt
    have hlt' : w a < w r := by omega
    have : (heavier w U r).card ≤ (heavier w U a).card := by
      refine card_le_card fun b hb => ?_
      obtain ⟨hbU, hbw⟩ := mem_filter.1 hb
      exact mem_filter.2 ⟨hbU, by omega⟩
    omega
  calc ∑ a ∈ B, w a ≤ ∑ _a ∈ B, w r := sum_le_sum fun a ha => hmax a ha
    _ = B.card * w r := by simp
    _ ≤ (halving w U).card * w r := Nat.mul_le_mul_right _ hcardB
    _ = ∑ _a ∈ halving w U, w r := by simp
    _ ≤ ∑ a ∈ halving w U, w a := sum_le_sum hheavy

end Weights

/-! ## The bound function -/

/-- The bound on the expected rounds with `u` rows left: `1 + 2 (⌊log₂ u⌋ + 1)`, and `1` for `u = 0`. -/
def roundsBound (u : ℕ) : ℝ := if u = 0 then 1 else 1 + 2 * ((Nat.log 2 u : ℝ) + 1)

theorem roundsBound_mono {u v : ℕ} (h : u ≤ v) : roundsBound u ≤ roundsBound v := by
  unfold roundsBound
  by_cases hu : u = 0
  · by_cases hv : v = 0
    · simp [hu, hv]
    · simp only [hu, hv, if_true, if_false]
      have : (0 : ℝ) ≤ (Nat.log 2 v : ℝ) := by positivity
      linarith
  · have hv : v ≠ 0 := by omega
    simp only [hu, hv, if_false]
    have : (Nat.log 2 u : ℝ) ≤ (Nat.log 2 v : ℝ) := by exact_mod_cast Nat.log_mono_right h
    linarith

/-- The step of the recurrence: halving saves `2`. -/
theorem roundsBound_half {u : ℕ} (hu : 1 ≤ u) : roundsBound (u / 2) + 2 ≤ roundsBound u := by
  unfold roundsBound
  have hu0 : u ≠ 0 := by omega
  by_cases h : u / 2 = 0
  · simp only [h, hu0, if_true, if_false]
    have : (0 : ℝ) ≤ (Nat.log 2 u : ℝ) := by positivity
    linarith
  · simp only [h, hu0, if_false]
    have hu2 : 2 ≤ u := by omega
    have e : Nat.log 2 u = Nat.log 2 (u / 2) + 1 := Nat.log_of_one_lt_of_le (by norm_num) hu2
    rw [e]
    push_cast
    linarith

/-- The recurrence: if at least half the weight drops to `u / 2` and the rest stays below `u`, then the average plus
one round is within the bound. Here `n` is the number of marked entries, `g` of them good. -/
theorem rounds_step {u n g : ℕ} (hu : 1 ≤ u) (hn : 0 < n) (hg : n ≤ 2 * g) (hgn : g ≤ n) :
    1 + ((g : ℝ) * roundsBound (u / 2) + ((n : ℝ) - g) * roundsBound u) / n ≤ roundsBound u := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hg' : (n : ℝ) ≤ 2 * g := by exact_mod_cast hg
  have hgn' : (g : ℝ) ≤ n := by exact_mod_cast hgn
  have hb := roundsBound_half hu
  rw [← sub_nonneg]
  have key : roundsBound u - (1 + ((g : ℝ) * roundsBound (u / 2) + ((n : ℝ) - g) * roundsBound u) / n) =
      ((g : ℝ) * (roundsBound u - roundsBound (u / 2)) - n) / n := by
    field_simp
    ring
  rw [key]
  apply div_nonneg _ hn'.le
  have hg0 : (0 : ℝ) ≤ g := by positivity
  have h2 : (g : ℝ) * 2 ≤ g * (roundsBound u - roundsBound (u / 2)) :=
    mul_le_mul_of_nonneg_left (by linarith) hg0
  linarith

/-! ## The expected rounds of Holding -/

variable {R C : Type*} [DecidableEq R] [DecidableEq C]

/-- The marked entries: `val`-entries outside `K`. -/
def marks (M : R → C → Bool) (A : Finset R) (B K : Finset C) (val : Bool) : Finset (R × C) :=
  (A ×ˢ (B \ K)).filter fun e => M e.1 e.2 = val

/-- The columns read when a row is found. -/
def rowVals (M : R → C → Bool) (B : Finset C) (val : Bool) (r : R) : Finset C := B.filter fun c => M r c = val

/-- **The expected rounds of Holding with uniform search.** One round, and if it finds something, the average over
the marked entries of what remains after reading the row found. With no fuel, nothing is counted. -/
noncomputable def expRounds (M : R → C → Bool) (A : Finset R) (B : Finset C) (val : Bool) : ℕ → Finset C → ℝ
  | 0, _ => 0
  | n + 1, K =>
    if (marks M A B K val).card = 0 then 1
    else 1 + (∑ e ∈ marks M A B K val, expRounds M A B val n (K ∪ rowVals M B val e.1)) /
      (marks M A B K val).card

/-- The rows with a `val`-entry outside `K`. -/
def openRows (M : R → C → Bool) (A : Finset R) (B K : Finset C) (val : Bool) : Finset R :=
  A.filter fun r => ((rowVals M B val r) \ K).Nonempty

theorem nestedOn_val {M : R → C → Bool} {A : Finset R} {B : Finset C} (h : NestedOn M A B) (val : Bool) :
    ∀ r ∈ A, ∀ s ∈ A, rowVals M B val r ⊆ rowVals M B val s ∨ rowVals M B val s ⊆ rowVals M B val r := by
  intro r hr s hs
  cases val
  · rcases h.complement r hr s hs with g | g
    · left
      intro c hc
      obtain ⟨hcB, hm⟩ := mem_filter.1 hc
      have := g c hcB (by simpa using hm)
      exact mem_filter.2 ⟨hcB, by simpa using this⟩
    · right
      intro c hc
      obtain ⟨hcB, hm⟩ := mem_filter.1 hc
      have := g c hcB (by simpa using hm)
      exact mem_filter.2 ⟨hcB, by simpa using this⟩
  · rcases h r hr s hs with g | g
    · left
      intro c hc
      obtain ⟨hcB, hm⟩ := mem_filter.1 hc
      exact mem_filter.2 ⟨hcB, g c hcB hm⟩
    · right
      intro c hc
      obtain ⟨hcB, hm⟩ := mem_filter.1 hc
      exact mem_filter.2 ⟨hcB, g c hcB hm⟩

/-- The weight of a row: its number of marked entries. -/
def rowWeight (M : R → C → Bool) (B K : Finset C) (val : Bool) (r : R) : ℕ := ((rowVals M B val r) \ K).card

/-- After reading row `r`, the rows left open are exactly the strictly heavier ones. -/
theorem openRows_after {M : R → C → Bool} {A : Finset R} {B K : Finset C} {val : Bool} (h : NestedOn M A B)
    {r : R} (hr : r ∈ openRows M A B K val) :
    openRows M A B (K ∪ rowVals M B val r) val =
      heavier (rowWeight M B K val) (openRows M A B K val) r := by
  have hrA : r ∈ A := (mem_filter.1 hr).1
  ext s
  have hL : s ∈ openRows M A B (K ∪ rowVals M B val r) val ↔
      s ∈ A ∧ ((rowVals M B val s) \ (K ∪ rowVals M B val r)).Nonempty := mem_filter
  have hR : s ∈ heavier (rowWeight M B K val) (openRows M A B K val) r ↔
      (s ∈ A ∧ ((rowVals M B val s) \ K).Nonempty) ∧
        ((rowVals M B val r) \ K).card < ((rowVals M B val s) \ K).card := by
    unfold heavier openRows rowWeight
    rw [mem_filter, mem_filter]
  rw [hL, hR]
  constructor
  · rintro ⟨hsA, c, hc⟩
    obtain ⟨hc1, hc2⟩ := mem_sdiff.1 hc
    simp only [mem_union, not_or] at hc2
    have hopen : ((rowVals M B val s) \ K).Nonempty := ⟨c, mem_sdiff.2 ⟨hc1, hc2.1⟩⟩
    refine ⟨⟨hsA, hopen⟩, ?_⟩
    rcases nestedOn_val h val r hrA s hsA with g | g
    · refine card_lt_card ⟨fun z hz => ?_, fun hsub => ?_⟩
      · obtain ⟨h1, h2⟩ := mem_sdiff.1 hz
        exact mem_sdiff.2 ⟨g h1, h2⟩
      · have := hsub (mem_sdiff.2 ⟨hc1, hc2.1⟩)
        exact hc2.2 (mem_sdiff.1 this).1
    · exact absurd (g hc1) hc2.2
  · rintro ⟨⟨hsA, _⟩, hlt⟩
    refine ⟨hsA, ?_⟩
    by_contra hemp
    rw [not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset] at hemp
    have hsub : (rowVals M B val s) \ K ⊆ (rowVals M B val r) \ K := by
      intro z hz
      obtain ⟨h1, h2⟩ := mem_sdiff.1 hz
      rcases mem_union.1 (hemp h1) with h3 | h3
      · exact absurd h3 h2
      · exact mem_sdiff.2 ⟨h3, h2⟩
    have := card_le_card hsub
    omega

/-- The marked entries lie in the open rows, and a row holds its weight of them. -/
theorem marks_card_fiber {M : R → C → Bool} {A : Finset R} {B K : Finset C} {val : Bool} (T : Finset R)
    (hT : T ⊆ A) : ((marks M A B K val).filter fun e => e.1 ∈ T).card = ∑ r ∈ T, rowWeight M B K val r := by
  have : (marks M A B K val).filter (fun e => e.1 ∈ T) =
      T.biUnion fun r => ((rowVals M B val r) \ K).image fun c => (r, c) := by
    ext ⟨r, c⟩
    simp only [marks, mem_filter, mem_product, mem_sdiff, mem_biUnion, mem_image, rowVals, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨_, hcB, hcK⟩, hm⟩, hrT⟩
      exact ⟨r, hrT, c, ⟨⟨hcB, hm⟩, hcK⟩, rfl, rfl⟩
    · rintro ⟨a, haT, b, ⟨⟨hbB, hm⟩, hbK⟩, rfl, rfl⟩
      exact ⟨⟨⟨hT haT, hbB, hbK⟩, hm⟩, haT⟩
  rw [this, card_biUnion]
  · refine sum_congr rfl fun r _ => ?_
    rw [card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2)]
    rfl
  · intro a _ b _ hab
    refine disjoint_left.2 fun e h1 h2 => ?_
    obtain ⟨_, _, rfl⟩ := mem_image.1 h1
    obtain ⟨_, _, h3⟩ := mem_image.1 h2
    exact hab (Prod.mk.inj h3).1.symm

/-- **Lemma 2, the rounds.** On a nested block, with a search that returns a uniformly random marked entry, Holding
takes at most `1 + 2 (⌊log₂ u⌋ + 1)` expected rounds, where `u ≤ |R|` is the number of rows with an entry `val` outside
`K`. The bound holds at any fuel, and so in the limit. -/
theorem expRounds_le {M : R → C → Bool} {A : Finset R} {B : Finset C} (h : NestedOn M A B) (val : Bool) :
    ∀ (n : ℕ) (K : Finset C), expRounds M A B val n K ≤ roundsBound (openRows M A B K val).card := by
  intro n
  induction n with
  | zero =>
    intro K
    simp only [expRounds]
    have := roundsBound_mono (Nat.zero_le (openRows M A B K val).card)
    have h0 : roundsBound 0 = 1 := by simp [roundsBound]
    linarith
  | succ n ih =>
    intro K
    rw [expRounds]
    set U := openRows M A B K val with hU
    have h0 : roundsBound 0 = 1 := by simp [roundsBound]
    by_cases hm : (marks M A B K val).card = 0
    · rw [if_pos hm]
      have := roundsBound_mono (Nat.zero_le U.card)
      linarith
    rw [if_neg hm]
    have hne : 0 < (marks M A B K val).card := by omega
    -- a marked entry's row is open
    have hopen : ∀ e ∈ marks M A B K val, e.1 ∈ U := by
      rintro ⟨r, c⟩ he
      simp only [marks, mem_filter, mem_product, mem_sdiff] at he
      exact mem_filter.2 ⟨he.1.1, c, mem_sdiff.2 ⟨mem_filter.2 ⟨he.1.2.1, he.2⟩, he.1.2.2⟩⟩
    have hUpos : 1 ≤ U.card := by
      obtain ⟨e, he⟩ := card_pos.1 hne
      exact card_pos.2 ⟨e.1, hopen e he⟩
    let w := rowWeight M B K val
    let G := (marks M A B K val).filter fun e => e.1 ∈ halving w U
    -- each entry: bound by the size left open after reading its row
    have hval : ∀ e ∈ marks M A B K val,
        expRounds M A B val n (K ∪ rowVals M B val e.1) ≤
          if e ∈ G then roundsBound (U.card / 2) else roundsBound U.card := by
      intro e he
      have h1 := ih (K ∪ rowVals M B val e.1)
      rw [openRows_after h (hopen e he)] at h1
      refine h1.trans ?_
      by_cases hg : e ∈ G
      · rw [if_pos hg]
        apply roundsBound_mono
        have h2 : 2 * (heavier w U e.1).card ≤ U.card := (mem_filter.1 (mem_filter.1 hg).2).2
        show (heavier w U e.1).card ≤ U.card / 2
        omega
      · rw [if_neg hg]
        exact roundsBound_mono (card_le_card (filter_subset _ _))
    have hsum := sum_le_sum hval
    -- count the good entries
    have hUA : U ⊆ A := filter_subset _ _
    have hTU : halving w U ⊆ U := filter_subset _ _
    have hG : G.card = ∑ r ∈ halving w U, w r := marks_card_fiber _ (hTU.trans hUA)
    have hall : (marks M A B K val).card = ∑ r ∈ U, w r := by
      rw [← marks_card_fiber U hUA]
      congr 1
      exact (filter_true_of_mem hopen).symm
    have hsplit := sum_filter_add_sum_filter_not U (fun a => a ∈ halving w U) w
    have hfil : U.filter (fun a => a ∈ halving w U) = halving w U := by
      ext a
      simp only [mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hTU h, h⟩⟩
    rw [hfil] at hsplit
    have hw := weight_halving w U
    have hgood : (marks M A B K val).card ≤ 2 * G.card := by omega
    have hgn : G.card ≤ (marks M A B K val).card := card_filter_le _ _
    have hite : (∑ e ∈ marks M A B K val, if e ∈ G then roundsBound (U.card / 2) else roundsBound U.card) =
        (G.card : ℝ) * roundsBound (U.card / 2) +
          (((marks M A B K val).card : ℝ) - G.card) * roundsBound U.card := by
      rw [sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
      have e1 : (marks M A B K val).filter (fun e => e ∈ G) = G := by
        ext e
        simp only [mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨(mem_filter.1 h).1, h⟩⟩
      have e2 := card_filter_add_card_filter_not (s := marks M A B K val) (fun e => e ∈ G)
      rw [e1] at e2 ⊢
      have e3 : (((marks M A B K val).filter fun e => e ∉ G).card : ℝ) =
          ((marks M A B K val).card : ℝ) - G.card := by
        rw [← e2]
        push_cast
        ring
      rw [e3]
    rw [hite] at hsum
    have hn' : (0 : ℝ) < (marks M A B K val).card := by exact_mod_cast hne
    have hstep := rounds_step hUpos hne hgood hgn
    calc 1 + (∑ e ∈ marks M A B K val, expRounds M A B val n (K ∪ rowVals M B val e.1)) /
          (marks M A B K val).card
        ≤ 1 + ((G.card : ℝ) * roundsBound (U.card / 2) +
          (((marks M A B K val).card : ℝ) - G.card) * roundsBound U.card) / (marks M A B K val).card := by
          have := div_le_div_of_nonneg_right hsum hn'.le
          linarith
      _ ≤ roundsBound U.card := hstep

/-- **Lemma 2, the rounds, from the start.** `O(log |R|)` expected rounds. -/
theorem expRounds_le_rows {M : R → C → Bool} {A : Finset R} {B : Finset C} (h : NestedOn M A B) (val : Bool)
    (n : ℕ) : expRounds M A B val n ∅ ≤ roundsBound A.card :=
  (expRounds_le h val n ∅).trans (roundsBound_mono (card_le_card (filter_subset _ _)))

end GraphClasses
