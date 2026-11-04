import GraphClasses.Recognition

/-!
# Threshold graphs

A threshold graph is built by repeatedly adding an isolated or a dominating vertex. Equivalently (proved here as
`threshold_iff_noAlt`) it has no alternating 4-cycle. The recursive split sends each pair to
exactly one cross block, and each cross block of a threshold graph is nested.
-/

open Finset

namespace GraphClasses

variable {V : Type*}

/-- An **alternating 4-cycle**: `ab`, `cd` edges and `ac`, `bd` non-edges, with `a ≠ c` and `b ≠ d`, since otherwise a
non-edge would be a trivial loop. The other vertices are then distinct as well (`AltCycle.ne`). -/
def AltCycle (G : SimpleGraph V) (a b c d : V) : Prop :=
  G.Adj a b ∧ G.Adj c d ∧ ¬ G.Adj a c ∧ ¬ G.Adj b d ∧ a ≠ c ∧ b ≠ d

/-- All four vertices of an alternating 4-cycle are distinct. -/
theorem AltCycle.ne {G : SimpleGraph V} {a b c d : V} (h : AltCycle G a b c d) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1.ne, h5, ?_, ?_, h6, h2.ne⟩
  · rintro rfl
    exact h3 h2.symm
  · rintro rfl
    exact h4 h2

/-- The graph has no alternating 4-cycle. -/
def NoAlt (G : SimpleGraph V) : Prop := ∀ a b c d, ¬ AltCycle G a b c d

/-- The vertex set `S` can be built by repeatedly adding a vertex that is isolated or dominating among those before. -/
inductive ThresholdOn (G : SimpleGraph V) : Finset V → Prop
  | empty : ThresholdOn G ∅
  | isolated {S : Finset V} {v : V} (hv : v ∉ S) (h : ThresholdOn G S) (hi : ∀ u ∈ S, ¬ G.Adj v u) :
      ThresholdOn G (S.cons v hv)
  | dominating {S : Finset V} {v : V} (hv : v ∉ S) (h : ThresholdOn G S) (hd : ∀ u ∈ S, G.Adj v u) :
      ThresholdOn G (S.cons v hv)

/-- **Threshold graph.** The whole vertex set can be built by adding isolated or dominating vertices. -/
def IsThreshold [Fintype V] (G : SimpleGraph V) : Prop := ThresholdOn G univ

/-- An alternating 4-cycle inside `S`. -/
def NoAltOn (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, ¬ AltCycle G a b c d

/-- Adding an isolated or a dominating vertex creates no alternating 4-cycle. -/
theorem ThresholdOn.noAltOn {G : SimpleGraph V} {S : Finset V} (h : ThresholdOn G S) : NoAltOn G S := by
  induction h with
  | empty => intro a ha; simp at ha
  | @isolated S v hv _ hi ih =>
    intro a ha b hb c hc d hd hcyc
    simp only [mem_cons] at ha hb hc hd
    have hne := hcyc.ne
    obtain ⟨h1, h2, h3, h4, _, _⟩ := hcyc
    rcases ha with rfl | ha
    · have hbS : b ∈ S := by rcases hb with rfl | hb; exact absurd rfl hne.1; exact hb
      exact hi b hbS h1
    rcases hb with rfl | hb
    · exact hi a ha h1.symm
    rcases hc with rfl | hc
    · have hdS : d ∈ S := by rcases hd with rfl | hd; exact absurd rfl hne.2.2.2.2.2; exact hd
      exact hi d hdS h2
    rcases hd with rfl | hd
    · exact hi c hc h2.symm
    exact ih a ha b hb c hc d hd ⟨h1, h2, h3, h4, hne.2.1, hne.2.2.2.2.1⟩
  | @dominating S v hv _ hd ih =>
    intro a ha b hb c hc d hd' hcyc
    simp only [mem_cons] at ha hb hc hd'
    have hne := hcyc.ne
    obtain ⟨h1, h2, h3, h4, _, _⟩ := hcyc
    rcases ha with rfl | ha
    · have hcS : c ∈ S := by rcases hc with rfl | hc; exact absurd rfl hne.2.1; exact hc
      exact h3 (hd c hcS)
    rcases hc with rfl | hc
    · exact h3 (hd a ha).symm
    rcases hb with rfl | hb
    · have hdS : d ∈ S := by rcases hd' with rfl | hd'; exact absurd rfl hne.2.2.2.2.1; exact hd'
      exact h4 (hd d hdS)
    rcases hd' with rfl | hd'
    · exact h4 (hd b hb).symm
    exact ih a ha b hb c hc d hd' ⟨h1, h2, h3, h4, hne.2.1, hne.2.2.2.2.1⟩

/-- A graph with no alternating 4-cycle on a nonempty `S` has an isolated or a dominating vertex within `S`. -/
private theorem exists_iso_or_dom [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V}
    (hS : S.Nonempty) (h : NoAltOn G S) :
    ∃ v ∈ S, (∀ u ∈ S, ¬ G.Adj v u) ∨ (∀ u ∈ S, u ≠ v → G.Adj v u) := by
  classical
  let nb : V → Finset V := fun v => S.filter (G.Adj v)
  obtain ⟨v, hv, hmax⟩ := exists_max_image S (fun v => (nb v).card) hS
  by_cases hdom : ∀ u ∈ S, u ≠ v → G.Adj v u
  · exact ⟨v, hv, Or.inr hdom⟩
  push Not at hdom
  obtain ⟨u, hu, huv, hnuv⟩ := hdom
  by_cases hiso : ∀ t ∈ S, ¬ G.Adj u t
  · exact ⟨u, hu, Or.inl hiso⟩
  push Not at hiso
  obtain ⟨t, ht, hut⟩ := hiso
  exfalso
  by_cases hvt : G.Adj v t
  · -- `t` is a neighbour of `v`, and `u` is a neighbour of `t` and not of `v`.
    have hle := hmax t ht
    have hex : ∃ s ∈ S, G.Adj v s ∧ s ≠ t ∧ ¬ G.Adj t s := by
      by_contra hno
      push Not at hno
      have hsub : insert u ((nb v).erase t) ⊆ (nb t).erase v := by
        intro z hz
        simp only [mem_insert, mem_erase, mem_filter, nb] at hz ⊢
        rcases hz with rfl | ⟨hzt, hzS, hvz⟩
        · exact ⟨huv, hu, hut.symm⟩
        · exact ⟨hvz.ne', hzS, hno z hzS hvz hzt⟩
      have hc := card_le_card hsub
      have hu' : u ∉ (nb v).erase t := by
        simp only [mem_erase, mem_filter, nb]
        rintro ⟨_, _, h3⟩
        exact hnuv h3
      have e1 : ((nb v).erase t).card = (nb v).card - 1 := card_erase_of_mem (mem_filter.2 ⟨ht, hvt⟩)
      have e2 : ((nb t).erase v).card = (nb t).card - 1 := card_erase_of_mem (mem_filter.2 ⟨hv, hvt.symm⟩)
      rw [card_insert_of_notMem hu', e1, e2] at hc
      have hpos : 0 < (nb v).card := card_pos.2 ⟨t, mem_filter.2 ⟨ht, hvt⟩⟩
      have hle' : (nb t).card ≤ (nb v).card := hle
      omega
    obtain ⟨s, hs, hvs, hst, hts⟩ := hex
    refine h v hv s hs u hu t ht ⟨hvs, hut, hnuv, fun hst' => hts hst'.symm, huv.symm, hst⟩
  · -- `t` is a neighbour of `u` and not of `v`.
    have hle := hmax u hu
    have hex : ∃ s ∈ S, G.Adj v s ∧ ¬ G.Adj u s := by
      by_contra hno
      push Not at hno
      have hsub : insert t (nb v) ⊆ nb u := by
        intro z hz
        simp only [mem_insert, mem_filter, nb] at hz ⊢
        rcases hz with rfl | ⟨hzS, hvz⟩
        · exact ⟨ht, hut⟩
        · exact ⟨hzS, hno z hzS hvz⟩
      have hc := card_le_card hsub
      have ht' : t ∉ nb v := by
        simp only [mem_filter, nb]
        exact fun h' => hvt h'.2
      rw [card_insert_of_notMem ht'] at hc
      have hle' : (nb u).card ≤ (nb v).card := hle
      omega
    obtain ⟨s, hs, hvs, hus⟩ := hex
    have hne : v ≠ t := by
      rintro rfl
      exact hnuv hut.symm
    have hsu : s ≠ u := by
      rintro rfl
      exact hnuv hvs
    exact h v hv s hs t ht u hu ⟨hvs, hut.symm, hvt, fun h' => hus h'.symm, hne, hsu⟩

/-- No alternating 4-cycle gives a build order. -/
theorem thresholdOn_of_noAltOn [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] :
    ∀ (n : ℕ) (S : Finset V), S.card = n → NoAltOn G S → ThresholdOn G S := by
  intro n
  induction n with
  | zero =>
    intro S hS _
    rw [card_eq_zero.1 hS]
    exact ThresholdOn.empty
  | succ n ih =>
    intro S hS h
    obtain ⟨v, hv, hcase⟩ := exists_iso_or_dom (card_pos.1 (by omega)) h
    have hsub : S.erase v ⊆ S := erase_subset _ _
    have hrec : ThresholdOn G (S.erase v) := by
      refine ih _ (by rw [card_erase_of_mem hv]; omega) ?_
      intro a ha b hb c hc d hd
      exact h a (hsub ha) b (hsub hb) c (hsub hc) d (hsub hd)
    have heq : (S.erase v).cons v (notMem_erase v S) = S := by
      rw [cons_eq_insert, insert_erase hv]
    rw [← heq]
    rcases hcase with hi | hd
    · exact ThresholdOn.isolated _ hrec fun u hu => hi u (hsub hu)
    · exact ThresholdOn.dominating _ hrec fun u hu => hd u (hsub hu) (ne_of_mem_erase hu)

/-- **Characterization.** A graph is a threshold graph iff it has no alternating 4-cycle. -/
theorem threshold_iff_noAlt [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsThreshold G ↔ NoAlt G := by
  constructor
  · intro h a b c d
    exact h.noAltOn a (mem_univ _) b (mem_univ _) c (mem_univ _) d (mem_univ _)
  · intro h
    exact thresholdOn_of_noAltOn _ univ rfl fun a _ b _ c _ d _ => h a b c d

/-! ## Cross blocks -/

/-- The adjacency matrix. -/
def adjM (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : Bool := decide (G.Adj u v)

@[simp] theorem adjM_eq_true {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} : adjM G u v = true ↔ G.Adj u v := by
  simp [adjM]

/-- **Threshold to nested.** With no alternating 4-cycle, every cross block is nested. Disjointness of the two parts
is what makes the 2 × 2 pattern a genuine alternating 4-cycle. -/
theorem cross_block_nested {G : SimpleGraph V} [DecidableRel G.Adj] (h : NoAlt G) {A B : Finset V}
    (hAB : Disjoint A B) : NestedOn (adjM G) A B := by
  intro r hr s hs
  by_contra hno
  push Not at hno
  obtain ⟨⟨c, hc, hrc, hsc⟩, d, hd, hsd, hrd⟩ := hno
  have hrc' : G.Adj r c := by simpa [adjM] using hrc
  have hsd' : G.Adj s d := by simpa [adjM] using hsd
  have hsc' : ¬ G.Adj s c := by simpa [adjM] using hsc
  have hrd' : ¬ G.Adj r d := by simpa [adjM] using hrd
  have hrdne : r ≠ d := fun e => disjoint_left.1 hAB hr (e ▸ hd)
  have hcsne : c ≠ s := fun e => disjoint_left.1 hAB hs (e ▸ hc)
  exact h r c d s ⟨hrc', hsd'.symm, hrd', fun h' => hsc' h'.symm, hrdne, hcsne⟩

/-! ## The recursive split -/

/-- A correct and balanced split of a vertex set in two parts. -/
def SplitSpec [DecidableEq V] (split : Finset V → Finset V × Finset V) : Prop :=
  ∀ S : Finset V, 2 ≤ S.card →
    Disjoint (split S).1 (split S).2 ∧ (split S).1 ∪ (split S).2 = S ∧
    (split S).1.Nonempty ∧ (split S).2.Nonempty ∧
    2 * (split S).1.card ≤ S.card + 1 ∧ 2 * (split S).2.card ≤ S.card + 1

/-- The specification can be met. -/
theorem exists_splitSpec [DecidableEq V] : ∃ split : Finset V → Finset V × Finset V, SplitSpec split := by
  have key : ∀ S : Finset V, ∃ A : Finset V, A ⊆ S ∧ A.card = S.card / 2 := fun S =>
    exists_subset_card_eq (Nat.div_le_self _ _)
  choose f hf1 hf2 using key
  refine ⟨fun S => (f S, S \ f S), fun S hS => ?_⟩
  have hc : (S \ f S).card = S.card - S.card / 2 := by
    rw [card_sdiff_of_subset (hf1 S), hf2 S]
  refine ⟨disjoint_sdiff, union_sdiff_of_subset (hf1 S), card_pos.1 ?_, card_pos.1 ?_, ?_, ?_⟩
  · simp only [hf2 S]; omega
  · simp only [hc]; omega
  · simp only [hf2 S]; omega
  · simp only [hc]; omega

/-- The cross blocks of the recursive split, with fuel. -/
def blocks (split : Finset V → Finset V × Finset V) : ℕ → Finset V → List (Finset V × Finset V)
  | 0, _ => []
  | n + 1, S =>
    if S.card ≤ 1 then [] else split S :: (blocks split n (split S).1 ++ blocks split n (split S).2)

/-- The block separates `u` and `v`. -/
def Crosses [DecidableEq V] (u v : V) (b : Finset V × Finset V) : Prop :=
  (u ∈ b.1 ∧ v ∈ b.2) ∨ (v ∈ b.1 ∧ u ∈ b.2)

instance [DecidableEq V] (u v : V) : DecidablePred (Crosses u v) := fun b => by
  unfold Crosses; infer_instance

section Split

variable [DecidableEq V] {split : Finset V → Finset V × Finset V}

/-- Every block is a pair of disjoint subsets of `S`. -/
theorem mem_blocks (hsp : SplitSpec split) : ∀ (n : ℕ) (S : Finset V), ∀ b ∈ blocks split n S,
    b.1 ⊆ S ∧ b.2 ⊆ S ∧ Disjoint b.1 b.2 := by
  intro n
  induction n with
  | zero => intro S b hb; simp [blocks] at hb
  | succ n ih =>
    intro S b hb
    rw [blocks] at hb
    split_ifs at hb with h
    · simp at hb
    · obtain ⟨hd, hu, _, _, _, _⟩ := hsp S (by omega)
      have h1 : (split S).1 ⊆ S := fun z hz => by
        have := mem_union_left (split S).2 hz
        rwa [hu] at this
      have h2 : (split S).2 ⊆ S := fun z hz => by
        have := mem_union_right (split S).1 hz
        rwa [hu] at this
      simp only [List.mem_cons, List.mem_append] at hb
      rcases hb with rfl | hb | hb
      · exact ⟨h1, h2, hd⟩
      · obtain ⟨a, b', c⟩ := ih _ b hb
        exact ⟨a.trans h1, b'.trans h1, c⟩
      · obtain ⟨a, b', c⟩ := ih _ b hb
        exact ⟨a.trans h2, b'.trans h2, c⟩

/-- Every block has at least two rows and columns: both parts are nonempty. -/
theorem blocks_two_le (hsp : SplitSpec split) : ∀ (n : ℕ) (S : Finset V), ∀ b ∈ blocks split n S,
    2 ≤ b.1.card + b.2.card := by
  intro n
  induction n with
  | zero => intro S b hb; simp [blocks] at hb
  | succ n ih =>
    intro S b hb
    rw [blocks] at hb
    split_ifs at hb with h
    · simp at hb
    · obtain ⟨_, _, h1, h2, _, _⟩ := hsp S (by omega)
      simp only [List.mem_cons, List.mem_append] at hb
      rcases hb with rfl | hb | hb
      · have := card_pos.2 h1
        have := card_pos.2 h2
        omega
      · exact ih _ b hb
      · exact ih _ b hb

private theorem count_zero (hsp : SplitSpec split) (n : ℕ) (S : Finset V) (u v : V) (h : u ∉ S ∨ v ∉ S) :
    (blocks split n S).countP (fun b => decide (Crosses u v b)) = 0 := by
  rw [List.countP_eq_zero]
  intro b hb
  obtain ⟨h1, h2, _⟩ := mem_blocks hsp n S b hb
  simp only [decide_eq_true_eq, Crosses]
  rintro (⟨a, c⟩ | ⟨a, c⟩)
  · rcases h with h | h
    · exact h (h1 a)
    · exact h (h2 c)
  · rcases h with h | h
    · exact h (h2 c)
    · exact h (h1 a)

/-- **Each pair falls in exactly one block** of the recursive split. -/
theorem pair_in_one_block (hsp : SplitSpec split) : ∀ (n : ℕ) (S : Finset V), S.card ≤ n → ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
    (blocks split n S).countP (fun b => decide (Crosses u v b)) = 1 := by
  intro n
  induction n with
  | zero =>
    intro S hS u hu
    have := card_pos.2 ⟨u, hu⟩
    omega
  | succ n ih =>
    intro S hS u hu v hv huv
    rw [blocks]
    have h2 : 2 ≤ S.card := by
      have : 1 < S.card := one_lt_card.2 ⟨u, hu, v, hv, huv⟩
      omega
    rw [if_neg (by omega)]
    obtain ⟨hd, hun, hne1, hne2, _, _⟩ := hsp S h2
    have hc1 : (split S).1.card ≤ n := by
      have hsum : (split S).1.card + (split S).2.card = S.card := by
        rw [← card_union_of_disjoint hd, hun]
      have := card_pos.2 hne2
      omega
    have hc2 : (split S).2.card ≤ n := by
      have hsum : (split S).1.card + (split S).2.card = S.card := by
        rw [← card_union_of_disjoint hd, hun]
      have := card_pos.2 hne1
      omega
    have hmem : ∀ z ∈ S, z ∈ (split S).1 ∨ z ∈ (split S).2 := fun z hz => by
      rw [← hun] at hz
      exact mem_union.1 hz
    have hnot : ∀ z, z ∈ (split S).1 → z ∉ (split S).2 := fun z hz => disjoint_left.1 hd hz
    have hnot' : ∀ z, z ∈ (split S).2 → z ∉ (split S).1 := fun z h1 h2 => hnot z h2 h1
    rw [List.countP_cons, List.countP_append]
    rcases hmem u hu with hu1 | hu2 <;> rcases hmem v hv with hv1 | hv2
    · have e1 := ih _ hc1 u hu1 v hv1 huv
      have e2 := count_zero hsp n (split S).2 u v (Or.inl (hnot u hu1))
      have e3 : ¬ Crosses u v (split S) := by
        rintro (⟨_, a⟩ | ⟨_, a⟩)
        · exact hnot v hv1 a
        · exact hnot u hu1 a
      simp [e1, e2, e3]
    · have e1 := count_zero hsp n (split S).1 u v (Or.inr (hnot' v hv2))
      have e2 := count_zero hsp n (split S).2 u v (Or.inl (hnot u hu1))
      have e3 : Crosses u v (split S) := Or.inl ⟨hu1, hv2⟩
      simp [e1, e2, e3]
    · have e1 := count_zero hsp n (split S).1 u v (Or.inl (hnot' u hu2))
      have e2 := count_zero hsp n (split S).2 u v (Or.inr (hnot v hv1))
      have e3 : Crosses u v (split S) := Or.inr ⟨hv1, hu2⟩
      simp [e1, e2, e3]
    · have e1 := count_zero hsp n (split S).1 u v (Or.inl (hnot' u hu2))
      have e2 := ih _ hc2 u hu2 v hv2 huv
      have e3 : ¬ Crosses u v (split S) := by
        rintro (⟨a, _⟩ | ⟨a, _⟩)
        · exact hnot' u hu2 a
        · exact hnot' v hv2 a
      simp [e1, e2, e3]

/-- **Threshold to nested, all blocks.** Every block of the recursive split of a graph with no alternating 4-cycle is
nested. -/
theorem blocks_nested (hsp : SplitSpec split) {G : SimpleGraph V} [DecidableRel G.Adj] (h : NoAlt G) (n : ℕ)
    (S : Finset V) : ∀ b ∈ blocks split n S, NestedOn (adjM G) b.1 b.2 := fun b hb =>
  cross_block_nested h (mem_blocks hsp n S b hb).2.2

/-! ## Theorem 3, the logic -/

variable [Fintype V]

/-- The table of all blocks: Learn each block with enough fuel. -/
def learnBlocks (s : Search (V × V)) (pick : Finset V → Finset V → Option (V × V)) (M : V → V → Bool)
    (bs : List (Finset V × Finset V)) : Table V V :=
  bs.foldr (fun b T => learn s s pick M (b.1.card + b.2.card) b.1 b.2 ∪ T) ∅

theorem mem_learnBlocks {s : Search (V × V)} {pick : Finset V → Finset V → Option (V × V)} {M : V → V → Bool}
    {bs : List (Finset V × Finset V)} {e : V × V × Bool} :
    e ∈ learnBlocks s pick M bs ↔ ∃ b ∈ bs, e ∈ learn s s pick M (b.1.card + b.2.card) b.1 b.2 := by
  induction bs with
  | nil => simp [learnBlocks]
  | cons b bs ih =>
    have : learnBlocks s pick M (b :: bs) =
        learn s s pick M (b.1.card + b.2.card) b.1 b.2 ∪ learnBlocks s pick M bs := rfl
    rw [this, mem_union, ih]
    simp only [List.mem_cons, exists_eq_or_imp]

/-- The hypothesis graph of a table: `uv` is an edge iff the table records `(u, v)` or `(v, u)` as `1`. -/
def tableGraph (T : Table V V) : SimpleGraph V := SimpleGraph.fromRel fun u v => (u, v, true) ∈ T

instance (T : Table V V) : DecidableRel (tableGraph T).Adj := fun u v => by
  unfold tableGraph
  rw [SimpleGraph.fromRel_adj]
  infer_instance

/-- All ordered pairs of distinct vertices. -/
def allPairs (V : Type*) [Fintype V] [DecidableEq V] : Finset (V × V) := (univ : Finset V).offDiag

/-- A graph as a function on the pairs. -/
def pairFn (G : SimpleGraph V) [DecidableRel G.Adj] (e : V × V) : Bool := decide (G.Adj e.1 e.2)

/-- The recognizer: Learn all cross blocks, reject if the hypothesis has an alternating 4-cycle, and search all pairs
for a disagreement with the input. The class test is free, since it only looks at the hypothesis. -/
noncomputable def recognizeThreshold (s : Search (V × V)) (pick : Finset V → Finset V → Option (V × V))
    (split : Finset V → Finset V × Finset V) (G : SimpleGraph V) [DecidableRel G.Adj] : Bool :=
  let H := tableGraph (learnBlocks s pick (adjM G) (blocks split (Fintype.card V) univ))
  (open Classical in decide (NoAlt H)) && (s (allPairs V) fun e => pairFn H e != pairFn G e).isNone

/-- Two graphs that agree on all pairs are equal. -/
private theorem graph_eq_of_pairs {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : ∀ e ∈ allPairs V, pairFn H e = pairFn G e) : H = G := by
  ext u v
  by_cases huv : u = v
  · subst huv
    simp
  · have := h (u, v) (by simp [allPairs, huv])
    simpa [pairFn] using this

/-- With a correct search, equal graphs have no disagreement. -/
theorem search_none_of_eq {s : Search (V × V)} (hs : SearchSpec s) {H G : SimpleGraph V} [DecidableRel H.Adj]
    [DecidableRel G.Adj] (h : H = G) : s (allPairs V) (fun e => pairFn H e != pairFn G e) = none := by
  cases he : s (allPairs V) (fun e => pairFn H e != pairFn G e) with
  | none => rfl
  | some a =>
    obtain ⟨_, h2⟩ := (hs (allPairs V) fun e => pairFn H e != pairFn G e).1 a he
    have : pairFn H a = pairFn G a := by
      simp only [pairFn, decide_eq_decide]
      rw [h]
    simp [this] at h2

/-- **Theorem 3, the logic.** With a correct search, the recognizer accepts exactly the threshold graphs. -/
theorem recognizeThreshold_iff {s : Search (V × V)} (hs : SearchSpec s) {pick : Finset V → Finset V → Option (V × V)}
    (hp : PickSpec pick) (hsp : SplitSpec split) (G : SimpleGraph V) [DecidableRel G.Adj] :
    recognizeThreshold s pick split G = true ↔ IsThreshold G := by
  rw [threshold_iff_noAlt]
  simp only [recognizeThreshold, Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none]
  set H := tableGraph (learnBlocks s pick (adjM G) (blocks split (Fintype.card V) univ)) with hH
  constructor
  · rintro ⟨h1, h2⟩
    have hag : ∀ e ∈ allPairs V, pairFn H e = pairFn G e := by
      intro e he
      have := (hs (allPairs V) fun e => pairFn H e != pairFn G e).2 h2 e he
      simpa using this
    rw [← graph_eq_of_pairs hag]
    exact h1
  · intro hG
    have hHG : H = G := by
      ext u v
      by_cases huv : u = v
      · subst huv
        simp
      rw [hH, tableGraph, SimpleGraph.fromRel_adj]
      have hcorrect : ∀ b ∈ blocks split (Fintype.card V) univ,
          learn s s pick (adjM G) (b.1.card + b.2.card) b.1 b.2 = graphOn (adjM G) b.1 b.2 := fun b hb =>
        learn_correct hs hs hp _ _ _ _ (blocks_nested hsp hG _ _ b hb) le_rfl
      have hmem : ∀ a c : V, (a, c, true) ∈ learnBlocks s pick (adjM G) (blocks split (Fintype.card V) univ) ↔
          ∃ b ∈ blocks split (Fintype.card V) univ, a ∈ b.1 ∧ c ∈ b.2 ∧ G.Adj a c := by
        intro a c
        rw [mem_learnBlocks]
        constructor
        · rintro ⟨b, hb, he⟩
          rw [hcorrect b hb] at he
          obtain ⟨h1, h2, h3⟩ := mem_graphOn.1 he
          exact ⟨b, hb, h1, h2, adjM_eq_true.1 h3⟩
        · rintro ⟨b, hb, h1, h2, h3⟩
          refine ⟨b, hb, ?_⟩
          rw [hcorrect b hb]
          exact mem_graphOn.2 ⟨h1, h2, adjM_eq_true.2 h3⟩
      simp only [hmem]
      constructor
      · rintro ⟨_, ⟨b, _, _, _, h⟩ | ⟨b, _, _, _, h⟩⟩
        · exact h
        · exact h.symm
      · intro hadj
        refine ⟨huv, ?_⟩
        have hcount := pair_in_one_block hsp (Fintype.card V) univ le_rfl u (mem_univ u) v (mem_univ v) huv
        have hpos : 0 < (blocks split (Fintype.card V) univ).countP (fun b => decide (Crosses u v b)) := by
          rw [hcount]; exact Nat.one_pos
        obtain ⟨b, hb, hcr⟩ := List.countP_pos_iff.1 hpos
        rcases of_decide_eq_true hcr with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨b, hb, h1, h2, hadj⟩
        · exact Or.inr ⟨b, hb, h1, h2, hadj.symm⟩
    refine ⟨?_, search_none_of_eq hs hHG⟩
    show NoAlt H
    rw [hHG]
    exact hG

end Split

end GraphClasses
