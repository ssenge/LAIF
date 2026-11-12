import PlanarMatching.Tutte

/-!
# The search for mates

`notes/GENERAL.md`, Section 4, Lemma 6, over a field `K` and a finite index type `V`. A set `U` is *nonsingular*
when the block of `A` on `U` is (`Nsg`). A candidate mate of `s` in `U` is a neighbour `v ≠ s` with a nonzero entry
`(A_{U,U})⁻¹_{v,s}` (`cand`).

* `pick_step`: if `A_{U,U}` is nonsingular and `s ∈ U`, then `s` has a candidate, and for every candidate `v` the block
  on `U ∖ {s, v}` is nonsingular (Lemmas 4 and 5).
* `search_spec`: the search at a bag matches every hub to a neighbour, for any rule that picks a candidate, and
  leaves a nonsingular block.
* `nsg_block`: a block that has no entries to the rest of `U` is nonsingular together with the rest.
* `Sched.matched`: bags run one after the other, each on its part of the unmatched vertices. If that part has no
  entries to the other unmatched vertices, and every vertex of `B` is a hub of a bag that holds it, then the pairs
  found are a perfect matching of `B` by edges of `A`.
-/

namespace PlanarMatching

open Matrix

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] {V : Type*} [Fintype V] [DecidableEq V]

/-- The block of `A` on `U` is nonsingular. -/
def Nsg (A : Matrix V V K) (U : Finset V) : Prop := IsUnit (principal A U).det

/-- The entry `(v, s)` of the inverse of the block on `U`. -/
noncomputable def invOn (A : Matrix V V K) (U : Finset V) (v s : V) : K :=
  if h : v ∈ U ∧ s ∈ U then (principal A U)⁻¹ ⟨v, h.1⟩ ⟨s, h.2⟩ else 0

open Classical in
/-- The candidate mates of `s` in `U`. -/
noncomputable def cand (A : Matrix V V K) (U : Finset V) (s : V) : Finset V :=
  U.filter fun v => v ≠ s ∧ A s v ≠ 0 ∧ invOn A U v s ≠ 0

/-- Removing two indices from `U` is a principal block of the block on `U`. -/
theorem det_sdiff_pair (A : Matrix V V K) {U : Finset V} {s v : V} (hs : s ∈ U) (hv : v ∈ U) :
    (principal A (U \ {s, v})).det =
      (principal (principal A U) ({⟨s, hs⟩, ⟨v, hv⟩} : Finset ↥U)ᶜ).det := by
  let e : ↥(U \ {s, v}) ≃ ↥(({⟨s, hs⟩, ⟨v, hv⟩} : Finset ↥U)ᶜ) :=
    { toFun := fun x => ⟨⟨x.1, (Finset.mem_sdiff.1 x.2).1⟩, by
        have := (Finset.mem_sdiff.1 x.2).2
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at this
        simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or, Subtype.ext_iff]
        exact this⟩
      invFun := fun y => ⟨y.1.1, by
        have := Finset.mem_compl.1 y.2
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or, Subtype.ext_iff] at this
        exact Finset.mem_sdiff.2 ⟨y.1.2, by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact this⟩⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  rw [← det_submatrix_equiv_self e]
  rfl

/-- **One pick.** If the block on `U` is nonsingular and `s ∈ U`, then `s` has a candidate mate, and removing `s`
with any candidate leaves a nonsingular block. -/
theorem pick_step {A : Matrix V V K} (hA : IsAlternating A) {U : Finset V} (hU : Nsg A U) {s : V} (hs : s ∈ U) :
    (cand A U s).Nonempty ∧ ∀ v ∈ cand A U s, Nsg A (U \ {s, v}) := by
  classical
  have hM : IsAlternating (principal A U) := hA.submatrix _
  constructor
  · obtain ⟨v, h1, h2⟩ := mate_exists (mul_nonsing_inv _ hU) ⟨s, hs⟩
    refine ⟨v.1, Finset.mem_filter.2 ⟨v.2, ?_, h1, ?_⟩⟩
    · intro e
      have : v = ⟨s, hs⟩ := Subtype.ext e
      rw [this] at h1
      exact h1 (hM.diag _)
    · rw [invOn, dite_eq_left_of_eq_true (eq_true ⟨v.2, hs⟩)]; exact h2
  · intro v hv
    obtain ⟨hvU, hne, -, hinv⟩ := Finset.mem_filter.1 hv
    rw [invOn, dite_eq_left_of_eq_true (eq_true ⟨hvU, hs⟩)] at hinv
    have hsv : (⟨s, hs⟩ : ↥U) ≠ ⟨v, hvU⟩ := fun e => hne (congrArg Subtype.val e).symm
    rw [Nsg, isUnit_iff_ne_zero, det_sdiff_pair A hs hvU]
    exact (minor_ne_zero_iff hM hU hsv).2 hinv

/-- The ends of a list of pairs. -/
def ends (ps : List (V × V)) : List V := ps.flatMap fun p => [p.1, p.2]

/-- The search at a bag: each hub in turn, unless it is matched already, takes the mate given by `pick`. -/
def search (pick : Finset V → V → V) : List V → Finset V → List (V × V) × Finset V
  | [], U => ([], U)
  | s :: hs, U =>
    if s ∈ U then
      let r := search pick hs (U \ {s, pick U s})
      ((s, pick U s) :: r.1, r.2)
    else search pick hs U

theorem search_sub (pick : Finset V → V → V) : ∀ (hubs : List V) (U : Finset V), (search pick hubs U).2 ⊆ U
  | [], U => le_rfl
  | s :: hs, U => by
    unfold search
    split_ifs
    · exact (search_sub pick hs _).trans Finset.sdiff_subset
    · exact search_sub pick hs U

/-- Every hub leaves the unmatched set, whatever the rule picks. -/
theorem search_hub (pick : Finset V → V → V) : ∀ (hubs : List V) (U : Finset V), ∀ h ∈ hubs,
    h ∉ (search pick hubs U).2
  | [], _, _, hh => absurd hh List.not_mem_nil
  | s :: hs, U, h, hh => by
    unfold search
    rcases List.mem_cons.1 hh with rfl | hh
    · split_ifs with hsU
      · intro h'
        have := Finset.mem_sdiff.1 (search_sub pick hs _ h')
        simp at this
      · exact fun h' => hsU (search_sub pick hs U h')
    · split_ifs
      · exact search_hub pick hs _ h hh
      · exact search_hub pick hs U h hh

/-- **The search at a bag.** For any rule that picks a candidate, every hub is matched, each pair is an edge of
`A`, the pairs cover exactly the matched vertices, each once, and the unmatched vertices form a nonsingular block. -/
theorem search_spec {A : Matrix V V K} (hA : IsAlternating A) {pick : Finset V → V → V}
    (hpick : ∀ U s, (cand A U s).Nonempty → pick U s ∈ cand A U s) :
    ∀ (hubs : List V) (U : Finset V), Nsg A U →
      Nsg A (search pick hubs U).2 ∧ (search pick hubs U).2 ⊆ U ∧
      (∀ h ∈ hubs, h ∉ (search pick hubs U).2) ∧
      (∀ p ∈ (search pick hubs U).1, A p.1 p.2 ≠ 0) ∧
      (ends (search pick hubs U).1).Nodup ∧
      (∀ x, x ∈ ends (search pick hubs U).1 ↔ x ∈ U ∧ x ∉ (search pick hubs U).2) := by
  classical
  intro hubs
  induction hubs with
  | nil => intro U hU; simp [search, ends, hU]
  | cons s hs ih =>
    intro U hU
    by_cases hsU : s ∈ U
    · obtain ⟨hne, hall⟩ := pick_step hA hU hsU
      have hv := hpick U s hne
      obtain ⟨hvU, hvs, hAv, -⟩ := Finset.mem_filter.1 hv
      set v := pick U s
      have hU1 := hall v hv
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih (U \ {s, v}) hU1
      simp only [search, hsU, ↓reduceIte]
      have hsn : s ∉ (search pick hs (U \ {s, v})).2 := fun h => by
        have := Finset.mem_sdiff.1 (h2 h); simp at this
      have hvn : v ∉ (search pick hs (U \ {s, v})).2 := fun h => by
        have := Finset.mem_sdiff.1 (h2 h); simp at this
      refine ⟨h1, h2.trans Finset.sdiff_subset, ?_, ?_, ?_, ?_⟩
      · intro h hh
        rcases List.mem_cons.1 hh with rfl | hh
        · exact hsn
        · exact h3 h hh
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact hAv
        · exact h4 p hp
      · have hs6 : s ∉ ends (search pick hs (U \ {s, v})).1 := fun h => by
          have := ((h6 s).1 h).1; simp at this
        have hv6 : v ∉ ends (search pick hs (U \ {s, v})).1 := fun h => by
          have := ((h6 v).1 h).1; simp at this
        simp only [ends, List.flatMap_cons, List.cons_append, List.nil_append] at hs6 hv6 h5 ⊢
        refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨hv6, h5⟩⟩
        simp only [List.mem_cons, not_or]
        exact ⟨Ne.symm hvs, hs6⟩
      · intro x
        simp only [ends, List.flatMap_cons, List.cons_append, List.nil_append, List.mem_cons] at h6 ⊢
        rw [h6 x]
        constructor
        · rintro (rfl | rfl | ⟨hx, hx'⟩)
          · exact ⟨hsU, hsn⟩
          · exact ⟨hvU, hvn⟩
          · exact ⟨(Finset.mem_sdiff.1 hx).1, hx'⟩
        · rintro ⟨hx, hx'⟩
          by_cases e1 : x = s
          · exact Or.inl e1
          by_cases e2 : x = v
          · exact Or.inr (Or.inl e2)
          exact Or.inr (Or.inr ⟨Finset.mem_sdiff.2 ⟨hx, by simp [e1, e2]⟩, hx'⟩)
    · simp only [search, hsU, ↓reduceIte]
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih U hU
      refine ⟨h1, h2, fun h hh => ?_, h4, h5, h6⟩
      rcases List.mem_cons.1 hh with rfl | hh
      · exact fun h' => hsU (h2 h')
      · exact h3 h hh

/-- A block with no entries to the rest of `U` is nonsingular together with the rest. -/
theorem nsg_block {A : Matrix V V K} {S U : Finset V} (hS : S ⊆ U)
    (h0 : ∀ i ∈ S, ∀ j ∈ U \ S, A i j = 0 ∧ A j i = 0) : Nsg A U ↔ Nsg A S ∧ Nsg A (U \ S) := by
  let e : ↥S ⊕ ↥(U \ S) ≃ ↥U :=
    { toFun := Sum.elim (fun x => ⟨x.1, hS x.2⟩) (fun y => ⟨y.1, (Finset.mem_sdiff.1 y.2).1⟩)
      invFun := fun z => if h : z.1 ∈ S then Sum.inl ⟨z.1, h⟩ else Sum.inr ⟨z.1, Finset.mem_sdiff.2 ⟨z.2, h⟩⟩
      left_inv := by
        rintro (x | y)
        · simp [x.2]
        · simp [(Finset.mem_sdiff.1 y.2).2]
      right_inv := by
        intro z
        by_cases h : z.1 ∈ S <;> simp [h] }
  have hb : (principal A U).submatrix e e = fromBlocks (principal A S) 0 0 (principal A (U \ S)) := by
    ext (x | y) (x' | y')
    · rfl
    · exact (h0 x x.2 y' y'.2).1
    · exact (h0 x' x'.2 y y.2).2
    · rfl
  rw [Nsg, Nsg, Nsg, ← det_submatrix_equiv_self e, hb, det_fromBlocks_zero₂₁, IsUnit.mul_iff]

/-- A run of the search over the bags `t < T`, one after the other. Bag `t` works on the unmatched vertices
`W t = U t ∩ O t` of its part `O t`, with the hubs `H t`. -/
structure Sched (A : Matrix V V K) (B : Finset V) (O : ℕ → Finset V) (H : ℕ → List V)
    (pick : Finset V → V → V) (U : ℕ → Finset V) (T : ℕ) : Prop where
  start : U 0 = B
  next : ∀ t < T, U (t + 1) = (U t \ (U t ∩ O t)) ∪ (search pick (H t) (U t ∩ O t)).2
  /-- The part of a bag has no entries to the other unmatched vertices. -/
  block : ∀ t < T, ∀ i ∈ U t ∩ O t, ∀ j ∈ U t \ (U t ∩ O t), A i j = 0 ∧ A j i = 0
  /-- Every vertex of `B` is a hub of a bag whose part holds it. -/
  cover : ∀ b ∈ B, ∃ t < T, b ∈ O t ∧ b ∈ H t

namespace Sched

variable {A : Matrix V V K} {B : Finset V} {O : ℕ → Finset V} {H : ℕ → List V} {pick : Finset V → V → V}
  {U : ℕ → Finset V} {T : ℕ}

theorem mono (h : Sched A B O H pick U T) {t : ℕ} (ht : t < T) : U (t + 1) ⊆ U t := by
  rw [h.next t ht]
  exact Finset.union_subset Finset.sdiff_subset ((search_sub pick _ _).trans Finset.inter_subset_left)

theorem mono_le (h : Sched A B O H pick U T) {s t : ℕ} (hst : s ≤ t) (ht : t ≤ T) : U t ⊆ U s := by
  induction t, hst using Nat.le_induction with
  | base => exact le_rfl
  | succ t hst ih => exact (h.mono (by omega)).trans (ih (by omega))

/-- The unmatched vertices stay a nonsingular block. -/
theorem nsg (h : Sched A B O H pick U T) (hA : IsAlternating A)
    (hpick : ∀ U s, (cand A U s).Nonempty → pick U s ∈ cand A U s) (hB : Nsg A B) :
    ∀ t ≤ T, Nsg A (U t) := by
  intro t
  induction t with
  | zero => intro _; rw [h.start]; exact hB
  | succ t ih =>
    intro ht
    have hU := ih (by omega)
    set W := U t ∩ O t
    have hWU : W ⊆ U t := Finset.inter_subset_left
    obtain ⟨hW, hR⟩ := (nsg_block hWU (h.block t (by omega))).1 hU
    have hs := (search_spec hA hpick (H t) W hW)
    set W' := (search pick (H t) W).2
    have hW'W : W' ⊆ W := hs.2.1
    have hnext : U (t + 1) = (U t \ W) ∪ W' := h.next t (by omega)
    have hsub : W' ⊆ U (t + 1) := by rw [hnext]; exact Finset.subset_union_right
    have hrest : U (t + 1) \ W' = U t \ W := by
      rw [hnext]
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact h1
        · exact absurd h1 h2
      · intro h1
        exact ⟨Or.inl h1, fun h2 => h1.2 (hW'W h2)⟩
    rw [nsg_block hsub ?_, hrest]
    · exact ⟨hs.1, hR⟩
    · intro i hi j hj
      rw [hrest] at hj
      exact h.block t (by omega) i (hW'W hi) j hj

/-- Every vertex of `B` is matched in the end. -/
theorem done (h : Sched A B O H pick U T) (hA : IsAlternating A)
    (hpick : ∀ U s, (cand A U s).Nonempty → pick U s ∈ cand A U s) (hB : Nsg A B) : U T = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun b hb => ?_
  have hbB : b ∈ B := by rw [← h.start]; exact h.mono_le (Nat.zero_le T) le_rfl hb
  obtain ⟨t, ht, hO, hH⟩ := h.cover b hbB
  have hnot : b ∉ U (t + 1) := by
    intro hb'
    have hbt := h.mono ht hb'
    have hW := ((nsg_block (Finset.inter_subset_left : U t ∩ O t ⊆ U t) (h.block t ht)).1
      (h.nsg hA hpick hB t ht.le)).1
    have hs := search_spec hA hpick (H t) _ hW
    rw [h.next t ht, Finset.mem_union, Finset.mem_sdiff] at hb'
    rcases hb' with ⟨-, h2⟩ | h2
    · exact h2 (Finset.mem_inter.2 ⟨hbt, hO⟩)
    · exact hs.2.2.1 b hH h2
  exact hnot (h.mono_le (by omega) le_rfl hb)

/-- The pairs found at bag `t`. -/
noncomputable def pairs (O : ℕ → Finset V) (H : ℕ → List V) (pick : Finset V → V → V)
    (U : ℕ → Finset V) (t : ℕ) : List (V × V) := (search pick (H t) (U t ∩ O t)).1

theorem ends_pairs (h : Sched A B O H pick U T) (hA : IsAlternating A)
    (hpick : ∀ U s, (cand A U s).Nonempty → pick U s ∈ cand A U s) (hB : Nsg A B) {t : ℕ} (ht : t < T) :
    (∀ p ∈ pairs O H pick U t, A p.1 p.2 ≠ 0) ∧ (ends (pairs O H pick U t)).Nodup ∧
      ∀ x, x ∈ ends (pairs O H pick U t) ↔ x ∈ U t ∧ x ∉ U (t + 1) := by
  have hW := ((nsg_block (Finset.inter_subset_left : U t ∩ O t ⊆ U t) (h.block t ht)).1
    (h.nsg hA hpick hB t ht.le)).1
  obtain ⟨-, h2, -, h4, h5, h6⟩ := search_spec hA hpick (H t) _ hW
  refine ⟨h4, h5, fun x => ?_⟩
  rw [pairs, h6 x, h.next t ht, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
  constructor
  · rintro ⟨⟨hx, hO⟩, hx'⟩
    exact ⟨hx, fun h' => h'.elim (fun h'' => h''.2 ⟨hx, hO⟩) hx'⟩
  · rintro ⟨hx, hx'⟩
    have hO : x ∈ O t := by
      by_contra hO
      exact hx' (Or.inl ⟨hx, fun h' => hO h'.2⟩)
    exact ⟨⟨hx, hO⟩, fun h' => hx' (Or.inr h')⟩

/-- **Lemma 6.** If `A_{B,B}` is nonsingular, the pairs found at all bags are a perfect matching of `B` by edges
of `A`, for any rule that picks a candidate. -/
theorem matched (h : Sched A B O H pick U T) (hA : IsAlternating A)
    (hpick : ∀ U s, (cand A U s).Nonempty → pick U s ∈ cand A U s) (hB : Nsg A B) :
    (∀ t < T, ∀ p ∈ pairs O H pick U t, A p.1 p.2 ≠ 0) ∧
      ((List.range T).flatMap fun t => ends (pairs O H pick U t)).Nodup ∧
      ∀ x, x ∈ (List.range T).flatMap (fun t => ends (pairs O H pick U t)) ↔ x ∈ B := by
  have he := fun t (ht : t < T) => h.ends_pairs hA hpick hB ht
  refine ⟨fun t ht => (he t ht).1, ?_, fun x => ?_⟩
  · refine List.nodup_flatMap.2 ⟨fun t ht => (he t (List.mem_range.1 ht)).2.1, ?_⟩
    refine List.Pairwise.imp_of_mem ?_ List.pairwise_lt_range
    intro s t hs ht hst
    show List.Disjoint _ _
    rw [List.disjoint_left]
    intro x hxs hxt
    have h1 := ((he s (List.mem_range.1 hs)).2.2 x).1 hxs
    have h2 := ((he t (List.mem_range.1 ht)).2.2 x).1 hxt
    exact h1.2 (h.mono_le (Nat.succ_le_of_lt hst) (List.mem_range.1 ht).le h2.1)
  · rw [List.mem_flatMap]
    constructor
    · rintro ⟨t, ht, hx⟩
      have := (((he t (List.mem_range.1 ht)).2.2 x).1 hx).1
      rw [← h.start]
      exact h.mono_le (Nat.zero_le t) (List.mem_range.1 ht).le this
    · intro hx
      have hex : ∃ t, t < T ∧ x ∈ U t ∧ x ∉ U (t + 1) := by
        by_contra hne
        push_neg at hne
        have : ∀ t ≤ T, x ∈ U t := by
          intro t
          induction t with
          | zero => intro _; rw [h.start]; exact hx
          | succ t ih => exact fun ht => hne t (by omega) (ih (by omega))
        simpa [h.done hA hpick hB] using this T le_rfl
      obtain ⟨t, ht, h1, h2⟩ := hex
      exact ⟨t, List.mem_range.2 ht, ((he t ht).2.2 x).2 ⟨h1, h2⟩⟩

end Sched

end PlanarMatching
