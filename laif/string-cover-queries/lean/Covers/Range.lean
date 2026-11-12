import Covers.Basic
import Mathlib.Data.List.Range

/-!
# The Corollary of Section 1

For each `k` let `b_k` be the shortest border with length in `[2^k, 2^{k+1})` (`IsRangeMin`). The shortest cover is the
first `b_k` that covers `S`, and within a range the covers are a prefix of the borders by length.
-/

namespace Strings

variable {α : Type*}

/-- The length `l` lies in the dyadic range of `k`. -/
def InRange (k l : ℕ) : Prop := 2 ^ k ≤ l ∧ l < 2 ^ (k + 1)

/-- `b` is the shortest border of `S` in the range of `k`: this is `b_k` in the README. -/
def IsRangeMin (k : ℕ) (b S : List α) : Prop :=
  IsBorder b S ∧ InRange k b.length ∧ ∀ b', IsBorder b' S → InRange k b'.length → b.length ≤ b'.length

/-- `C` is a shortest cover of `S`. -/
def IsShortestCover (C S : List α) : Prop :=
  Covers C S ∧ ∀ D, Covers D S → C.length ≤ D.length

theorem inRange_log {l : ℕ} (hl : l ≠ 0) : InRange (Nat.log 2 l) l :=
  ⟨Nat.pow_log_le_self 2 hl, Nat.lt_pow_succ_log_self (by norm_num) l⟩

theorem InRange.lt_of_lt {j k a b : ℕ} (ha : InRange j a) (hb : InRange k b) (h : j < k) : a < b :=
  calc a < 2 ^ (j + 1) := ha.2
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
    _ ≤ b := hb.1

/-- Two lengths in one range satisfy the hypothesis of Lemma 1. -/
theorem InRange.lt_two_mul {k a b : ℕ} (ha : InRange k a) (hb : InRange k b) : b < 2 * a := by
  have := ha.1
  have := hb.2
  rw [pow_succ] at *
  omega

/-- Every string has a shortest cover. -/
theorem exists_shortestCover (S : List α) : ∃ C, IsShortestCover C S := by
  classical
  have hex : ∃ m, ∃ C : List α, Covers C S ∧ C.length = m := ⟨_, S, covers_self S, rfl⟩
  obtain ⟨C, hC, hm⟩ := Nat.find_spec hex
  refine ⟨C, hC, fun D hD => ?_⟩
  rw [hm]
  exact Nat.find_min' hex ⟨D, hD, rfl⟩

/-- Any border in the range of `k` gives a `b_k`. -/
theorem exists_rangeMin {k : ℕ} {u S : List α} (hu : IsBorder u S) (hk : InRange k u.length) :
    ∃ b, IsRangeMin k b S := by
  classical
  have hex : ∃ m, ∃ C : List α, IsBorder C S ∧ InRange k C.length ∧ C.length = m := ⟨_, u, hu, hk, rfl⟩
  obtain ⟨C, hC, hCk, hm⟩ := Nat.find_spec hex
  refine ⟨C, hC, hCk, fun D hD hDk => ?_⟩
  rw [hm]
  exact Nat.find_min' hex ⟨D, hD, hDk, rfl⟩

/-- `b_k` is unique. -/
theorem IsRangeMin.unique {k : ℕ} {b b' S : List α} (h : IsRangeMin k b S) (h' : IsRangeMin k b' S) :
    b = b' :=
  h.1.eq_of_length_eq h'.1 (le_antisymm (h.2.2 _ h'.1 h'.2.1) (h'.2.2 _ h.1 h.2.1))

/-- The shortest border in the range of a cover covers that cover, so it covers `S`. -/
theorem IsRangeMin.covers_of_cover {k : ℕ} {b C S : List α} (hS : S ≠ []) (hb : IsRangeMin k b S)
    (hC : Covers C S) (hk : InRange k C.length) : Covers b S :=
  (lemma1 hb.1 (hC.isBorder hS) (hb.2.2 _ (hC.isBorder hS) hk) (hb.2.1.lt_two_mul hk)).trans hC

/-- **Corollary, first part.** If `C` is a shortest cover in the range of `k`, then `C = b_k`. -/
theorem IsShortestCover.eq_rangeMin {k : ℕ} {b C S : List α} (hS : S ≠ []) (hC : IsShortestCover C S)
    (hb : IsRangeMin k b S) (hk : InRange k C.length) : b = C :=
  hb.1.eq_of_length_eq (hC.1.isBorder hS)
    (le_antisymm (hb.2.2 _ (hC.1.isBorder hS) hk) (hC.2 _ (hb.covers_of_cover hS hC.1 hk)))

/-- **Corollary, second part.** Ranges below that of the shortest cover contain no cover at all. -/
theorem IsShortestCover.no_cover_below {j k : ℕ} {C D S : List α} (hC : IsShortestCover C S)
    (hk : InRange k C.length) (hj : j < k) (hD : InRange j D.length) : ¬ Covers D S := fun hcov =>
  absurd (hC.2 D hcov) (not_le.2 (hD.lt_of_lt hk hj))

/-- **Corollary: the shortest cover is the first `b_k` that covers `S`**, the forward direction. A shortest cover
of a nonempty string is `b_k` for its own `k`, and no earlier `b_j` covers `S`. -/
theorem corollary_shortest {C S : List α} (hS : S ≠ []) (hC : IsShortestCover C S) :
    ∃ k, IsRangeMin k C S ∧ ∀ j, j < k → ∀ b, IsRangeMin j b S → ¬ Covers b S := by
  have hne : C.length ≠ 0 := by
    have := hC.1.ne_nil hS
    simpa using this
  have hk := inRange_log hne
  refine ⟨Nat.log 2 C.length, ?_, fun j hj b hb => hC.no_cover_below hk hj hb.2.1⟩
  obtain ⟨b, hb⟩ := exists_rangeMin (hC.1.isBorder hS) hk
  have heq := hC.eq_rangeMin hS hb hk
  subst heq
  exact hb

/-- **Corollary: the shortest cover is the first `b_k` that covers `S`**, the direction the algorithm uses. If `b_k`
covers `S` and no earlier `b_j` does, then `b_k` is a shortest cover. -/
theorem first_covering_rangeMin_isShortest {k : ℕ} {b S : List α} (hS : S ≠ [])
    (hb : IsRangeMin k b S) (hcov : Covers b S)
    (hfirst : ∀ j, j < k → ∀ b', IsRangeMin j b' S → ¬ Covers b' S) : IsShortestCover b S := by
  refine ⟨hcov, fun D hD => ?_⟩
  by_contra hlt
  have hlt : D.length < b.length := by omega
  have hne : D.length ≠ 0 := by
    have := hD.ne_nil hS
    simpa using this
  have hj := inRange_log hne
  rcases lt_trichotomy (Nat.log 2 D.length) k with h | h | h
  · obtain ⟨b', hb'⟩ := exists_rangeMin (hD.isBorder hS) hj
    exact hfirst _ h b' hb' (hb'.covers_of_cover hS hD hj)
  · rw [h] at hj
    exact absurd (hb.2.2 _ (hD.isBorder hS) hj) (by omega)
  · exact absurd (hb.2.1.lt_of_lt hj h) (by omega)

/-- **Corollary, last claim.** Within a range, a border shorter than a covering border covers: the covers are
downward closed among the borders of the range. -/
theorem covers_downward_in_range {k : ℕ} {u v S : List α} (hu : IsBorder u S) (hv : IsBorder v S)
    (hku : InRange k u.length) (hkv : InRange k v.length) (hle : u.length ≤ v.length)
    (hcov : Covers v S) : Covers u S :=
  (lemma1 hu hv hle (hku.lt_two_mul hkv)).trans hcov

/-! ## The prefix statement, on lists of lengths -/

/-- If `p` is downward closed along a sorted list, then filtering by `p` is taking a prefix. -/
theorem filter_eq_takeWhile_of_downward (p : ℕ → Bool) :
    ∀ l : List ℕ, l.Pairwise (· ≤ ·) →
      (∀ a ∈ l, ∀ b ∈ l, a ≤ b → p b = true → p a = true) → l.filter p = l.takeWhile p
  | [], _, _ => rfl
  | a :: t, hs, hd => by
    have hs' := List.pairwise_cons.1 hs
    by_cases ha : p a = true
    · have ih := filter_eq_takeWhile_of_downward p t hs'.2 fun x hx y hy =>
        hd x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
      simp [ha, ih]
    · have hnil : t.filter p = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb hpb
        exact ha (hd a (by simp) b (List.mem_cons_of_mem _ hb) (hs'.1 b hb) hpb)
      simp [ha, hnil]

open Classical in
/-- The lengths in the range of `k` that are borders of `S`, in increasing order. -/
noncomputable def borderLengths (S : List α) (k : ℕ) : List ℕ :=
  (List.range' (2 ^ k) (2 ^ k)).filter fun l => decide (l ≤ S.length ∧ IsBorder (S.take l) S)

open Classical in
/-- Whether the length-`l` prefix of `S` covers `S`. -/
noncomputable def coversLen (S : List α) (l : ℕ) : Bool := decide (Covers (S.take l) S)

/-- **Corollary, last claim, as a prefix.** The lengths of the covers in a range are an initial segment of the list
of border lengths of that range, sorted by length. -/
theorem coverLengths_eq_takeWhile (S : List α) (k : ℕ) :
    (borderLengths S k).filter (coversLen S) = (borderLengths S k).takeWhile (coversLen S) := by
  apply filter_eq_takeWhile_of_downward
  · refine List.Pairwise.filter _ ?_
    exact (List.pairwise_lt_range').imp (fun h => le_of_lt h)
  · intro a ha b hb hab hcov
    simp only [borderLengths, List.mem_filter, List.mem_range'_1, decide_eq_true_eq] at ha hb
    simp only [coversLen, decide_eq_true_eq] at hcov ⊢
    have hra : InRange k (S.take a).length := by
      rw [List.length_take, min_eq_left ha.2.1, InRange, pow_succ]; omega
    have hrb : InRange k (S.take b).length := by
      rw [List.length_take, min_eq_left hb.2.1, InRange, pow_succ]; omega
    refine covers_downward_in_range ha.2.2 hb.2.2 hra hrb ?_ hcov
    rw [List.length_take, List.length_take, min_eq_left ha.2.1, min_eq_left hb.2.1]
    exact hab

/-- `borderLengths` lists exactly the lengths of the borders in the range. -/
theorem mem_borderLengths {S : List α} {k l : ℕ} :
    l ∈ borderLengths S k ↔ InRange k l ∧ ∃ u, IsBorder u S ∧ u.length = l := by
  simp only [borderLengths, List.mem_filter, List.mem_range'_1, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hl, hb⟩
    refine ⟨?_, _, hb, by simp [hl]⟩
    rw [InRange, pow_succ]; omega
  · rintro ⟨h, u, hu, rfl⟩
    have hle := hu.length_le
    have hr := h
    rw [InRange, pow_succ] at hr
    refine ⟨by omega, hle, ?_⟩
    have : S.take u.length = u := (List.prefix_iff_eq_take.1 hu.1).symm
    rwa [this]

end Strings
