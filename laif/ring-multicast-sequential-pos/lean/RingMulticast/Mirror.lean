import RingMulticast.Main
import RingMulticast.Play

/-!
# The mirror image of the ring, and the price of stability for every ring

Reading the ring clockwise maps edge k to edge n − k and player j to player n − 1 − j, and swaps the left and right
paths. Myopic sequential play and the network cost carry over, so the orientation of `two_orders` holds after
mirroring when it fails before. The result: every ring has an arrival order whose every outcome of myopic
sequential play costs at most 4/3 of every network, and such outcomes exist.
-/

open Finset

namespace RingMulticast

/-- Edge costs of the mirror image. -/
def mirA (a : ℕ → ℚ) (n : ℕ) : ℕ → ℚ := fun k => a (n - k)

/-- Choices in the mirror image: player j of the image is player n − 1 − j, with left and right swapped. -/
def mirC (n : ℕ) (c : ℕ → Bool) : ℕ → Bool := fun j => !c (n - 1 - j)

/-- Arrival times in the mirror image. -/
def mirT (n : ℕ) (t : ℕ → ℕ) : ℕ → ℕ := fun j => t (n - 1 - j)

theorem usesB_mir (c : ℕ → Bool) (n j k : ℕ) (hj : j < n) (hk : k ≤ n) :
    usesB (mirC n c) j k = usesB c (n - 1 - j) (n - k) := by
  unfold usesB mirC
  cases c (n - 1 - j) <;>
    simp only [Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and, Bool.or_false, Bool.false_or] <;>
    exact decide_eq_decide.2 ⟨fun _ => by omega, fun _ => by omega⟩

theorem users_mir (S S' : Finset ℕ) (c : ℕ → Bool) (n k : ℕ) (hk : k ≤ n)
    (hS' : ∀ j, j ∈ S' ↔ j < n ∧ n - 1 - j ∈ S) (hS : ∀ j ∈ S, j < n) :
    users S' (mirC n c) k = users S c (n - k) := by
  unfold users
  apply card_nbij' (fun j => n - 1 - j) (fun j => n - 1 - j)
  · intro j hj
    simp only [mem_coe, mem_filter] at hj ⊢
    have h := (hS' j).1 hj.1
    exact ⟨h.2, by rw [← usesB_mir c n j k h.1 hk]; exact hj.2⟩
  · intro j hj
    simp only [mem_coe, mem_filter] at hj ⊢
    have hjn := hS j hj.1
    have e : n - 1 - (n - 1 - j) = j := by omega
    refine ⟨(hS' (n - 1 - j)).2 ⟨by omega, by rw [e]; exact hj.1⟩, ?_⟩
    rw [usesB_mir c n _ k (by omega) hk, e]
    exact hj.2
  · intro j hj
    simp only [mem_coe, mem_filter] at hj ⊢
    have := ((hS' j).1 hj.1).1
    omega
  · intro j hj
    simp only [mem_coe, mem_filter] at hj ⊢
    have := hS j hj.1
    omega

theorem share_mir (a : ℕ → ℚ) (S S' : Finset ℕ) (c : ℕ → Bool) (n k : ℕ) (hk : k ≤ n)
    (hS' : ∀ j, j ∈ S' ↔ j < n ∧ n - 1 - j ∈ S) (hS : ∀ j ∈ S, j < n) :
    share (mirA a n) S' (mirC n c) k = share a S c (n - k) := by
  unfold share mirA
  rw [users_mir S S' c n k hk hS' hS]

theorem left_mir (a : ℕ → ℚ) (S S' : Finset ℕ) (c : ℕ → Bool) (n i : ℕ) (hi : i < n)
    (hS' : ∀ j, j ∈ S' ↔ j < n ∧ n - 1 - j ∈ S) (hS : ∀ j ∈ S, j < n) :
    leftCost (mirA a n) S' (mirC n c) i = rightCost a n S c (n - 1 - i) := by
  unfold leftCost rightCost
  apply sum_nbij' (fun k => n - k) (fun k => n - k)
  · intro k hk; simp only [mem_range, mem_Ico] at hk ⊢; omega
  · intro k hk; simp only [mem_range, mem_Ico] at hk ⊢; omega
  · intro k hk; simp only [mem_range] at hk ⊢; omega
  · intro k hk; simp only [mem_Ico] at hk ⊢; omega
  · intro k hk
    simp only [mem_range] at hk
    exact share_mir a S S' c n k (by omega) hS' hS

theorem right_mir (a : ℕ → ℚ) (S S' : Finset ℕ) (c : ℕ → Bool) (n i : ℕ) (hi : i < n)
    (hS' : ∀ j, j ∈ S' ↔ j < n ∧ n - 1 - j ∈ S) (hS : ∀ j ∈ S, j < n) :
    rightCost (mirA a n) n S' (mirC n c) i = leftCost a S c (n - 1 - i) := by
  unfold leftCost rightCost
  apply sum_nbij' (fun k => n - k) (fun k => n - k)
  · intro k hk; simp only [mem_range, mem_Ico] at hk ⊢; omega
  · intro k hk; simp only [mem_range, mem_Ico] at hk ⊢; omega
  · intro k hk; simp only [mem_Ico] at hk ⊢; omega
  · intro k hk; simp only [mem_range] at hk ⊢; omega
  · intro k hk
    simp only [mem_Ico] at hk
    exact share_mir a S S' c n k (by omega) hS' hS

theorem before_mir (t : ℕ → ℕ) (n i : ℕ) (hi : i < n) :
    ∀ j, j ∈ before (mirT n t) n i ↔ j < n ∧ n - 1 - j ∈ before t n (n - 1 - i) := by
  intro j
  simp only [before, mem_filter, mem_range]
  simp only [mirT]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega, h2⟩
  · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩

theorem before_lt (t : ℕ → ℕ) (n i : ℕ) : ∀ j ∈ before t n i, j < n := by
  intro j hj
  simp only [before, mem_filter, mem_range] at hj
  exact hj.1

/-- Myopic sequential play carries over to the mirror image. -/
theorem myopic_mir (a : ℕ → ℚ) (n : ℕ) (t : ℕ → ℕ) (c : ℕ → Bool) (h : Myopic a n t c) :
    Myopic (mirA a n) n (mirT n t) (mirC n c) := by
  intro i hi
  have hS' := before_mir t n i hi
  have hS := before_lt t n (n - 1 - i)
  rw [left_mir a _ _ c n i hi hS' hS, right_mir a _ _ c n i hi hS' hS]
  obtain ⟨h1, h2⟩ := h (n - 1 - i) (by omega)
  constructor
  · intro hc
    apply h2
    simpa [mirC] using hc
  · intro hc
    apply h1
    simpa [mirC] using hc

/-- The network cost carries over to the mirror image. -/
theorem netCost_mir (a : ℕ → ℚ) (n : ℕ) (c : ℕ → Bool) : netCost (mirA a n) n (mirC n c) = netCost a n c := by
  unfold netCost
  apply sum_nbij' (fun k => n - k) (fun k => n - k)
  · intro k hk; simp only [mem_range] at hk ⊢; omega
  · intro k hk; simp only [mem_range] at hk ⊢; omega
  · intro k hk; simp only [mem_range] at hk ⊢; omega
  · intro k hk; simp only [mem_range] at hk ⊢; omega
  · intro k hk
    simp only [mem_range] at hk
    have hS' : ∀ j, j ∈ range n ↔ j < n ∧ n - 1 - j ∈ range n := by
      intro j
      simp only [mem_range]
      constructor
      · intro h; omega
      · intro h; omega
    rw [users_mir (range n) (range n) c n k (by omega) hS' fun j hj => mem_range.1 hj]
    rfl

theorem myopic_congr (a : ℕ → ℚ) (n : ℕ) (t t' : ℕ → ℕ) (c : ℕ → Bool) (h : ∀ j, j < n → t j = t' j)
    (hm : Myopic a n t c) : Myopic a n t' c := by
  have hb : ∀ i, i < n → before t n i = before t' n i := by
    intro i hi
    unfold before
    apply filter_congr
    intro j hj
    rw [h j (mem_range.1 hj), h i hi]
  intro i hi
  rw [← hb i hi]
  exact hm i hi

theorem sum_mir_lo (a : ℕ → ℚ) (n o : ℕ) (hon : o ≤ n) :
    ∑ k ∈ Ico (n - o + 1) (n + 1), mirA a n k = ∑ k ∈ range o, a k := by
  apply sum_nbij' (fun k => n - k) (fun k => n - k)
  · intro k hk; simp only [mem_range, mem_Ico] at hk ⊢; omega
  · intro k hk; simp only [mem_range, mem_Ico] at hk ⊢; omega
  · intro k hk; simp only [mem_Ico] at hk ⊢; omega
  · intro k hk; simp only [mem_range] at hk ⊢; omega
  · intro k _; rfl

theorem sum_mir_hi (a : ℕ → ℚ) (n o : ℕ) (hon : o ≤ n) :
    ∑ k ∈ range (n - o), mirA a n k = ∑ k ∈ Ico (o + 1) (n + 1), a k := by
  apply sum_nbij' (fun k => n - k) (fun k => n - k)
  · intro k hk; simp only [mem_range, mem_Ico] at hk ⊢; omega
  · intro k hk; simp only [mem_range, mem_Ico] at hk ⊢; omega
  · intro k hk; simp only [mem_range] at hk ⊢; omega
  · intro k hk; simp only [mem_Ico] at hk ⊢; omega
  · intro k _; rfl

theorem tB_injOn (n : ℕ) : Set.InjOn (tB n) (Set.Iio n) := by
  intro i hi j hj h
  simp only [Set.mem_Iio] at hi hj
  unfold tB at h
  omega

theorem mirT_injOn (n : ℕ) (t : ℕ → ℕ) (ht : Set.InjOn t (Set.Iio n)) : Set.InjOn (mirT n t) (Set.Iio n) := by
  intro i hi j hj h
  simp only [Set.mem_Iio] at hi hj
  have := ht (show n - 1 - i ∈ Set.Iio n from Set.mem_Iio.2 (by omega))
    (show n - 1 - j ∈ Set.Iio n from Set.mem_Iio.2 (by omega)) h
  omega

/-- In the orientation of `two_orders`, order A or order B ends within 4/3 of Σ_{k ≠ o} a k for every outcome. -/
theorem oriented_order (a : ℕ → ℚ) (n o : ℕ) (ha : ∀ k, 0 ≤ a k) (hon : o ≤ n)
    (hmax : ∀ k, k ≤ n → a k ≤ a o)
    (horient : ∑ k ∈ Ico (o + 1) (n + 1), a k ≤ ∑ k ∈ range o, a k) :
    ∃ t : ℕ → ℕ, Set.InjOn t (Set.Iio n) ∧ ∀ c, Myopic a n t c →
      3 * netCost a n c ≤ 4 * ((∑ k ∈ range o, a k) + ∑ k ∈ Ico (o + 1) (n + 1), a k) := by
  by_cases hA : ∀ c, Myopic a n (tA o n) c →
      3 * netCost a n c ≤ 4 * ((∑ k ∈ range o, a k) + ∑ k ∈ Ico (o + 1) (n + 1), a k)
  · exact ⟨tA o n, tA_injOn o n hon, hA⟩
  · push_neg at hA
    obtain ⟨cA, hmyA, hbad⟩ := hA
    refine ⟨tB n, tB_injOn n, fun cB hmyB => ?_⟩
    have key := two_orders a n o ha hon hmax horient cA cB hmyA hmyB
    rcases min_choice (netCost a n cA) (netCost a n cB) with h | h
    · rw [h] at key; linarith
    · rw [h] at key; exact key

/-- Myopic sequential price of stability on rings: for every ring there is an arrival order such that every outcome
of myopic sequential play, with ties broken either way, costs at most 4/3 of every network, and such an outcome
exists. -/
theorem sequential_pos (a : ℕ → ℚ) (ha : ∀ k, 0 ≤ a k) (n : ℕ) :
    ∃ t : ℕ → ℕ, Set.InjOn t (Set.Iio n) ∧ (∃ c, Myopic a n t c) ∧
      ∀ c, Myopic a n t c → ∀ c', 3 * netCost a n c ≤ 4 * netCost a n c' := by
  obtain ⟨o, ho, hmax⟩ := exists_max_image (range (n + 1)) a ⟨0, by simp⟩
  have hon : o ≤ n := by have := mem_range.1 ho; omega
  have hmax' : ∀ k, k ≤ n → a k ≤ a o := fun k hk => hmax k (mem_range.2 (by omega))
  have hT : ∑ k ∈ range (n + 1), a k = ((∑ k ∈ range o, a k) + ∑ k ∈ Ico (o + 1) (n + 1), a k) + a o := by
    have h1 := sum_range_add_sum_Ico a (by omega : o + 1 ≤ n + 1)
    rw [sum_range_succ] at h1
    linarith
  suffices H : ∃ t : ℕ → ℕ, Set.InjOn t (Set.Iio n) ∧ ∀ c, Myopic a n t c →
      3 * netCost a n c ≤ 4 * ((∑ k ∈ range o, a k) + ∑ k ∈ Ico (o + 1) (n + 1), a k) by
    obtain ⟨t, ht, hc⟩ := H
    refine ⟨t, ht, exists_myopic a n t, fun c hmy c' => ?_⟩
    have h1 := netCost_ge a ha n o hon hmax' c'
    have h2 := hc c hmy
    linarith
  by_cases hor : ∑ k ∈ Ico (o + 1) (n + 1), a k ≤ ∑ k ∈ range o, a k
  · exact oriented_order a n o ha hon hmax' hor
  rw [not_le] at hor
  -- the mirror image, with the most expensive edge n − o
  have ha' : ∀ k, 0 ≤ mirA a n k := fun k => ha (n - k)
  have hmax'' : ∀ k, k ≤ n → mirA a n k ≤ mirA a n (n - o) := by
    intro k hk
    simp only [mirA]
    rw [show n - (n - o) = o by omega]
    exact hmax' (n - k) (by omega)
  have hlo := sum_mir_lo a n o hon
  have hhi := sum_mir_hi a n o hon
  have hor' : ∑ k ∈ Ico (n - o + 1) (n + 1), mirA a n k ≤ ∑ k ∈ range (n - o), mirA a n k := by
    rw [hlo, hhi]; linarith
  obtain ⟨t', ht', hc'⟩ := oriented_order (mirA a n) n (n - o) ha' (by omega) hmax'' hor'
  refine ⟨mirT n t', mirT_injOn n t' ht', fun c hmy => ?_⟩
  have hm := myopic_mir a n (mirT n t') c hmy
  have hm' : Myopic (mirA a n) n t' (mirC n c) :=
    myopic_congr _ n _ t' _ (fun j hj => by simp only [mirT]; congr 1; omega) hm
  have := hc' (mirC n c) hm'
  rw [netCost_mir, hlo, hhi] at this
  linarith

end RingMulticast
