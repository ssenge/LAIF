import RingMulticast.Game

/-!
# Structure of the two orders

Edge o is a most expensive edge with a o > 0, and the edges after o cost at most as much in total as the edges
before o. In both orders the players o, ..., n − 1 go right. In order A, if p is the first of 0, ..., o − 1 to go
right, all later players of that range go right too, so edge p is unused. In order B, if q is the last of
0, ..., o − 1 to go left, all players before q go left too, so edge q + 1 is unused.
-/

open Finset

namespace RingMulticast

theorem share_congr (a : ℕ → ℚ) (S : Finset ℕ) (c c' : ℕ → Bool) (k : ℕ) (h : ∀ j ∈ S, c j = c' j) :
    share a S c k = share a S c' k := by
  unfold share; rw [users_congr S c c' k h]

theorem share_zero (a : ℕ → ℚ) (S c k) (h : users S c k = 0) : share a S c k = a k := by
  rw [share_of_users a S c k 0 h]; simp

/-- Players o, ..., n − 1 go right in every order in which each of them arrives after exactly the players
with larger index. -/
theorem right_of_ge (a : ℕ → ℚ) (n o : ℕ) (t : ℕ → ℕ) (c : ℕ → Bool) (ha : ∀ k, 0 ≤ a k) (hon : o ≤ n)
    (hs : 0 < a o) (horient : ∑ k ∈ Ico (o + 1) (n + 1), a k ≤ ∑ k ∈ range o, a k)
    (hbef : ∀ i, o ≤ i → i < n → before t n i = (range n).filter fun j => i < j)
    (hmy : Myopic a n t c) : ∀ i, o ≤ i → i < n → c i = true := by
  suffices H : ∀ m i, n - i ≤ m → o ≤ i → i < n → c i = true from fun i h1 h2 => H _ i le_rfl h1 h2
  intro m
  induction m with
  | zero => intro i h _ h2; omega
  | succ m ih =>
    intro i hm hoi hin
    set S := before t n i with hS
    have hprev : ∀ j ∈ S, c j = (fun _ => true) j := by
      intro j hj
      rw [hS, hbef i hoi hin, mem_filter, mem_range] at hj
      exact ih j (by omega) (by omega) hj.1
    have hleft : leftCost a S c i = ∑ k ∈ range (i + 1), a k := by
      unfold leftCost
      apply sum_congr rfl
      intro k hk
      rw [share_congr a S c _ k hprev]
      apply share_zero
      rw [users, card_eq_zero, filter_eq_empty_iff]
      intro j hj
      rw [hS, hbef i hoi hin, mem_filter, mem_range] at hj
      simp only [mem_range] at hk
      simp [usesB] <;> omega
    have hright : rightCost a n S c i ≤ ∑ k ∈ Ico (o + 1) (n + 1), a k := by
      unfold rightCost
      calc ∑ k ∈ Ico (i + 1) (n + 1), share a S c k ≤ ∑ k ∈ Ico (i + 1) (n + 1), a k :=
            sum_le_sum fun k _ => share_le a ha S c k
        _ ≤ ∑ k ∈ Ico (o + 1) (n + 1), a k :=
            sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico (by omega) le_rfl) fun k _ _ => ha k
    have hbig : (∑ k ∈ range o, a k) + a o ≤ ∑ k ∈ range (i + 1), a k := by
      rw [← sum_range_succ]
      exact sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega)) fun k _ _ => ha k
    cases hc : c i with
    | true => rfl
    | false =>
      have := (hmy i hin).2 hc
      linarith

/-- The arrival sets of order A, players below o. -/
theorem before_A (o n i : ℕ) (hio : i < o) (hon : o ≤ n) :
    before (tA o n) n i = (range n).filter fun j => o ≤ j ∨ j < i := before_tA_lt o n i hio hon

section OrderA

variable (a : ℕ → ℚ) (n o : ℕ) (c : ℕ → Bool) (ha : ∀ k, 0 ≤ a k) (hon : o ≤ n) (hs : 0 < a o)
  (hR : ∀ i, o ≤ i → i < n → c i = true) (hmy : Myopic a n (tA o n) c)

include ha hon hs hR hmy in
/-- Order A: once a player of 0, ..., o − 1 goes right, every later one does. -/
theorem A_mid (p : ℕ) (hpo : p < o) (hp : c p = true) (hleft : ∀ j < p, c j = false) :
    ∀ j, p ≤ j → j < o → c j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hpj hjo
  rcases Nat.eq_or_lt_of_le hpj with h | h
  · subst h; exact hp
  -- the arrival sets of p and j, with the choices made there
  set Sp := before (tA o n) n p with hSp
  set Sj := before (tA o n) n j with hSj
  have eSp : Sp = (range n).filter fun i => o ≤ i ∨ i < p := before_A o n p hpo hon
  have eSj : Sj = (range n).filter fun i => o ≤ i ∨ i < j := before_A o n j hjo hon
  set cp : ℕ → Bool := fun i => decide (o ≤ i) with hcp
  set cj : ℕ → Bool := fun i => decide (o ≤ i ∨ p ≤ i) with hcj
  have hcSp : ∀ i ∈ Sp, c i = cp i := by
    intro i hi
    rw [eSp, mem_filter, mem_range] at hi
    by_cases h1 : o ≤ i
    · rw [hR i h1 hi.1]; simp [hcp, h1]
    · have : i < p := by omega
      rw [hleft i this]; simp [hcp, h1]
  have hcSj : ∀ i ∈ Sj, c i = cj i := by
    intro i hi
    rw [eSj, mem_filter, mem_range] at hi
    by_cases h1 : o ≤ i
    · rw [hR i h1 hi.1]; simp [hcj, h1]
    · by_cases h2 : p ≤ i
      · rw [ih i (by omega) h2 (by omega)]; simp [hcj, h2]
      · rw [hleft i (by omega)]; simp [hcj, h1, h2]
  -- right of j is strictly cheaper than right of p
  have hlt : ∀ k, j < k → k ≤ n → users Sp cp k < users Sj cj k := by
    intro k hjk hkn
    unfold users
    apply card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨p, ?_, ?_⟩
      · rw [eSj]; simp [usesB, hcj] <;> omega
      · rw [eSp]; simp [usesB, hcp] <;> omega
    · intro i hi
      rw [eSp] at hi; rw [eSj]
      simp [usesB, hcp, hcj] at hi ⊢
      omega
  have hright : rightCost a n Sj c j < rightCost a n Sp c p := by
    unfold rightCost
    calc ∑ k ∈ Ico (j + 1) (n + 1), share a Sj c k < ∑ k ∈ Ico (j + 1) (n + 1), share a Sp c k := by
          apply sum_lt_sum
          · intro k hk
            rw [share_congr a Sj c cj k hcSj, share_congr a Sp c cp k hcSp]
            simp only [mem_Ico] at hk
            exact share_anti a ha Sp Sj cp cj k (le_of_lt (hlt k (by omega) (by omega)))
          · refine ⟨o, by simp; omega, ?_⟩
            rw [share_congr a Sj c cj o hcSj, share_congr a Sp c cp o hcSp]
            exact share_strict a Sp Sj cp cj o hs (hlt o (by omega) hon)
      _ ≤ ∑ k ∈ Ico (p + 1) (n + 1), share a Sp c k :=
          sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico (by omega) le_rfl)
            fun k _ _ => share_nonneg a ha Sp c k
  -- left of j is at least left of p
  have heq : ∀ k, k ≤ p → users Sp cp k = users Sj cj k := by
    intro k hkp
    unfold users
    congr 1
    ext i
    rw [eSp, eSj]
    simp [usesB, hcp, hcj] <;> omega
  have hleftc : leftCost a Sp c p ≤ leftCost a Sj c j := by
    unfold leftCost
    calc ∑ k ∈ range (p + 1), share a Sp c k = ∑ k ∈ range (p + 1), share a Sj c k := by
          apply sum_congr rfl
          intro k hk
          rw [share_congr a Sj c cj k hcSj, share_congr a Sp c cp k hcSp]
          unfold share
          rw [heq k (by simp at hk; omega)]
      _ ≤ ∑ k ∈ range (j + 1), share a Sj c k :=
          sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega)) fun k _ _ => share_nonneg a ha Sj c k
  have hpcond := (hmy p (by omega)).1 hp
  cases hc : c j with
  | true => rfl
  | false =>
    have := (hmy j (by omega)).2 hc
    linarith

include ha hon hs hR hmy in
/-- Order A leaves edge p unused. -/
theorem A_unused (p : ℕ) (hpo : p < o) (hp : c p = true) (hleft : ∀ j < p, c j = false) :
    users (range n) c p = 0 := by
  have hmid := A_mid a n o c ha hon hs hR hmy p hpo hp hleft
  rw [users, card_eq_zero, filter_eq_empty_iff]
  intro i hi
  rw [mem_range] at hi
  by_cases h1 : i < p
  · simp [usesB, hleft i h1] <;> omega
  · have : c i = true := by
      by_cases h2 : o ≤ i
      · exact hR i h2 hi
      · exact hmid i (by omega) (by omega)
    simp [usesB, this] <;> omega

include hR in
/-- With no player of 0, ..., o − 1 going right in order A, edge o is unused. -/
theorem A_unused_o (hno : ∀ j < o, c j = false) : users (range n) c o = 0 := by
  rw [users, card_eq_zero, filter_eq_empty_iff]
  intro i hi
  rw [mem_range] at hi
  by_cases h1 : i < o
  · simp [usesB, hno i h1] <;> omega
  · simp [usesB, hR i (by omega) hi] <;> omega

end OrderA


section OrderB

variable (a : ℕ → ℚ) (n o : ℕ) (c : ℕ → Bool) (ha : ∀ k, 0 ≤ a k) (hon : o ≤ n) (hs : 0 < a o)
  (hR : ∀ i, o ≤ i → i < n → c i = true) (hmy : Myopic a n (tB n) c)

include ha hon hs hR hmy in
/-- Order B: once a player of o − 1, ..., 0 goes left, every later one does. -/
theorem B_low (q : ℕ) (hqo : q < o) (hq : c q = false) (hup : ∀ j, q < j → j < o → c j = true) :
    ∀ j < q, c j = false := by
  suffices H : ∀ m j, q - j ≤ m → j < q → c j = false from fun j hj => H _ j le_rfl hj
  intro m
  induction m with
  | zero => intro j h hj; omega
  | succ m ih =>
  intro j hm hjq
  set Sq := before (tB n) n q with hSq
  set Sj := before (tB n) n j with hSj
  have eSq : Sq = (range n).filter fun i => q < i := before_tB n q (by omega)
  have eSj : Sj = (range n).filter fun i => j < i := before_tB n j (by omega)
  set cb : ℕ → Bool := fun i => decide (q < i) with hcb
  have hval : ∀ i, j < i → i < n → c i = cb i := by
    intro i h1 h2
    by_cases h3 : q < i
    · have : c i = true := by
        by_cases h4 : o ≤ i
        · exact hR i h4 h2
        · exact hup i h3 (by omega)
      rw [this]; simp [hcb, h3]
    · by_cases h4 : i = q
      · subst h4; rw [hq]; simp [hcb]
      · rw [ih i (by omega) (by omega)]; simp [hcb, h3]
  have hcSj : ∀ i ∈ Sj, c i = cb i := by
    intro i hi; rw [eSj, mem_filter, mem_range] at hi; exact hval i hi.2 hi.1
  have hcSq : ∀ i ∈ Sq, c i = cb i := by
    intro i hi; rw [eSq, mem_filter, mem_range] at hi; exact hval i (by omega) hi.1
  -- at q's arrival the left path of q is empty
  have hleftq : leftCost a Sq c q = ∑ k ∈ range (q + 1), a k := by
    unfold leftCost
    apply sum_congr rfl
    intro k hk
    rw [share_congr a Sq c cb k hcSq]
    apply share_zero
    rw [users, card_eq_zero, filter_eq_empty_iff]
    intro i hi
    rw [eSq, mem_filter, mem_range] at hi
    simp only [mem_range] at hk
    simp [usesB, hcb] <;> omega
  -- right of j costs at least right of q
  have hrightq : rightCost a n Sq c q ≤ rightCost a n Sj c j := by
    unfold rightCost
    calc ∑ k ∈ Ico (q + 1) (n + 1), share a Sq c k = ∑ k ∈ Ico (q + 1) (n + 1), share a Sj c k := by
          apply sum_congr rfl
          intro k hk
          rw [share_congr a Sj c cb k hcSj, share_congr a Sq c cb k hcSq]
          simp only [mem_Ico] at hk
          have heq : users Sq cb k = users Sj cb k := by
            unfold users
            congr 1
            ext i
            rw [eSq, eSj]
            simp [usesB, hcb] <;> omega
          unfold share
          rw [heq]
      _ ≤ ∑ k ∈ Ico (j + 1) (n + 1), share a Sj c k :=
          sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico (by omega) le_rfl)
            fun k _ _ => share_nonneg a ha Sj c k
  have hqcond := (hmy q (by omega)).2 hq
  -- every edge of the left path of j has q as a user
  have hpos : ∀ k, k ≤ j → 0 < users Sj cb k := by
    intro k hk
    unfold users
    apply card_pos.2
    refine ⟨q, ?_⟩
    rw [eSj]; simp [usesB, hcb] <;> omega
  have hlj : leftCost a Sj c j ≤ ∑ k ∈ range (j + 1), a k :=
    sum_le_sum fun k _ => share_le a ha Sj c k
  have hstrict : leftCost a Sj c j < rightCost a n Sj c j := by
    by_cases h0 : ∑ k ∈ range (j + 1), a k = 0
    · have hro : 0 < share a Sj c o := by
        unfold share; exact div_pos hs (by positivity)
      have : share a Sj c o ≤ rightCost a n Sj c j :=
        single_le_sum (f := fun k => share a Sj c k) (fun k _ => share_nonneg a ha Sj c k)
          (mem_Ico.2 ⟨by omega, by omega⟩)
      linarith
    · have hpos' : 0 < ∑ k ∈ range (j + 1), a k :=
        lt_of_le_of_ne (sum_nonneg fun k _ => ha k) (Ne.symm h0)
      obtain ⟨k, hk, hak⟩ := (sum_pos_iff_of_nonneg fun k _ => ha k).1 hpos'
      have hlt : leftCost a Sj c j < ∑ k ∈ range (j + 1), a k := by
        unfold leftCost
        apply sum_lt_sum (fun k _ => share_le a ha Sj c k)
        refine ⟨k, hk, ?_⟩
        rw [share_congr a Sj c cb k hcSj]
        unfold share
        apply div_lt_self hak
        have := hpos k (by simp at hk; omega)
        have : (1 : ℚ) ≤ users Sj cb k := by exact_mod_cast this
        linarith
      have hsub : ∑ k ∈ range (j + 1), a k ≤ ∑ k ∈ range (q + 1), a k :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega)) fun k _ _ => ha k
      linarith
  cases hc : c j with
  | false => rfl
  | true =>
    have := (hmy j (by omega)).1 hc
    linarith

include ha hon hs hR hmy in
/-- Order B leaves edge q + 1 unused. -/
theorem B_unused (q : ℕ) (hqo : q < o) (hq : c q = false) (hup : ∀ j, q < j → j < o → c j = true) :
    users (range n) c (q + 1) = 0 := by
  have hlow := B_low a n o c ha hon hs hR hmy q hqo hq hup
  rw [users, card_eq_zero, filter_eq_empty_iff]
  intro i hi
  rw [mem_range] at hi
  by_cases h1 : i ≤ q
  · have : c i = false := by
      rcases Nat.eq_or_lt_of_le h1 with h | h
      · rw [h]; exact hq
      · exact hlow i h
    simp [usesB, this] <;> omega
  · have : c i = true := by
      by_cases h2 : o ≤ i
      · exact hR i h2 hi
      · exact hup i (by omega) (by omega)
    simp [usesB, this] <;> omega

include hR in
/-- With nobody going left in order B, edge 0 is unused. -/
theorem B_unused_none (hall : ∀ j < o, c j = true) : users (range n) c 0 = 0 := by
  rw [users, card_eq_zero, filter_eq_empty_iff]
  intro i hi
  rw [mem_range] at hi
  have : c i = true := by
    by_cases h2 : o ≤ i
    · exact hR i h2 hi
    · exact hall i (by omega)
  simp [usesB, this]

end OrderB

/-! ## The costs at arrival, as finite sums -/

/-- Order A, player r < o, with 0, ..., r − 1 on the left and o, ..., n − 1 on the right. -/
theorem costs_A (a : ℕ → ℚ) (n o : ℕ) (c : ℕ → Bool) (hon : o ≤ n)
    (hR : ∀ i, o ≤ i → i < n → c i = true) (r : ℕ) (hro : r < o) (hleft : ∀ j < r, c j = false) :
    leftCost a (before (tA o n) n r) c r = ∑ k ∈ range (r + 1), a k / ((r : ℚ) - k + 1) ∧
    rightCost a n (before (tA o n) n r) c r
      = (∑ k ∈ Ico (r + 1) (o + 1), a k) + ∑ k ∈ Ico (o + 1) (n + 1), a k / ((k : ℚ) - o + 1) := by
  set S := before (tA o n) n r with hS
  have eS : S = (range n).filter fun i => o ≤ i ∨ i < r := before_A o n r hro hon
  set cp : ℕ → Bool := fun i => decide (o ≤ i) with hcp
  have hc : ∀ i ∈ S, c i = cp i := by
    intro i hi
    rw [eS, mem_filter, mem_range] at hi
    by_cases h1 : o ≤ i
    · rw [hR i h1 hi.1]; simp [hcp, h1]
    · rw [hleft i (by omega)]; simp [hcp, h1]
  constructor
  · unfold leftCost
    apply sum_congr rfl
    intro k hk
    simp only [mem_range] at hk
    rw [share_congr a S c cp k hc]
    have hu : users S cp k = r - k := by
      unfold users
      rw [show (S.filter fun j => usesB cp j k = true) = Ico k r by
        ext i; rw [eS]; simp [usesB, hcp] <;> omega]
      simp
    rw [share_of_users a S cp k _ hu, Nat.cast_sub (by omega)]
  · unfold rightCost
    rw [← sum_Ico_consecutive _ (by omega : r + 1 ≤ o + 1) (by omega : o + 1 ≤ n + 1)]
    congr 1
    · apply sum_congr rfl
      intro k hk
      simp only [mem_Ico] at hk
      rw [share_congr a S c cp k hc]
      apply share_zero
      rw [users, card_eq_zero, filter_eq_empty_iff]
      intro i hi
      rw [eS, mem_filter, mem_range] at hi
      simp [usesB, hcp] <;> omega
    · apply sum_congr rfl
      intro k hk
      simp only [mem_Ico] at hk
      rw [share_congr a S c cp k hc]
      have hu : users S cp k = k - o := by
        unfold users
        rw [show (S.filter fun j => usesB cp j k = true) = Ico o k by
          ext i; rw [eS]; simp [usesB, hcp] <;> omega]
        simp
      rw [share_of_users a S cp k _ hu, Nat.cast_sub (by omega)]

/-- Order B, player j, with everybody after j on the right. -/
theorem costs_B (a : ℕ → ℚ) (n : ℕ) (c : ℕ → Bool) (j : ℕ) (hjn : j < n)
    (hall : ∀ i, j < i → i < n → c i = true) :
    leftCost a (before (tB n) n j) c j = ∑ k ∈ range (j + 1), a k ∧
    rightCost a n (before (tB n) n j) c j = ∑ k ∈ Ico (j + 1) (n + 1), a k / ((k : ℚ) - j) := by
  set S := before (tB n) n j with hS
  have eS : S = (range n).filter fun i => j < i := before_tB n j hjn
  have hc : ∀ i ∈ S, c i = (fun _ => true) i := by
    intro i hi; rw [eS, mem_filter, mem_range] at hi; exact hall i hi.2 hi.1
  constructor
  · unfold leftCost
    apply sum_congr rfl
    intro k hk
    simp only [mem_range] at hk
    rw [share_congr a S c _ k hc]
    apply share_zero
    rw [users, card_eq_zero, filter_eq_empty_iff]
    intro i hi
    rw [eS, mem_filter, mem_range] at hi
    simp [usesB] <;> omega
  · unfold rightCost
    apply sum_congr rfl
    intro k hk
    simp only [mem_Ico] at hk
    rw [share_congr a S c _ k hc]
    have hu : users S (fun _ => true) k = k - (j + 1) := by
      unfold users
      rw [show (S.filter fun i => usesB (fun _ => true) i k = true) = Ico (j + 1) k by
        ext i; rw [eS]; simp [usesB] <;> omega]
      simp
    rw [share_of_users a S _ k _ hu, Nat.cast_sub (by omega)]
    push_cast
    ring

end RingMulticast
