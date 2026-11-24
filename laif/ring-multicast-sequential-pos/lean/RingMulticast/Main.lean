import RingMulticast.Structure
import RingMulticast.Cases
import RingMulticast.Window

/-!
# Two orders suffice

For every ring whose edges after a most expensive edge o cost at most as much in total as the edges before o,
and for every result of myopic sequential play in order A and in order B (ties broken either way), one of the two
networks costs at most 4/3 of the optimum Σ_{k ≠ o} a k. Every network costs at least this optimum
(`netCost_ge`), so the myopic sequential price of stability is at most 4/3. The other orientation is the mirror
image of the ring.
-/

open Finset

namespace RingMulticast

theorem conv_A (a : ℕ → ℚ) (o m : ℕ) (W : ℚ)
    (h : (∑ k ∈ Ico (m + 3 + 1) (o + 1), a k) + W ≤ ∑ k ∈ range (m + 3 + 1), a k / (((m + 3 : ℕ) : ℚ) - k + 1)) :
    (∑ k ∈ Ico (m + 4) (o + 1), a k) + W ≤ ∑ k ∈ range (m + 4), a k / ((m : ℚ) + 3 - k + 1) := by
  have e : ∀ k : ℕ, a k / (((m + 3 : ℕ) : ℚ) - k + 1) = a k / ((m : ℚ) + 3 - k + 1) := by
    intro k; push_cast; ring
  simp only [e] at h
  exact h

theorem conv_AL (a : ℕ → ℚ) (o m : ℕ) (W : ℚ)
    (h : ∑ k ∈ range (m + 2 + 1), a k / (((m + 2 : ℕ) : ℚ) - k + 1) ≤ (∑ k ∈ Ico (m + 2 + 1) (o + 1), a k) + W) :
    ∑ k ∈ range (m + 3), a k / ((m : ℚ) + 3 - k) ≤ (∑ k ∈ Ico (m + 3) (o + 1), a k) + W := by
  have e : ∀ k : ℕ, a k / (((m + 2 : ℕ) : ℚ) - k + 1) = a k / ((m : ℚ) + 3 - k) := by
    intro k; push_cast; ring
  simp only [e] at h
  exact h

/-- Two orders suffice: 3 min (cost A, cost B) ≤ 4 Opt. -/
theorem two_orders (a : ℕ → ℚ) (n o : ℕ) (ha : ∀ k, 0 ≤ a k) (hon : o ≤ n)
    (hmax : ∀ k, k ≤ n → a k ≤ a o)
    (horient : ∑ k ∈ Ico (o + 1) (n + 1), a k ≤ ∑ k ∈ range o, a k)
    (cA cB : ℕ → Bool) (hA : Myopic a n (tA o n) cA) (hB : Myopic a n (tB n) cB) :
    3 * min (netCost a n cA) (netCost a n cB)
      ≤ 4 * ((∑ k ∈ range o, a k) + ∑ k ∈ Ico (o + 1) (n + 1), a k) := by
  set Opt := (∑ k ∈ range o, a k) + ∑ k ∈ Ico (o + 1) (n + 1), a k with hOpt
  have hopt : (∑ k ∈ range o, a k) + ∑ k ∈ Ico (o + 1) (n + 1), a k = Opt := rfl
  have hT : ∑ k ∈ range (n + 1), a k = Opt + a o := by
    have h1 := sum_range_add_sum_Ico a (by omega : o + 1 ≤ n + 1)
    rw [sum_range_succ] at h1; linarith
  have hOpt0 : 0 ≤ Opt := add_nonneg (sum_nonneg fun k _ => ha k) (sum_nonneg fun k _ => ha k)
  suffices H : netCost a n cA ≤ Opt + Opt / 3 ∨ netCost a n cB ≤ Opt + Opt / 3 by
    rcases H with h | h
    · have := min_le_left (netCost a n cA) (netCost a n cB); linarith
    · have := min_le_right (netCost a n cA) (netCost a n cB); linarith
  rcases eq_or_lt_of_le (ha o) with hs0 | hs
  · left
    have : netCost a n cA ≤ ∑ k ∈ range (n + 1), a k := by
      unfold netCost
      apply sum_le_sum
      intro k _
      split_ifs
      · exact ha k
      · exact le_rfl
    linarith
  have hRA := right_of_ge a n o (tA o n) cA ha hon hs horient
    (fun i h1 h2 => before_tA_ge o n i h1 h2) hA
  have hRB := right_of_ge a n o (tB n) cB ha hon hs horient (fun i _ h2 => before_tB n i h2) hB
  have hW0 : 0 ≤ ∑ k ∈ Ico (o + 1) (n + 1), a k / ((k : ℚ) - o + 1) := sum_nonneg fun k hk => by
    have : (o : ℚ) + 1 ≤ k := by exact_mod_cast (mem_Ico.1 hk).1
    exact div_nonneg (ha k) (by linarith)
  -- order A
  by_cases hpex : ∃ p, p < o ∧ cA p = true
  swap
  · left
    push_neg at hpex
    have hno : ∀ j < o, cA j = false := fun j hj => Bool.eq_false_iff.2 (hpex j hj)
    have := netCost_le a ha n cA o hon (A_unused_o n o cA hRA hno)
    linarith
  set p := Nat.find hpex with hpdef
  have hpo : p < o := (Nat.find_spec hpex).1
  have hp : cA p = true := (Nat.find_spec hpex).2
  have hleft : ∀ j < p, cA j = false := fun j hj =>
    Bool.eq_false_iff.2 fun h => Nat.find_min hpex hj ⟨by omega, h⟩
  clear_value p
  have hcostA : netCost a n cA ≤ Opt + a o - a p := by
    have := netCost_le a ha n cA p (by omega) (A_unused a n o cA ha hon hs hRA hA p hpo hp hleft)
    linarith
  have hAp : (∑ k ∈ Ico (p + 1) (o + 1), a k) + (∑ k ∈ Ico (o + 1) (n + 1), a k / ((k : ℚ) - o + 1))
      ≤ ∑ k ∈ range (p + 1), a k / ((p : ℚ) - k + 1) := by
    obtain ⟨hl, hr⟩ := costs_A a n o cA hon hRA p hpo hleft
    have := (hA p (by omega)).1 hp
    rw [hl, hr] at this
    exact this
  -- the condition of player p − 1 in order A
  have hAL : ∀ r, r + 1 = p → ∑ k ∈ range (r + 1), a k / ((r : ℚ) - k + 1)
      ≤ (∑ k ∈ Ico (r + 1) (o + 1), a k) + ∑ k ∈ Ico (o + 1) (n + 1), a k / ((k : ℚ) - o + 1) := by
    intro r hr
    obtain ⟨hl, hr'⟩ := costs_A a n o cA hon hRA r (by omega) fun j hj => hleft j (by omega)
    have := (hA r (by omega)).2 (hleft r (by omega))
    rw [hl, hr'] at this
    exact this
  -- player 0 going right in order A
  rcases Nat.eq_zero_or_pos p with hp0 | hp0
  · left
    have e : ∑ k ∈ range (0 + 1), a k / (((0 : ℕ) : ℚ) - k + 1) = a 0 := by simp
    rw [hp0] at hAp
    rw [e] at hAp
    have := bound_p_zero a n o (by omega) ha hAp
    rw [hp0] at hcostA
    linarith
  -- order B: the conditions of right-goers below o
  have hBR : ∀ j, j < o → cB j = true → (∀ i, j < i → i < o → cB i = true) →
      (∑ k ∈ Ico (j + 1) (n + 1), a k / ((k : ℚ) - j)) ≤ ∑ k ∈ range (j + 1), a k := by
    intro j hjo hj hup
    have hall : ∀ i, j < i → i < n → cB i = true := fun i h1 h2 => by
      by_cases h3 : o ≤ i
      · exact hRB i h3 h2
      · exact hup i h1 (by omega)
    obtain ⟨hl, hr⟩ := costs_B a n cB j (by omega) hall
    have := (hB j (by omega)).1 hj
    rw [hl, hr] at this
    exact this
  have hcap : ∀ k, k ≤ n → a k ≤ a o := hmax
  by_cases hqex : ∃ q, q < o ∧ cB q = false
  swap
  · -- nobody goes left in order B: edge 0 is unused
    push_neg at hqex
    have hallB : ∀ j < o, cB j = true := fun j hj => by
      cases h : cB j
      · exact absurd h (hqex j hj)
      · rfl
    have hcostB : netCost a n cB ≤ Opt + a o - a 0 := by
      have := netCost_le a ha n cB 0 (by omega) (B_unused_none n o cB hRB hallB)
      linarith
    have hBRall : ∀ j, j < o → (∑ k ∈ Ico (j + 1) (n + 1), a k / ((k : ℚ) - j)) ≤ ∑ k ∈ range (j + 1), a k :=
      fun j hj => hBR j hj (hallB j hj) fun i _ h2 => hallB i h2
    rcases Nat.lt_or_ge p 3 with hp3 | hp3
    · interval_cases p
      · -- p = 1
        have := bound_d2_none a n o Opt hpo hon ha hopt hAp
        rcases min_le_iff.1 this with h | h
        · left; linarith
        · right; linarith
      · -- p = 2
        have hAL1 := hAL 1 rfl
        have e : ∀ k : ℕ, a k / (((1 : ℕ) : ℚ) - k + 1) = a k / ((2 : ℚ) - k) := by
          intro k; push_cast; ring
        simp only [e] at hAL1
        have hB0 := hBRall 0 (by omega)
        simp only [Nat.cast_zero] at hB0
        have := bound_d3_none a n o Opt hpo hon ha hcap hopt hAp hAL1 hB0
        rcases min_le_iff.1 this with h | h
        · left; linarith
        · right; linarith
    · obtain ⟨m, hm⟩ : ∃ m, p = m + 3 := ⟨p - 3, by omega⟩
      rw [hm] at hAp hpo hcostA
      have hA' := conv_A a o m _ hAp
      have hAL' := conv_AL a o m _ (hAL (m + 2) (by omega))
      have := window_bound a n o m Opt hpo hon ha hcap hopt hA' hAL'
        fun j _ h2 => hBRall j (by omega)
      left; linarith
  -- q: the last player below o that goes left in order B
  set q := Nat.findGreatest (fun j => j < o ∧ cB j = false) n with hqdef
  obtain ⟨q0, hq0o, hq0⟩ := hqex
  have hqP : q < o ∧ cB q = false := Nat.findGreatest_spec (P := fun j => j < o ∧ cB j = false)
    (by omega : q0 ≤ n) ⟨hq0o, hq0⟩
  have hqo := hqP.1
  have hq := hqP.2
  have hup : ∀ j, q < j → j < o → cB j = true := fun j h1 h2 => by
    have := Nat.findGreatest_is_greatest (P := fun j => j < o ∧ cB j = false) h1 (by omega)
    cases h : cB j
    · exact absurd ⟨h2, h⟩ this
    · rfl
  clear_value q
  have hcostB : netCost a n cB ≤ Opt + a o - a (q + 1) := by
    have := netCost_le a ha n cB (q + 1) (by omega) (B_unused a n o cB ha hon hs hRB hB q hqo hq hup)
    linarith
  have hBq : (∑ k ∈ range (q + 1), a k) ≤ ∑ k ∈ Ico (q + 1) (n + 1), a k / ((k : ℚ) - q) := by
    have hall : ∀ i, q < i → i < n → cB i = true := fun i h1 h2 => by
      by_cases h3 : o ≤ i
      · exact hRB i h3 h2
      · exact hup i h1 (by omega)
    obtain ⟨hl, hr⟩ := costs_B a n cB q (by omega) hall
    have := (hB q (by omega)).2 hq
    rw [hl, hr] at this
    exact this
  have hBRq : ∀ j, q < j → j < o →
      (∑ k ∈ Ico (j + 1) (n + 1), a k / ((k : ℚ) - j)) ≤ ∑ k ∈ range (j + 1), a k :=
    fun j h1 h2 => hBR j h2 (hup j h1 h2) fun i h3 h4 => hup i (by omega) h4
  rcases Nat.lt_or_ge q p with hqp | hqp
  · -- q < p: d = p − q ≥ 1
    obtain ⟨d, hd⟩ : ∃ d, p = q + 1 + d := ⟨p - q - 1, by omega⟩
    rcases Nat.lt_or_ge d 3 with hd3 | hd3
    · interval_cases d
      · -- p = q + 1
        have hp1 : p = q + 1 := by omega
        rw [hp1] at hAp hpo hcostA
        have := bound_succ a n o q Opt hpo hon ha hcap hopt hAp hBq
        right; linarith
      · -- p = q + 2
        have hp2 : p = q + 2 := by omega
        rw [hp2] at hAp hpo hcostA
        have := bound_d2 a n o q Opt hpo hon ha hcap hopt hAp hBq
        rcases min_le_iff.1 this with h | h
        · left; linarith
        · right; linarith
      · -- p = q + 3
        have hp3 : p = q + 3 := by omega
        rw [hp3] at hAp hpo hcostA
        have hA' := conv_A a o q _ hAp
        have hAL' := conv_AL a o q _ (hAL (q + 2) (by omega))
        have hB1 := hBRq (q + 1) (by omega) (by omega)
        have := bound_d3 a n o q Opt hpo hon ha hcap hopt hA' hAL' hB1
        rcases min_le_iff.1 this with h | h
        · left; linarith
        · right; linarith
    · -- p ≥ q + 4
      obtain ⟨m, hm⟩ : ∃ m, p = m + 3 := ⟨p - 3, by omega⟩
      rw [hm] at hAp hpo hcostA
      have hA' := conv_A a o m _ hAp
      have hAL' := conv_AL a o m _ (hAL (m + 2) (by omega))
      have := window_bound a n o m Opt hpo hon ha hcap hopt hA' hAL'
        fun j h1 h2 => hBRq j (by omega) (by omega)
      left; linarith
  · -- q ≥ p
    have := bound_ge a n o p q Opt hqp hqo hon ha hcap hopt hAp hBq
    rcases min_le_iff.1 this with h | h
    · left; linarith
    · right; linarith

end RingMulticast
