import Mathlib

/-!
# The cases d ≤ 3 of the ring bound, from the best-response conditions

Notation as in `RingMulticast.Window`: edges a 0, ..., a n, a most expensive edge o, the optimum normalized to 1.
Player p is the first of 0, ..., o − 1 to go right in the first order (players before p go left), and player q is
the first of o − 1, ..., 0 to go left in the second order (players o − 1, ..., q + 1 go right before it). Each
theorem takes the weak best-response conditions of the players it names and bounds
z = min (a o − a p) (a o − a (q + 1)) by 1/3.
-/

open Finset

namespace RingMulticast

/-- The tail of a right path: shares a k / (k − q) for k > p are at most a k / (p + 1 − q). -/
theorem tail_le (a : ℕ → ℚ) (ha : ∀ k, 0 ≤ a k) (q p n : ℕ) (hqp : q ≤ p) (hpn : p ≤ n) :
    ∑ k ∈ Ico (q + 1) (n + 1), a k / ((k : ℚ) - q)
      ≤ (∑ k ∈ Ico (q + 1) (p + 1), a k / ((k : ℚ) - q))
        + (∑ k ∈ Ico (p + 1) (n + 1), a k) / ((p : ℚ) + 1 - q) := by
  rw [← sum_Ico_consecutive _ (by omega : q + 1 ≤ p + 1) (by omega : p + 1 ≤ n + 1), sum_div]
  apply add_le_add le_rfl
  apply sum_le_sum
  intro k hk
  have : (p : ℚ) + 1 ≤ k := by exact_mod_cast (mem_Ico.1 hk).1
  have hq : (q : ℚ) ≤ p := by exact_mod_cast hqp
  exact div_le_div_of_nonneg_left (ha k) (by linarith) (by linarith)

/-- The mass after p, with the optimum normalized to 1. -/
theorem after_eq (a : ℕ → ℚ) (n o p : ℕ) (hpo : p < o) (hon : o ≤ n)
    (hopt : (∑ k ∈ range o, a k) + ∑ k ∈ Ico (o + 1) (n + 1), a k = 1) :
    ∑ k ∈ Ico (p + 1) (n + 1), a k = 1 + a o - ∑ k ∈ range (p + 1), a k := by
  have h1 := sum_range_add_sum_Ico a (by omega : p + 1 ≤ o + 1)
  have h2 := sum_range_add_sum_Ico a (by omega : o + 1 ≤ n + 1)
  have h3 := sum_range_add_sum_Ico a (by omega : p + 1 ≤ n + 1)
  rw [sum_range_succ] at h1 h2
  linarith

/-- Case p = 0: player 0 goes right in the first order, so a o ≤ a 0. -/
theorem bound_p_zero (a : ℕ → ℚ) (n o : ℕ) (h0o : 0 < o) (ha : ∀ k, 0 ≤ a k)
    (hA : (∑ k ∈ Ico 1 (o + 1), a k) + (∑ k ∈ Ico (o + 1) (n + 1), a k / ((k : ℚ) - o + 1)) ≤ a 0) :
    a o - a 0 ≤ 0 := by
  have h1 : a o ≤ ∑ k ∈ Ico 1 (o + 1), a k := single_le_sum (fun k _ => ha k) (mem_Ico.2 ⟨h0o, by omega⟩)
  have h2 : 0 ≤ ∑ k ∈ Ico (o + 1) (n + 1), a k / ((k : ℚ) - o + 1) := sum_nonneg fun k hk => by
    have : (o : ℚ) + 1 ≤ k := by exact_mod_cast (mem_Ico.1 hk).1
    exact div_nonneg (ha k) (by linarith)
  linarith

/-- The condition of player p in the first order implies a o ≤ Σ_{k ≤ p} a k / (p − k + 1). -/
theorem cond_A (a : ℕ → ℚ) (n o p : ℕ) (hpo : p < o) (ha : ∀ k, 0 ≤ a k)
    (hA : (∑ k ∈ Ico (p + 1) (o + 1), a k) + (∑ k ∈ Ico (o + 1) (n + 1), a k / ((k : ℚ) - o + 1))
        ≤ ∑ k ∈ range (p + 1), a k / ((p : ℚ) - k + 1)) :
    a o ≤ ∑ k ∈ range (p + 1), a k / ((p : ℚ) - k + 1) := by
  have h1 : a o ≤ ∑ k ∈ Ico (p + 1) (o + 1), a k := single_le_sum (fun k _ => ha k) (mem_Ico.2 ⟨hpo, by omega⟩)
  have h2 : 0 ≤ ∑ k ∈ Ico (o + 1) (n + 1), a k / ((k : ℚ) - o + 1) := sum_nonneg fun k hk => by
    have : (o : ℚ) + 1 ≤ k := by exact_mod_cast (mem_Ico.1 hk).1
    exact div_nonneg (ha k) (by linarith)
  linarith

/-- Shares on a left path: Σ_{k ≤ p} a k / (p − k + 1) ≤ a p + (Σ_{k < p} a k) / 2. -/
theorem left_share (a : ℕ → ℚ) (ha : ∀ k, 0 ≤ a k) (p : ℕ) :
    ∑ k ∈ range (p + 1), a k / ((p : ℚ) - k + 1) ≤ a p + (∑ k ∈ range p, a k) / 2 := by
  rw [sum_range_succ, sum_div]
  have e : a p / ((p : ℚ) - p + 1) = a p := by ring
  rw [e]
  have : ∑ k ∈ range p, a k / ((p : ℚ) - k + 1) ≤ ∑ k ∈ range p, a k / 2 := by
    apply sum_le_sum
    intro k hk
    have h1 : k + 1 ≤ p := mem_range.1 hk
    have : (k : ℚ) + 1 ≤ p := by exact_mod_cast h1
    exact div_le_div_of_nonneg_left (ha k) (by norm_num) (by linarith)
  linarith

/-- Case q + 1 = p ≥ 1: a o − a p ≤ 1/3. -/
theorem bound_succ (a : ℕ → ℚ) (n o q : ℕ) (hpo : q + 1 < o) (hon : o ≤ n)
    (ha : ∀ k, 0 ≤ a k) (hcap : ∀ k, k ≤ n → a k ≤ a o)
    (hopt : (∑ k ∈ range o, a k) + ∑ k ∈ Ico (o + 1) (n + 1), a k = 1)
    (hA : (∑ k ∈ Ico (q + 1 + 1) (o + 1), a k) + (∑ k ∈ Ico (o + 1) (n + 1), a k / ((k : ℚ) - o + 1))
        ≤ ∑ k ∈ range (q + 1 + 1), a k / (((q + 1 : ℕ) : ℚ) - k + 1))
    (hB : (∑ k ∈ range (q + 1), a k) ≤ ∑ k ∈ Ico (q + 1) (n + 1), a k / ((k : ℚ) - q)) :
    a o - a (q + 1) ≤ 1 / 3 := by
  have hA' := cond_A a n o (q + 1) hpo ha hA
  have hL := left_share a ha (q + 1)
  have hT := tail_le a ha q (q + 1) n (by omega) (by omega)
  have hE := after_eq a n o (q + 1) hpo hon hopt
  have e1 : ∑ k ∈ Ico (q + 1) (q + 1 + 1), a k / ((k : ℚ) - q) = a (q + 1) := by
    rw [sum_Ico_succ_top le_rfl, Ico_self, sum_empty]; push_cast; ring
  rw [e1] at hT
  have e2 : ((q + 1 : ℕ) : ℚ) + 1 - q = 2 := by push_cast; ring
  rw [e2] at hT
  have hr : ∑ k ∈ range (q + 1 + 1), a k = (∑ k ∈ range (q + 1), a k) + a (q + 1) := sum_range_succ _ _
  have c := hcap (q + 1) (by omega)
  have n1 := ha (q + 1)
  have hm : 0 ≤ ∑ k ∈ Ico (q + 1 + 1) (n + 1), a k := sum_nonneg fun k _ => ha k
  have hro := sum_range_add_sum_Ico a (by omega : q + 1 + 1 ≤ o)
  have hI : 0 ≤ ∑ k ∈ Ico (q + 1 + 1) o, a k := sum_nonneg fun k _ => ha k
  have hR0 : 0 ≤ ∑ k ∈ Ico (o + 1) (n + 1), a k := sum_nonneg fun k _ => ha k
  linarith

/-- Case q ≥ p: min (a o − a p) (a o − a (q + 1)) ≤ 1/5. -/
theorem bound_ge (a : ℕ → ℚ) (n o p q : ℕ) (hpq : p ≤ q) (hqo : q < o) (hon : o ≤ n)
    (ha : ∀ k, 0 ≤ a k) (hcap : ∀ k, k ≤ n → a k ≤ a o)
    (hopt : (∑ k ∈ range o, a k) + ∑ k ∈ Ico (o + 1) (n + 1), a k = 1)
    (hA : (∑ k ∈ Ico (p + 1) (o + 1), a k) + (∑ k ∈ Ico (o + 1) (n + 1), a k / ((k : ℚ) - o + 1))
        ≤ ∑ k ∈ range (p + 1), a k / ((p : ℚ) - k + 1))
    (hB : (∑ k ∈ range (q + 1), a k) ≤ ∑ k ∈ Ico (q + 1) (n + 1), a k / ((k : ℚ) - q)) :
    min (a o - a p) (a o - a (q + 1)) ≤ 1 / 5 := by
  have hA' := cond_A a n o p (by omega) ha hA
  have hL := left_share a ha p
  have hT := tail_le a ha q (q + 1) n (by omega) (by omega)
  have e1 : ∑ k ∈ Ico (q + 1) (q + 1 + 1), a k / ((k : ℚ) - q) = a (q + 1) := by
    rw [sum_Ico_succ_top le_rfl, Ico_self, sum_empty]; push_cast; ring
  rw [e1] at hT
  have e2 : ((q + 1 : ℕ) : ℚ) + 1 - q = 2 := by push_cast; ring
  rw [e2] at hT
  -- mass after q + 1, against the optimum: 1 + a o = Σ_{k ≤ q+1} a k + Σ_{k > q+1} a k
  have h1 := sum_range_add_sum_Ico a (by omega : q + 1 + 1 ≤ n + 1)
  have h2 := sum_range_add_sum_Ico a (by omega : o + 1 ≤ n + 1)
  rw [sum_range_succ] at h2
  have hr : ∑ k ∈ range (q + 1 + 1), a k = (∑ k ∈ range (q + 1), a k) + a (q + 1) := sum_range_succ _ _
  -- the left part up to q contains the edges 0, ..., p
  have hsub := sum_range_add_sum_Ico a (by omega : p + 1 ≤ q + 1)
  have hI : 0 ≤ ∑ k ∈ Ico (p + 1) (q + 1), a k := sum_nonneg fun k _ => ha k
  have hp := sum_range_succ a p
  have hpo := sum_range_add_sum_Ico a (by omega : p + 1 ≤ o)
  have hI2 : 0 ≤ ∑ k ∈ Ico (p + 1) o, a k := sum_nonneg fun k _ => ha k
  have hR0 : 0 ≤ ∑ k ∈ Ico (o + 1) (n + 1), a k := sum_nonneg fun k _ => ha k
  have c1 := hcap p (by omega); have c2 := hcap (q + 1) (by omega)
  have n1 := ha p; have n2 := ha (q + 1)
  have hP0 : 0 ≤ ∑ k ∈ range p, a k := sum_nonneg fun k _ => ha k
  rw [min_le_iff]
  by_contra hc
  rw [not_or, not_le, not_le] at hc
  obtain ⟨hc1, hc2⟩ := hc
  linarith


/-- Case d = 2 with q = m ≥ 0, p = m + 2: min (a o − a p) (a o − a (q + 1)) ≤ 1/3. -/
theorem bound_d2 (a : ℕ → ℚ) (n o m : ℕ) (hpo : m + 2 < o) (hon : o ≤ n)
    (ha : ∀ k, 0 ≤ a k) (hcap : ∀ k, k ≤ n → a k ≤ a o)
    (hopt : (∑ k ∈ range o, a k) + ∑ k ∈ Ico (o + 1) (n + 1), a k = 1)
    (hA : (∑ k ∈ Ico (m + 2 + 1) (o + 1), a k) + (∑ k ∈ Ico (o + 1) (n + 1), a k / ((k : ℚ) - o + 1))
        ≤ ∑ k ∈ range (m + 2 + 1), a k / (((m + 2 : ℕ) : ℚ) - k + 1))
    (hB : (∑ k ∈ range (m + 1), a k) ≤ ∑ k ∈ Ico (m + 1) (n + 1), a k / ((k : ℚ) - m)) :
    min (a o - a (m + 2)) (a o - a (m + 1)) ≤ 1 / 3 := by
  have hA' := cond_A a n o (m + 2) hpo ha hA
  have hs : ∑ k ∈ range (m + 2 + 1), a k / (((m + 2 : ℕ) : ℚ) - k + 1)
      = (∑ k ∈ range (m + 1), a k / (((m + 2 : ℕ) : ℚ) - k + 1)) + a (m + 1) / 2 + a (m + 2) := by
    rw [sum_range_succ, sum_range_succ]; push_cast; ring
  have hU : ∑ k ∈ range (m + 1), a k / (((m + 2 : ℕ) : ℚ) - k + 1) ≤ (∑ k ∈ range (m + 1), a k) / 3 := by
    rw [sum_div]
    apply sum_le_sum
    intro k hk
    have h1 : k ≤ m := Nat.lt_succ_iff.mp (mem_range.1 hk)
    have : (k : ℚ) ≤ m := by exact_mod_cast h1
    exact div_le_div_of_nonneg_left (ha k) (by norm_num) (by push_cast; linarith)
  have hT := tail_le a ha m (m + 2) n (by omega) (by omega)
  have e1 : ∑ k ∈ Ico (m + 1) (m + 2 + 1), a k / ((k : ℚ) - m) = a (m + 1) + a (m + 2) / 2 := by
    rw [sum_Ico_succ_top (by omega), sum_Ico_succ_top (by omega), Ico_self, sum_empty]; push_cast; ring
  have e2 : ((m + 2 : ℕ) : ℚ) + 1 - m = 3 := by push_cast; ring
  rw [e1, e2] at hT
  have hE := after_eq a n o (m + 2) hpo hon hopt
  have hr : ∑ k ∈ range (m + 2 + 1), a k = (∑ k ∈ range (m + 1), a k) + a (m + 1) + a (m + 2) := by
    rw [sum_range_succ, sum_range_succ]
  have hro := sum_range_add_sum_Ico a (by omega : m + 2 + 1 ≤ o)
  have hI : 0 ≤ ∑ k ∈ Ico (m + 2 + 1) o, a k := sum_nonneg fun k _ => ha k
  have hR0 : 0 ≤ ∑ k ∈ Ico (o + 1) (n + 1), a k := sum_nonneg fun k _ => ha k
  have hU0 : 0 ≤ ∑ k ∈ range (m + 1), a k := sum_nonneg fun k _ => ha k
  have c1 := hcap (m + 1) (by omega); have c2 := hcap (m + 2) (by omega)
  have n1 := ha (m + 1); have n2 := ha (m + 2)
  rw [min_le_iff]
  by_contra hc
  rw [not_or, not_le, not_le] at hc
  obtain ⟨hc1, hc2⟩ := hc
  linarith

/-- Case d = 2 with q = −1 (nobody goes left in the second order), p = 1. -/
theorem bound_d2_none (a : ℕ → ℚ) (n o : ℕ) (hpo : 1 < o) (hon : o ≤ n)
    (ha : ∀ k, 0 ≤ a k)
    (hopt : (∑ k ∈ range o, a k) + ∑ k ∈ Ico (o + 1) (n + 1), a k = 1)
    (hA : (∑ k ∈ Ico (1 + 1) (o + 1), a k) + (∑ k ∈ Ico (o + 1) (n + 1), a k / ((k : ℚ) - o + 1))
        ≤ ∑ k ∈ range (1 + 1), a k / (((1 : ℕ) : ℚ) - k + 1)) :
    min (a o - a 1) (a o - a 0) ≤ 1 / 3 := by
  have hA' := cond_A a n o 1 hpo ha hA
  simp only [sum_range_succ, sum_range_zero] at hA'
  norm_num at hA'
  have hro := sum_range_add_sum_Ico a (by omega : 2 ≤ o)
  simp only [sum_range_succ, sum_range_zero] at hro
  have hI : 0 ≤ ∑ k ∈ Ico 2 o, a k := sum_nonneg fun k _ => ha k
  have hR0 : 0 ≤ ∑ k ∈ Ico (o + 1) (n + 1), a k := sum_nonneg fun k _ => ha k
  have n0 := ha 0; have n1 := ha 1
  rw [min_le_iff]
  by_contra hc
  rw [not_or, not_le, not_le] at hc
  obtain ⟨hc1, hc2⟩ := hc
  linarith

/-- Case d = 3 with q = −1, p = 2: players 0 and 1 go left and player 2 goes right in the first order, and
player 0 goes right in the second order. -/
theorem bound_d3_none (a : ℕ → ℚ) (n o : ℕ) (hpo : 2 < o) (hon : o ≤ n)
    (ha : ∀ k, 0 ≤ a k) (hcap : ∀ k, k ≤ n → a k ≤ a o)
    (hopt : (∑ k ∈ range o, a k) + ∑ k ∈ Ico (o + 1) (n + 1), a k = 1)
    (hA : (∑ k ∈ Ico (2 + 1) (o + 1), a k) + (∑ k ∈ Ico (o + 1) (n + 1), a k / ((k : ℚ) - o + 1))
        ≤ ∑ k ∈ range (2 + 1), a k / (((2 : ℕ) : ℚ) - k + 1))
    (hAL : (∑ k ∈ range 2, a k / ((2 : ℚ) - k))
        ≤ (∑ k ∈ Ico 2 (o + 1), a k) + ∑ k ∈ Ico (o + 1) (n + 1), a k / ((k : ℚ) - o + 1))
    (hBR : (∑ k ∈ Ico 1 (n + 1), a k / ((k : ℚ) - 0)) ≤ ∑ k ∈ range 1, a k) :
    min (a o - a 2) (a o - a 0) ≤ 1 / 3 := by
  have hA' := cond_A a n o 2 hpo ha hA
  simp only [sum_range_succ, sum_range_zero] at hA' hAL hBR
  norm_num at hA' hAL
  have hW0 : 0 ≤ ∑ k ∈ Ico (o + 1) (n + 1), a k / ((k : ℚ) - o + 1) := sum_nonneg fun k hk => by
    have : (o : ℚ) + 1 ≤ k := by exact_mod_cast (mem_Ico.1 hk).1
    exact div_nonneg (ha k) (by linarith)
  have hWR : ∑ k ∈ Ico (o + 1) (n + 1), a k / ((k : ℚ) - o + 1) ≤ ∑ k ∈ Ico (o + 1) (n + 1), a k :=
    sum_le_sum fun k hk => by
      have : (o : ℚ) + 1 ≤ k := by exact_mod_cast (mem_Ico.1 hk).1
      exact div_le_self (ha k) (by linarith)
  have hsplitO : (∑ k ∈ range 2, a k) + ∑ k ∈ Ico 2 (o + 1), a k = (∑ k ∈ range o, a k) + a o := by
    rw [sum_range_add_sum_Ico _ (by omega : 2 ≤ o + 1), sum_range_succ]
  simp only [sum_range_succ, sum_range_zero] at hsplitO
  have hro := sum_range_add_sum_Ico a (by omega : 3 ≤ o)
  simp only [sum_range_succ, sum_range_zero] at hro
  have hI : 0 ≤ ∑ k ∈ Ico 3 o, a k := sum_nonneg fun k _ => ha k
  have hR0 : 0 ≤ ∑ k ∈ Ico (o + 1) (n + 1), a k := sum_nonneg fun k _ => ha k
  -- player 0 in the second order: keep the terms k = 1, 2
  have hlow : a 1 + a 2 / 2 ≤ ∑ k ∈ Ico 1 (n + 1), a k / ((k : ℚ) - 0) := by
    have h := sum_le_sum_of_subset_of_nonneg (f := fun k => a k / ((k : ℚ) - 0))
      (Ico_subset_Ico (le_refl 1) (by omega : 3 ≤ n + 1)) (fun k hk _ => by
        have : (1 : ℚ) ≤ k := by exact_mod_cast (mem_Ico.1 hk).1
        exact div_nonneg (ha k) (by linarith))
    have e : ∑ k ∈ Ico 1 3, a k / ((k : ℚ) - 0) = a 1 + a 2 / 2 := by
      rw [sum_Ico_succ_top (by norm_num), sum_Ico_succ_top (by norm_num), Ico_self, sum_empty]; norm_num
    linarith
  have c0 := hcap 0 (by omega); have c1 := hcap 1 (by omega); have c2 := hcap 2 (by omega)
  have n0 := ha 0; have n1 := ha 1; have n2 := ha 2
  rw [min_le_iff]
  by_contra hc
  rw [not_or, not_le, not_le] at hc
  obtain ⟨hc1, hc2⟩ := hc
  linarith

end RingMulticast
