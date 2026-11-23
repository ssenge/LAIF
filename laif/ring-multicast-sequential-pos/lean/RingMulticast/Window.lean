import Mathlib

/-!
# The case d ≥ 4 of the ring bound, from the best-response conditions

Edges a 0, ..., a n of a ring, a most expensive edge o, the optimum Σ_{k ≠ o} a k normalized to 1. In the first
arrival order, players 0, ..., p − 1 go left and player p goes right, with p = m + 3 < o; in the second order,
players p − 1, p − 2, p − 3 go right. The hypotheses are the weak best-response conditions of these players, with
the cost shares at their arrival. The conclusion is a o − a p ≤ 1/3.
-/

open Finset

namespace RingMulticast

theorem window_bound (a : ℕ → ℚ) (n o m : ℕ) (hpo : m + 3 < o) (hon : o ≤ n)
    (ha : ∀ k, 0 ≤ a k) (hcap : ∀ k, k ≤ n → a k ≤ a o)
    (hopt : (∑ k ∈ range o, a k) + ∑ k ∈ Ico (o + 1) (n + 1), a k = 1)
    -- player p = m + 3 prefers right in the first order
    (hA : (∑ k ∈ Ico (m + 4) (o + 1), a k) + (∑ k ∈ Ico (o + 1) (n + 1), a k / ((k : ℚ) - o + 1))
        ≤ ∑ k ∈ range (m + 4), a k / ((m : ℚ) + 3 - k + 1))
    -- player p − 1 = m + 2 prefers left in the first order
    (hAL : (∑ k ∈ range (m + 3), a k / ((m : ℚ) + 3 - k))
        ≤ (∑ k ∈ Ico (m + 3) (o + 1), a k) + ∑ k ∈ Ico (o + 1) (n + 1), a k / ((k : ℚ) - o + 1))
    -- players m, m + 1, m + 2 prefer right in the second order
    (hBR : ∀ j, m ≤ j → j < m + 3 →
        (∑ k ∈ Ico (j + 1) (n + 1), a k / ((k : ℚ) - j)) ≤ ∑ k ∈ range (j + 1), a k) :
    a o - a (m + 3) ≤ 1 / 3 := by
  have hV0 : 0 ≤ ∑ k ∈ range m, a k := sum_nonneg fun k _ => ha k
  have hW0 : 0 ≤ ∑ k ∈ Ico (o + 1) (n + 1), a k / ((k : ℚ) - o + 1) := sum_nonneg fun k hk => by
    have : (o : ℚ) + 1 ≤ k := by exact_mod_cast (mem_Ico.1 hk).1
    exact div_nonneg (ha k) (by linarith)
  have hWR : ∑ k ∈ Ico (o + 1) (n + 1), a k / ((k : ℚ) - o + 1) ≤ ∑ k ∈ Ico (o + 1) (n + 1), a k :=
    sum_le_sum fun k hk => by
      have : (o : ℚ) + 1 ≤ k := by exact_mod_cast (mem_Ico.1 hk).1
      exact div_le_self (ha k) (by linarith)
  have hR0 : 0 ≤ ∑ k ∈ Ico (o + 1) (n + 1), a k := sum_nonneg fun k _ => ha k
  -- the condition of p, weakened
  have hAr : ∑ k ∈ range (m + 4), a k / ((m : ℚ) + 3 - k + 1)
      ≤ (∑ k ∈ range m, a k) / 5 + a m / 4 + a (m + 1) / 3 + a (m + 2) / 2 + a (m + 3) := by
    have hsplit : ∑ k ∈ range (m + 4), a k / ((m : ℚ) + 3 - k + 1)
        = (∑ k ∈ range m, a k / ((m : ℚ) + 3 - k + 1))
          + a m / 4 + a (m + 1) / 3 + a (m + 2) / 2 + a (m + 3) := by
      simp only [sum_range_succ]; push_cast; ring
    have hle : ∑ k ∈ range m, a k / ((m : ℚ) + 3 - k + 1) ≤ (∑ k ∈ range m, a k) / 5 := by
      rw [sum_div]
      exact sum_le_sum fun k hk => by
        have h1 : k + 1 ≤ m := mem_range.1 hk
        have : (k : ℚ) + 1 ≤ m := by exact_mod_cast h1
        exact div_le_div_of_nonneg_left (ha k) (by norm_num) (by linarith)
    linarith
  have hAo : a o ≤ ∑ k ∈ Ico (m + 4) (o + 1), a k :=
    single_le_sum (fun k _ => ha k) (mem_Ico.2 ⟨by omega, by omega⟩)
  -- the condition of p − 1, weakened
  have hALr : a (m + 2) + a (m + 1) / 2 + a m / 3 ≤ ∑ k ∈ range (m + 3), a k / ((m : ℚ) + 3 - k) := by
    have hsplit : ∑ k ∈ range (m + 3), a k / ((m : ℚ) + 3 - k)
        = (∑ k ∈ range m, a k / ((m : ℚ) + 3 - k)) + a m / 3 + a (m + 1) / 2 + a (m + 2) := by
      simp only [sum_range_succ]; push_cast; ring
    have h0 : 0 ≤ ∑ k ∈ range m, a k / ((m : ℚ) + 3 - k) := sum_nonneg fun k hk => by
      have h1 : k + 1 ≤ m := mem_range.1 hk
      have : (k : ℚ) + 1 ≤ m := by exact_mod_cast h1
      exact div_nonneg (ha k) (by linarith)
    linarith
  have hsplitO : (∑ k ∈ range (m + 3), a k) + ∑ k ∈ Ico (m + 3) (o + 1), a k
      = (∑ k ∈ range o, a k) + a o := by
    rw [sum_range_add_sum_Ico _ (by omega : m + 3 ≤ o + 1), sum_range_succ]
  have hr3 : ∑ k ∈ range (m + 3), a k = (∑ k ∈ range m, a k) + a m + a (m + 1) + a (m + 2) := by
    simp only [sum_range_succ]
  have hr4 : (∑ k ∈ range (m + 4), a k) + ∑ k ∈ Ico (m + 4) o, a k = ∑ k ∈ range o, a k :=
    sum_range_add_sum_Ico _ (by omega)
  have hI0 : 0 ≤ ∑ k ∈ Ico (m + 4) o, a k := sum_nonneg fun k _ => ha k
  have hr4' : ∑ k ∈ range (m + 4), a k = (∑ k ∈ range m, a k) + a m + a (m + 1) + a (m + 2) + a (m + 3) := by
    simp only [sum_range_succ]
  -- the conditions of m, m + 1, m + 2 in the second order, keeping the terms up to p
  have low : ∀ j t, m ≤ j → j < m + 3 → j + t ≤ m + 3 →
      ∑ k ∈ Ico (j + 1) (j + t + 1), a k / ((k : ℚ) - j) ≤ ∑ k ∈ range (j + 1), a k := by
    intro j t h1 h2 h3
    refine le_trans (sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico le_rfl (by omega)) ?_) (hBR j h1 h2)
    intro k hk _
    have : (j : ℚ) + 1 ≤ k := by exact_mod_cast (mem_Ico.1 hk).1
    exact div_nonneg (ha k) (by linarith)
  have hB1 : a (m + 3) ≤ (∑ k ∈ range m, a k) + a m + a (m + 1) + a (m + 2) := by
    have h := low (m + 2) 1 (by omega) (by omega) (by omega)
    have e : ∑ k ∈ Ico (m + 2 + 1) (m + 2 + 1 + 1), a k / ((k : ℚ) - ↑(m + 2)) = a (m + 3) := by
      rw [sum_Ico_succ_top (le_refl _), Ico_self, sum_empty]; push_cast; ring_nf
    rw [e] at h
    simp only [sum_range_succ] at h
    linarith
  have hB2 : a (m + 2) + a (m + 3) / 2 ≤ (∑ k ∈ range m, a k) + a m + a (m + 1) := by
    have h := low (m + 1) 2 (by omega) (by omega) (by omega)
    have e : ∑ k ∈ Ico (m + 1 + 1) (m + 1 + 2 + 1), a k / ((k : ℚ) - ↑(m + 1))
        = a (m + 2) + a (m + 3) / 2 := by
      rw [sum_Ico_succ_top (by omega), sum_Ico_succ_top (by omega), Ico_self, sum_empty]; push_cast; ring_nf
    rw [e] at h
    simp only [sum_range_succ] at h
    linarith
  have hB3 : a (m + 1) + a (m + 2) / 2 + a (m + 3) / 3 ≤ (∑ k ∈ range m, a k) + a m := by
    have h := low m 3 le_rfl (by omega) (by omega)
    have e : ∑ k ∈ Ico (m + 1) (m + 3 + 1), a k / ((k : ℚ) - ↑m)
        = a (m + 1) + a (m + 2) / 2 + a (m + 3) / 3 := by
      rw [sum_Ico_succ_top (by omega), sum_Ico_succ_top (by omega), sum_Ico_succ_top (by omega),
        Ico_self, sum_empty]; push_cast; ring_nf
    rw [e] at h
    simp only [sum_range_succ] at h
    linarith
  have c0 := hcap (m + 3) (by omega)
  have c1 := hcap (m + 2) (by omega)
  have c2 := hcap (m + 1) (by omega)
  have c3 := hcap m (by omega)
  have n0 := ha m; have n1 := ha (m + 1); have n2 := ha (m + 2); have n3 := ha (m + 3)
  linarith

/-- Case d = 3 with q = m ≥ 0: min (a o − a p) (a o − a (q + 1)) ≤ 1/3, with p = m + 3. -/
theorem bound_d3 (a : ℕ → ℚ) (n o m : ℕ) (hpo : m + 3 < o) (hon : o ≤ n)
    (ha : ∀ k, 0 ≤ a k) (hcap : ∀ k, k ≤ n → a k ≤ a o)
    (hopt : (∑ k ∈ range o, a k) + ∑ k ∈ Ico (o + 1) (n + 1), a k = 1)
    -- player p = m + 3 prefers right in the first order
    (hA : (∑ k ∈ Ico (m + 4) (o + 1), a k) + (∑ k ∈ Ico (o + 1) (n + 1), a k / ((k : ℚ) - o + 1))
        ≤ ∑ k ∈ range (m + 4), a k / ((m : ℚ) + 3 - k + 1))
    -- player p − 1 = m + 2 prefers left in the first order
    (hAL : (∑ k ∈ range (m + 3), a k / ((m : ℚ) + 3 - k))
        ≤ (∑ k ∈ Ico (m + 3) (o + 1), a k) + ∑ k ∈ Ico (o + 1) (n + 1), a k / ((k : ℚ) - o + 1))
    -- player q + 1 = m + 1 prefers right in the second order
    (hBR1 : (∑ k ∈ Ico (m + 1 + 1) (n + 1), a k / ((k : ℚ) - ↑(m + 1))) ≤ ∑ k ∈ range (m + 1 + 1), a k) :
    min (a o - a (m + 3)) (a o - a (m + 1)) ≤ 1 / 3 := by
  have hBR : ∀ j, j = m + 1 →
      (∑ k ∈ Ico (j + 1) (n + 1), a k / ((k : ℚ) - j)) ≤ ∑ k ∈ range (j + 1), a k := by
    rintro j rfl; exact hBR1
  have hV0 : 0 ≤ ∑ k ∈ range m, a k := sum_nonneg fun k _ => ha k
  have hW0 : 0 ≤ ∑ k ∈ Ico (o + 1) (n + 1), a k / ((k : ℚ) - o + 1) := sum_nonneg fun k hk => by
    have : (o : ℚ) + 1 ≤ k := by exact_mod_cast (mem_Ico.1 hk).1
    exact div_nonneg (ha k) (by linarith)
  have hWR : ∑ k ∈ Ico (o + 1) (n + 1), a k / ((k : ℚ) - o + 1) ≤ ∑ k ∈ Ico (o + 1) (n + 1), a k :=
    sum_le_sum fun k hk => by
      have : (o : ℚ) + 1 ≤ k := by exact_mod_cast (mem_Ico.1 hk).1
      exact div_le_self (ha k) (by linarith)
  have hR0 : 0 ≤ ∑ k ∈ Ico (o + 1) (n + 1), a k := sum_nonneg fun k _ => ha k
  -- the condition of p, weakened
  have hAr : ∑ k ∈ range (m + 4), a k / ((m : ℚ) + 3 - k + 1)
      ≤ (∑ k ∈ range m, a k) / 5 + a m / 4 + a (m + 1) / 3 + a (m + 2) / 2 + a (m + 3) := by
    have hsplit : ∑ k ∈ range (m + 4), a k / ((m : ℚ) + 3 - k + 1)
        = (∑ k ∈ range m, a k / ((m : ℚ) + 3 - k + 1))
          + a m / 4 + a (m + 1) / 3 + a (m + 2) / 2 + a (m + 3) := by
      simp only [sum_range_succ]; push_cast; ring
    have hle : ∑ k ∈ range m, a k / ((m : ℚ) + 3 - k + 1) ≤ (∑ k ∈ range m, a k) / 5 := by
      rw [sum_div]
      exact sum_le_sum fun k hk => by
        have h1 : k + 1 ≤ m := mem_range.1 hk
        have : (k : ℚ) + 1 ≤ m := by exact_mod_cast h1
        exact div_le_div_of_nonneg_left (ha k) (by norm_num) (by linarith)
    linarith
  have hAo : a o ≤ ∑ k ∈ Ico (m + 4) (o + 1), a k :=
    single_le_sum (fun k _ => ha k) (mem_Ico.2 ⟨by omega, by omega⟩)
  -- the condition of p − 1, weakened
  have hALr : a (m + 2) + a (m + 1) / 2 + a m / 3 ≤ ∑ k ∈ range (m + 3), a k / ((m : ℚ) + 3 - k) := by
    have hsplit : ∑ k ∈ range (m + 3), a k / ((m : ℚ) + 3 - k)
        = (∑ k ∈ range m, a k / ((m : ℚ) + 3 - k)) + a m / 3 + a (m + 1) / 2 + a (m + 2) := by
      simp only [sum_range_succ]; push_cast; ring
    have h0 : 0 ≤ ∑ k ∈ range m, a k / ((m : ℚ) + 3 - k) := sum_nonneg fun k hk => by
      have h1 : k + 1 ≤ m := mem_range.1 hk
      have : (k : ℚ) + 1 ≤ m := by exact_mod_cast h1
      exact div_nonneg (ha k) (by linarith)
    linarith
  have hsplitO : (∑ k ∈ range (m + 3), a k) + ∑ k ∈ Ico (m + 3) (o + 1), a k
      = (∑ k ∈ range o, a k) + a o := by
    rw [sum_range_add_sum_Ico _ (by omega : m + 3 ≤ o + 1), sum_range_succ]
  have hr3 : ∑ k ∈ range (m + 3), a k = (∑ k ∈ range m, a k) + a m + a (m + 1) + a (m + 2) := by
    simp only [sum_range_succ]
  have hr4 : (∑ k ∈ range (m + 4), a k) + ∑ k ∈ Ico (m + 4) o, a k = ∑ k ∈ range o, a k :=
    sum_range_add_sum_Ico _ (by omega)
  have hI0 : 0 ≤ ∑ k ∈ Ico (m + 4) o, a k := sum_nonneg fun k _ => ha k
  have hr4' : ∑ k ∈ range (m + 4), a k = (∑ k ∈ range m, a k) + a m + a (m + 1) + a (m + 2) + a (m + 3) := by
    simp only [sum_range_succ]
  -- the conditions of m, m + 1, m + 2 in the second order, keeping the terms up to p
  have low : ∀ j t, j = m + 1 → j + t ≤ m + 3 →
      ∑ k ∈ Ico (j + 1) (j + t + 1), a k / ((k : ℚ) - j) ≤ ∑ k ∈ range (j + 1), a k := by
    intro j t h1 h3
    refine le_trans (sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico le_rfl (by omega)) ?_) (hBR j h1)
    intro k hk _
    have : (j : ℚ) + 1 ≤ k := by exact_mod_cast (mem_Ico.1 hk).1
    exact div_nonneg (ha k) (by linarith)
  have hB2 : a (m + 2) + a (m + 3) / 2 ≤ (∑ k ∈ range m, a k) + a m + a (m + 1) := by
    have h := low (m + 1) 2 rfl (by omega)
    have e : ∑ k ∈ Ico (m + 1 + 1) (m + 1 + 2 + 1), a k / ((k : ℚ) - ↑(m + 1))
        = a (m + 2) + a (m + 3) / 2 := by
      rw [sum_Ico_succ_top (by omega), sum_Ico_succ_top (by omega), Ico_self, sum_empty]; push_cast; ring_nf
    rw [e] at h
    simp only [sum_range_succ] at h
    linarith
  have c0 := hcap (m + 3) (by omega)
  have c1 := hcap (m + 2) (by omega)
  have c2 := hcap (m + 1) (by omega)
  have c3 := hcap m (by omega)
  have n0 := ha m; have n1 := ha (m + 1); have n2 := ha (m + 2); have n3 := ha (m + 3)
  rw [min_le_iff]
  by_contra hc
  rw [not_or, not_le, not_le] at hc
  obtain ⟨hc1, hc2⟩ := hc
  linarith


end RingMulticast
