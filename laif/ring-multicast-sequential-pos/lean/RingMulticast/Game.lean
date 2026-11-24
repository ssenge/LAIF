import Mathlib

/-!
# The multicast game on a ring and myopic sequential play

Edges a 0, ..., a n of a ring with target t, counter-clockwise; players 0, ..., n − 1, player j between edge j and
edge j + 1. Player j takes its left path (edges 0, ..., j) when `c j = false` and its right path (edges
j + 1, ..., n) when `c j = true`. The cost of an edge is shared equally among its users. In myopic sequential play
the players arrive in the order given by the arrival times `t`, and each arriving player picks a path whose cost,
given the players that arrived before it, is not larger than the cost of the other path (ties either way).
-/

open Finset

namespace RingMulticast

/-- Player j uses edge k. -/
def usesB (c : ℕ → Bool) (j k : ℕ) : Bool := (c j && decide (j < k)) || (!c j && decide (k ≤ j))

/-- Number of players of S that use edge k. -/
def users (S : Finset ℕ) (c : ℕ → Bool) (k : ℕ) : ℕ := (S.filter fun j => usesB c j k = true).card

/-- Cost of edge k for a newcomer, when the players of S are already there. -/
def share (a : ℕ → ℚ) (S : Finset ℕ) (c : ℕ → Bool) (k : ℕ) : ℚ := a k / ((users S c k : ℚ) + 1)

/-- Cost of the left path of player i for a newcomer. -/
def leftCost (a : ℕ → ℚ) (S : Finset ℕ) (c : ℕ → Bool) (i : ℕ) : ℚ := ∑ k ∈ range (i + 1), share a S c k

/-- Cost of the right path of player i for a newcomer. -/
def rightCost (a : ℕ → ℚ) (n : ℕ) (S : Finset ℕ) (c : ℕ → Bool) (i : ℕ) : ℚ :=
  ∑ k ∈ Ico (i + 1) (n + 1), share a S c k

/-- The players that arrive before player i. -/
def before (t : ℕ → ℕ) (n i : ℕ) : Finset ℕ := (range n).filter fun j => t j < t i

/-- The choices c are a result of myopic sequential play in the order t. -/
def Myopic (a : ℕ → ℚ) (n : ℕ) (t : ℕ → ℕ) (c : ℕ → Bool) : Prop :=
  ∀ i < n, (c i = true → rightCost a n (before t n i) c i ≤ leftCost a (before t n i) c i) ∧
    (c i = false → leftCost a (before t n i) c i ≤ rightCost a n (before t n i) c i)

/-- Cost of the network built by the choices c: the sum of the used edges. -/
def netCost (a : ℕ → ℚ) (n : ℕ) (c : ℕ → Bool) : ℚ :=
  ∑ k ∈ range (n + 1), if users (range n) c k = 0 then 0 else a k

/-- Order A: players n − 1, ..., o arrive first, then 0, 1, ..., o − 1. -/
def tA (o n j : ℕ) : ℕ := if o ≤ j then n - 1 - j else n - o + j

/-- Order B: players n − 1, n − 2, ..., 0. -/
def tB (n j : ℕ) : ℕ := n - 1 - j

theorem tA_injOn (o n : ℕ) (hon : o ≤ n) : Set.InjOn (tA o n) (Set.Iio n) := by
  intro i hi j hj h
  simp only [Set.mem_Iio] at hi hj
  unfold tA at h
  split_ifs at h <;> omega

theorem tA_lt (o n j : ℕ) (hon : o ≤ n) (hj : j < n) : tA o n j < n := by
  unfold tA; split_ifs <;> omega

theorem before_tA_ge (o n i : ℕ) (hoi : o ≤ i) (hin : i < n) :
    before (tA o n) n i = (range n).filter fun j => i < j := by
  ext j; simp only [before, mem_filter, mem_range]; simp only [tA]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by split_ifs at h2 <;> omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by split_ifs <;> omega⟩

theorem before_tA_lt (o n i : ℕ) (hio : i < o) (hon : o ≤ n) :
    before (tA o n) n i = (range n).filter fun j => o ≤ j ∨ j < i := by
  ext j; simp only [before, mem_filter, mem_range]; simp only [tA]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by split_ifs at h2 <;> omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by split_ifs <;> omega⟩

theorem before_tB (n i : ℕ) (hin : i < n) : before (tB n) n i = (range n).filter fun j => i < j := by
  ext j; simp only [before, mem_filter, mem_range]; simp only [tB]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩

theorem users_congr (S : Finset ℕ) (c c' : ℕ → Bool) (k : ℕ) (h : ∀ j ∈ S, c j = c' j) :
    users S c k = users S c' k := by
  unfold users usesB
  congr 1
  apply filter_congr
  intro j hj
  rw [h j hj]

theorem share_nonneg (a : ℕ → ℚ) (ha : ∀ k, 0 ≤ a k) (S c k) : 0 ≤ share a S c k :=
  div_nonneg (ha k) (by positivity)

theorem share_le (a : ℕ → ℚ) (ha : ∀ k, 0 ≤ a k) (S c k) : share a S c k ≤ a k :=
  div_le_self (ha k) (by have : (0 : ℚ) ≤ users S c k := by positivity
                         linarith)

theorem share_of_users (a : ℕ → ℚ) (S c k) (u : ℕ) (h : users S c k = u) :
    share a S c k = a k / ((u : ℚ) + 1) := by
  rw [share, h]

/-- More users, smaller share. -/
theorem share_anti (a : ℕ → ℚ) (ha : ∀ k, 0 ≤ a k) (S S' c c' k) (h : users S c k ≤ users S' c' k) :
    share a S' c' k ≤ share a S c k := by
  unfold share
  apply div_le_div_of_nonneg_left (ha k) (by positivity)
  exact_mod_cast Nat.add_le_add_right h 1

theorem share_strict (a : ℕ → ℚ) (S S' c c' k) (hk : 0 < a k) (h : users S c k < users S' c' k) :
    share a S' c' k < share a S c k := by
  unfold share
  apply div_lt_div_of_pos_left hk (by positivity)
  exact_mod_cast Nat.add_lt_add_right h 1

/-- A network that leaves edge k unused costs at most the total minus a k. -/
theorem netCost_le (a : ℕ → ℚ) (ha : ∀ k, 0 ≤ a k) (n c k) (hk : k ≤ n) (h0 : users (range n) c k = 0) :
    netCost a n c ≤ (∑ j ∈ range (n + 1), a j) - a k := by
  have hsplit : ∀ j, a j = (if j = k then 0 else a j) + (if j = k then a j else 0) := by
    intro j; split_ifs <;> simp
  have htot : ∑ j ∈ range (n + 1), a j
      = (∑ j ∈ range (n + 1), (if j = k then 0 else a j)) + a k := by
    conv_lhs => rw [sum_congr rfl fun j _ => hsplit j]
    rw [sum_add_distrib, sum_ite_eq' (range (n + 1)) k a, if_pos (mem_range.2 (by omega))]
  have hle : netCost a n c ≤ ∑ j ∈ range (n + 1), (if j = k then 0 else a j) := by
    unfold netCost
    apply sum_le_sum
    intro j _
    by_cases hj : j = k
    · subst hj; simp [h0]
    · rw [if_neg hj]; split_ifs
      · exact ha j
      · exact le_rfl
  linarith

/-- Every network costs at least the total minus a most expensive edge: two unused edges k₁ < k₂ would leave
player k₁ without a path. -/
theorem netCost_ge (a : ℕ → ℚ) (ha : ∀ k, 0 ≤ a k) (n o : ℕ) (hon : o ≤ n) (hmax : ∀ k, k ≤ n → a k ≤ a o)
    (c : ℕ → Bool) : (∑ j ∈ range (n + 1), a j) - a o ≤ netCost a n c := by
  by_cases hall : ∀ k, k ≤ n → users (range n) c k ≠ 0
  · have : netCost a n c = ∑ j ∈ range (n + 1), a j := by
      unfold netCost
      apply sum_congr rfl
      intro j hj
      rw [if_neg (hall j (by simp at hj; omega))]
    have := ha o
    linarith
  · push_neg at hall
    obtain ⟨k, hk, h0⟩ := hall
    -- every other edge is used
    have hother : ∀ j, j ≤ n → j ≠ k → users (range n) c j ≠ 0 := by
      intro j hj hjk hj0
      -- the player between the two unused edges has no path
      have key : ∀ e, e ≤ n → users (range n) c e = 0 → ∀ i < n, usesB c i e = false := by
        intro e _ he i hi
        unfold users at he
        rw [card_eq_zero, filter_eq_empty_iff] at he
        have := he (mem_range.2 hi)
        simpa using this
      rcases Nat.lt_or_gt_of_ne hjk with hlt | hlt
      · have h1 := key j hj hj0 j (by omega)
        have h2 := key k hk h0 j (by omega)
        cases hc : c j <;> simp [usesB, hc] at h1 h2 <;> omega
      · have h1 := key k hk h0 k (by omega)
        have h2 := key j hj hj0 k (by omega)
        cases hc : c k <;> simp [usesB, hc] at h1 h2 <;> omega
    have : netCost a n c = (∑ j ∈ range (n + 1), a j) - a k := by
      have hsplit : ∀ j, a j = (if j = k then 0 else a j) + (if j = k then a j else 0) := by
        intro j; split_ifs <;> simp
      have htot : ∑ j ∈ range (n + 1), a j
          = (∑ j ∈ range (n + 1), (if j = k then 0 else a j)) + a k := by
        conv_lhs => rw [sum_congr rfl fun j _ => hsplit j]
        rw [sum_add_distrib, sum_ite_eq' (range (n + 1)) k a, if_pos (mem_range.2 (by omega))]
      rw [htot, add_sub_cancel_right]
      unfold netCost
      apply sum_congr rfl
      intro j hj
      by_cases hjk : j = k
      · subst hjk; simp [h0]
      · rw [if_neg hjk, if_neg (hother j (by simp at hj; omega) hjk)]
    have := hmax k hk
    linarith

end RingMulticast
