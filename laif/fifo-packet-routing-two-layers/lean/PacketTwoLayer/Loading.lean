import PacketTwoLayer.Instance
import Mathlib

/-!
# The loading of one layer

Facts about `layer`.

* `layer_eq`: `layer` folds the step `lstep` over the processing order `order`.
* `order_eq_range`: if the arrival times are nondecreasing in the player index, the processing order is the index
  order.
* `layer_lower` and `layer_ne`: in every state each player reaches the head of her edge no earlier than her
  arrival at the tail plus the transit time, and two players on the same edge reach its head at different times.
* `st`, `layer_eq_st`, `out_st`, `NF_st_succ`: when the processing order is the index order, the head arrival of
  player `i` is `max (arr i) (NF i e) + τ e`, where `NF i e` is the next free departure time of edge `e` after the
  players `0, …, i - 1`.
-/

namespace PacketTwoLayer

open Finset

/-- The processing order of `layer`. -/
def order (arr : List ℕ) : List ℕ :=
  (List.range (arr.foldl max 0 + 1)).flatMap fun t =>
    (List.range arr.length).filter fun i => arr.getD i 0 == t

/-- The step of `layer`: player `i` departs at `max (arrival) (next free time)`. -/
def lstep (τ arr ch : List ℕ) (s : List ℕ × List ℕ) (i : ℕ) : List ℕ × List ℕ :=
  (s.1.set (ch.getD i 0) (max (arr.getD i 0) (s.1.getD (ch.getD i 0) 0) + 1),
   s.2.set i (max (arr.getD i 0) (s.1.getD (ch.getD i 0) 0) + τ.getD (ch.getD i 0) 0))

/-- The initial state of `layer`. -/
def init (τ arr : List ℕ) : List ℕ × List ℕ := (List.replicate τ.length 0, List.replicate arr.length 0)

theorem layer_eq (τ arr ch : List ℕ) :
    layer τ arr ch = ((order arr).foldl (lstep τ arr ch) (init τ arr)).2 := rfl

theorem getD_of_lt (l : List ℕ) {i : ℕ} (h : i < l.length) : l.getD i 0 = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem getD_of_ge (l : List ℕ) {i : ℕ} (h : l.length ≤ i) : l.getD i 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_set_eq (l : List ℕ) (e v g : ℕ) (he : e < l.length) :
    (l.set e v).getD g 0 = if g = e then v else l.getD g 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : g = e
  · subst h; simp [he]
  · simp [h, Ne.symm h]

theorem getD_replicate_zero (n i : ℕ) : (List.replicate n 0).getD i 0 = 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split_ifs <;> rfl

theorem le_foldl_max (l : List ℕ) (init : ℕ) :
    init ≤ l.foldl max init ∧ ∀ x ∈ l, x ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => simp
  | cons y l ih =>
    simp only [List.foldl_cons, List.mem_cons]
    obtain ⟨h1, h2⟩ := ih (max init y)
    refine ⟨le_trans (le_max_left _ _) h1, ?_⟩
    rintro x (rfl | hx)
    · exact le_trans (le_max_right _ _) h1
    · exact h2 x hx

theorem foldl_max_mem (l : List ℕ) (init : ℕ) : l.foldl max init = init ∨ l.foldl max init ∈ l := by
  induction l generalizing init with
  | nil => simp
  | cons y l ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rcases ih (max init y) with h | h
    · rw [h]
      rcases max_choice init y with h' | h' <;> simp [h']
    · exact Or.inr (Or.inr h)

theorem getD_le_foldl_max (l : List ℕ) (i : ℕ) : l.getD i 0 ≤ l.foldl max 0 := by
  by_cases h : i < l.length
  · rw [getD_of_lt _ h]
    exact (le_foldl_max l 0).2 _ (List.getElem_mem h)
  · rw [getD_of_ge _ (by omega)]
    exact Nat.zero_le _

/-- The maximum of a nonempty list is one of its entries. -/
theorem exists_getD_eq_foldl_max (l : List ℕ) (hl : l ≠ []) :
    ∃ i < l.length, l.getD i 0 = l.foldl max 0 := by
  rcases foldl_max_mem l 0 with h | h
  · refine ⟨0, List.length_pos_iff.mpr hl, le_antisymm ?_ ?_⟩
    · exact getD_le_foldl_max l 0
    · rw [h]; exact Nat.zero_le _
  · obtain ⟨i, hi, hx⟩ := List.getElem_of_mem h
    exact ⟨i, hi, by rw [getD_of_lt _ hi, hx]⟩

theorem mem_order {arr : List ℕ} {i : ℕ} (hi : i < arr.length) : i ∈ order arr := by
  unfold order
  simp only [List.mem_flatMap, List.mem_range, List.mem_filter, beq_iff_eq]
  exact ⟨arr.getD i 0, Nat.lt_succ_of_le (getD_le_foldl_max arr i), hi, rfl⟩

theorem lt_of_mem_order {arr : List ℕ} {i : ℕ} (h : i ∈ order arr) : i < arr.length := by
  unfold order at h
  simp only [List.mem_flatMap, List.mem_range, List.mem_filter] at h
  obtain ⟨_, _, h, _⟩ := h
  exact h

/-- For nondecreasing arrival times the processing order is the index order. -/
theorem order_eq_range {arr : List ℕ}
    (hmono : ∀ i j, i ≤ j → j < arr.length → arr.getD i 0 ≤ arr.getD j 0) :
    order arr = List.range arr.length := by
  have hp : (order arr).Pairwise (· < ·) := by
    unfold order
    rw [List.pairwise_flatMap]
    refine ⟨fun t _ => List.pairwise_lt_range.filter _, ?_⟩
    refine List.Pairwise.imp ?_ List.pairwise_lt_range
    intro t₁ t₂ ht x hx y hy
    simp only [List.mem_filter, List.mem_range, beq_iff_eq] at hx hy
    by_contra hxy
    have := hmono y x (by omega) hx.1
    omega
  have hn1 : (order arr).Nodup := hp.imp (fun h => ne_of_lt h)
  have hn2 : (List.range arr.length).Nodup := List.nodup_range
  have hperm : (order arr).Perm (List.range arr.length) := by
    rw [List.perm_ext_iff_of_nodup hn1 hn2]
    intro x
    simp only [List.mem_range]
    exact ⟨lt_of_mem_order, mem_order⟩
  exact hperm.eq_of_pairwise' (r := (· ≤ ·)) (hp.imp (fun h => le_of_lt h))
    (List.pairwise_lt_range.imp (fun h => le_of_lt h))

/-! ### Lower bounds and distinct head arrivals in every state -/

/-- The invariant of the fold: lengths, the lower bound, the bound by the next free time, and distinct head
arrivals on each edge, for the players in `P`. -/
def Good (τ arr ch : List ℕ) (P : ℕ → Prop) (s : List ℕ × List ℕ) : Prop :=
  s.1.length = τ.length ∧ s.2.length = arr.length ∧
  (∀ i, P i → arr.getD i 0 + τ.getD (ch.getD i 0) 0 ≤ s.2.getD i 0 ∧
      s.2.getD i 0 < s.1.getD (ch.getD i 0) 0 + τ.getD (ch.getD i 0) 0) ∧
  (∀ i j, P i → P j → i ≠ j → ch.getD i 0 = ch.getD j 0 → s.2.getD i 0 ≠ s.2.getD j 0)

theorem good_congr {τ arr ch : List ℕ} {P Q : ℕ → Prop} {s : List ℕ × List ℕ} (h : Good τ arr ch P s)
    (hPQ : ∀ i, Q i → P i) : Good τ arr ch Q s :=
  ⟨h.1, h.2.1, fun i hi => h.2.2.1 i (hPQ i hi), fun i j hi hj => h.2.2.2 i j (hPQ i hi) (hPQ j hj)⟩

theorem good_step {τ arr ch : List ℕ} {P : ℕ → Prop} {s : List ℕ × List ℕ} (h : Good τ arr ch P s)
    (x : ℕ) (hx : x < arr.length) (hch : ch.getD x 0 < τ.length) :
    Good τ arr ch (fun i => P i ∨ i = x) (lstep τ arr ch s x) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hnf : ∀ g, (lstep τ arr ch s x).1.getD g 0 =
      if g = ch.getD x 0 then max (arr.getD x 0) (s.1.getD (ch.getD x 0) 0) + 1 else s.1.getD g 0 := by
    intro g; simp only [lstep]; rw [getD_set_eq _ _ _ _ (by omega)]
  have hout : ∀ j, (lstep τ arr ch s x).2.getD j 0 =
      if j = x then max (arr.getD x 0) (s.1.getD (ch.getD x 0) 0) + τ.getD (ch.getD x 0) 0
      else s.2.getD j 0 := by
    intro j; simp only [lstep]; rw [getD_set_eq _ _ _ _ (by omega)]
  have hmax1 := le_max_left (arr.getD x 0) (s.1.getD (ch.getD x 0) 0)
  have hmax2 := le_max_right (arr.getD x 0) (s.1.getD (ch.getD x 0) 0)
  refine ⟨by simp [lstep, h1], by simp [lstep, h2], ?_, ?_⟩
  · intro i hi
    rw [hout, hnf]
    by_cases hix : i = x
    · subst hix
      rw [if_pos rfl, if_pos rfl]
      constructor <;> omega
    · have hPi : P i := hi.resolve_right hix
      obtain ⟨hl, hu⟩ := h3 i hPi
      rw [if_neg hix]
      by_cases hie : ch.getD i 0 = ch.getD x 0
      · rw [if_pos hie]; rw [hie] at hl hu ⊢; constructor <;> omega
      · rw [if_neg hie]; exact ⟨hl, hu⟩
  · intro i j hi hj hij hch'
    rw [hout, hout]
    by_cases hix : i = x
    · subst hix
      have hjx : j ≠ i := Ne.symm hij
      obtain ⟨_, hu⟩ := h3 j (hj.resolve_right hjx)
      rw [if_pos rfl, if_neg hjx]
      rw [← hch'] at hu
      omega
    · by_cases hjx : j = x
      · subst hjx
        obtain ⟨_, hu⟩ := h3 i (hi.resolve_right hix)
        rw [if_neg hix, if_pos rfl]
        rw [hch'] at hu
        omega
      · rw [if_neg hix, if_neg hjx]
        exact h4 i j (hi.resolve_right hix) (hj.resolve_right hjx) hij hch'

theorem good_fold {τ arr ch : List ℕ} (hch : ∀ i < arr.length, ch.getD i 0 < τ.length) :
    ∀ (l : List ℕ) (P : ℕ → Prop) (s : List ℕ × List ℕ), Good τ arr ch P s → (∀ x ∈ l, x < arr.length) →
      Good τ arr ch (fun i => P i ∨ i ∈ l) (l.foldl (lstep τ arr ch) s) := by
  intro l
  induction l with
  | nil => intro P s h _; exact good_congr h (fun i hi => by simpa using hi)
  | cons x l ih =>
    intro P s h hl
    have hx : x < arr.length := hl x (by simp)
    have := ih _ _ (good_step h x hx (hch x hx)) (fun y hy => hl y (by simp [hy]))
    refine good_congr this ?_
    intro i hi
    simp only [List.mem_cons] at hi
    tauto

theorem good_init (τ arr ch : List ℕ) : Good τ arr ch (fun _ => False) (init τ arr) :=
  ⟨by simp [init], by simp [init], fun _ h => h.elim, fun _ _ h => h.elim⟩

theorem good_layer {τ arr ch : List ℕ} (hch : ∀ i < arr.length, ch.getD i 0 < τ.length) :
    Good τ arr ch (fun i => i < arr.length) ((order arr).foldl (lstep τ arr ch) (init τ arr)) := by
  refine good_congr (good_fold hch (order arr) _ _ (good_init τ arr ch) (fun x hx => lt_of_mem_order hx)) ?_
  intro i hi
  exact Or.inr (mem_order hi)

theorem layer_length (τ arr ch : List ℕ) (hch : ∀ i < arr.length, ch.getD i 0 < τ.length) :
    (layer τ arr ch).length = arr.length := (good_layer hch).2.1

/-- Every player reaches the head of her edge no earlier than her arrival at the tail plus the transit time. -/
theorem layer_lower {τ arr ch : List ℕ} (hch : ∀ i < arr.length, ch.getD i 0 < τ.length) {i : ℕ}
    (hi : i < arr.length) : arr.getD i 0 + τ.getD (ch.getD i 0) 0 ≤ (layer τ arr ch).getD i 0 :=
  ((good_layer hch).2.2.1 i hi).1

/-- Two players on the same edge reach its head at different times. -/
theorem layer_ne {τ arr ch : List ℕ} (hch : ∀ i < arr.length, ch.getD i 0 < τ.length) {i j : ℕ}
    (hi : i < arr.length) (hj : j < arr.length) (hij : i ≠ j) (he : ch.getD i 0 = ch.getD j 0) :
    (layer τ arr ch).getD i 0 ≠ (layer τ arr ch).getD j 0 :=
  (good_layer hch).2.2.2 i j hi hj hij he

/-! ### The fold in index order -/

/-- The state after the players `0, …, i - 1` in index order. -/
def st (τ arr ch : List ℕ) (i : ℕ) : List ℕ × List ℕ := (List.range i).foldl (lstep τ arr ch) (init τ arr)

/-- The next free departure time of edge `g` after the players `0, …, i - 1`. -/
def NF (τ arr ch : List ℕ) (i g : ℕ) : ℕ := (st τ arr ch i).1.getD g 0

theorem st_succ (τ arr ch : List ℕ) (i : ℕ) : st τ arr ch (i + 1) = lstep τ arr ch (st τ arr ch i) i := by
  simp [st, List.range_succ, List.foldl_append]

theorem st_length (τ arr ch : List ℕ) (i : ℕ) :
    (st τ arr ch i).1.length = τ.length ∧ (st τ arr ch i).2.length = arr.length := by
  induction i with
  | zero => simp [st, init]
  | succ i ih => rw [st_succ]; simp [lstep, ih]

theorem layer_eq_st {τ arr ch : List ℕ}
    (hmono : ∀ i j, i ≤ j → j < arr.length → arr.getD i 0 ≤ arr.getD j 0) :
    layer τ arr ch = (st τ arr ch arr.length).2 := by
  rw [layer_eq, order_eq_range hmono]; rfl

theorem NF_zero (τ arr ch : List ℕ) (g : ℕ) : NF τ arr ch 0 g = 0 := by
  simp [NF, st, init, getD_replicate_zero]

theorem NF_succ (τ arr ch : List ℕ) (i g : ℕ) (hch : ch.getD i 0 < τ.length) :
    NF τ arr ch (i + 1) g =
      if g = ch.getD i 0 then max (arr.getD i 0) (NF τ arr ch i g) + 1 else NF τ arr ch i g := by
  have hl := (st_length τ arr ch i).1
  simp only [NF, st_succ, lstep]
  rw [getD_set_eq _ _ _ _ (by omega)]
  split_ifs with h
  · subst h; rfl
  · rfl

theorem out_succ_self (τ arr ch : List ℕ) (i : ℕ) (hi : i < arr.length) :
    (st τ arr ch (i + 1)).2.getD i 0 =
      max (arr.getD i 0) (NF τ arr ch i (ch.getD i 0)) + τ.getD (ch.getD i 0) 0 := by
  have hl := (st_length τ arr ch i).2
  simp only [st_succ, lstep]
  rw [getD_set_eq _ _ _ _ (by omega)]
  simp [NF]

theorem out_stable (τ arr ch : List ℕ) (i : ℕ) :
    ∀ j, i < j → j ≤ arr.length → (st τ arr ch j).2.getD i 0 = (st τ arr ch (i + 1)).2.getD i 0 := by
  intro j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
    · have hl := (st_length τ arr ch j).2
      rw [st_succ]
      simp only [lstep]
      rw [getD_set_eq _ _ _ _ (by omega), if_neg (by omega)]
      exact ih h (by omega)
    · rw [h]

/-- The head arrival of player `i` when the processing order is the index order. -/
theorem out_st (τ arr ch : List ℕ) (i : ℕ) (hi : i < arr.length) :
    (st τ arr ch arr.length).2.getD i 0 =
      max (arr.getD i 0) (NF τ arr ch i (ch.getD i 0)) + τ.getD (ch.getD i 0) 0 := by
  rw [out_stable τ arr ch i arr.length hi le_rfl, out_succ_self τ arr ch i hi]

/-- The state after the players `0, …, i - 1` depends only on their edges. -/
theorem st_congr (τ arr ch ch' : List ℕ) (i : ℕ) (h : ∀ j < i, ch.getD j 0 = ch'.getD j 0) :
    st τ arr ch i = st τ arr ch' i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [st_succ, st_succ, ih (fun j hj => h j (by omega))]
    simp only [lstep, h i (by omega)]

end PacketTwoLayer
