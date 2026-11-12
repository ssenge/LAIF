import Monge.Decision
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Order.Interval.Finset.Fin

/-!
# The corollary of Theorem 3: the maximum, with no dependence on the value range

Rows are visited in a random order `σ`. Each round finds the first row of the order whose maximum
exceeds the current `θ`, by bisection on prefixes of the order, reads that row's maximum, and sets
`θ` to it.

What is proved here:

* `someAbove_query_le`, `someAbove_sqrt_log`: the decision on any set of rows with the strict test;
* `firstTrue_spec`, `firstTrueCalls_le`: prefix bisection with `⌈log₂⌉` decisions;
* `visited_spec`, `visited_finds_max`: with exact decisions the loop visits only strict records and
  ends at the global maximum;
* `sum_recordCount_le`, `mean_rounds_le`: over a uniform order, the mean number of rounds is at most
  `H_r ≤ 1 + ln r`. This is the expected-halving step, proved rather than assumed;
* `mean_cost_le`, `maximum_mean_cost`: the expected query count `O(√n log³ n · E)`, where `E` is the
  repetition factor for a decision. The README takes `E = O(log log n)`.

What is not proved: the query bound as a statement about `queryQ`. That would also need bounded-error
adaptive composition with error reduction and a first moment step from the mean to a worst case, in the
quantum model. So `maximum_mean_cost` is an accounting of decisions and maximum findings in the
classical control loop, with exact decisions, and not a theorem about `queryQ`.
-/

open Finset

namespace Monge

/-! ## A set of rows, with the strict test -/

variable {r c k : ℕ}

/-- `[some entry in the rows of `S` is above `θ`]`. -/
noncomputable def someAbove (S : Finset (Fin r)) (θ : Fin k) (x : Mat r c k) : Bool := by
  classical exact decide (∃ i ∈ S, ∃ j, θ < x (i, j))

theorem someAbove_eq_someEntry (S : Finset (Fin r)) (θ : Fin k) :
    (someAbove S θ : Mat r c k → Bool) =
      someEntry (fun a => decide (θ < a)) (S.orderEmbOfFin (rfl : S.card = S.card)) := by
  funext x
  rw [Bool.eq_iff_iff, someEntry_eq_true]
  have hmem : ∀ i, i ∈ S ↔ ∃ t, S.orderEmbOfFin (rfl : S.card = S.card) t = i := by
    intro i
    constructor
    · intro hi
      have hr : i ∈ Set.range (S.orderEmbOfFin (rfl : S.card = S.card)) := by
        rw [Finset.range_orderEmbOfFin]
        exact hi
      exact hr
    · rintro ⟨t, rfl⟩
      exact Finset.orderEmbOfFin_mem S rfl t
  constructor
  · intro h
    have h' : ∃ i ∈ S, ∃ j, θ < x (i, j) := by simpa [someAbove] using h
    obtain ⟨i, hi, j, hj⟩ := h'
    obtain ⟨t, rfl⟩ := (hmem i).mp hi
    exact ⟨t, j, by simpa using hj⟩
  · rintro ⟨t, j, h⟩
    have h' : ∃ i ∈ S, ∃ j, θ < x (i, j) :=
      ⟨_, (hmem _).mpr ⟨t, rfl⟩, j, by simpa using h⟩
    simpa [someAbove] using h'

/-- The strict decision on any set of rows costs what Theorem 3 says for `|S|` rows. -/
theorem someAbove_query_le {C κ₀ : ℝ} (hC : 0 ≤ C) (hκ₀ : 0 ≤ κ₀) (hLQ : LeeQueryAdv C)
    (hLG : LeeAdvGamma) (hDH : DurrHoyer κ₀) [NeZero c] (S : Finset (Fin r)) (θ : Fin k) :
    (queryQ (tmInputs r c k) (someAbove S θ) : ℝ) ≤
      C * ((2 * (2 * C * κ₀) + 1) * ell S.card * √((c : ℝ) + S.card)) := by
  rw [someAbove_eq_someEntry]
  exact decision_query_le hC hκ₀ hLQ hLG hDH (fun a b hab h => by
    simp only [decide_eq_true_eq] at h ⊢
    exact lt_of_lt_of_le h hab) (S.orderEmbOfFin (rfl : S.card = S.card)).strictMono

/-- The strict decision on any set of rows is `O(√n log n)`, uniformly in the alphabet. -/
theorem someAbove_sqrt_log {C κ₀ : ℝ} (hC : 0 ≤ C) (hκ₀ : 0 ≤ κ₀) (hLQ : LeeQueryAdv C)
    (hLG : LeeAdvGamma) (hDH : DurrHoyer κ₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (r c k n : ℕ) [NeZero c] (S : Finset (Fin r)) (θ : Fin k),
      r ≤ n → c ≤ n → 2 ≤ n →
      (queryQ (tmInputs r c k) (someAbove S θ) : ℝ) ≤ K * √(n : ℝ) * Real.logb 2 n := by
  set a := 2 * (2 * C * κ₀) + 1 with ha
  have ha0 : 0 ≤ a := by positivity
  refine ⟨C * a * (2 * √2), by positivity, ?_⟩
  intro r c k n _ S θ hr hc hn
  refine (someAbove_query_le hC hκ₀ hLQ hLG hDH S θ).trans ?_
  have hcard : S.card ≤ r := by
    have := Finset.card_le_univ S
    simpa using this
  have hell := ell_le_two_logb (hcard.trans hr) hn
  have hsqrt : √((c : ℝ) + S.card) ≤ √2 * √(n : ℝ) := by
    rw [← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    have h1 : (S.card : ℝ) ≤ n := by exact_mod_cast hcard.trans hr
    have h2 : (c : ℝ) ≤ n := by exact_mod_cast hc
    linarith
  have hprod : (ell S.card : ℝ) * √((c : ℝ) + S.card) ≤ (2 * Real.logb 2 n) * (√2 * √(n : ℝ)) :=
    mul_le_mul hell hsqrt (Real.sqrt_nonneg _) ((Nat.cast_nonneg _).trans hell)
  calc C * (a * ell S.card * √((c : ℝ) + S.card)) =
      C * a * ((ell S.card : ℝ) * √((c : ℝ) + S.card)) := by ring
    _ ≤ C * a * ((2 * Real.logb 2 n) * (√2 * √(n : ℝ))) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = C * a * (2 * √2) * √(n : ℝ) * Real.logb 2 n := by ring

/-! ## Prefix bisection -/

/-- Bisection for a crossing point of `dec` between `lo` and `hi`. -/
def firstTrue (dec : ℕ → Bool) (lo hi : ℕ) : ℕ :=
  if lo + 1 < hi then
    if dec ((lo + hi) / 2) then firstTrue dec lo ((lo + hi) / 2)
    else firstTrue dec ((lo + hi) / 2) hi
  else hi
termination_by hi - lo
decreasing_by all_goals omega

/-- The number of decisions `firstTrue` makes. -/
def firstTrueCalls (dec : ℕ → Bool) (lo hi : ℕ) : ℕ :=
  if lo + 1 < hi then
    if dec ((lo + hi) / 2) then firstTrueCalls dec lo ((lo + hi) / 2) + 1
    else firstTrueCalls dec ((lo + hi) / 2) hi + 1
  else 0
termination_by hi - lo
decreasing_by all_goals omega

/-- `firstTrue` returns `t` with `dec t` true and `dec (t - 1)` false. For a monotone `dec`, this is
the first true position. -/
theorem firstTrue_spec (dec : ℕ → Bool) (d lo hi : ℕ) (hd : hi - lo = d) (hlt : lo < hi)
    (hlo : dec lo = false) (hhi : dec hi = true) :
    lo < firstTrue dec lo hi ∧ firstTrue dec lo hi ≤ hi ∧ dec (firstTrue dec lo hi) = true ∧
      dec (firstTrue dec lo hi - 1) = false := by
  induction d using Nat.strong_induction_on generalizing lo hi with
  | _ d ih =>
    rw [firstTrue]
    by_cases h : lo + 1 < hi
    · simp only [h, ↓reduceIte]
      cases hmid : dec ((lo + hi) / 2)
      · have := ih (hi - (lo + hi) / 2) (by omega) ((lo + hi) / 2) hi rfl (by omega) hmid hhi
        have h5 := this.1
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨by omega, this.2.1, this.2.2⟩
      · have := ih ((lo + hi) / 2 - lo) (by omega) lo ((lo + hi) / 2) rfl (by omega) hlo hmid
        have h5 := this.2.1
        simp only [↓reduceIte]
        exact ⟨this.1, by omega, this.2.2⟩
    · simp only [h, ↓reduceIte]
      have heq : hi - 1 = lo := by omega
      exact ⟨hlt, le_rfl, hhi, by rw [heq]; exact hlo⟩

/-- Bisection on `d` positions uses at most `⌈log₂ d⌉` decisions. -/
theorem firstTrueCalls_le (dec : ℕ → Bool) (d lo hi : ℕ) (hd : hi - lo = d) :
    firstTrueCalls dec lo hi ≤ Nat.clog 2 d := by
  induction d using Nat.strong_induction_on generalizing lo hi with
  | _ d ih =>
    rw [firstTrueCalls]
    by_cases h : lo + 1 < hi
    · simp only [h, ↓reduceIte]
      have hd2 : 2 ≤ d := by omega
      have hclog : Nat.clog 2 d = Nat.clog 2 ((d + 2 - 1) / 2) + 1 :=
        Nat.clog_of_two_le (by norm_num) hd2
      cases dec ((lo + hi) / 2)
      · have h1 := ih (hi - (lo + hi) / 2) (by omega) ((lo + hi) / 2) hi rfl
        have h2 : Nat.clog 2 (hi - (lo + hi) / 2) ≤ Nat.clog 2 ((d + 2 - 1) / 2) :=
          Nat.clog_mono_right 2 (by omega)
        simp only [Bool.false_eq_true, ↓reduceIte]
        omega
      · have h1 := ih ((lo + hi) / 2 - lo) (by omega) lo ((lo + hi) / 2) rfl
        have h2 : Nat.clog 2 ((lo + hi) / 2 - lo) ≤ Nat.clog 2 ((d + 2 - 1) / 2) :=
          Nat.clog_mono_right 2 (by omega)
        simp only [↓reduceIte]
        omega
    · simp [h]

/-! ## The rounds -/

variable {α : Type*} [LinearOrder α]

/-- Is some row among the first `t` of the order above `θ`? Here `w` lists the row maxima in the
order, so this is the decision on a prefix. -/
def prefixAbove (w : Fin r → α) (θ : α) (t : ℕ) : Bool :=
  decide (∃ i : Fin r, (i : ℕ) < t ∧ θ < w i)

/-- The positions visited by the loop, starting from `p`. With exact decisions, the next position is
the first one above the current value. -/
def visited (w : Fin r → α) : ℕ → Fin r → List (Fin r)
  | 0, p => [p]
  | fuel + 1, p =>
    if prefixAbove w (w p) r then
      if h : firstTrue (prefixAbove w (w p)) (p + 1) r - 1 < r then
        p :: visited w fuel ⟨firstTrue (prefixAbove w (w p)) (p + 1) r - 1, h⟩
      else [p]
    else [p]

/-- Position `p` is a strict record of the sequence. -/
def IsRecord (w : Fin r → α) (p : Fin r) : Prop := ∀ i, i < p → w i < w p

instance (w : Fin r → α) (p : Fin r) : Decidable (IsRecord w p) := by
  unfold IsRecord
  infer_instance

/-- The number of strict records. -/
def recordCount (w : Fin r → α) : ℕ := (univ.filter (IsRecord w)).card

theorem IsRecord.le {w : Fin r → α} {p : Fin r} (hp : IsRecord w p) {i : Fin r} (hi : i ≤ p) :
    w i ≤ w p := by
  rcases hi.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact (hp i hlt).le

theorem single_spec {w : Fin r → α} {p : Fin r} (hp : IsRecord w p) (hmax : ∀ i, w i ≤ w p) :
    (∀ q ∈ [p], IsRecord w q) ∧ ([p] : List (Fin r)).Pairwise (· < ·) ∧
      (∀ q ∈ [p], p ≤ q) ∧ ∃ q ∈ [p], ∀ i, w i ≤ w q := by
  refine ⟨?_, by simp, ?_, p, by simp, hmax⟩
  · intro q hq
    rw [List.mem_singleton] at hq
    rw [hq]
    exact hp
  · intro q hq
    rw [List.mem_singleton] at hq
    rw [hq]

/-- With exact decisions, the loop visits strict records in increasing order and reaches a global
maximum. -/
theorem visited_spec (w : Fin r → α) (fuel : ℕ) (p : Fin r) (hp : IsRecord w p)
    (hfuel : r ≤ p + fuel + 1) :
    (∀ q ∈ visited w fuel p, IsRecord w q) ∧ (visited w fuel p).Pairwise (· < ·) ∧
      (∀ q ∈ visited w fuel p, p ≤ q) ∧ ∃ q ∈ visited w fuel p, ∀ i, w i ≤ w q := by
  induction fuel generalizing p with
  | zero =>
    exact single_spec hp fun i => hp.le (by
      rw [Fin.le_def]
      have := i.2
      omega)
  | succ fuel ih =>
    rw [visited]
    have hprefix : ∀ t : ℕ, t ≤ (p : ℕ) + 1 → prefixAbove w (w p) t = false := by
      intro t ht
      rw [prefixAbove, decide_eq_false_iff_not]
      rintro ⟨i, hi, hgt⟩
      exact absurd (hp.le (i := i) (by rw [Fin.le_def]; omega)) (not_le.mpr hgt)
    cases hdec : prefixAbove w (w p) r with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply single_spec hp
      intro i
      rw [prefixAbove, decide_eq_false_iff_not] at hdec
      exact not_lt.mp fun hgt => hdec ⟨i, i.2, hgt⟩
    | true =>
      simp only [↓reduceIte]
      have hlt : p + 1 < r := by
        by_contra hcon
        have := hprefix r (by omega)
        rw [this] at hdec
        exact absurd hdec (by simp)
      obtain ⟨h1, h2, h3, h4⟩ := firstTrue_spec (prefixAbove w (w p)) _ ((p : ℕ) + 1) r rfl hlt
        (hprefix _ le_rfl) hdec
      set t := firstTrue (prefixAbove w (w p)) (p + 1) r with ht
      have htr : t - 1 < r := by omega
      simp only [htr, ↓reduceDIte]
      set next : Fin r := ⟨t - 1, htr⟩ with hnext
      have hnv : (next : ℕ) = t - 1 := rfl
      have hpn : p < next := by
        rw [Fin.lt_def]
        omega
      -- the next position is above the current value, and nothing before it is
      rw [prefixAbove, decide_eq_true_eq] at h3
      rw [prefixAbove, decide_eq_false_iff_not] at h4
      obtain ⟨i, hi, hgt⟩ := h3
      have hin : i = next := by
        apply Fin.ext
        by_contra hne
        exact h4 ⟨i, by omega, hgt⟩
      have hbigger : w p < w next := by
        rw [← hin]
        exact hgt
      have hrec : IsRecord w next := by
        intro j hj
        rw [Fin.lt_def] at hj
        have : ¬ w p < w j := fun hc => h4 ⟨j, by omega, hc⟩
        exact lt_of_le_of_lt (not_lt.mp this) hbigger
      obtain ⟨r1, r2, r3, q, hq, hqmax⟩ := ih next hrec (by
        have := Fin.lt_def.mp hpn
        omega)
      refine ⟨?_, ?_, ?_, q, List.mem_cons_of_mem _ hq, hqmax⟩
      · intro q' hq'
        rcases List.mem_cons.mp hq' with rfl | hq'
        · exact hp
        · exact r1 q' hq'
      · rw [List.pairwise_cons]
        exact ⟨fun q' hq' => lt_of_lt_of_le hpn (r3 q' hq'), r2⟩
      · intro q' hq'
        rcases List.mem_cons.mp hq' with rfl | hq'
        · exact le_rfl
        · exact hpn.le.trans (r3 q' hq')

/-- The loop from the first row of the order. -/
def rounds (w : Fin r → α) (hr : 0 < r) : List (Fin r) := visited w r ⟨0, hr⟩

theorem isRecord_zero (w : Fin r → α) (hr : 0 < r) : IsRecord w ⟨0, hr⟩ := by
  intro i hi
  exact absurd hi (by simp [Fin.lt_def])

/-- **Correctness.** For every order, the loop reaches a row holding the global maximum. -/
theorem visited_finds_max (v : Fin r → α) (σ : Equiv.Perm (Fin r)) (hr : 0 < r) :
    ∃ q ∈ rounds (v ∘ σ) hr, ∀ i, v i ≤ v (σ q) := by
  obtain ⟨-, -, -, q, hq, hmax⟩ :=
    visited_spec (v ∘ σ) r ⟨0, hr⟩ (isRecord_zero _ hr) (by show r ≤ 0 + r + 1; omega)
  refine ⟨q, hq, fun i => ?_⟩
  have := hmax (σ⁻¹ i)
  simpa using this

/-- The number of rounds is at most the number of strict records. -/
theorem rounds_length_le (w : Fin r → α) (hr : 0 < r) :
    (rounds w hr).length ≤ recordCount w := by
  obtain ⟨h1, h2, -, -⟩ := visited_spec w r ⟨0, hr⟩ (isRecord_zero _ hr)
    (by show r ≤ 0 + r + 1; omega)
  have hnodup : (rounds w hr).Nodup := h2.imp fun h => h.ne
  rw [← List.toFinset_card_of_nodup hnodup]
  unfold recordCount
  apply Finset.card_le_card
  intro q hq
  simp only [mem_filter, mem_univ, true_and]
  exact h1 q (List.mem_toFinset.mp hq)

/-! ## The mean number of rounds over a uniform order -/

/-- For `i ≤ t`, the orders with a strict maximum of the first `t + 1` rows at position `i`. -/
def topAt (v : Fin r → α) (t i : Fin r) : Finset (Equiv.Perm (Fin r)) :=
  univ.filter fun σ => ∀ j : Fin r, j ≤ t → j ≠ i → v (σ j) < v (σ i)

/-- Swapping positions `i` and `t` sends the orders with a record at `t` into `topAt v t i`. -/
theorem record_card_le_topAt (v : Fin r → α) {t i : Fin r} (hit : i ≤ t) :
    (univ.filter fun σ : Equiv.Perm (Fin r) => IsRecord (v ∘ σ) t).card ≤ (topAt v t i).card := by
  apply Finset.card_le_card_of_injOn (fun σ => σ * Equiv.swap i t)
  · intro σ hσ
    have hrec : IsRecord (v ∘ σ) t := by simpa using hσ
    simp only [topAt, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, Equiv.Perm.coe_mul,
      Function.comp_apply, Equiv.swap_apply_left]
    intro j hjt hji
    by_cases hjt' : j = t
    · rw [hjt', Equiv.swap_apply_right]
      exact hrec i (lt_of_le_of_ne hit fun h => hji (hjt'.trans h.symm))
    · rw [Equiv.swap_apply_of_ne_of_ne hji hjt']
      exact hrec j (lt_of_le_of_ne hjt hjt')
  · intro σ _ τ _ h
    exact mul_right_cancel h

/-- Position `t` is a record in at most a `1 / (t + 1)` fraction of the orders: the sets `topAt v t i`
for `i ≤ t` are disjoint, and each is at least as large as the set of orders with a record at `t`. -/
theorem succ_mul_record_le (v : Fin r → α) (t : Fin r) :
    ((t : ℕ) + 1) * (univ.filter fun σ : Equiv.Perm (Fin r) => IsRecord (v ∘ σ) t).card ≤
      r.factorial := by
  classical
  have hdisj : ((Finset.Iic t : Finset (Fin r)) : Set (Fin r)).PairwiseDisjoint (topAt v t) := by
    intro i hi i' hi' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro σ h1 h2
    have hi1 : i ≤ t := by simpa using hi
    have hi2 : i' ≤ t := by simpa using hi'
    have h1' : ∀ j : Fin r, j ≤ t → j ≠ i → v (σ j) < v (σ i) := by
      simpa [topAt] using h1
    have h2' : ∀ j : Fin r, j ≤ t → j ≠ i' → v (σ j) < v (σ i') := by
      simpa [topAt] using h2
    exact lt_asymm (h1' i' hi2 hne.symm) (h2' i hi1 hne)
  calc ((t : ℕ) + 1) * (univ.filter fun σ : Equiv.Perm (Fin r) => IsRecord (v ∘ σ) t).card
      = ∑ _i ∈ Finset.Iic t, (univ.filter fun σ : Equiv.Perm (Fin r) => IsRecord (v ∘ σ) t).card := by
        rw [Finset.sum_const, Fin.card_Iic, smul_eq_mul]
    _ ≤ ∑ i ∈ Finset.Iic t, (topAt v t i).card :=
        Finset.sum_le_sum fun i hi => record_card_le_topAt v (by simpa using hi)
    _ = ((Finset.Iic t).biUnion (topAt v t)).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (univ : Finset (Equiv.Perm (Fin r))).card := Finset.card_le_univ _
    _ = r.factorial := by rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

/-- Summed over all orders, the number of strict records is at most `r! H_r`. -/
theorem sum_recordCount_le (v : Fin r → α) :
    ((∑ σ : Equiv.Perm (Fin r), recordCount (v ∘ σ) : ℕ) : ℝ) ≤
      (r.factorial : ℝ) * (harmonic r : ℝ) := by
  have hswap : ∑ σ : Equiv.Perm (Fin r), recordCount (v ∘ σ) =
      ∑ t : Fin r, (univ.filter fun σ : Equiv.Perm (Fin r) => IsRecord (v ∘ σ) t).card := by
    simp only [recordCount, Finset.card_filter]
    exact Finset.sum_comm
  have hharm : (harmonic r : ℝ) = ∑ t : Fin r, ((t : ℕ) + 1 : ℝ)⁻¹ := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((i : ℝ) + 1)⁻¹) r]
    simp [harmonic]
  rw [hswap, hharm, Finset.mul_sum]
  push_cast
  apply Finset.sum_le_sum
  intro t _
  have hpos : (0 : ℝ) < (t : ℕ) + 1 := by positivity
  have h := succ_mul_record_le v t
  have h' : ((t : ℕ) + 1 : ℝ) *
      ((univ.filter fun σ : Equiv.Perm (Fin r) => IsRecord (v ∘ σ) t).card : ℝ) ≤
      (r.factorial : ℝ) := by
    exact_mod_cast h
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  linarith

/-- **Expected rounds.** Over a uniform order, the mean number of rounds is at most `1 + ln r`. -/
theorem mean_rounds_le (v : Fin r → α) (hr : 0 < r) :
    ((∑ σ : Equiv.Perm (Fin r), (rounds (v ∘ σ) hr).length : ℕ) : ℝ) / (r.factorial : ℝ) ≤
      1 + Real.log r := by
  have hfact : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  rw [div_le_iff₀ hfact]
  have h1 : ((∑ σ : Equiv.Perm (Fin r), (rounds (v ∘ σ) hr).length : ℕ) : ℝ) ≤
      ((∑ σ : Equiv.Perm (Fin r), recordCount (v ∘ σ) : ℕ) : ℝ) := by
    have h0 : ∑ σ : Equiv.Perm (Fin r), (rounds (v ∘ σ) hr).length ≤
        ∑ σ : Equiv.Perm (Fin r), recordCount (v ∘ σ) :=
      Finset.sum_le_sum fun σ _ => rounds_length_le (v ∘ σ) hr
    exact_mod_cast h0
  have h2 := sum_recordCount_le v
  have h3 := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log r) hfact.le
  linarith

/-! ## The expected cost -/

theorem one_le_logb_two {n : ℕ} (hn : 2 ≤ n) : (1 : ℝ) ≤ Real.logb 2 n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have := Real.logb_le_logb_of_le (b := 2) (x := 2) (y := n) (by norm_num) (by norm_num) hn'
  rwa [Real.logb_self_eq_one (by norm_num)] at this

/-- The arithmetic: `H_r` rounds, each with `⌈log₂ (r + 1)⌉ + 1` decisions and one maximum finding,
give `O(√n log³ n · E)`, where a decision costs `E K √n log₂ n` and a maximum finding `κ √n`. -/
theorem mean_cost_le (v : Fin r → α) (hr : 0 < r) {n : ℕ} (hrn : r ≤ n) (hn : 2 ≤ n)
    {K κ E : ℝ} (hK : 0 ≤ K) (hκ : 0 ≤ κ) (hE : 1 ≤ E) :
    ((∑ σ : Equiv.Perm (Fin r), (rounds (v ∘ σ) hr).length : ℕ) : ℝ) / (r.factorial : ℝ) *
        (((ell r : ℝ) + 1) * (E * (K * √(n : ℝ) * Real.logb 2 n)) + κ * √(n : ℝ)) ≤
      (6 * K + 2 * κ) * √(n : ℝ) * Real.logb 2 n ^ 3 * E := by
  set L := Real.logb 2 n with hL
  set R := √(n : ℝ) with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hL1 : 1 ≤ L := one_le_logb_two hn
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hrn' : (r : ℝ) ≤ n := by exact_mod_cast hrn
  have hlogn : Real.log n ≤ L := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2' : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg (by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith)
    rw [hL, Real.logb, le_div_iff₀ hlog2]
    nlinarith
  have hmean : ((∑ σ : Equiv.Perm (Fin r), (rounds (v ∘ σ) hr).length : ℕ) : ℝ) /
      (r.factorial : ℝ) ≤ 2 * L := by
    have h1 := mean_rounds_le v hr
    have h2 := Real.log_le_log hr0 hrn'
    linarith
  have hell : (ell r : ℝ) + 1 ≤ 3 * L := by
    have := ell_le_two_logb hrn hn
    linarith
  have hmean0 : 0 ≤ ((∑ σ : Equiv.Perm (Fin r), (rounds (v ∘ σ) hr).length : ℕ) : ℝ) /
      (r.factorial : ℝ) := by positivity
  have hL0 : 0 ≤ L := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hunit : 1 ≤ L ^ 2 * E := by nlinarith [one_le_pow₀ hL1 (n := 2)]
  have hround : ((ell r : ℝ) + 1) * (E * (K * R * L)) + κ * R ≤ (3 * K + κ) * R * L ^ 2 * E := by
    have h1 : ((ell r : ℝ) + 1) * (E * (K * R * L)) ≤ (3 * L) * (E * (K * R * L)) :=
      mul_le_mul_of_nonneg_right hell (by positivity)
    have h2 : κ * R * 1 ≤ κ * R * (L ^ 2 * E) :=
      mul_le_mul_of_nonneg_left hunit (by positivity)
    nlinarith
  have hround0 : 0 ≤ ((ell r : ℝ) + 1) * (E * (K * R * L)) + κ * R := by positivity
  calc _ ≤ (2 * L) * (((ell r : ℝ) + 1) * (E * (K * R * L)) + κ * R) :=
        mul_le_mul_of_nonneg_right hmean hround0
    _ ≤ (2 * L) * ((3 * K + κ) * R * L ^ 2 * E) :=
        mul_le_mul_of_nonneg_left hround (by positivity)
    _ = (6 * K + 2 * κ) * R * L ^ 3 * E := by ring

/-- **The corollary, as an accounting.** From the named hypotheses, there are constants such that:
a strict decision on any set of rows costs at most `K₁ √n log₂ n` queries in the model; and the loop
over a uniform order, charging `E` such decisions for each decision and `κ₀ √n` for each maximum
finding, has mean total at most `K₂ √n (log₂ n)³ E`. Neither constant depends on the alphabet, so no
factor `log W` appears. The README takes `E = O(log log n)`. -/
theorem maximum_mean_cost {C κ₀ : ℝ} (hC : 0 ≤ C) (hκ₀ : 0 ≤ κ₀) (hLQ : LeeQueryAdv C)
    (hLG : LeeAdvGamma) (hDH : DurrHoyer κ₀) :
    ∃ K₁ K₂ : ℝ, 0 ≤ K₁ ∧ 0 ≤ K₂ ∧
      (∀ (r c k n : ℕ) [NeZero c] (S : Finset (Fin r)) (θ : Fin k), r ≤ n → c ≤ n → 2 ≤ n →
        (queryQ (tmInputs r c k) (someAbove S θ) : ℝ) ≤ K₁ * √(n : ℝ) * Real.logb 2 n) ∧
      ∀ (r n : ℕ) (hr : 0 < r) (v : Fin r → Fin n) (E : ℝ), r ≤ n → 2 ≤ n → 1 ≤ E →
        ((∑ σ : Equiv.Perm (Fin r), (rounds (v ∘ σ) hr).length : ℕ) : ℝ) / (r.factorial : ℝ) *
          (((ell r : ℝ) + 1) * (E * (K₁ * √(n : ℝ) * Real.logb 2 n)) + κ₀ * √(n : ℝ)) ≤
        K₂ * √(n : ℝ) * Real.logb 2 n ^ 3 * E := by
  obtain ⟨K₁, hK₁, h⟩ := someAbove_sqrt_log hC hκ₀ hLQ hLG hDH
  refine ⟨K₁, 6 * K₁ + 2 * κ₀, hK₁, by positivity, h, ?_⟩
  intro r n hr v E hrn hn hE
  exact mean_cost_le v hr hrn hn hK₁ hκ₀ hE

/-! ## Why leftmost -/

/-- The example from the README. -/
def tieMatrix : Fin 2 → Fin 2 → ℕ := ![![1, 1], ![2, 0]]

/-- `[[1, 1], [2, 0]]` is totally monotone, and column `1` is a maximum of row `0`, but the only
maximum of row `1` is in column `0`. So a window `[1, 1]` from a non-leftmost choice for row `0` would
hide the maximum of row `1`. The leftmost choice is column `0` in both rows. -/
theorem tieMatrix_facts :
    TotallyMonotone tieMatrix ∧ (∀ j, tieMatrix 0 j ≤ tieMatrix 0 1) ∧ tieMatrix 1 1 < tieMatrix 1 0 ∧
      IsLeftmostMax (tieMatrix 0) 0 ∧ IsLeftmostMax (tieMatrix 1) 0 := by
  unfold TotallyMonotone IsLeftmostMax
  decide

end Monge
