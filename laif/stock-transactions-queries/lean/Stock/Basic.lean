import Mathlib.Tactic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Stock trading with at most `t` transactions

* `dpStep`: one price of the fee programme, `cash ← max cash (hold + q - λ)`, `hold ← max hold (cash - q)`.
* `zStep`, `zVal`: the threshold zigzag and its value.
* `zigzag_eq_dp` (Lemma 1): for a fee `λ ≥ 0`, the zigzag value equals the final `cash` of the fee programme.
* `slope_antitone`, `le_slope_mul`, `slope_mul_le`: slopes of a concave sequence.
* `recover` (Lemma 4): if `K ≤ t` maximizes `f k - k (a + ε)` and either `a = 0` or some `K' > t` maximizes
  `f k - k (a - 1 + ε)`, then `f t = f K + (t - K) a`.
* `sum_sqrt_le`: `∑ √ℓ_i ≤ √(m ∑ ℓ_i)` for `m` phases, the cost of one run.
-/

namespace Stock

/-- One price `q` of the fee programme with fee `lam`; the pair is `(cash, hold)`. -/
def dpStep (lam : ℚ) (s : ℚ × ℚ) (q : ℚ) : ℚ × ℚ :=
  (max s.1 (s.2 + q - lam), max s.2 (s.1 - q))

/-- State of the zigzag: total `C` of completed legs, current `lo` and `hi`, the direction, the number of legs. -/
structure Z where
  C : ℚ
  lo : ℚ
  hi : ℚ
  up : Bool
  legs : ℕ

/-- One price `q` of the threshold zigzag with threshold `lam`. -/
def zStep (lam : ℚ) (s : Z) (q : ℚ) : Z :=
  if s.up then
    if lam ≤ s.hi - q then ⟨s.C + (s.hi - s.lo - lam), q, s.hi, false, s.legs + 1⟩
    else ⟨s.C, s.lo, max s.hi q, true, s.legs⟩
  else
    if lam ≤ q - s.lo then ⟨s.C, s.lo, q, true, s.legs⟩
    else ⟨s.C, min s.lo q, s.hi, false, s.legs⟩

/-- Value of the zigzag: an open up state adds its leg. -/
def zVal (lam : ℚ) (s : Z) : ℚ := if s.up then s.C + (s.hi - s.lo - lam) else s.C

/-- The invariant linking the zigzag to the fee programme. -/
def Inv (lam : ℚ) (s : Z) (d : ℚ × ℚ) : Prop := d.1 = zVal lam s ∧ d.2 = s.C - s.lo

theorem inv_step (lam : ℚ) (hl : 0 ≤ lam) (s : Z) (d : ℚ × ℚ) (q : ℚ) (h : Inv lam s d) :
    Inv lam (zStep lam s q) (dpStep lam d q) := by
  rcases s with ⟨C, lo, hi, up, legs⟩
  rcases d with ⟨c, k⟩
  obtain ⟨h1, h2⟩ := h
  simp only [zVal] at h1 h2
  cases up
  · simp only [Bool.false_eq_true, ite_false] at h1
    subst h1 h2
    by_cases hq : lam ≤ q - lo
    · simp only [zStep, Bool.false_eq_true, ite_false, hq, ite_true, Inv, zVal, dpStep]
      refine ⟨?_, ?_⟩
      · rw [max_eq_right (by linarith)]; ring
      · rw [max_eq_left (by linarith)]
    · simp only [zStep, Bool.false_eq_true, ite_false, hq, Inv, zVal, dpStep]
      push_neg at hq
      refine ⟨?_, ?_⟩
      · rw [max_eq_left (by linarith)]
      · rcases le_total lo q with h | h
        · rw [min_eq_left h, max_eq_left (by linarith)]
        · rw [min_eq_right h, max_eq_right (by linarith)]
  · simp only [ite_true] at h1
    subst h1 h2
    by_cases hq : lam ≤ hi - q
    · simp only [zStep, ite_true, hq, Inv, zVal, dpStep, Bool.false_eq_true, ite_false]
      refine ⟨?_, ?_⟩
      · rw [max_eq_left (by linarith)]
      · rw [max_eq_right (by linarith)]
    · simp only [zStep, ite_true, hq, ite_false, Inv, zVal, dpStep]
      push_neg at hq
      refine ⟨?_, ?_⟩
      · rcases le_total hi q with h | h
        · rw [max_eq_right h, max_eq_right (by linarith)]; ring
        · rw [max_eq_left h, max_eq_left (by linarith)]
      · rw [max_eq_left (by linarith)]

theorem inv_foldl (lam : ℚ) (hl : 0 ≤ lam) (ps : List ℚ) :
    ∀ s d, Inv lam s d → Inv lam (ps.foldl (zStep lam) s) (ps.foldl (dpStep lam) d) := by
  induction ps with
  | nil => intro s d h; exact h
  | cons q ps ih => intro s d h; exact ih _ _ (inv_step lam hl s d q h)

/-- **Lemma 1.** For prices `p :: ps` and a fee `lam ≥ 0`, the fee programme started after the first price,
with `cash = 0` and `hold = -p`, ends with `cash` equal to the value of the zigzag started in the down state
with `lo = p`. -/
theorem zigzag_eq_dp (lam : ℚ) (hl : 0 ≤ lam) (p : ℚ) (ps : List ℚ) :
    (ps.foldl (dpStep lam) (0, -p)).1 = zVal lam (ps.foldl (zStep lam) ⟨0, p, p, false, 0⟩) :=
  (inv_foldl lam hl ps _ _ ⟨by simp [zVal], by simp⟩).1

/-- `f` is concave on `0, …, n`. -/
def ConcaveUpTo (f : ℕ → ℤ) (n : ℕ) : Prop := ∀ k, k + 2 ≤ n → f (k + 2) - f (k + 1) ≤ f (k + 1) - f k

theorem slope_antitone {f : ℕ → ℤ} {n : ℕ} (hc : ConcaveUpTo f n) {j k : ℕ} (hjk : j ≤ k) (hk : k + 1 ≤ n) :
    f (k + 1) - f k ≤ f (j + 1) - f j := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hjk ih => exact le_trans (hc k (by omega)) (ih (by omega))

/-- The first slope bounds the average slope to the right. -/
theorem slope_mul_le {f : ℕ → ℤ} {n : ℕ} (hc : ConcaveUpTo f n) {t K : ℕ} (htK : t ≤ K) (hK : K ≤ n)
    (ht : t + 1 ≤ n) : f K - f t ≤ ((K : ℤ) - t) * (f (t + 1) - f t) := by
  induction K, htK using Nat.le_induction with
  | base => simp
  | succ K htK ih =>
    have h1 := ih (by omega)
    have h2 := slope_antitone hc htK hK
    push_cast
    nlinarith

/-- The slope after `t` bounds the average slope to the left. -/
theorem le_slope_mul {f : ℕ → ℤ} {n : ℕ} (hc : ConcaveUpTo f n) {K t : ℕ} (hKt : K ≤ t) (ht : t + 1 ≤ n) :
    ((t : ℤ) - K) * (f (t + 1) - f t) ≤ f t - f K := by
  induction t, hKt using Nat.le_induction with
  | base => simp
  | succ t hKt ih =>
    have h1 := ih (by omega)
    have h2 := slope_antitone hc (Nat.le_succ t) ht
    push_cast
    nlinarith

/-- **Lemma 4.** Let `f` be nondecreasing and concave on `0, …, n`, `t ≤ n`, `0 < ε` with `n ε < 1`. If `K ≤ t`
maximizes `f k - k (a + ε)` over `k ≤ n`, and either `a = 0` or some `K'` with `t < K' ≤ n` maximizes
`f k - k (a - 1 + ε)`, then `f t = f K + (t - K) a`. -/
theorem recover (f : ℕ → ℤ) (n t K a : ℕ) (ε : ℚ) (hε : 0 < ε) (hεn : (n : ℚ) * ε < 1)
    (hc : ConcaveUpTo f n) (hmono : ∀ k, k < n → f k ≤ f (k + 1)) (ht : t ≤ n) (hK : K ≤ t)
    (hmax : ∀ k ≤ n, (f k : ℚ) - k * (a + ε) ≤ f K - K * (a + ε))
    (hlow : a = 0 ∨ ∃ K', t < K' ∧ K' ≤ n ∧
      ∀ k ≤ n, (f k : ℚ) - k * ((a : ℚ) - 1 + ε) ≤ f K' - K' * ((a : ℚ) - 1 + ε)) :
    f t = f K + ((t : ℤ) - K) * a := by
  -- upper bound: f t - f K ≤ (t - K) a
  have hup : f t - f K - ((t : ℤ) - K) * a ≤ 0 := by
    have h := hmax t ht
    have htK : ((t : ℚ) - K) * ε < 1 := by
      have : ((t : ℚ) - K) ≤ n := by
        have : (t : ℚ) ≤ n := by exact_mod_cast ht
        have : (0 : ℚ) ≤ K := by positivity
        linarith
      nlinarith
    have hq : ((f t - f K - ((t : ℤ) - K) * a : ℤ) : ℚ) < 1 := by push_cast; nlinarith
    have : f t - f K - ((t : ℤ) - K) * a < 1 := by exact_mod_cast hq
    omega
  -- lower bound
  have hlo : ((t : ℤ) - K) * a ≤ f t - f K := by
    rcases hlow with h0 | ⟨K', htK', hK'n, hmax'⟩
    · subst h0
      simp only [Nat.cast_zero, mul_zero]
      have : ∀ j, K + j ≤ t → f K ≤ f (K + j) := by
        intro j
        induction j with
        | zero => intro; simp
        | succ j ih => intro hj; exact le_trans (ih (by omega)) (hmono _ (by omega))
      have := this (t - K) (by omega)
      rw [Nat.add_sub_cancel' hK] at this
      linarith
    · have h1 := hmax' t ht
      have h2 := slope_mul_le hc htK'.le hK'n (by omega)
      have hd : (a : ℤ) ≤ f (t + 1) - f t := by
        have hpos : (0 : ℚ) < (K' : ℚ) - t := by
          have : (t : ℚ) < K' := by exact_mod_cast htK'
          linarith
        have h2q : ((f K' : ℚ) - f t) ≤ ((K' : ℚ) - t) * ((f (t + 1) : ℚ) - f t) := by
          exact_mod_cast h2
        have h3 : ((a : ℚ) - 1 + ε) * ((K' : ℚ) - t) ≤ ((f (t + 1) : ℚ) - f t) * ((K' : ℚ) - t) := by
          nlinarith
        have h4 : (a : ℚ) - 1 + ε ≤ (f (t + 1) : ℚ) - f t := le_of_mul_le_mul_right h3 hpos
        have h5 : ((a : ℤ) - 1 : ℚ) < ((f (t + 1) - f t : ℤ) : ℚ) := by push_cast; linarith
        have : (a : ℤ) - 1 < f (t + 1) - f t := by exact_mod_cast h5
        omega
      have h6 := le_slope_mul hc hK (by omega)
      have h7 : (0 : ℤ) ≤ (t : ℤ) - K := by omega
      nlinarith
  linarith

/-- **Cost of a run.** For `m` phases of lengths `ℓ i`, `∑ √(ℓ i) ≤ √(m ∑ ℓ i)`. -/
theorem sum_sqrt_le {ι : Type*} (I : Finset ι) (l : ι → ℝ) (hl : ∀ i, 0 ≤ l i) :
    ∑ i ∈ I, Real.sqrt (l i) ≤ Real.sqrt (I.card * ∑ i ∈ I, l i) := by
  apply Real.le_sqrt_of_sq_le
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq I (fun _ => (1 : ℝ)) (fun i => Real.sqrt (l i))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  calc (∑ i ∈ I, Real.sqrt (l i)) ^ 2 ≤ I.card * ∑ i ∈ I, Real.sqrt (l i) ^ 2 := hcs
    _ = I.card * ∑ i ∈ I, l i := by
      congr 1; exact Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (hl i))

end Stock
