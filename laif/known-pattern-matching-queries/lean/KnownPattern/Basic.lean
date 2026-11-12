import Mathlib

/-!
# Periods of pattern windows and breaks of the text

Strings are maps `ℕ → α`. `HasPeriod f a b q` says that `f k = f (k + q)` whenever `a ≤ k` and `k + q < b`.

* `period_gcd`: periods `p` and `q` of an interval of length `L ≥ p + q` give the period `gcd p q`
  (a weak form of the periodicity lemma, proved here).
* `windows_period` (Lemma 1): if two windows `y[δ, δ + L)` and `y[δ', δ' + L)` are equal, `q` is the least period of
  the first, and `q + (δ' - δ) ≤ L`, then `q` divides `δ' - δ` and `y` has period `q` on `[δ, δ' + L)`.
* `left_break`, `run_copied` (Lemma 2, parts 1 and 2): an occurrence of `y` at `i` copies the breaks and the periodic
  runs of `y` to the text.
* `periodic_occ` (Lemma 2, part 3): if `y` and the text on `[i, i + m)` have period `q`, and they agree on a window of
  length at least `q`, then `y` occurs at `i`.
-/

namespace KnownPattern

variable {α : Type*}

/-- `f` has period `q` on `[a, b)`. -/
def HasPeriod (f : ℕ → α) (a b q : ℕ) : Prop :=
  ∀ k, a ≤ k → k + q < b → f k = f (k + q)

theorem HasPeriod.mono {f : ℕ → α} {a b a' b' q : ℕ} (h : HasPeriod f a b q) (ha : a ≤ a') (hb : b' ≤ b) :
    HasPeriod f a' b' q :=
  fun k h1 h2 => h k (le_trans ha h1) (lt_of_lt_of_le h2 hb)

/-- One step of the periodicity lemma: periods `p ≤ q` with `p + q ≤ L` give the period `q - p`. -/
theorem period_sub {f : ℕ → α} {a L p q : ℕ} (hp : HasPeriod f a (a + L) p) (hq : HasPeriod f a (a + L) q)
    (hpq : p ≤ q) (hL : p + q ≤ L) : HasPeriod f a (a + L) (q - p) := by
  intro k h1 h2
  by_cases hk : k + q < a + L
  · have e1 := hq k h1 hk
    have e2 := hp (k + (q - p)) (by omega) (by omega)
    have h3 : k + (q - p) + p = k + q := by omega
    rw [h3] at e2
    rw [e1, e2]
  · have e1 := hp (k - p) (by omega) (by omega)
    have e2 := hq (k - p) (by omega) (by omega)
    have h3 : k - p + p = k := by omega
    have h4 : k - p + q = k + (q - p) := by omega
    rw [h3] at e1
    rw [h4] at e2
    rw [← e1, e2]

/-- **Periodicity lemma, weak form.** Periods `p` and `q` of an interval of length `L ≥ p + q` give the period
`gcd p q`. -/
theorem period_gcd {f : ℕ → α} {a L : ℕ} :
    ∀ n p q, p + q = n → HasPeriod f a (a + L) p → HasPeriod f a (a + L) q → p + q ≤ L →
      HasPeriod f a (a + L) (Nat.gcd p q) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p q hn hp hq hL
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · subst h0; simpa using hq
    rcases Nat.eq_zero_or_pos q with h1 | h1
    · subst h1; simpa using hp
    rcases le_total p q with hpq | hqp
    · have hs := period_sub hp hq hpq hL
      have := ih q (by omega) p (q - p) (by omega) hp hs (by omega)
      rwa [Nat.gcd_sub_self_right hpq] at this
    · have hs := period_sub hq hp hqp (by omega)
      have := ih p (by omega) q (p - q) (by omega) hq hs (by omega)
      rwa [Nat.gcd_sub_self_right hqp, Nat.gcd_comm] at this

/-- **Lemma 1.** Equal windows at `δ ≤ δ'`, with `q` the least period of the first and `q + (δ' - δ) ≤ L`: then `q`
divides `δ' - δ`, and `y` has period `q` on the union `[δ, δ' + L)`. -/
theorem windows_period {y : ℕ → α} {δ δ' L q : ℕ} (hle : δ ≤ δ') (hw : ∀ k < L, y (δ + k) = y (δ' + k))
    (hq : HasPeriod y δ (δ + L) q) (hq0 : 0 < q) (hmin : ∀ p, 0 < p → p < q → ¬ HasPeriod y δ (δ + L) p)
    (hL : q + (δ' - δ) ≤ L) : q ∣ (δ' - δ) ∧ HasPeriod y δ (δ' + L) q := by
  set d := δ' - δ with hd
  have hdp : HasPeriod y δ (δ' + L) d := by
    intro k h1 h2
    have e := hw (k - δ) (by omega)
    have h3 : δ + (k - δ) = k := by omega
    have h4 : δ' + (k - δ) = k + d := by omega
    rwa [h3, h4] at e
  have hdM : HasPeriod y δ (δ + L) d := hdp.mono le_rfl (by omega)
  have hdvd : q ∣ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [h0]; exact dvd_zero q
    have hg := period_gcd (q + d) q d rfl hq hdM hL
    have hgpos : 0 < Nat.gcd q d := Nat.gcd_pos_of_pos_left d hq0
    have hgle : Nat.gcd q d ≤ q := Nat.gcd_le_left d hq0
    rcases hgle.lt_or_eq with hlt | heq
    · exact absurd hg (hmin _ hgpos hlt)
    · exact Nat.gcd_eq_left_iff_dvd.1 heq
  refine ⟨hdvd, fun k h1 h2 => ?_⟩
  by_cases hk : k + q < δ + L
  · exact hq k h1 hk
  · have e1 := hdp (k - d) (by omega) (by omega)
    have e2 := hq (k - d) (by omega) (by omega)
    have e3 := hdp (k - d + q) (by omega) (by omega)
    have h3 : k - d + d = k := by omega
    have h4 : k - d + q + d = k + q := by omega
    rw [h3] at e1
    rw [h4] at e3
    rw [← e1, e2, e3]

/-- **Lemma 2, part 1.** An occurrence of `y` at `i` copies a break `y l ≠ y (l + q)` to the text. -/
theorem left_break {x y : ℕ → α} {i m l q : ℕ} (hocc : ∀ k < m, x (i + k) = y k) (hb : y l ≠ y (l + q))
    (hm : l + q < m) : x (i + l) ≠ x (i + l + q) := by
  rw [hocc l (by omega), add_assoc, hocc (l + q) hm]
  exact hb

/-- **Lemma 2, runs.** An occurrence of `y` at `i` copies a run of period `q` on `[l, r)` to `[i + l, i + r)`. -/
theorem run_copied {x y : ℕ → α} {i m l r q : ℕ} (hocc : ∀ k < m, x (i + k) = y k) (hy : HasPeriod y l r q)
    (hr : r ≤ m) : HasPeriod x (i + l) (i + r) q := by
  intro k h1 h2
  have e1 := hocc (k - i) (by omega)
  have e2 := hocc (k - i + q) (by omega)
  have h3 : i + (k - i) = k := by omega
  have h4 : i + (k - i + q) = k + q := by omega
  rw [h3] at e1
  rw [h4] at e2
  rw [e1, e2]
  exact hy (k - i) (by omega) (by omega)

/-- **Lemma 2, part 3.** If `y` has period `q` on `[0, m)`, the text has period `q` on `[i, i + m)`, and they agree on
the window `[δ, δ + L)` with `L ≥ q`, then `y` occurs at `i`. -/
theorem periodic_occ {x y : ℕ → α} {i δ L m q : ℕ} (hq0 : 0 < q) (hx : HasPeriod x i (i + m) q)
    (hy : HasPeriod y 0 m q) (hw : ∀ k < L, x (i + (δ + k)) = y (δ + k)) (hqL : q ≤ L) (hδ : δ + L ≤ m) :
    ∀ k < m, x (i + k) = y k := by
  -- below the end of the window, step up by q
  have below : ∀ n k, δ + L - k = n → k < δ + L → x (i + k) = y k := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro k hn hk
      by_cases h : δ ≤ k
      · have := hw (k - δ) (by omega)
        have h3 : δ + (k - δ) = k := by omega
        rwa [h3] at this
      · have e := ih (δ + L - (k + q)) (by omega) (k + q) rfl (by omega)
        have ex := hx (i + k) (by omega) (by omega)
        have ey := hy k (by omega) (by omega)
        rw [ex, ey, add_assoc, e]
  -- above the window, step down by q
  have above : ∀ k, k < m → x (i + k) = y k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      by_cases h : k < δ + L
      · exact below _ k rfl h
      · have e := ih (k - q) (by omega) (by omega)
        have ex := hx (i + (k - q)) (by omega) (by omega)
        have ey := hy (k - q) (by omega) (by omega)
        have h3 : i + (k - q) + q = i + k := by omega
        have h4 : k - q + q = k := by omega
        rw [h3] at ex
        rw [h4] at ey
        rw [← ex, ← ey, e]
  exact above

end KnownPattern
