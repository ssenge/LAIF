import Covers.Vishkin
import Mathlib.Data.List.PeriodicityLemma
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# Periods: Lemma 2, Fine and Wilf, and the case analysis of Section 2

`List.HasPeriod` and its Fine and Wilf theorem `List.HasPeriod.gcd` are in Mathlib. `HasPeriod w 0` holds there, so
positivity of periods is explicit below.

## Remarks on the notes

* **Lemma 2.** The proof is the invariant of the revised notes: closure under `±p`, `min U < w - p`, `max U ≥ p`
  (`IsPhase.invariant`). The first version argued that `a + p` or `a - p` is an alignment, which fails for
  `p = 5, w = 7, a = 3`. The invariant uses that a column carries the character of an extreme survivor.
* **Blocks.** `|B| ≤ ⌈ℓ/2⌉` and six blocks of `w = ⌊ℓ/8⌋` (`blocks_le_six`). Four blocks do not suffice when `8 ∤ ℓ`
  (`not_four_blocks`).
* **`Q`.** "`Q` has smallest period `p`" needs no Fine and Wilf: a period `q < p` of the prefix `Q` extends to `P` on its
  own (`hasPeriod_of_prefix`).
* **Capped runs.** The run is extended forward up to `z + ℓ` and backward down to the smallest element of `B`. If `y` lies
  below `B`, which can happen when `|B| < p`, the run does not contain `y`; then there is no occurrence in `B` and the
  output is empty (`lemma4_case2_below`).
-/

namespace Strings

variable {α : Type*}

/-- Index form of `List.HasPeriod`. -/
theorem hasPeriod_iff {P : List α} {d : ℕ} :
    P.HasPeriod d ↔ ∀ i, i + d < P.length → P[i]? = P[i + d]? := by
  rw [List.hasPeriod_iff_getElem?]
  exact ⟨fun h i hi => h i (by omega), fun h i hi => h i (by omega)⟩

/-- `p` is the smallest positive period of `P`. -/
structure IsSmallestPeriod (P : List α) (p : ℕ) : Prop where
  pos : 0 < p
  per : P.HasPeriod p
  min : ∀ q, 0 < q → P.HasPeriod q → p ≤ q

/-- **Fine and Wilf**, from Mathlib, in the form the notes use: `p + q ≤ |P|`. -/
theorem fine_wilf {P : List α} {p q : ℕ} (hp : P.HasPeriod p) (hq : P.HasPeriod q)
    (h : p + q ≤ P.length) : P.HasPeriod (p.gcd q) :=
  hp.gcd hq (by omega)

/-- **Section 2.** Every period `d` with `p + d ≤ |P|` is a multiple of the smallest period `p`. -/
theorem smallest_dvd {P : List α} {p d : ℕ} (hp : IsSmallestPeriod P p) (hd : P.HasPeriod d)
    (h : p + d ≤ P.length) : p ∣ d := by
  have hg := fine_wilf hp.per hd h
  have hgpos : 0 < p.gcd d := Nat.gcd_pos_of_pos_left _ hp.pos
  have hle := hp.min _ hgpos hg
  have hdvd : p.gcd d ∣ p := Nat.gcd_dvd_left _ _
  have heq : p.gcd d = p := le_antisymm (Nat.le_of_dvd hp.pos hdvd) hle
  exact heq ▸ Nat.gcd_dvd_right p d

/-- **Section 2, the restart.** If `d < q` are periods with `d + q ≤ |P|`, then `gcd d q` is a period, positive and at
most half of `q`. -/
theorem gcd_restart {P : List α} {d q : ℕ} (hd : P.HasPeriod d) (hq : P.HasPeriod q) (hd0 : 0 < d) (hdq : d < q)
    (h : d + q ≤ P.length) :
    P.HasPeriod (d.gcd q) ∧ 0 < d.gcd q ∧ 2 * d.gcd q ≤ q := by
  refine ⟨fine_wilf hd hq h, Nat.gcd_pos_of_pos_left _ hd0, ?_⟩
  have hq0 : 0 < q := by omega
  obtain ⟨m, hm⟩ : d.gcd q ∣ q := Nat.gcd_dvd_right d q
  have hle : d.gcd q ≤ d := Nat.le_of_dvd hd0 (Nat.gcd_dvd_left d q)
  have hg0 : 0 < d.gcd q := Nat.gcd_pos_of_pos_left _ hd0
  have hm2 : 2 ≤ m := by
    by_contra hlt
    interval_cases m
    · omega
    · omega
  calc 2 * d.gcd q ≤ m * d.gcd q := Nat.mul_le_mul_right _ hm2
    _ = q := by rw [Nat.mul_comm]; exact hm.symm

/-! ## Lemma 2 -/

/-- Survivors exist as extremes. -/
theorem exists_isLow {P : List α} {w e : ℕ} {cols : List (ℕ × α)} (he : e < w) (hs : Survives P cols e) :
    ∃ a, IsLow P w cols a := by
  classical
  have hex : ∃ a, a < w ∧ Survives P cols a := ⟨e, he, hs⟩
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  exact ⟨_, h1, h2, fun x hx hxs => Nat.find_min' hex ⟨hx, hxs⟩⟩

theorem exists_isHigh {P : List α} {w e : ℕ} {cols : List (ℕ × α)} (he : e < w) (hs : Survives P cols e) :
    ∃ b, IsHigh P w cols b := by
  classical
  have hP : e < w ∧ Survives P cols e := ⟨he, hs⟩
  have hspec := Nat.findGreatest_spec (P := fun x => x < w ∧ Survives P cols x) (m := e) (n := w) he.le hP
  refine ⟨Nat.findGreatest (fun x => x < w ∧ Survives P cols x) w, hspec.1, hspec.2, fun x hx hxs => ?_⟩
  exact Nat.le_findGreatest hx.le ⟨hx, hxs⟩

theorem IsLow.unique {P : List α} {w a a' : ℕ} {cols : List (ℕ × α)} (h : IsLow P w cols a)
    (h' : IsLow P w cols a') : a = a' :=
  le_antisymm (h.2.2 _ h'.1 h'.2.1) (h'.2.2 _ h.1 h.2.1)

theorem IsHigh.unique {P : List α} {w a a' : ℕ} {cols : List (ℕ × α)} (h : IsHigh P w cols a)
    (h' : IsHigh P w cols a') : a = a' :=
  le_antisymm (h'.2.2 _ h.1 h.2.1) (h.2.2 _ h'.1 h'.2.1)

/-- The invariant behind Lemma 2. If `P` has period `p` with `0 < p < w`, then along a phase:

* alignments at distance `p` survive together, and
* the extremes satisfy `lo + p < w` and `p ≤ hi`, so each extreme has a partner at distance `p`.

The second part is what the notes' proof misses. It holds since a column carries the character of an extreme. -/
theorem IsPhase.invariant {P : List α} {w p : ℕ} {cols : List (ℕ × α)} (h : IsPhase P w cols) (hp0 : 0 < p)
    (hpw : p < w) (hper : P.HasPeriod p) :
    (∀ a, a + p < w → (Survives P cols a ↔ Survives P cols (a + p))) ∧
      ∃ lo hi, IsLow P w cols lo ∧ IsHigh P w cols hi ∧ lo + p < w ∧ p ≤ hi := by
  have hperi := hasPeriod_iff.1 hper
  induction h with
  | nil =>
    refine ⟨fun a _ => by simp [Survives], 0, w - 1, ?_, ?_, by omega, by omega⟩
    · exact ⟨by omega, by simp [Survives], fun e _ _ => Nat.zero_le e⟩
    · exact ⟨by omega, by simp [Survives], fun e he _ => by omega⟩
  | @step cols a b x c _ hlo hhi hab hbx hxa _ hc ih =>
    obtain ⟨htied, lo, hi, hlo', hhi', hlop, hhip⟩ := ih
    obtain rfl : a = lo := hlo.unique hlo'
    obtain rfl : b = hi := hhi.unique hhi'
    have htied' : ∀ e, e + p < w →
        (Survives P (cols ++ [(x, c)]) e ↔ Survives P (cols ++ [(x, c)]) (e + p)) := by
      intro e he
      simp only [survives_append]
      constructor
      · rintro ⟨hs, _, hch⟩
        have hs' := (htied e he).1 hs
        have h1 := hhi.2.2 _ he hs'
        have h2 := hlo.2.2 e (by omega) hs
        have hi2 := hperi (x - (e + p)) (by omega)
        have e1 : x - (e + p) + p = x - e := by omega
        rw [e1] at hi2
        exact ⟨hs', by omega, hi2.trans hch⟩
      · rintro ⟨hs', _, hch⟩
        have hs := (htied e he).2 hs'
        have h1 := hhi.2.2 _ he hs'
        have h2 := hlo.2.2 e (by omega) hs
        have hi2 := hperi (x - (e + p)) (by omega)
        have e1 : x - (e + p) + p = x - e := by omega
        rw [e1] at hi2
        exact ⟨hs, by omega, hi2.symm.trans hch⟩
    refine ⟨htied', ?_⟩
    rcases hc with hc | hc
    · -- the low extreme keeps its character, and so does its partner
      have hsa : Survives P (cols ++ [(x, c)]) a :=
        survives_append.2 ⟨hlo.2.1, by omega, hc⟩
      have hsa' := (htied' a hlop).1 hsa
      obtain ⟨hi', hhi''⟩ := exists_isHigh hlop hsa'
      refine ⟨a, hi', ⟨hlo.1, hsa, fun e he hse => hlo.2.2 e he (survives_append.1 hse).1⟩, hhi'', hlop, ?_⟩
      have := hhi''.2.2 _ hlop hsa'
      omega
    · -- the high extreme keeps its character, and so does its partner
      have hsb : Survives P (cols ++ [(x, c)]) b :=
        survives_append.2 ⟨hhi.2.1, hbx, hc⟩
      have hbw := hhi.1
      have hsb' : Survives P (cols ++ [(x, c)]) (b - p) := by
        have e1 : b - p + p = b := by omega
        refine (htied' (b - p) (by omega)).2 ?_
        rwa [e1]
      obtain ⟨lo', hlo''⟩ := exists_isLow (by omega : b - p < w) hsb'
      refine ⟨lo', b, hlo'', ⟨hhi.1, hsb, fun e he hse => hhi.2.2 e he (survives_append.1 hse).1⟩, ?_, hhip⟩
      have := hlo''.2.2 _ (by omega) hsb'
      omega

/-- If `P` has period `p` with `0 < p < w`, a phase always has two survivors at distance `p`. -/
theorem IsPhase.exists_pair {P : List α} {w p : ℕ} {cols : List (ℕ × α)} (h : IsPhase P w cols) (hp0 : 0 < p)
    (hpw : p < w) (hper : P.HasPeriod p) :
    ∃ a, a + p < w ∧ Survives P cols a ∧ Survives P cols (a + p) := by
  obtain ⟨htied, lo, _, hlo, _, hlop, _⟩ := h.invariant hp0 hpw hper
  exact ⟨lo, hlop, hlo.2.1, (htied lo hlop).1 hlo.2.1⟩

/-- **Lemma 2, first part, corrected proof.** If a phase on `[0, w)` ends with one survivor, then every positive period
of `P` is at least `w`. In particular the smallest period is. -/
theorem lemma2_le {P : List α} {w p s : ℕ} {cols : List (ℕ × α)} (h : IsPhase P w cols)
    (huniq : ∀ a, a < w → Survives P cols a → a = s) (hp0 : 0 < p) (hper : P.HasPeriod p) : w ≤ p := by
  by_contra hlt
  obtain ⟨a, ha, h1, h2⟩ := h.exists_pair hp0 (by omega) hper
  have e1 := huniq a (by omega) h1
  have e2 := huniq (a + p) ha h2
  omega

/-- **Lemma 2, second part.** If in addition `w` is a period, then it is the smallest period. -/
theorem lemma2_eq {P : List α} {w s : ℕ} {cols : List (ℕ × α)} (h : IsPhase P w cols) (hw : 0 < w)
    (huniq : ∀ a, a < w → Survives P cols a → a = s) (hper : P.HasPeriod w) : IsSmallestPeriod P w :=
  ⟨hw, hper, fun _ hq hq' => lemma2_le h huniq hq hq'⟩

/-- A column on the extremes of a phase on `Q` with `w` at most the smallest period exists: two extremes that agree on
the whole overlap would give a period smaller than `p`. So the sample of `Q` with `w = p` of "Prepare" never restarts. -/
theorem exists_column_of_lt_smallest {Q : List α} {p a b : ℕ} (hQ : IsSmallestPeriod Q p) (hab : a < b)
    (hbp : b < a + p) : ∃ x, b ≤ x ∧ x < a + Q.length ∧ Q[x - a]? ≠ Q[x - b]? := by
  by_contra hno
  have hagree : ∀ x, b ≤ x → x < a + Q.length → Q[x - a]? = Q[x - b]? := fun x h1 h2 => by
    by_contra hne
    exact hno ⟨x, h1, h2, hne⟩
  have := hQ.min _ (by omega) (period_of_agree hab hagree)
  omega

/-! ## Periods of prefixes -/

/-- Periods pass to prefixes. -/
theorem HasPeriod.take {P : List α} {d : ℕ} (m : ℕ) (h : P.HasPeriod d) : (P.take m).HasPeriod d := by
  rw [hasPeriod_iff] at h ⊢
  intro i hi
  rw [List.length_take] at hi
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_take_of_lt (by omega)]
  exact h i (by omega)

/-- A period `q` of a prefix of length at least `p + q` extends along a period `p` of `P`. -/
theorem hasPeriod_of_prefix {P : List α} {p q m : ℕ} (hp0 : 0 < p) (hp : P.HasPeriod p)
    (hq : (P.take m).HasPeriod q) (hm : p + q ≤ m) : P.HasPeriod q := by
  rw [hasPeriod_iff] at hp hq ⊢
  by_cases hlen : m ≤ P.length
  · have hq' : ∀ i, i + q < m → P[i]? = P[i + q]? := by
      intro i hi
      have := hq i (by rw [List.length_take]; omega)
      rwa [List.getElem?_take_of_lt (by omega), List.getElem?_take_of_lt (by omega)] at this
    -- induct down by `p`
    have key : ∀ N i, i ≤ N → i + q < P.length → P[i]? = P[i + q]? := by
      intro N
      induction N with
      | zero =>
        intro i hi hl
        by_cases hin : i + q < m
        · exact hq' i hin
        · omega
      | succ N ih =>
        intro i hi hl
        by_cases hin : i + q < m
        · exact hq' i hin
        · have hip : p ≤ i := by omega
          have h1 := hp (i - p) (by omega)
          have h2 := hp (i + q - p) (by omega)
          have e1 : i - p + p = i := by omega
          have e2 : i + q - p + p = i + q := by omega
          rw [e1] at h1
          rw [e2] at h2
          have h3 := ih (i - p) (by omega) (by omega)
          have e3 : i - p + q = i + q - p := by omega
          rw [e3] at h3
          rw [← h1, h3, h2]
    exact fun i hi => key i i le_rfl hi
  · have hq' : ∀ i, i + q < P.length → P[i]? = P[i + q]? := by
      intro i hi
      have := hq i (by rw [List.length_take]; omega)
      rwa [List.getElem?_take_of_lt (by omega), List.getElem?_take_of_lt (by omega)] at this
    exact hq'

/-- **"Prepare".** The prefix `Q` of length at least `2p` has the same smallest period `p`. -/
theorem smallest_period_take {P : List α} {p m : ℕ} (hP : IsSmallestPeriod P p) (hm : 2 * p ≤ m) :
    IsSmallestPeriod (P.take m) p := by
  refine ⟨hP.pos, HasPeriod.take m hP.per, fun q hq0 hq => ?_⟩
  by_contra hlt
  exact hlt (hP.min q hq0 (hasPeriod_of_prefix hP.pos hP.per hq (by omega)))

/-! ## The first case: blocks of `w` -/

/-- **"B is at most 4 blocks of w" is false in general.** With `ℓ = 23` we have `w = ⌊ℓ/8⌋ = 2`, and a range of `11 ≤ ℓ/2`
starts needs 6 blocks of size 2. -/
theorem not_four_blocks : ¬ ∀ ℓ m : ℕ, 16 ≤ ℓ → 2 * m ≤ ℓ → m ≤ 4 * (ℓ / 8) := by
  intro h
  have := h 23 11 (by norm_num) (by norm_num)
  norm_num at this

/-- **Corrected.** For `ℓ ≥ 16` and `|B| ≤ ⌈ℓ/2⌉`, six blocks of `w = ⌊ℓ/8⌋` suffice. -/
theorem blocks_le_six {ℓ m : ℕ} (hℓ : 16 ≤ ℓ) (hm : m ≤ (ℓ + 1) / 2) : m ≤ 6 * (ℓ / 8) := by
  omega

/-- If `8 ∣ ℓ` and `|B| ≤ ℓ/2`, the four blocks of the notes do suffice. -/
theorem blocks_le_four {ℓ m : ℕ} (h8 : 8 ∣ ℓ) (hm : 2 * m ≤ ℓ) : m ≤ 4 * (ℓ / 8) := by
  omega

/-- **Lemma 4, first case.** Let `B = [lo, lo + 6w)`, cut into six blocks of `w`, and let `P` have a sample with `w`. An
occurrence of `P` in `B` is one of the two extreme passing starts of its block. -/
theorem lemma4_case1 {P S : List α} {w s lo t : ℕ} {cols : List (ℕ × α)} (hs : IsSample P w s cols)
    (ht1 : lo ≤ t) (ht2 : t < lo + 6 * w) (hocc : OccursAt P S t) :
    ∃ j, j < 6 ∧ lo + j * w ≤ t ∧ t < lo + (j + 1) * w ∧
      ∀ t₁ t₂,
        IsLeast {y | (lo + j * w ≤ y ∧ y < lo + (j + 1) * w) ∧ Passes S y s cols} t₁ →
        IsGreatest {y | (lo + j * w ≤ y ∧ y < lo + (j + 1) * w) ∧ Passes S y s cols} t₂ →
        t = t₁ ∨ t = t₂ := by
  have hw : 0 < w := lt_of_le_of_lt (Nat.zero_le _) hs.s_lt
  have hdiv : (t - lo) / w < 6 := by
    rw [Nat.div_lt_iff_lt_mul hw]
    omega
  have h1 : (t - lo) / w * w ≤ t - lo := Nat.div_mul_le_self _ _
  have h2 : t - lo < ((t - lo) / w + 1) * w := by
    have := Nat.lt_mul_div_succ (t - lo) hw
    rwa [Nat.mul_comm] at this
  refine ⟨(t - lo) / w, hdiv, by omega, by omega, fun t₁ t₂ hl hg => ?_⟩
  refine two_extremes_block (B := {y | lo + (t - lo) / w * w ≤ y ∧ y < lo + ((t - lo) / w + 1) * w}) hs ?_ hl hg
    ⟨by omega, by omega⟩ hocc
  rintro a ⟨ha, -⟩ b ⟨-, hb⟩
  have e : ((t - lo) / w + 1) * w = (t - lo) / w * w + w := by ring
  omega

/-! ## The second case: a `p`-periodic run -/

/-- The text `S` has period `p` on the interval `[lo, hi)`. -/
def PeriodicOn (S : List α) (lo hi p : ℕ) : Prop :=
  ∀ i, lo ≤ i → i + p < hi → S[i]? = S[i + p]?

/-- `[lo, hi)` is a `p`-periodic run of `S` as found by capped first-mismatch searches: going backward the search stops
at a break or at `capLo`, and going forward at a break or at `capHi ≤ n`. Caps `0` and `n` give a maximal run. -/
structure IsRun (S : List α) (capLo capHi lo hi p : ℕ) : Prop where
  capHi_le : capHi ≤ S.length
  hi_le : hi ≤ capHi
  per : PeriodicOn S lo hi p
  left : lo = capLo ∨ S[lo - 1]? ≠ S[lo - 1 + p]?
  right : hi = capHi ∨ S[hi - p]? ≠ S[hi]?

/-- A period of `P` shows on any occurrence of `P`. -/
theorem OccursAt.periodicOn {P S : List α} {p t : ℕ} (hocc : OccursAt P S t) (hper : P.HasPeriod p) :
    PeriodicOn S t (t + P.length) p := by
  intro i h1 h2
  have hperi := hasPeriod_iff.1 hper (i - t) (by omega)
  have e1 := hocc.2 (i - t) (by omega)
  have e2 := hocc.2 (i - t + p) (by omega)
  have i1 : t + (i - t) = i := by omega
  have i2 : t + (i - t + p) = i + p := by omega
  rw [i1] at e1
  rw [i2] at e2
  rw [e1, e2, hperi]

/-- Going forward by multiples of `p` inside a periodic interval. -/
theorem PeriodicOn.add_mul {S : List α} {lo hi p : ℕ} (h : PeriodicOn S lo hi p) {i : ℕ} (hi' : lo ≤ i) (m : ℕ)
    (hl : i + m * p < hi) : S[i]? = S[i + m * p]? := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : i + (m + 1) * p = i + m * p + p := by ring
    rw [e] at hl ⊢
    rw [ih (by omega)]
    exact h _ (by omega) hl

/-- **Lemma 4, second case, first step.** Let `P` have period `p`, `8p ≤ ℓ`, and let `t ≤ z < t + ⌈ℓ/2⌉` with `t` an
occurrence of `P`. Then some `t + m p` lies in `(z - p, z]` and is an occurrence of the prefix `Q` of length `4p`. -/
theorem exists_Q_occurrence {P S : List α} {p t z : ℕ} (hp0 : 0 < p) (hper : P.HasPeriod p)
    (h8 : 8 * p ≤ P.length) (hocc : OccursAt P S t) (htz : t ≤ z) (hz : z < t + (P.length + 1) / 2) :
    ∃ m, t + m * p ≤ z ∧ z < t + m * p + p ∧ OccursAt (P.take (4 * p)) S (t + m * p) := by
  refine ⟨(z - t) / p, ?_, ?_, ?_⟩
  · have := Nat.div_mul_le_self (z - t) p
    omega
  · have := Nat.lt_mul_div_succ (z - t) hp0
    have e : p * ((z - t) / p + 1) = (z - t) / p * p + p := by ring
    omega
  · have hle : (z - t) / p * p ≤ z - t := Nat.div_mul_le_self _ _
    set m := (z - t) / p with hm
    have hlen : (P.take (4 * p)).length = 4 * p := by
      rw [List.length_take]; omega
    have hb := hocc.1
    refine ⟨by rw [hlen]; omega, fun i hi => ?_⟩
    rw [hlen] at hi
    rw [List.getElem?_take_of_lt hi]
    have hrun := hocc.periodicOn hper
    have h1 := hrun.add_mul (i := t + i) (by omega) m (by omega)
    have e2 : t + m * p + i = t + i + m * p := by ring
    rw [e2, ← h1]
    exact hocc.2 i (by omega)

/-- **Lemma 4, second case.** `Q` has at most one occurrence in a range of `p` starts: two would differ by a shift smaller
than `p`, which would be a period of `Q`. -/
theorem Q_occurrence_unique {Q S : List α} {p y y' : ℕ} (hQ : IsSmallestPeriod Q p) (h : OccursAt Q S y)
    (h' : OccursAt Q S y') (hle : y ≤ y') (hlt : y' < y + p) : y = y' := by
  by_contra hne
  have hpos : 0 < y' - y := by omega
  have hper : Q.HasPeriod (y' - y) := by
    rw [hasPeriod_iff]
    intro i hi
    have e1 := h.2 (i + (y' - y)) hi
    have e2 := h'.2 i (by omega)
    have idx : y + (i + (y' - y)) = y' + i := by omega
    rw [idx] at e1
    rw [← e1, e2]
  have := hQ.min _ hpos hper
  omega

/-- A character of a periodic string depends only on the residue of its position. -/
theorem HasPeriod.getElem?_add_mul {P : List α} {p i : ℕ} (hper : P.HasPeriod p) (m : ℕ)
    (hl : i + m * p < P.length) : P[i]? = P[i + m * p]? := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : i + (m + 1) * p = i + m * p + p := by ring
    rw [e] at hl ⊢
    rw [ih (by omega)]
    exact hasPeriod_iff.1 hper _ hl

/-- Positions of a periodic interval in the same residue class carry the same character. -/
theorem PeriodicOn.eq_of_modEq {S : List α} {lo hi p a b : ℕ} (h : PeriodicOn S lo hi p) (hla : lo ≤ a) (hlb : lo ≤ b)
    (ha : a < hi) (hb : b < hi) (hmod : a ≡ b [MOD p]) : S[a]? = S[b]? := by
  have key : ∀ {a b : ℕ}, lo ≤ a → b < hi → a ≤ b → a ≡ b [MOD p] → S[a]? = S[b]? := by
    intro a b hla hb hab hmod
    obtain ⟨m, hm⟩ := (Nat.modEq_iff_dvd' hab).1 hmod
    have e : b = a + m * p := by rw [Nat.mul_comm] at hm; omega
    rw [e]
    exact h.add_mul hla m (by omega)
  rcases le_total a b with hab | hab
  · exact key hla hb hab hmod
  · exact (key hlb ha hab hmod.symm).symm

/-- **Lemma 4, second case, soundness.** Each `t` in the output is an occurrence of `P`. Here `y` is an occurrence of a
prefix `Q` of `P` with `|Q| ≥ p`, the interval `[lo, hi)` is `p`-periodic and contains `[y, y + p)` and `[t, t + ℓ)`, and
`t ≡ y (mod p)`. -/
theorem output_sound {P Q S : List α} {p y lo hi t : ℕ} (hp0 : 0 < p) (hper : P.HasPeriod p) (hQP : Q <+: P)
    (hQlen : p ≤ Q.length) (hy : OccursAt Q S y) (hrun : PeriodicOn S lo hi p) (hhi : hi ≤ S.length) (hylo : lo ≤ y)
    (hyhi : y + p ≤ hi) (htlo : lo ≤ t) (hthi : t + P.length ≤ hi) (hmod : t ≡ y [MOD p]) : OccursAt P S t := by
  have hQi : ∀ i, i < p → S[y + i]? = P[i]? := fun i hi => by
    have hlt : i < Q.length := by omega
    rw [hy.2 i hlt, List.prefix_iff_getElem?.1 hQP i hlt]
    exact List.getElem?_eq_getElem hlt
  refine ⟨by omega, fun i hi => ?_⟩
  have hlt : i % p < p := Nat.mod_lt _ hp0
  have hm : t + i ≡ y + i % p [MOD p] := hmod.add (Nat.mod_modEq i p).symm
  rw [hrun.eq_of_modEq (by omega) (by omega) (by omega) (by omega) hm, hQi _ hlt]
  exact hper.getElem?_mod p i P hi

/-- **Lemma 4, second case, completeness.** An occurrence `t` of `P` with `t ≤ y` and `y + p ≤ t + ℓ`, within the caps,
lies in the run around `y`. -/
theorem output_complete {P S : List α} {p y capLo capHi lo hi t : ℕ} (hper : P.HasPeriod p)
    (hrun : IsRun S capLo capHi lo hi p) (hocc : OccursAt P S t) (hty : t ≤ y) (hyP : y + p ≤ t + P.length)
    (hylo : lo ≤ y) (hyhi : y + p ≤ hi) (hcapLo : capLo ≤ t) (hcapHi : t + P.length ≤ capHi) :
    lo ≤ t ∧ t + P.length ≤ hi := by
  have hO := hocc.periodicOn hper
  constructor
  · by_contra hlt
    have hbad := hrun.left.resolve_left (by omega)
    exact hbad (hO _ (by omega) (by omega))
  · by_contra hlt
    have hbad := hrun.right.resolve_left (by omega)
    have e : hi - p + p = hi := by omega
    have := hO (hi - p) (by omega) (by omega)
    rw [e] at this
    exact hbad this

/-- **Lemma 4, second case.** Let `P` have period `p` with `8p ≤ ℓ`, let `Q` be its prefix of length `4p`, with smallest
period `p`, and let `y ∈ (z - p, z]` be an occurrence of `Q`. Let `B = [a, z]`, and let `[lo, hi)` be the run around `y`,
capped at `a` and at any forward cap between `min(z + ℓ, n)` and `n`. Then for `t ∈ B` with `z < t + ⌈ℓ/2⌉`, `t` is an occurrence of `P` iff it is in the
output `{t : t ≡ y (mod p), t ≥ lo, t + ℓ ≤ hi}`. The case `y < a` is `lemma4_case2_below`. -/
theorem lemma4_case2 {P S : List α} {p y a capHi lo hi z t : ℕ} (hper : P.HasPeriod p) (h8 : 8 * p ≤ P.length)
    (hQ : IsSmallestPeriod (P.take (4 * p)) p) (hy : OccursAt (P.take (4 * p)) S y) (hyz : y ≤ z) (hzy : z < y + p)
    (hcap : min (z + P.length) S.length ≤ capHi) (hrun : IsRun S a capHi lo hi p) (hylo : lo ≤ y) (hyhi : y + p ≤ hi)
    (hat : a ≤ t) (htz : t ≤ z) (hz : z < t + (P.length + 1) / 2) :
    OccursAt P S t ↔ t ≡ y [MOD p] ∧ lo ≤ t ∧ t + P.length ≤ hi := by
  have hp0 := hQ.pos
  constructor
  · intro hocc
    obtain ⟨m, h1, h2, h3⟩ := exists_Q_occurrence hp0 hper h8 hocc htz hz
    have heq : y = t + m * p := by
      rcases le_total y (t + m * p) with hle | hle
      · exact Q_occurrence_unique hQ hy h3 hle (by omega)
      · exact (Q_occurrence_unique hQ h3 hy hle (by omega)).symm
    have hmod : t ≡ y [MOD p] := by
      rw [heq]
      simp [Nat.ModEq]
    have hb := hocc.1
    exact ⟨hmod, output_complete hper hrun hocc (by omega) (by omega) hylo hyhi hat (by omega)⟩
  · rintro ⟨hmod, hlo, hhi⟩
    have hcap := hrun.hi_le.trans hrun.capHi_le
    refine output_sound hp0 hper (List.take_prefix _ _) ?_ hy hrun.per hcap hylo hyhi hlo hhi hmod
    rw [List.length_take]
    omega

/-- **Lemma 4, second case, `y` below `B`.** If `y < a ≤ t ≤ z < y + p`, then `t` is not an occurrence of `P` and is not in
the residue class of `y`, so the output has no such `t`. -/
theorem lemma4_case2_below {P S : List α} {p y a z t : ℕ} (hper : P.HasPeriod p) (h8 : 8 * p ≤ P.length)
    (hQ : IsSmallestPeriod (P.take (4 * p)) p) (hy : OccursAt (P.take (4 * p)) S y) (hzy : z < y + p)
    (hya : y < a) (hat : a ≤ t) (htz : t ≤ z) (hz : z < t + (P.length + 1) / 2) :
    ¬ OccursAt P S t ∧ ¬ t ≡ y [MOD p] := by
  have hp0 := hQ.pos
  constructor
  · intro hocc
    obtain ⟨m, h1, h2, h3⟩ := exists_Q_occurrence hp0 hper h8 hocc htz hz
    have heq : y = t + m * p := by
      rcases le_total y (t + m * p) with hle | hle
      · exact Q_occurrence_unique hQ hy h3 hle (by omega)
      · exact (Q_occurrence_unique hQ h3 hy hle (by omega)).symm
    omega
  · intro hmod
    obtain ⟨m, hm⟩ := (Nat.modEq_iff_dvd' (by omega : y ≤ t)).1 hmod.symm
    rcases m with _ | m
    · simp at hm
      omega
    · have e : p * (m + 1) = p * m + p := by ring
      have := Nat.zero_le (p * m)
      omega

/-- **Lemma 4, second case, no output.** If `Q` has no occurrence in `(z - p, z]`, then `P` has no occurrence `t` with
`t ≤ z < t + ⌈ℓ/2⌉`. -/
theorem no_occurrence_of_no_Q {P S : List α} {p z t : ℕ} (hp0 : 0 < p) (hper : P.HasPeriod p) (h8 : 8 * p ≤ P.length)
    (hno : ∀ y, y ≤ z → z < y + p → ¬ OccursAt (P.take (4 * p)) S y) (htz : t ≤ z)
    (hz : z < t + (P.length + 1) / 2) : ¬ OccursAt P S t := fun hocc => by
  obtain ⟨m, h1, h2, h3⟩ := exists_Q_occurrence hp0 hper h8 hocc htz hz
  exact hno _ h1 h2 h3

end Strings
