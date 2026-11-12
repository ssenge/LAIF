import KnownPattern.Basic

/-!
# Exposed candidates of a pattern with wildcards

A pattern with wildcards is a map `P : ℕ → Option α` (`none` is a wildcard). The text `x` agrees with a word `W` of
period `q` on the region `(lam, rho)`. A candidate start `t` is consistent if every fixed letter of `P` that falls into
the region equals `W` there.

* `same_class`: two consistent copies of the anchor run that both cover the identified middle `M` lie at a distance
  that `q` divides, where `q` is the least period of `M`.
* `left_fixed_unique`: two consistent candidates in one class modulo `q` cannot both put a fixed letter different from
  `W lam` on the break `lam`.
* `left_exposed_card`: at most `k + 1` consistent candidates of one class reach the break `lam`, where `k` is the
  number of wildcards.
* `occ_iff_outside`: an occurrence is a consistent candidate whose fixed letters outside the region match the text.
-/

namespace KnownPattern

variable {α : Type*}

/-- `P` occurs at `t` in `x`: every fixed letter of `P` in `[0, m)` matches the text. -/
def WOcc (x : ℕ → α) (P : ℕ → Option α) (m t : ℕ) : Prop :=
  ∀ i < m, ∀ c, P i = some c → x (t + i) = c

/-- `t` is consistent: every fixed letter of `P` that falls into the region `(lam, rho)` equals `W` there. -/
def Consistent (W : ℕ → α) (P : ℕ → Option α) (m lam rho t : ℕ) : Prop :=
  ∀ i < m, ∀ c, P i = some c → lam < t + i → t + i < rho → c = W (t + i)

theorem periodic_mul {W : ℕ → α} {q : ℕ} (hW : ∀ j, W (j + q) = W j) : ∀ n j, W (j + q * n) = W j := by
  intro n
  induction n with
  | zero => intro j; simp
  | succ n ih => intro j; rw [Nat.mul_succ, ← add_assoc, hW, ih]

/-- **Same class.** If the run `y` agrees with the middle `M` at the windows `δ ≤ δ'`, `q` is the least period of `M`,
and `2 (δ' - δ) ≤ L`, then `q` divides `δ' - δ`. -/
theorem same_class {y M : ℕ → α} {δ δ' L q : ℕ} (hle : δ ≤ δ') (h1 : ∀ j < L, y (δ + j) = M j)
    (h2 : ∀ j < L, y (δ' + j) = M j) (hq : HasPeriod M 0 L q) (hq0 : 0 < q)
    (hmin : ∀ p, 0 < p → p < q → ¬ HasPeriod M 0 L p) (hL : 2 * (δ' - δ) ≤ L) : q ∣ (δ' - δ) := by
  set d := δ' - δ with hd
  rcases Nat.eq_zero_or_pos d with h0 | h0
  · rw [h0]; exact dvd_zero q
  -- `d` is a period of `M`
  have hdM : HasPeriod M 0 L d := by
    intro j _ hj
    rw [← h1 j (by omega), ← h1 (j + d) (by omega)]
    have e : δ + (j + d) = δ' + j := by omega
    rw [e, h2 j (by omega), h1 j (by omega)]
  have hqd : q ≤ d := by
    by_contra h
    exact hmin d h0 (by omega) hdM
  have hq' : HasPeriod M 0 (0 + L) q := by simpa using hq
  have hd' : HasPeriod M 0 (0 + L) d := by simpa using hdM
  have hg := period_gcd (q + d) q d rfl hq' hd' (by omega)
  have hgpos : 0 < Nat.gcd q d := Nat.gcd_pos_of_pos_left d hq0
  have hgle : Nat.gcd q d ≤ q := Nat.gcd_le_left d hq0
  rcases hgle.lt_or_eq with hlt | heq
  · exact absurd (by simpa using hg) (hmin _ hgpos hlt)
  · exact Nat.gcd_eq_left_iff_dvd.1 heq

/-- **One fixed break per class.** Let `t < t'` be consistent candidates with `q ∣ t' - t`, both reaching `lam`, and
`lam + (t' - t) < rho`. Then the fixed letter of `P` at `lam - t` equals `W lam`. -/
theorem left_fixed_unique {W : ℕ → α} {P : ℕ → Option α} {m lam rho t t' q : ℕ} {c : α}
    (hW : ∀ j, W (j + q) = W j) (htt : t < t') (hdvd : q ∣ t' - t) (hlam : t' ≤ lam) (hm : lam < t + m)
    (hrho : lam + (t' - t) < rho) (hc' : Consistent W P m lam rho t') (hP : P (lam - t) = some c) :
    c = W lam := by
  have e := hc' (lam - t) (by omega) c hP (by omega) (by omega)
  obtain ⟨n, hn⟩ := hdvd
  have h1 : t' + (lam - t) = lam + q * n := by omega
  rw [e, h1, periodic_mul hW]

/-- **Left-exposed candidates.** Let `E` be a set of consistent candidates, pairwise in one class modulo `q`, each
reaching the break `lam` (so `t ≤ lam < t + m`), with `lam + (t' - t) < rho` for `t < t'` in `E`, and such that the
letter of `P` at `lam - t` is a wildcard or a fixed letter different from `W lam`. Then `E` has at most `k + 1`
elements, where `k` is the number of wildcards of `P` in `[0, m)`. -/
theorem left_exposed_card [DecidableEq α] {W : ℕ → α} {P : ℕ → Option α} {m lam rho q : ℕ} (E : Finset ℕ)
    (hW : ∀ j, W (j + q) = W j)
    (hcons : ∀ t ∈ E, Consistent W P m lam rho t) (hclass : ∀ t ∈ E, ∀ t' ∈ E, t < t' → q ∣ t' - t)
    (hreach : ∀ t ∈ E, t ≤ lam ∧ lam < t + m) (hrho : ∀ t ∈ E, ∀ t' ∈ E, t < t' → lam + (t' - t) < rho)
    (hbreak : ∀ t ∈ E, ∀ c, P (lam - t) = some c → c ≠ W lam) :
    E.card ≤ ((Finset.range m).filter (fun i => P i = none)).card + 1 := by
  classical
  set Ew := E.filter (fun t => P (lam - t) = none)
  set Ef := E.filter (fun t => P (lam - t) ≠ none)
  have hsplit : E.card = Ew.card + Ef.card := (Finset.card_filter_add_card_filter_not _).symm
  have hEf : Ef.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Ef, Finset.mem_filter] at ha hb
    by_contra hne
    rcases lt_or_gt_of_ne hne with hab | hab
    · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 ha.2
      have := left_fixed_unique hW hab (hclass a ha.1 b hb.1 hab) (hreach b hb.1).1 (hreach a ha.1).2
        (hrho a ha.1 b hb.1 hab) (hcons b hb.1) hc
      exact hbreak a ha.1 c hc this
    · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hb.2
      have := left_fixed_unique hW hab (hclass b hb.1 a ha.1 hab) (hreach a ha.1).1 (hreach b hb.1).2
        (hrho b hb.1 a ha.1 hab) (hcons a ha.1) hc
      exact hbreak b hb.1 c hc this
  have hEw : Ew.card ≤ ((Finset.range m).filter (fun i => P i = none)).card := by
    apply Finset.card_le_card_of_injOn (fun t => lam - t)
    · intro t ht
      simp only [Ew, Finset.coe_filter, Set.mem_ofPred_eq] at ht
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
      have := hreach t ht.1
      exact ⟨by omega, ht.2⟩
    · intro a ha b hb hab
      simp only [Ew, Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
      have := hreach a ha.1
      have := hreach b hb.1
      simp only at hab
      omega
  omega

/-- **Occurrence from the region.** If the text equals `W` on `(lam, rho)`, then `P` occurs at `t` exactly when `t`
is consistent and every fixed letter of `P` outside the region matches the text. -/
theorem occ_iff_outside {x W : ℕ → α} {P : ℕ → Option α} {m lam rho t : ℕ}
    (hx : ∀ j, lam < j → j < rho → x j = W j) :
    WOcc x P m t ↔ Consistent W P m lam rho t ∧
      ∀ i < m, ∀ c, P i = some c → ¬ (lam < t + i ∧ t + i < rho) → x (t + i) = c := by
  constructor
  · intro h
    refine ⟨fun i hi c hc h1 h2 => ?_, fun i hi c hc _ => h i hi c hc⟩
    rw [← hx _ h1 h2, h i hi c hc]
  · rintro ⟨hc, ho⟩ i hi c hP
    by_cases hr : lam < t + i ∧ t + i < rho
    · rw [hx _ hr.1 hr.2, hc i hi c hP hr.1 hr.2]
    · exact ho i hi c hP hr

end KnownPattern
