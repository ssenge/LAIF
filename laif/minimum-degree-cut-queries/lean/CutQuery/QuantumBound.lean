import CutQuery.QPath
import CutQuery.QPoly

/-!
# The quantum lower bound for minimum degree with cut queries

* `exists_re_poly`: the real part of a complex polynomial on real points;
* `exists_and_approx`: from a correct algorithm, a real polynomial of degree at most `3 (12 T + 6)` that
  approximates `AND` on the cube;
* `params`: the choice of `m`, `L`, `W₀` for `W = 2^(24 n² (log₂ n + 1))`;
* `quantum_bound`: the bound `c √n ≤ T + 1`.
-/

open Finset

namespace CutQuery

section RealPart

variable {V : Type*} [Fintype V]

/-- The real part of a complex polynomial, on real points, is a real polynomial of no larger degree. -/
theorem exists_re_poly (Q : MvPolynomial V ℂ) :
    ∃ R : MvPolynomial V ℝ, R.totalDegree ≤ Q.totalDegree ∧
      ∀ x : V → ℝ, MvPolynomial.eval x R = (MvPolynomial.eval (fun v => (x v : ℂ)) Q).re := by
  classical
  refine ⟨∑ d ∈ Q.support, MvPolynomial.monomial d (Q.coeff d).re, ?_, ?_⟩
  · refine MvPolynomial.totalDegree_finsetSum_le fun d hd => ?_
    exact (MvPolynomial.totalDegree_monomial_le _ _).trans (MvPolynomial.le_totalDegree hd)
  · intro x
    rw [map_sum, MvPolynomial.eval_eq', Complex.re_sum]
    refine sum_congr rfl fun d _ => ?_
    rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (by simp)]
    have h : (∏ i, ((x i : ℝ) : ℂ) ^ d i) = ((∏ i, x i ^ d i : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [h, Complex.re_mul_ofReal]

end RealPart

section Smooth

/-- The amplification polynomial. -/
def smooth (t : ℝ) : ℝ := 3 * t ^ 2 - 2 * t ^ 3

theorem smooth_nonneg {t : ℝ} (h1 : t ≤ 1) : 0 ≤ smooth t := by
  unfold smooth
  nlinarith [mul_nonneg (sq_nonneg t) (by linarith : (0 : ℝ) ≤ 3 - 2 * t)]

theorem smooth_le_one {t : ℝ} (h0 : 0 ≤ t) : smooth t ≤ 1 := by
  unfold smooth
  nlinarith [mul_nonneg (sq_nonneg (1 - t)) (by linarith : (0 : ℝ) ≤ 1 + 2 * t)]

theorem two_thirds_le_smooth {t : ℝ} (h0 : 11 / 17 ≤ t) (h1 : t ≤ 1) : 2 / 3 ≤ smooth t := by
  unfold smooth
  have ha : 0 ≤ t - 11 / 17 := by linarith
  have hb : 0 ≤ 1 - t := by linarith
  nlinarith [mul_nonneg ha hb, mul_nonneg (mul_nonneg ha hb) (by linarith : (0 : ℝ) ≤ t)]

theorem smooth_le_one_third {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 6 / 17) : smooth t ≤ 1 / 3 := by
  unfold smooth
  have ha : 0 ≤ 6 / 17 - t := by linarith
  nlinarith [mul_nonneg ha h0, mul_nonneg (mul_nonneg ha h0) (by linarith : (0 : ℝ) ≤ 1 - t)]

end Smooth

section Chain

variable {k T : ℕ} {S : Type*} [Fintype S] [DecidableEq S]

/-- From an algorithm that is correct on the range of the family, a real polynomial approximating `AND`. -/
theorem exists_and_approx [NeZero (k + 3)] (q : QAlg (k + 3) T S) (N : ℕ) [NeZero N] (W W₀ : ℤ) (G m L : ℕ)
    (hG : ∀ d : ℕ, 1 ≤ d → d ≤ k + 3 → d ∣ G) (hGpos : 0 < G) (hm : 0 < m) (hmN : 2 * m ≤ N) (hL : 0 < L)
    (hclass : ∀ (h : Fin (k + 3) → Bool) (a : LabelIdx k → ℤ), (∀ j, (a j).natAbs ≤ L) →
      InClass W (family W₀ (G : ℤ) h a))
    (herr : ∀ A : Weights (k + 3), InClass W A → q.errAt N A (minDegree A) ≤ 1 / 3)
    (hδ : (Fintype.card (LabelIdx k) : ℝ) * ((N : ℝ) / (2 * m * L)) ≤ 1 / 100)
    (hε : (m : ℝ) ^ Fintype.card (LabelIdx k)
      * (2 * Real.pi * (((k + 3 : ℕ) : ℝ) * ((G : ℝ) * (sparsityConst k : ℝ) * ((m : ℝ) / N)))) ≤ 1 / 100) :
    ∃ r : MvPolynomial (Fin (k + 3)) ℝ, r.totalDegree ≤ 3 * (12 * T + 6) ∧
      ∀ x : Fin (k + 3) → Bool,
        |MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) r - andBool x| ≤ 1 / 3 := by
  classical
  set d₀ : ℤ := ((k : ℤ) + 2) * W₀ with hd₀
  obtain ⟨α, hα⟩ := q.exists_acc_expansion N d₀
  let X : (Fin T → S) × (Fin T → S) × S → Fin T ⊕ Fin T → Fin (k + 3) → Bool := fun i =>
    Sum.elim (fun t => q.x (i.1 t)) (fun t => q.x (i.2.1 t))
  let Y : (Fin T → S) × (Fin T → S) × S → Fin T ⊕ Fin T → ℤ := fun i =>
    Sum.elim (fun t => q.z (i.1 t)) (fun t => - q.z (i.2.1 t))
  have hbr : ∀ (h : Fin (k + 3) → Bool) (c : LabelIdx k → ZMod N), accFn X Y α W₀ (G : ℤ) h c
      = (q.acc N (family W₀ (G : ℤ) h fun j => (c j).valMinAbs) d₀ : ℂ) := by
    intro h c
    rw [hα]
    unfold accFn
    refine sum_congr rfl fun i _ => ?_
    have : pairing (X i) (Y i) (family W₀ (G : ℤ) h fun j => (c j).valMinAbs)
        = q.pathPhase (family W₀ (G : ℤ) h fun j => (c j).valMinAbs) i.1
          - q.pathPhase (family W₀ (G : ℤ) h fun j => (c j).valMinAbs) i.2.1 :=
      pairing_elim _ _ _ _ _
    rw [this]
  have hacc : ∀ (h : Fin (k + 3) → Bool) (c : LabelIdx k → ZMod N), ‖accFn X Y α W₀ (G : ℤ) h c‖ ≤ 1 := by
    intro h c
    rw [hbr, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (q.acc_nonneg _ _ _)]
    exact q.acc_le_one _ _ _
  obtain ⟨Q, hQd, hQ⟩ := exists_low_degree X Y α W₀ G hG hm hmN hacc
  obtain ⟨R, hRd, hR⟩ := exists_re_poly Q
  have hcardσ : Fintype.card (Fin T ⊕ Fin T) = T + T := by simp
  rw [hcardσ] at hQd
  have hRdeg : R.totalDegree ≤ 12 * T + 6 := by omega
  -- the average of the acceptance probability
  let w : (LabelIdx k → ZMod N) → ℝ := fun c => ∏ j, fejer m (c j)
  have hw : ∀ c, 0 ≤ w c := fun c => prod_fejer_nonneg m c
  have hmN' : m ≤ N := by omega
  have hw1 : ∑ c, w c = 1 := sum_prod_fejer hm hmN'
  let bad : (LabelIdx k → ZMod N) → ℝ := fun c => if ∃ j, L < (c j).valMinAbs.natAbs then 1 else 0
  have hbad : ∑ c, w c * bad c ≤ 1 / 100 :=
    (sum_prod_fejer_tail hm hmN' hL).trans hδ
  let Pr : (Fin (k + 3) → Bool) → ℝ := fun h =>
    ∑ c, w c * q.acc N (family W₀ (G : ℤ) h fun j => (c j).valMinAbs) d₀
  have hnear : ∀ h : Fin (k + 3) → Bool,
      |MvPolynomial.eval (fun v => bit (h v)) R - Pr h| ≤ 1 / 100 := by
    intro h
    have h1 := hQ h
    simp_rw [hbr] at h1
    have h2 : (∑ c : LabelIdx k → ZMod N, ((∏ j, fejer m (c j) : ℝ) : ℂ)
        * ((q.acc N (family W₀ (G : ℤ) h fun j => (c j).valMinAbs) d₀ : ℝ) : ℂ)) = ((Pr h : ℝ) : ℂ) := by
      simp only [Pr, w]
      push_cast
      rfl
    rw [h2] at h1
    rw [hR]
    have h3 := h1.trans hε
    rw [norm_sub_rev] at h3
    refine le_trans ?_ h3
    have h4 := Complex.abs_re_le_norm (MvPolynomial.eval (fun v => (bit (h v) : ℂ)) Q - (Pr h : ℂ))
    simpa using h4
  have hin : ∀ c : LabelIdx k → ZMod N, ¬ (∃ j, L < (c j).valMinAbs.natAbs) →
      ∀ j, (c j).valMinAbs.natAbs ≤ L := by
    intro c hc j
    by_contra hj
    exact hc ⟨j, by omega⟩
  have hPr0 : ∀ h, 0 ≤ Pr h := fun h =>
    sum_nonneg fun c _ => mul_nonneg (hw c) (q.acc_nonneg _ _ _)
  have hPr1 : ∀ h, Pr h ≤ 1 := by
    intro h
    calc Pr h ≤ ∑ c, w c * 1 := sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_left (q.acc_le_one _ _ _) (hw c)
      _ = 1 := by simpa using hw1
  have hlow : ∀ (h : Fin (k + 3) → Bool) (v : Fin (k + 3)), h v = false → 33 / 50 ≤ Pr h := by
    intro h v hv
    have hpt : ∀ c, w c * ((2 / 3) * (1 - bad c))
        ≤ w c * q.acc N (family W₀ (G : ℤ) h fun j => (c j).valMinAbs) d₀ := by
      intro c
      refine mul_le_mul_of_nonneg_left ?_ (hw c)
      by_cases hc : ∃ j, L < (c j).valMinAbs.natAbs
      · have : bad c = 1 := by simp only [bad, hc, ↓reduceIte]
        rw [this]
        have := q.acc_nonneg N (family W₀ (G : ℤ) h fun j => (c j).valMinAbs) d₀
        linarith
      · have hb : bad c = 0 := by simp only [bad, hc, ↓reduceIte]
        rw [hb]
        have hcl := hclass h (fun j => (c j).valMinAbs) (hin c hc)
        have he := herr _ hcl
        rw [minDegree_family_of_false W₀ (G : ℤ) (by positivity) h _ v hv] at he
        have hs := q.acc_add_errAt N (family W₀ (G : ℤ) h fun j => (c j).valMinAbs) d₀
        linarith
    have hsum : ∑ c, w c * ((2 / 3) * (1 - bad c)) = (2 / 3) * (1 - ∑ c, w c * bad c) := by
      have h1 : ∑ c, w c * ((2 / 3) * (1 - bad c)) = (2 / 3) * (∑ c, w c - ∑ c, w c * bad c) := by
        rw [← sum_sub_distrib, mul_sum]
        refine sum_congr rfl fun c _ => ?_
        ring
      rw [h1, hw1]
    have := sum_le_sum fun c (_ : c ∈ univ) => hpt c
    rw [hsum] at this
    have hP : ∑ c, w c * q.acc N (family W₀ (G : ℤ) h fun j => (c j).valMinAbs) d₀ = Pr h := rfl
    rw [hP] at this
    linarith
  have hhigh : Pr (fun _ => true) ≤ 17 / 50 := by
    have hpt : ∀ c, w c * q.acc N (family W₀ (G : ℤ) (fun _ => true) fun j => (c j).valMinAbs) d₀
        ≤ w c * (1 / 3 + (2 / 3) * bad c) := by
      intro c
      refine mul_le_mul_of_nonneg_left ?_ (hw c)
      by_cases hc : ∃ j, L < (c j).valMinAbs.natAbs
      · have : bad c = 1 := by simp only [bad, hc, ↓reduceIte]
        rw [this]
        have := q.acc_le_one N (family W₀ (G : ℤ) (fun _ => true) fun j => (c j).valMinAbs) d₀
        linarith
      · have hb : bad c = 0 := by simp only [bad, hc, ↓reduceIte]
        rw [hb]
        have hcl := hclass (fun _ => true) (fun j => (c j).valMinAbs) (hin c hc)
        have he := herr _ hcl
        have hne : d₀ ≠ minDegree (family W₀ (G : ℤ) (fun _ => true) fun j => (c j).valMinAbs) := by
          rw [minDegree_family_all_true, hd₀]
          have : (0 : ℤ) < G := by exact_mod_cast hGpos
          omega
        have hle := q.acc_le_errAt N (family W₀ (G : ℤ) (fun _ => true) fun j => (c j).valMinAbs) hne
        linarith
    have hsum : ∑ c, w c * (1 / 3 + (2 / 3) * bad c) = 1 / 3 + (2 / 3) * ∑ c, w c * bad c := by
      have h1 : ∑ c, w c * (1 / 3 + (2 / 3) * bad c)
          = (1 / 3) * ∑ c, w c + (2 / 3) * ∑ c, w c * bad c := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun c _ => ?_
        ring
      rw [h1, hw1, mul_one]
    have := sum_le_sum fun c (_ : c ∈ univ) => hpt c
    rw [hsum] at this
    have hP : ∑ c, w c * q.acc N (family W₀ (G : ℤ) (fun _ => true) fun j => (c j).valMinAbs) d₀
        = Pr (fun _ => true) := rfl
    rw [hP] at this
    linarith
  -- the rescaled polynomial
  let r₀ : MvPolynomial (Fin (k + 3)) ℝ :=
    MvPolynomial.C (101 / 102) - MvPolynomial.C (100 / 102) * R
  have hr₀d : r₀.totalDegree ≤ 12 * T + 6 := by
    refine (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp) ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simpa using hRdeg
  have hr₀ : ∀ h : Fin (k + 3) → Bool, MvPolynomial.eval (fun v => bit (h v)) r₀
      = 101 / 102 - (100 / 102) * MvPolynomial.eval (fun v => bit (h v)) R := by
    intro h
    simp [r₀]
  refine ⟨MvPolynomial.C 3 * r₀ ^ 2 - MvPolynomial.C 2 * r₀ ^ 3, ?_, ?_⟩
  · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
    · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      have := MvPolynomial.totalDegree_pow r₀ 2
      simp only [MvPolynomial.totalDegree_C, zero_add]
      omega
    · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      have := MvPolynomial.totalDegree_pow r₀ 3
      simp only [MvPolynomial.totalDegree_C, zero_add]
      omega
  · intro x
    have hev : (fun i => if x i then (1 : ℝ) else 0) = fun v => bit (x v) := rfl
    rw [hev]
    have hF : MvPolynomial.eval (fun v => bit (x v)) (MvPolynomial.C 3 * r₀ ^ 2 - MvPolynomial.C 2 * r₀ ^ 3)
        = smooth (MvPolynomial.eval (fun v => bit (x v)) r₀) := by
      simp [smooth]
    rw [hF]
    have hn := abs_le.mp (hnear x)
    have hP0 := hPr0 x
    have hP1 := hPr1 x
    set t := MvPolynomial.eval (fun v => bit (x v)) r₀ with ht
    have htv := hr₀ x
    rw [← ht] at htv
    have ht0 : 0 ≤ t := by rw [htv]; linarith [hn.1, hn.2]
    have ht1 : t ≤ 1 := by rw [htv]; linarith [hn.1, hn.2]
    by_cases hall : ∀ i, x i = true
    · have hxe : x = fun _ => true := funext hall
      have hand : andBool x = 1 := by simp [andBool, hall]
      rw [hand]
      have hP := hhigh
      rw [← hxe] at hP
      have hbig : 11 / 17 ≤ t := by rw [htv]; linarith [hn.1, hn.2]
      have h1 := two_thirds_le_smooth hbig ht1
      have h2 := smooth_le_one ht0
      rw [abs_le]
      constructor <;> linarith
    · have hand : andBool x = 0 := by simp only [andBool, hall, ↓reduceIte]
      rw [hand, sub_zero]
      push Not at hall
      obtain ⟨v, hv⟩ := hall
      have hP := hlow x v (by simpa using hv)
      have hsmall : t ≤ 6 / 17 := by rw [htv]; linarith [hn.1, hn.2]
      have h1 := smooth_le_one_third ht0 hsmall
      have h2 := smooth_nonneg ht1
      rw [abs_le]
      constructor <;> linarith

end Chain

section Params

/-- The numeric inequality behind the choice `C = 24`. -/
theorem params_pow (n : ℕ) (hn : 3 ≤ n) :
    (2400 * n ^ 6) ^ (n ^ 2 + 1) * (700 * n * n.factorial * (n ^ 2 * n.factorial + 3))
      ≤ 2 ^ (24 * n ^ 2 * (Nat.log 2 n + 1)) := by
  set l := Nat.log 2 n + 1 with hl
  set P := 2 ^ l with hP
  have hl1 : 1 ≤ l := by omega
  have hnP : n ≤ P := (Nat.lt_pow_succ_log_self (by norm_num) n).le
  have h2P : 2 ≤ P := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl1
  have hPpos : 0 < P := by omega
  have hfac : n.factorial ≤ P ^ n := (Nat.factorial_le_pow n).trans (Nat.pow_le_pow_left hnP n)
  have hm : 2400 * n ^ 6 ≤ P ^ 18 := by
    calc 2400 * n ^ 6 ≤ 2 ^ 12 * P ^ 6 := Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left hnP 6)
      _ ≤ P ^ 12 * P ^ 6 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h2P 12)
      _ = P ^ 18 := by ring
  have hE1 : n ^ 2 * n.factorial + 3 ≤ P ^ 3 * P ^ n := by
    have h1 : 3 ≤ n ^ 2 * n.factorial := by
      have : 1 ≤ n.factorial := Nat.factorial_pos n
      nlinarith
    calc n ^ 2 * n.factorial + 3 ≤ 2 * (n ^ 2 * n.factorial) := by omega
      _ ≤ P * (P ^ 2 * P ^ n) :=
          Nat.mul_le_mul h2P (Nat.mul_le_mul (Nat.pow_le_pow_left hnP 2) hfac)
      _ = P ^ 3 * P ^ n := by ring
  have hE : 700 * n * n.factorial * (n ^ 2 * n.factorial + 3) ≤ P ^ 10 * P * P ^ n * (P ^ 3 * P ^ n) := by
    have h700 : 700 ≤ P ^ 10 := by
      calc 700 ≤ 2 ^ 10 := by norm_num
        _ ≤ P ^ 10 := Nat.pow_le_pow_left h2P 10
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h700 hnP) hfac) hE1
  calc (2400 * n ^ 6) ^ (n ^ 2 + 1) * (700 * n * n.factorial * (n ^ 2 * n.factorial + 3))
      ≤ (P ^ 18) ^ (n ^ 2 + 1) * (P ^ 10 * P * P ^ n * (P ^ 3 * P ^ n)) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hm _) hE
    _ = P ^ (18 * n ^ 2 + 32 + 2 * n) := by ring_nf
    _ ≤ P ^ (24 * n ^ 2) := Nat.pow_le_pow_right hPpos (by nlinarith)
    _ = 2 ^ (24 * n ^ 2 * l) := by
        rw [hP, ← pow_mul]
        congr 1
        ring

variable {k : ℕ}

/-- Entries of a family member stay within `n G + J L` of `W₀` when all `|a_j| ≤ L`. -/
theorem family_entry_bound (W₀ G : ℤ) (hG : 0 ≤ G) (L : ℕ) (h : Fin (k + 3) → Bool) (a : LabelIdx k → ℤ)
    (ha : ∀ j, (a j).natAbs ≤ L) (f : Edge (k + 3)) :
    |family W₀ G h a f - W₀| ≤ ((k : ℤ) + 3) * G + (Fintype.card (LabelIdx k) : ℤ) * L := by
  have h1 : |∑ v, bitZ (h v) * shiftVec v f| ≤ (k : ℤ) + 3 := by
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun v _ => ?_).trans (sum_abs_shiftVec_le f))
    rw [abs_mul]
    have : |bitZ (h v)| ≤ 1 := by unfold bitZ; split_ifs <;> simp
    nlinarith [abs_nonneg (shiftVec v f), abs_nonneg (bitZ (h v))]
  have h2 : |∑ j, a j * b j f| ≤ (Fintype.card (LabelIdx k) : ℤ) * L := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |a j * b j f| ≤ ∑ j, (L : ℤ) * |b j f| := sum_le_sum fun j _ => by
          rw [abs_mul]
          have : |a j| ≤ (L : ℤ) := by
            rw [Int.abs_eq_natAbs]
            exact_mod_cast ha j
          exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
      _ = (L : ℤ) * ∑ j, |b j f| := by rw [mul_sum]
      _ ≤ (L : ℤ) * (Fintype.card (LabelIdx k) : ℤ) :=
          mul_le_mul_of_nonneg_left (sum_abs_b_le f) (by positivity)
      _ = _ := by ring
  have h3 : family W₀ G h a f - W₀ = G * ∑ v, bitZ (h v) * shiftVec v f + ∑ j, a j * b j f := by
    unfold family
    ring
  rw [h3]
  refine (abs_add_le _ _).trans (add_le_add ?_ h2)
  rw [abs_mul, abs_of_nonneg hG, mul_comm]
  exact mul_le_mul_of_nonneg_right h1 hG

/-- The numeric facts about the parameters `m = 2400 n⁶`, `L = ⌊W / (24 n²)⌋`, with `W = 2^(24 n² (log₂ n + 1))`. -/
theorem params_num (n J : ℕ) (hn3 : 3 ≤ n) (hJ : J ≤ n ^ 2) :
    0 < quantumWeight n 24 / (24 * n ^ 2) ∧
    2 * (2400 * n ^ 6) ≤ n ^ 2 * quantumWeight n 24 ∧
    2 * (n * n.factorial + J * (quantumWeight n 24 / (24 * n ^ 2))) ≤ quantumWeight n 24 ∧
    (J : ℝ) * (((n ^ 2 * quantumWeight n 24 : ℕ) : ℝ)
      / (2 * ((2400 * n ^ 6 : ℕ) : ℝ) * ((quantumWeight n 24 / (24 * n ^ 2) : ℕ) : ℝ))) ≤ 1 / 100 ∧
    ((2400 * n ^ 6 : ℕ) : ℝ) ^ J * (2 * Real.pi * ((n : ℝ) * ((n.factorial : ℝ)
      * ((n ^ 2 * n.factorial + 3 : ℕ) : ℝ) * (((2400 * n ^ 6 : ℕ) : ℝ) / ((n ^ 2 * quantumWeight n 24 : ℕ) : ℝ)))))
      ≤ 1 / 100 := by
  set W := quantumWeight n 24 with hW
  set G := n.factorial with hGdef
  set m := 2400 * n ^ 6 with hm
  have hnpos : 0 < n := by omega
  have hmpos : 0 < m := by positivity
  have hGpos : 0 < G := Nat.factorial_pos n
  set E := 700 * n * G * (n ^ 2 * G + 3) with hE
  have hmain : m ^ (n ^ 2 + 1) * E ≤ W := params_pow n hn3
  have hE700 : 700 ≤ E := by
    have h5 : 1 ≤ n ^ 2 * G + 3 := by omega
    calc 700 = 700 * 1 * 1 * 1 := by norm_num
      _ ≤ E := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl hnpos) hGpos) h5
  have hmle : m ≤ m ^ (n ^ 2 + 1) := Nat.le_self_pow (by omega) m
  have hmE : m * E ≤ W := (Nat.mul_le_mul_right _ hmle).trans hmain
  have h2mW : 2 * m ≤ W := by nlinarith
  have hEW : E ≤ W := by
    have h1 : 1 ≤ m ^ (n ^ 2 + 1) := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hmpos.ne')
    exact (Nat.le_mul_of_pos_left _ h1).trans hmain
  have h4nG : 4 * (n * G) ≤ W := by
    refine le_trans ?_ hEW
    have : 1 ≤ n ^ 2 * G + 3 := by omega
    calc 4 * (n * G) ≤ 700 * (n * G) * 1 := by omega
      _ ≤ 700 * (n * G) * (n ^ 2 * G + 3) := Nat.mul_le_mul_left _ this
      _ = E := by rw [hE]; ring
  have h24 : 24 * n ^ 2 ≤ W := by
    have h2 : n ^ 2 ≤ n ^ 6 := Nat.pow_le_pow_right hnpos (by norm_num)
    omega
  have hn2 : 1 ≤ n ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  set L := W / (24 * n ^ 2) with hLdef
  have hLpos : 0 < L := Nat.div_pos h24 (by positivity)
  have hLle : 24 * n ^ 2 * L ≤ W := Nat.mul_div_le W _
  have hLge : W ≤ 48 * n ^ 2 * L := by
    have h1 : W < 24 * n ^ 2 * (L + 1) := Nat.lt_mul_div_succ W (by positivity)
    have h2 : 24 * n ^ 2 * (L + 1) ≤ 24 * n ^ 2 * (2 * L) := Nat.mul_le_mul_left _ (by omega)
    calc W ≤ 24 * n ^ 2 * (L + 1) := h1.le
      _ ≤ 24 * n ^ 2 * (2 * L) := h2
      _ = 48 * n ^ 2 * L := by ring
  have hWN : W ≤ n ^ 2 * W := Nat.le_mul_of_pos_left _ hn2
  have hWpos : 0 < W := by omega
  refine ⟨hLpos, h2mW.trans hWN, ?_, ?_, ?_⟩
  · have h1 : J * L ≤ n ^ 2 * L := Nat.mul_le_mul_right _ hJ
    have h2 : 24 * (n ^ 2 * L) ≤ W := by
      calc 24 * (n ^ 2 * L) = 24 * n ^ 2 * L := by ring
        _ ≤ W := hLle
    omega
  · have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
    have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    have hN : 100 * (J * (n ^ 2 * W)) ≤ 2 * m * L := by
      calc 100 * (J * (n ^ 2 * W)) ≤ 100 * (n ^ 2 * (n ^ 2 * (48 * n ^ 2 * L))) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul hJ (Nat.mul_le_mul_left _ hLge))
        _ = 2 * m * L := by rw [hm]; ring
    have hR : (100 : ℝ) * ((J : ℝ) * ((n ^ 2 * W : ℕ) : ℝ)) ≤ 2 * (m : ℝ) * (L : ℝ) := by
      exact_mod_cast hN
    linarith
  · have hNpos : (0 : ℝ) < ((n ^ 2 * W : ℕ) : ℝ) := by
      have : 0 < n ^ 2 * W := by positivity
      exact_mod_cast this
    have hpi : 2 * Real.pi ≤ 7 := by linarith [Real.pi_lt_d2]
    have hpi0 := Real.pi_pos
    have hpow : (m : ℝ) ^ J * (m : ℝ) ≤ (m : ℝ) ^ (n ^ 2 + 1) := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ (by exact_mod_cast hmpos) (by omega)
    have hmainR : (m : ℝ) ^ (n ^ 2 + 1) * ((700 : ℝ) * n * G * ((n ^ 2 * G + 3 : ℕ) : ℝ)) ≤ (W : ℝ) := by
      have : ((m ^ (n ^ 2 + 1) * E : ℕ) : ℝ) ≤ (W : ℝ) := by exact_mod_cast hmain
      rw [hE] at this
      push_cast at this ⊢
      linarith
    have hWNR : (W : ℝ) ≤ ((n ^ 2 * W : ℕ) : ℝ) := by exact_mod_cast hWN
    set K : ℝ := ((n ^ 2 * G + 3 : ℕ) : ℝ) with hK
    have hKpos : 0 ≤ K := by positivity
    have hstep : (m : ℝ) ^ J * (2 * Real.pi * ((n : ℝ) * ((G : ℝ) * K * ((m : ℝ) / ((n ^ 2 * W : ℕ) : ℝ)))))
        = ((m : ℝ) ^ J * (m : ℝ)) * (2 * Real.pi) * ((n : ℝ) * G * K) / ((n ^ 2 * W : ℕ) : ℝ) := by
      field_simp
    rw [hstep, div_le_iff₀ hNpos]
    have hnGK : 0 ≤ (n : ℝ) * G * K := by positivity
    have hA : ((m : ℝ) ^ J * (m : ℝ)) * (2 * Real.pi) * ((n : ℝ) * G * K)
        ≤ (m : ℝ) ^ (n ^ 2 + 1) * 7 * ((n : ℝ) * G * K) := by
      refine mul_le_mul_of_nonneg_right ?_ hnGK
      exact mul_le_mul hpow hpi (by positivity) (by positivity)
    have hB : (m : ℝ) ^ (n ^ 2 + 1) * 7 * ((n : ℝ) * G * K) * 100
        = (m : ℝ) ^ (n ^ 2 + 1) * ((700 : ℝ) * n * G * K) := by ring
    nlinarith

/-- The parameters of the construction for `n = k + 3` and `C = 24`. -/
theorem params (k : ℕ) :
    ∃ (m L : ℕ) (W₀ : ℤ), 0 < m ∧ 0 < L ∧
      2 * m ≤ (k + 3) ^ 2 * quantumWeight (k + 3) 24 ∧
      (∀ (h : Fin (k + 3) → Bool) (a : LabelIdx k → ℤ), (∀ j, (a j).natAbs ≤ L) →
        InClass (quantumWeight (k + 3) 24 : ℤ) (family W₀ (((k + 3).factorial : ℕ) : ℤ) h a)) ∧
      (Fintype.card (LabelIdx k) : ℝ)
        * ((((k + 3) ^ 2 * quantumWeight (k + 3) 24 : ℕ) : ℝ) / (2 * m * L)) ≤ 1 / 100 ∧
      (m : ℝ) ^ Fintype.card (LabelIdx k)
        * (2 * Real.pi * (((k + 3 : ℕ) : ℝ) * ((((k + 3).factorial : ℕ) : ℝ) * (sparsityConst k : ℝ)
          * ((m : ℝ) / ((k + 3) ^ 2 * quantumWeight (k + 3) 24 : ℕ))))) ≤ 1 / 100 := by
  obtain ⟨hL, hmN, h2W, hδ, hε⟩ := params_num (k + 3) (Fintype.card (LabelIdx k)) (by omega) card_labelIdx_le
  refine ⟨2400 * (k + 3) ^ 6, quantumWeight (k + 3) 24 / (24 * (k + 3) ^ 2),
    ((k : ℤ) + 3) * ((k + 3).factorial : ℤ)
      + (Fintype.card (LabelIdx k) : ℤ) * ((quantumWeight (k + 3) 24 / (24 * (k + 3) ^ 2) : ℕ) : ℤ),
    by positivity, hL, hmN, ?_, hδ, hε⟩
  intro h a ha f
  have hb := abs_le.mp (family_entry_bound
    (((k : ℤ) + 3) * ((k + 3).factorial : ℤ)
      + (Fintype.card (LabelIdx k) : ℤ) * ((quantumWeight (k + 3) 24 / (24 * (k + 3) ^ 2) : ℕ) : ℤ))
    ((k + 3).factorial : ℤ) (by positivity) _ h a ha f)
  have h2W' : 2 * (((k : ℤ) + 3) * ((k + 3).factorial : ℤ)
      + (Fintype.card (LabelIdx k) : ℤ) * ((quantumWeight (k + 3) 24 / (24 * (k + 3) ^ 2) : ℕ) : ℤ))
      ≤ (quantumWeight (k + 3) 24 : ℤ) := by
    have : ((2 * ((k + 3) * (k + 3).factorial + Fintype.card (LabelIdx k)
        * (quantumWeight (k + 3) 24 / (24 * (k + 3) ^ 2))) : ℕ) : ℤ) ≤ (quantumWeight (k + 3) 24 : ℤ) := by
      exact_mod_cast h2W
    push_cast at this
    exact this
  constructor <;> linarith [hb.1, hb.2]

end Params

/-- The quantum lower bound: computing the minimum degree with error at most `1/3` on all graphs with integer
weights in `[0, 2^(24 n² (log₂ n + 1))]` needs `Ω(√n)` queries of the phase form. -/
theorem quantum_bound (hA : AndApproxDegree) : ∃ (C : ℕ) (c : ℝ), 0 < c ∧
    ∀ (n : ℕ) [NeZero n] (T : ℕ) (S : Type) [Fintype S] [DecidableEq S] (q : QAlg n T S),
    (∀ A : Weights n, InClass (quantumWeight n C : ℤ) A →
      q.errAt (n ^ 2 * quantumWeight n C) A (minDegree A) ≤ 1 / 3) →
    c * Real.sqrt n ≤ T + 1 := by
  obtain ⟨c₀, hc₀, hdeg⟩ := hA
  refine ⟨24, min (c₀ / 36) (1 / 2), by positivity, ?_⟩
  intro n _ T S _ _ q herr
  have hT : (0 : ℝ) ≤ T := by positivity
  have hsq0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  by_cases hn : n < 3
  · have h1 : Real.sqrt n ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      have : (n : ℝ) ≤ 2 := by exact_mod_cast (by omega : n ≤ 2)
      linarith
    have h2 : min (c₀ / 36) (1 / 2) * Real.sqrt n ≤ (1 / 2) * 2 :=
      mul_le_mul (min_le_right _ _) h1 hsq0 (by norm_num)
    linarith
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    obtain ⟨m, L, W₀, hm, hL, hmN, hclass, hδ, hε⟩ := params k
    have : NeZero ((k + 3) ^ 2 * quantumWeight (k + 3) 24) := ⟨by
      unfold quantumWeight
      positivity⟩
    obtain ⟨r, hrd, hr⟩ := exists_and_approx q ((k + 3) ^ 2 * quantumWeight (k + 3) 24)
      (quantumWeight (k + 3) 24 : ℤ) W₀ (k + 3).factorial m L
      (fun d hd1 hd2 => Nat.dvd_factorial hd1 hd2) (Nat.factorial_pos _) hm hmN hL hclass herr hδ hε
    have h1 := hdeg (k + 3) r hr
    have h2 : (r.totalDegree : ℝ) ≤ 3 * (12 * T + 6) := by exact_mod_cast hrd
    have h3 : min (c₀ / 36) (1 / 2) * Real.sqrt ((k + 3 : ℕ) : ℝ) ≤ (c₀ / 36) * Real.sqrt ((k + 3 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hsq0
    linarith


end CutQuery
