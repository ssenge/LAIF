import Mathlib

/-!
# Counting steps of the lower bound for minimum degree with quantum cut queries

Notation follows `QC/cutquery/RESULTS.md`:
* `prod_abs_le_abs_det`: a nonzero minor with columns divisible by `g_u` is at least `∏ |g_u|`;
* `two_mul_le_of_pow_le`, `mul_log_le_of_pow_le`: the nullity bound from `det K`;
* `bezout_bounded`: Bézout coefficients with `Σ |c_i| ≤ 2 κ A + 1`;
* `polynomial_assembly`: the low-degree polynomial of Section 4.
-/

open Finset

namespace CutQuery

/-- A nonzero integer determinant with column `j` divisible by `g j` has absolute value at least `∏ |g j|`. -/
theorem prod_abs_le_abs_det {κ : Type*} [Fintype κ] [DecidableEq κ] (B : Matrix κ κ ℤ) (g : κ → ℤ)
    (h : ∀ i j, g j ∣ B i j) (hdet : B.det ≠ 0) : ∏ j, |g j| ≤ |B.det| := by
  choose B' hB' using h
  have hB : B = Matrix.of fun i j => g j * B' i j := by
    ext i j; simp [hB' i j]
  have hd : B.det = (∏ j, g j) * (Matrix.of B').det := by
    rw [hB]
    exact Matrix.det_mul_row g (Matrix.of B')
  have hne : (Matrix.of B').det ≠ 0 := by
    intro h0; rw [hd, h0, mul_zero] at hdet; exact hdet rfl
  rw [hd, abs_mul, Finset.abs_prod]
  have h1 : (1 : ℤ) ≤ |(Matrix.of B').det| := Int.one_le_abs hne
  have h2 : (0 : ℤ) ≤ ∏ j, |g j| := prod_nonneg fun _ _ => abs_nonneg _
  nlinarith

/-- `(m+1)^(2κ) ≤ r^ρ` with `r ≤ m+1` and `m ≥ 1` gives `2κ ≤ ρ`, that is `r' ≤ (3/2) ρ` when `m = n`. -/
theorem two_mul_le_of_pow_le {m r κ ρ : ℕ} (hm : 1 ≤ m) (hr : r ≤ m + 1)
    (h : (m + 1) ^ (2 * κ) ≤ r ^ ρ) : 2 * κ ≤ ρ := by
  have h1 : (m + 1) ^ (2 * κ) ≤ (m + 1) ^ ρ := h.trans (Nat.pow_le_pow_left hr ρ)
  exact (Nat.pow_le_pow_iff_right (by omega)).mp h1

/-- The general form: `2 κ log (m+1) ≤ ρ log r`. -/
theorem mul_log_le_of_pow_le {m r κ ρ : ℕ}
    (h : (m + 1) ^ (2 * κ) ≤ r ^ ρ) :
    (2 * κ : ℝ) * Real.log (m + 1) ≤ ρ * Real.log r := by
  have h' : (((m + 1 : ℕ) : ℝ)) ^ (2 * κ) ≤ ((r : ℕ) : ℝ) ^ ρ := by exact_mod_cast h
  have hl := Real.log_le_log (by positivity) h'
  rw [Real.log_pow, Real.log_pow] at hl
  push_cast at hl
  exact hl

section Bezout

variable {α : Type*} [DecidableEq α]

/-- Bézout for a finite family, with no size control. -/
theorem exists_bezout (s : Finset α) (a : α → ℤ) :
    ∃ (g : ℤ) (c : α → ℤ), 0 ≤ g ∧ (∀ i ∈ s, g ∣ a i) ∧ ∑ i ∈ s, c i * a i = g := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, le_rfl, by simp, by simp⟩
  | insert k s hk ih =>
    obtain ⟨g, c, hg, hd, hs⟩ := ih
    refine ⟨(Int.gcd (a k) g : ℤ), fun i => if i = k then Int.gcdA (a k) g else Int.gcdB (a k) g * c i,
      by positivity, ?_, ?_⟩
    · intro i hi
      rcases mem_insert.mp hi with rfl | hi'
      · exact Int.gcd_dvd_left ..
      · exact (Int.gcd_dvd_right ..).trans (hd i hi')
    · rw [sum_insert hk]
      simp only [↓reduceIte]
      have h1 : ∑ i ∈ s, (if i = k then Int.gcdA (a k) g else Int.gcdB (a k) g * c i) * a i
          = Int.gcdB (a k) g * ∑ i ∈ s, c i * a i := by
        rw [mul_sum]
        refine sum_congr rfl fun i hi => ?_
        have hne : i ≠ k := fun h => hk (h ▸ hi)
        simp only [hne, ↓reduceIte]
        ring
      rw [h1, hs, Int.gcd_eq_gcd_ab (a k) g]
      ring

/-- Bézout with `Σ |c_i| ≤ 2 κ A + 1`, for integers of absolute value at most `A`. -/
theorem bezout_bounded (s : Finset α) (a : α → ℤ) (A : ℤ) (hA : ∀ i ∈ s, |a i| ≤ A) :
    ∃ (g : ℤ) (c : α → ℤ), 0 ≤ g ∧ (∀ i ∈ s, g ∣ a i) ∧ ∑ i ∈ s, c i * a i = g ∧
      ∑ i ∈ s, |c i| ≤ 2 * s.card * A + 1 := by
  obtain ⟨g, c, hg, hd, hs⟩ := exists_bezout s a
  by_cases hzero : ∀ i ∈ s, a i = 0
  · refine ⟨g, 0, hg, hd, ?_, ?_⟩
    · have h0 : ∑ i ∈ s, c i * a i = 0 := sum_eq_zero fun i hi => by rw [hzero i hi, mul_zero]
      rw [← hs, h0]; simp
    · have hnn : 0 ≤ (2 * (s.card : ℤ) * A) := by
        rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
        · simp
        · exact mul_nonneg (by positivity) ((abs_nonneg _).trans (hA i hi))
      simp; linarith
  push Not at hzero
  obtain ⟨i0, hi0, hi0'⟩ := hzero
  obtain ⟨k, hk, hmax⟩ := s.exists_max_image (fun i => |a i|) ⟨i0, hi0⟩
  have hak : a k ≠ 0 := by
    intro h
    have := hmax i0 hi0
    rw [h, abs_zero] at this
    exact hi0' (abs_nonpos_iff.mp this)
  have hAk : 0 < |a k| := abs_pos.mpr hak
  have hg0 : g ≠ 0 := by
    intro h
    rw [h] at hd
    exact hak (zero_dvd_iff.mp (hd k hk))
  have hgpos : 1 ≤ g := by omega
  choose! b hb using hd
  have hbk : b k ≠ 0 := by
    intro h
    apply hak
    rw [hb k hk, h, mul_zero]
  have hAbs : |a k| = g * |b k| := by
    rw [hb k hk, abs_mul, abs_of_pos (by omega : 0 < g)]
  have hbkpos : 0 < |b k| := abs_pos.mpr hbk
  have hbkle : |b k| ≤ |a k| := by nlinarith
  have hgle : g ≤ |a k| := by nlinarith
  have hAnn : |a k| ≤ A := hA k hk
  -- the reduced coefficients
  set E := s.erase k with hE
  set ck : ℤ := c k + ∑ i ∈ E, (c i / b k) * b i with hck
  let c' : α → ℤ := fun i => if i = k then ck else c i % b k
  have hc'k : c' k = ck := by simp [c']
  have hc'i : ∀ i ∈ E, c' i = c i % b k := fun i hi => by simp [c', ne_of_mem_erase hi]
  have hsplit : ∀ f : α → ℤ, ∑ i ∈ s, f i = f k + ∑ i ∈ E, f i := fun f =>
    (add_sum_erase s f hk).symm
  have hsum : ∑ i ∈ s, c' i * a i = g := by
    rw [hsplit, hc'k, ← hs, hsplit (fun i => c i * a i), hck, add_mul, sum_mul]
    have h1 : ∑ i ∈ E, c' i * a i = ∑ i ∈ E, (c i - b k * (c i / b k)) * a i :=
      sum_congr rfl fun i hi => by
        rw [hc'i i hi, Int.emod_def]
    rw [h1]
    have h2 : ∀ i ∈ E, (c i - b k * (c i / b k)) * a i
        = c i * a i - c i / b k * b i * a k := fun i hi => by
      rw [hb i (mem_of_mem_erase hi), hb k hk]
      ring
    rw [sum_congr rfl h2, sum_sub_distrib]
    ring
  have hrem : ∀ i ∈ E, |c' i| ≤ |b k| := fun i hi => by
    rw [hc'i i hi, abs_of_nonneg (Int.emod_nonneg _ hbk)]
    exact (Int.emod_lt_abs _ hbk).le
  have hEcard : (E.card : ℤ) + 1 = s.card := by
    have := card_erase_add_one hk
    rw [← hE] at this
    exact_mod_cast this
  have hEsum : ∑ i ∈ E, |c' i| ≤ E.card * |b k| := by
    have := sum_le_card_nsmul E (fun i => |c' i|) |b k| hrem
    rwa [nsmul_eq_mul] at this
  have hEsum2 : |∑ i ∈ E, c' i * a i| ≤ E.card * |b k| * |a k| := by
    calc |∑ i ∈ E, c' i * a i| ≤ ∑ i ∈ E, |c' i * a i| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ E, |c' i| * |a k| := sum_le_sum fun i hi => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hmax i (mem_of_mem_erase hi)) (abs_nonneg _)
      _ = (∑ i ∈ E, |c' i|) * |a k| := by rw [sum_mul]
      _ ≤ E.card * |b k| * |a k| := mul_le_mul_of_nonneg_right hEsum (abs_nonneg _)
  have hkbound : |ck| ≤ 1 + E.card * |b k| := by
    have hrel : ck * a k = g - ∑ i ∈ E, c' i * a i := by
      have := hsum
      rw [hsplit, hc'k] at this
      linarith
    have h3 : |ck| * |a k| ≤ (1 + E.card * |b k|) * |a k| := by
      rw [← abs_mul, hrel, add_mul, one_mul]
      calc |g - ∑ i ∈ E, c' i * a i| ≤ |g| + |∑ i ∈ E, c' i * a i| := abs_sub _ _
        _ ≤ |a k| + E.card * |b k| * |a k| := by
          rw [abs_of_nonneg hg]
          exact add_le_add hgle hEsum2
    exact le_of_mul_le_mul_right h3 hAk
  refine ⟨g, c', hg, fun i hi => ⟨b i, hb i hi⟩, hsum, ?_⟩
  rw [hsplit, hc'k]
  have hEnn : (0 : ℤ) ≤ E.card := Int.natCast_nonneg _
  have h4 : (E.card : ℤ) * |b k| ≤ E.card * A :=
    mul_le_mul_of_nonneg_left (hbkle.trans hAnn) hEnn
  have hAnn' : 0 ≤ A := (abs_nonneg _).trans hAnn
  have h5 : |ck| + ∑ i ∈ E, |c' i| ≤ 1 + 2 * (E.card * A) := by linarith
  have h6 : (2 * (E.card : ℤ) * A) ≤ 2 * (s.card : ℤ) * A := by
    rw [← hEcard]; nlinarith
  linarith

end Bezout

section Polynomial

variable {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]

/-- A vertex bit as a real number. -/
def bit (b : Bool) : ℝ := if b then 1 else 0

/-- The factor `1 + h_v (e^{2πiφ} - 1)` agrees with `e^{2πi h_v φ}` on the cube. -/
theorem factor_eval (b : Bool) (p : ℝ) :
    (1 : ℂ) + (bit b : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * p) - 1)
      = Complex.exp (2 * Real.pi * Complex.I * ((bit b * p : ℝ) : ℂ)) := by
  cases b <;> simp [bit]

omit [Fintype V] in
/-- `∏_{v ∈ Y} (1 + a_v X_v)` has total degree at most `|Y|`. -/
theorem totalDegree_prod_factor (Y : Finset V) (a : V → ℂ) :
    (∏ v ∈ Y, ((1 : MvPolynomial V ℂ) + MvPolynomial.C (a v) * MvPolynomial.X v)).totalDegree
      ≤ Y.card := by
  induction Y using Finset.induction_on with
  | empty => simp
  | insert v Y hv ih =>
    rw [prod_insert hv, card_insert_of_notMem hv]
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have h1 : ((1 : MvPolynomial V ℂ) + MvPolynomial.C (a v) * MvPolynomial.X v).totalDegree ≤ 1 := by
      refine (MvPolynomial.totalDegree_add _ _).trans (max_le (by simp) ?_)
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      simp [MvPolynomial.totalDegree_X]
    omega

/-- Section 4. Suppose `P(h) = Σ_u w_u e^{2πi Σ_v h_v φ_uv} q_u(h)` on the cube, with `‖q_u(h)‖ ≤ 1`,
`deg q_u ≤ d₁`, and `|φ_uv| ≤ τ` off a set `Y_u` of at most `d₂` vertices. Then a polynomial of degree at most
`d₁ + d₂` agrees with `P` on the cube up to `(Σ_u w_u) 2π |V| τ`. -/
theorem polynomial_assembly (w : U → ℝ) (hw : ∀ u, 0 ≤ w u) (p : U → V → ℝ)
    (q : U → MvPolynomial V ℂ) (Y : U → Finset V) (d₁ d₂ : ℕ) (τ : ℝ) (hτ : 0 ≤ τ)
    (hq : ∀ u, (q u).totalDegree ≤ d₁) (hY : ∀ u, (Y u).card ≤ d₂)
    (hsmall : ∀ u, ∀ v ∉ Y u, |p u v| ≤ τ)
    (hbd : ∀ u (h : V → Bool), ‖MvPolynomial.eval (fun v => (bit (h v) : ℂ)) (q u)‖ ≤ 1) :
    ∃ Q : MvPolynomial V ℂ, Q.totalDegree ≤ d₁ + d₂ ∧ ∀ h : V → Bool,
      ‖(∑ u, (w u : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * ((∑ v, bit (h v) * p u v : ℝ) : ℂ))
            * MvPolynomial.eval (fun v => (bit (h v) : ℂ)) (q u)))
        - MvPolynomial.eval (fun v => (bit (h v) : ℂ)) Q‖
        ≤ (∑ u, w u) * (2 * Real.pi * (Fintype.card V * τ)) := by
  classical
  let fac : U → MvPolynomial V ℂ := fun u =>
    ∏ v ∈ Y u, ((1 : MvPolynomial V ℂ)
      + MvPolynomial.C (Complex.exp (2 * Real.pi * Complex.I * (p u v : ℂ)) - 1) * MvPolynomial.X v)
  refine ⟨∑ u, MvPolynomial.C (w u : ℂ) * (q u * fac u), ?_, ?_⟩
  · refine MvPolynomial.totalDegree_finsetSum_le fun u _ => ?_
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have h1 : (q u * fac u).totalDegree ≤ d₁ + d₂ :=
      (MvPolynomial.totalDegree_mul _ _).trans
        (add_le_add (hq u) ((totalDegree_prod_factor (Y u) _).trans (hY u)))
    simp only [MvPolynomial.totalDegree_C]
    omega
  · intro h
    rw [map_sum, ← sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    rw [sum_mul]
    refine sum_le_sum fun u _ => ?_
    set ev := MvPolynomial.eval (fun v => (bit (h v) : ℂ)) with hev
    set inY : ℝ := ∑ v ∈ Y u, bit (h v) * p u v with hinY
    set offY : ℝ := ∑ v ∈ univ \ Y u, bit (h v) * p u v with hoffY
    have hsplit : (∑ v, bit (h v) * p u v) = inY + offY := by
      rw [hinY, hoffY, add_comm]
      exact (sum_sdiff (subset_univ (Y u))).symm
    have hfac : ev (fac u) = Complex.exp (2 * Real.pi * Complex.I * (inY : ℂ)) := by
      rw [hev, map_prod, hinY]
      push_cast
      rw [mul_sum, Complex.exp_sum]
      refine prod_congr rfl fun v _ => ?_
      simp only [map_add, map_one, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      rw [mul_comm (Complex.exp _ - 1), factor_eval]
      push_cast
      rfl
    have hoff : |offY| ≤ Fintype.card V * τ := by
      calc |offY| ≤ ∑ v ∈ univ \ Y u, |bit (h v) * p u v| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ v ∈ univ \ Y u, τ := sum_le_sum fun v hv => by
            have hv' : v ∉ Y u := (mem_sdiff.mp hv).2
            have hb : |bit (h v)| ≤ 1 := by cases h v <;> simp [bit]
            rw [abs_mul]
            calc |bit (h v)| * |p u v| ≤ 1 * τ :=
                  mul_le_mul hb (hsmall u v hv') (abs_nonneg _) zero_le_one
              _ = τ := one_mul τ
        _ = ((univ \ Y u).card : ℝ) * τ := by rw [sum_const, nsmul_eq_mul]
        _ ≤ Fintype.card V * τ := by
            refine mul_le_mul_of_nonneg_right ?_ hτ
            exact_mod_cast card_le_univ _
    have hdiff : ‖Complex.exp (2 * Real.pi * Complex.I * ((offY : ℝ) : ℂ)) - 1‖
        ≤ 2 * Real.pi * (Fintype.card V * τ) := by
      have h1 := Real.norm_eq_abs (2 * Real.pi * offY)
      have h2 : ‖Complex.exp (Complex.I * ((2 * Real.pi * offY : ℝ) : ℂ)) - 1‖
          ≤ ‖(2 * Real.pi * offY : ℝ)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
      have h3 : Complex.I * ((2 * Real.pi * offY : ℝ) : ℂ)
          = 2 * Real.pi * Complex.I * ((offY : ℝ) : ℂ) := by push_cast; ring
      rw [h3, h1, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h2
      exact h2.trans (mul_le_mul_of_nonneg_left hoff (by positivity))
    have hwn : ‖(w u : ℂ)‖ = w u := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw u)]
    have hexp1 : ‖Complex.exp (2 * Real.pi * Complex.I * ((inY : ℝ) : ℂ))‖ = 1 := by
      have : 2 * Real.pi * Complex.I * ((inY : ℝ) : ℂ) = ((2 * Real.pi * inY : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    have hrw : (w u : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * ((∑ v, bit (h v) * p u v : ℝ) : ℂ))
          * ev (q u)) - ev (MvPolynomial.C (w u : ℂ) * (q u * fac u))
        = (w u : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * ((inY : ℝ) : ℂ)) * ev (q u)
            * (Complex.exp (2 * Real.pi * Complex.I * ((offY : ℝ) : ℂ)) - 1)) := by
      rw [map_mul, map_mul, hfac, hsplit, hev, MvPolynomial.eval_C]
      push_cast
      rw [mul_add, Complex.exp_add]
      ring
    rw [hrw, norm_mul, hwn, norm_mul, norm_mul, hexp1, one_mul]
    refine mul_le_mul_of_nonneg_left ?_ (hw u)
    calc ‖ev (q u)‖ * ‖Complex.exp (2 * Real.pi * Complex.I * ((offY : ℝ) : ℂ)) - 1‖
        ≤ 1 * (2 * Real.pi * (Fintype.card V * τ)) :=
          mul_le_mul (hbd u h) hdiff (norm_nonneg _) zero_le_one
      _ = _ := one_mul _

end Polynomial

end CutQuery
