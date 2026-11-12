import QNNShatter.Average

/-!
# A kernel weight below one gives all sign patterns

Write `e(x) = exp(2π i x)`. A *bump* for the margin `γ` is a function `h : ℝ → ℝ` with
`h ≥ 0`, `γ ≤ cos(2π x)` wherever `h x ≠ 0`, and an absolutely convergent expansion
`h x = ∑_{z ∈ ℤ} w ρ(z) e(z x)` with `w > 0`, `ρ ≥ 0`, `ρ 0 = 1` and `ρ` summable.

For an `m × T` matrix `A` with entries in `{0, …, M}` and a sign pattern `p`, put
`t_j = 0` if `p j` holds and `t_j = 1/2` otherwise, and let
`G(φ) = ∏ j, h((Aφ)_j - t_j)`. Averaging `G` over the grid `φ ∈ (ℤ/N)^T / N` gives
`w^m ∑_{k : N ∣ Aᵀk} ∏ j, ρ(k j) e(-⟨k, t⟩)`, whose real part is at least
`w^m (1 - S(A) - ε)` once `N` exceeds the entries of `Aᵀk` for `k` in a finite set carrying all
but `ε` of the weight. If `S(A) < 1` some grid point has `G(φ) > 0`, and then
`θ = 2πφ` realizes the pattern: `p_j cos⟨A_j, θ⟩ ≥ γ` for all `j`.
-/

open Finset Complex Filter Topology
open scoped ENNReal Real

namespace QNNShatter

noncomputable section

/-- `e(x) = exp(2π i x)`. -/
def e (x : ℝ) : ℂ := Complex.exp (2 * π * I * x)

theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  simp only [e, ofReal_add, mul_add, Complex.exp_add]

theorem e_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    e (∑ i ∈ s, f i) = ∏ i ∈ s, e (f i) := by
  simp only [e, ofReal_sum, Finset.mul_sum, Complex.exp_sum]

theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  rw [e, Complex.norm_exp]
  simp

theorem e_eq_one_iff (x : ℝ) : e x = 1 ↔ ∃ n : ℤ, x = n := by
  rw [e, Complex.exp_eq_one_iff]
  have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have : (x : ℂ) = n := by
      apply mul_left_cancel₀ h2
      rw [hn]; ring
    exact_mod_cast this
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩

theorem e_int (n : ℤ) : e n = 1 := (e_eq_one_iff _).2 ⟨n, rfl⟩

theorem e_zero : e 0 = 1 := by simpa using e_int 0

theorem e_natMul (n : ℕ) (x : ℝ) : e (n * x) = e x ^ n := by
  rw [e, e, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The character sum over `ℤ/N`: `∑_{b < N} e(n b / N)` is `N` if `N ∣ n` and `0` otherwise. -/
theorem sum_e_fin (N : ℕ) (hN : 0 < N) (n : ℤ) :
    ∑ b : Fin N, e (n * ((b : ℕ) : ℝ) / N) = if (N : ℤ) ∣ n then (N : ℂ) else 0 := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hpow : ∀ b : ℕ, e (n * (b : ℝ) / N) = e (n / N) ^ b := by
    intro b
    rw [← e_natMul]
    congr 1
    ring
  rw [Fin.sum_univ_eq_sum_range (fun b : ℕ => e (n * (b : ℝ) / N)) N]
  simp_rw [hpow]
  split_ifs with hd
  · obtain ⟨c, hc⟩ := hd
    have : e (n / N) = 1 := by
      rw [e_eq_one_iff]
      refine ⟨c, ?_⟩
      rw [hc]
      push_cast
      field_simp
    simp [this]
  · have hne : e (n / N) ≠ 1 := by
      rw [Ne, e_eq_one_iff]
      rintro ⟨c, hc⟩
      apply hd
      refine ⟨c, ?_⟩
      have : (n : ℝ) = N * c := by
        rw [← hc]
        field_simp
      exact_mod_cast this
    have hN1 : e (n / N) ^ N = 1 := by
      rw [← hpow N, show (n : ℝ) * (N : ℝ) / N = n by field_simp, e_int]
    rw [geom_sum_eq hne, hN1, sub_self, zero_div]

set_option maxHeartbeats 1000000 in
/-- A product of absolutely convergent series over `ℤ` is the series over `ℤ^m` of the
products. -/
theorem hasSum_fin_prod (m : ℕ) : ∀ (f : Fin m → ℤ → ℂ) (a : Fin m → ℂ),
    (∀ j, HasSum (f j) (a j)) → (∀ j, Summable fun z => ‖f j z‖) →
    HasSum (fun k : Fin m → ℤ => ∏ j, f j (k j)) (∏ j, a j) ∧
      Summable (fun k : Fin m → ℤ => ‖∏ j, f j (k j)‖) := by
  induction m with
  | zero =>
    intro f a _ _
    simp only [Fin.prod_univ_zero]
    have h : HasSum (fun _ : Fin 0 → ℤ => (1 : ℂ)) 1 :=
      hasSum_single (f := fun _ : Fin 0 → ℤ => (1 : ℂ)) default
        (fun b hb => (hb (Subsingleton.elim _ _)).elim)
    have h' : HasSum (fun _ : Fin 0 → ℤ => ‖(1 : ℂ)‖) ‖(1 : ℂ)‖ :=
      hasSum_single (f := fun _ : Fin 0 → ℤ => ‖(1 : ℂ)‖) default
        (fun b hb => (hb (Subsingleton.elim _ _)).elim)
    exact ⟨h, h'.summable⟩
  | succ m ih =>
    intro f a hf hn
    have : T3Space ℂ := inferInstance
    obtain ⟨ih1, ih2⟩ := ih (fun j => f j.succ) (fun j => a j.succ)
      (fun j => hf j.succ) (fun j => hn j.succ)
    have hcomp : (fun k : Fin (m + 1) → ℤ => ∏ j, f j (k j)) ∘ Fin.consEquiv (fun _ => ℤ)
        = fun p : ℤ × (Fin m → ℤ) => f 0 p.1 * ∏ j, f j.succ (p.2 j) := by
      funext p
      simp [Fin.prod_univ_succ]
    have hs : Summable fun p : ℤ × (Fin m → ℤ) => f 0 p.1 * ∏ j, f j.succ (p.2 j) := by
      apply summable_mul_of_summable_norm (hn 0) ih2
    have hsn : Summable fun p : ℤ × (Fin m → ℤ) => ‖f 0 p.1‖ * ‖∏ j, f j.succ (p.2 j)‖ := by
      apply Summable.mul_of_nonneg (hn 0) ih2 <;> exact fun _ => norm_nonneg _
    constructor
    · rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => ℤ)).hasSum_iff, hcomp, Fin.prod_univ_succ]
      apply (hf 0).mul ih1 hs
    · rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => ℤ)).summable_iff]
      have : (fun k : Fin (m + 1) → ℤ => ‖∏ j, f j (k j)‖) ∘ Fin.consEquiv (fun _ => ℤ)
          = fun p : ℤ × (Fin m → ℤ) => ‖f 0 p.1‖ * ‖∏ j, f j.succ (p.2 j)‖ := by
        funext p
        simp [Fin.prod_univ_succ]
      rw [this]
      exact hsn

/-- A bump for the margin `γ`: `h ≥ 0`, `γ ≤ cos(2π x)` wherever `h x ≠ 0`, and
`h x = ∑_z w ρ(z) e(z x)` with `w > 0`, `ρ ≥ 0`, `ρ 0 = 1` and `ρ` summable. -/
structure Bump (γ : ℝ) where
  w : ℝ
  w_pos : 0 < w
  ρ : ℤ → ℝ
  ρ_nonneg : ∀ z, 0 ≤ ρ z
  ρ_zero : ρ 0 = 1
  ρ_summable : Summable ρ
  h : ℝ → ℝ
  h_nonneg : ∀ x, 0 ≤ h x
  h_ne_zero : ∀ x, h x ≠ 0 → γ ≤ Real.cos (2 * π * x)
  h_hasSum : ∀ x, HasSum (fun z : ℤ => ((w * ρ z : ℝ) : ℂ) * e (z * x)) (h x : ℂ)

namespace Bump

variable {γ : ℝ} (B : Bump γ)

/-- `c k = ∏ j, ρ (k j)`. -/
def c {m : ℕ} (k : Fin m → ℤ) : ℝ := ∏ j, B.ρ (k j)

theorem c_nonneg {m : ℕ} (k : Fin m → ℤ) : 0 ≤ B.c k :=
  prod_nonneg fun _ _ => B.ρ_nonneg _

theorem c_zero {m : ℕ} : B.c (0 : Fin m → ℤ) = 1 := by
  simp [c, B.ρ_zero]

theorem norm_term (z : ℤ) (x : ℝ) :
    ‖((B.w * B.ρ z : ℝ) : ℂ) * e (z * x)‖ = B.w * B.ρ z := by
  rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg B.w_pos.le (B.ρ_nonneg z))]

/-- The expansion `∏ j, h(x j) = ∑_{k ∈ ℤ^m} w^m c(k) e(⟨k, x⟩)`, absolutely convergent. -/
theorem expand {m : ℕ} (x : Fin m → ℝ) :
    HasSum (fun k : Fin m → ℤ => ((B.w ^ m * B.c k : ℝ) : ℂ) * e (∑ j, k j * x j))
      (∏ j, (B.h (x j) : ℂ)) ∧ Summable (fun k : Fin m → ℤ => B.w ^ m * B.c k) := by
  have hn : ∀ j : Fin m, Summable fun z : ℤ => ‖((B.w * B.ρ z : ℝ) : ℂ) * e (z * x j)‖ := by
    intro j
    simp_rw [B.norm_term]
    exact B.ρ_summable.mul_left _
  obtain ⟨h1, h2⟩ := hasSum_fin_prod m (fun j z => ((B.w * B.ρ z : ℝ) : ℂ) * e (z * x j))
    (fun j => (B.h (x j) : ℂ)) (fun j => B.h_hasSum (x j)) hn
  have hterm : ∀ k : Fin m → ℤ, ∏ j, (((B.w * B.ρ (k j) : ℝ) : ℂ) * e (k j * x j))
      = ((B.w ^ m * B.c k : ℝ) : ℂ) * e (∑ j, k j * x j) := by
    intro k
    rw [e_sum, Finset.prod_mul_distrib, c]
    push_cast
    rw [Finset.prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
  refine ⟨?_, ?_⟩
  · convert h1 using 2 with k
    exact (hterm k).symm
  · refine h2.congr fun k => ?_
    simp only [norm_prod, B.norm_term]
    rw [Finset.prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, c]

theorem summable_c {m : ℕ} : Summable (fun k : Fin m → ℤ => B.c k) :=
  (summable_mul_left_iff (pow_ne_zero m B.w_pos.ne')).1 (B.expand (0 : Fin m → ℝ)).2

end Bump

variable {m T M : ℕ}

/-- The coordinates `(Aᵀ k)_i = ∑ j, k j * A j i`. -/
def kerVec (A : Fin m → Fin T → Fin (M + 1)) (k : Fin m → ℤ) (i : Fin T) : ℤ :=
  ∑ j, k j * ((A j i : ℕ) : ℤ)

/-- The shift `t_j = 0` if `p j` holds and `t_j = 1/2` otherwise. -/
def shift (p : Fin m → Bool) (j : Fin m) : ℝ := if p j then 0 else 1 / 2

/-- The argument `(A φ)_j - t_j` at the grid point `φ_i = b_i / N`. -/
def gridArg (A : Fin m → Fin T → Fin (M + 1)) (p : Fin m → Bool) (N : ℕ) (b : Fin T → Fin N)
    (j : Fin m) : ℝ :=
  ∑ i, ((A j i : ℕ) : ℝ) * (((b i : ℕ) : ℝ) / N) - shift p j

theorem sum_k_gridArg (A : Fin m → Fin T → Fin (M + 1)) (p : Fin m → Bool) (N : ℕ)
    (b : Fin T → Fin N) (k : Fin m → ℤ) :
    ∑ j, (k j : ℝ) * gridArg A p N b j
      = ∑ i, (kerVec A k i : ℝ) * ((b i : ℕ) : ℝ) / N - ∑ j, (k j : ℝ) * shift p j := by
  simp only [gridArg, kerVec, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  rw [Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The character sum over the grid `(ℤ/N)^T`. -/
theorem sum_grid_e (N : ℕ) (hN : 0 < N) (n : Fin T → ℤ) :
    ∑ b : Fin T → Fin N, e (∑ i, (n i : ℝ) * ((b i : ℕ) : ℝ) / N)
      = if ∀ i, (N : ℤ) ∣ n i then (N : ℂ) ^ T else 0 := by
  simp_rw [e_sum]
  rw [← Fintype.prod_sum (fun i (c : Fin N) => e ((n i : ℝ) * ((c : ℕ) : ℝ) / N))]
  simp_rw [sum_e_fin N hN]
  rw [Finset.prod_ite_zero, prod_const, card_univ, Fintype.card_fin]
  simp

namespace Bump

variable {γ : ℝ} (B : Bump γ)

/-- The grid sum of `G` as a series over `k ∈ ℤ^m`. -/
theorem sum_grid (A : Fin m → Fin T → Fin (M + 1)) (p : Fin m → Bool) (N : ℕ) (hN : 0 < N) :
    ((∑ b : Fin T → Fin N, ∏ j, B.h (gridArg A p N b j) : ℝ) : ℂ)
      = ∑' k : Fin m → ℤ, ((B.w ^ m * B.c k : ℝ) : ℂ) * e (-(∑ j, (k j : ℝ) * shift p j))
          * (if ∀ i, (N : ℤ) ∣ kerVec A k i then (N : ℂ) ^ T else 0) := by
  push_cast
  have hexp : ∀ b : Fin T → Fin N, ∏ j, (B.h (gridArg A p N b j) : ℂ)
      = ∑' k : Fin m → ℤ, ((B.w ^ m * B.c k : ℝ) : ℂ) * e (∑ j, k j * gridArg A p N b j) :=
    fun b => ((B.expand (gridArg A p N b)).1.tsum_eq).symm
  have hsum : ∀ b : Fin T → Fin N, Summable fun k : Fin m → ℤ =>
      ((B.w ^ m * B.c k : ℝ) : ℂ) * e (∑ j, k j * gridArg A p N b j) :=
    fun b => (B.expand (gridArg A p N b)).1.summable
  simp_rw [hexp]
  rw [← Summable.tsum_finsetSum (fun b _ => hsum b)]
  refine tsum_congr fun k => ?_
  have hk : ∀ b : Fin T → Fin N, e (∑ j, (k j : ℝ) * gridArg A p N b j)
      = e (∑ i, (kerVec A k i : ℝ) * ((b i : ℕ) : ℝ) / N)
        * e (-(∑ j, (k j : ℝ) * shift p j)) := by
    intro b
    rw [sum_k_gridArg, sub_eq_add_neg, e_add]
  simp_rw [hk]
  rw [← Finset.mul_sum, ← Finset.sum_mul, sum_grid_e N hN]
  push_cast
  ring

/-- The kernel weight `∑_{k ≠ 0, Aᵀk = 0} c(k)` as a real number. -/
def Sreal (A : Fin m → Fin T → Fin (M + 1)) : ℝ :=
  ∑' k : Fin m → ℤ, if k ≠ 0 ∧ InKer A k then B.c k else 0

theorem summable_ite (P : (Fin m → ℤ) → Prop) [DecidablePred P] :
    Summable (fun k : Fin m → ℤ => if P k then B.c k else 0) :=
  Summable.of_nonneg_of_le
    (fun k => by split_ifs <;> first | exact le_rfl | exact B.c_nonneg k)
    (fun k => by split_ifs <;> first | exact le_rfl | exact B.c_nonneg k) B.summable_c

theorem S_eq_ofReal (A : Fin m → Fin T → Fin (M + 1)) :
    S (fun z => ENNReal.ofReal (B.ρ z)) A = ENNReal.ofReal (B.Sreal A) := by
  rw [Sreal, ENNReal.ofReal_tsum_of_nonneg
    (fun k => by split_ifs <;> first | exact le_rfl | exact B.c_nonneg k) (B.summable_ite _)]
  unfold S
  refine tsum_congr fun k => ?_
  split_ifs
  · rw [c, ENNReal.ofReal_prod_of_nonneg (fun j _ => B.ρ_nonneg _)]
  · simp

/-- If `S(A) < 1`, then for every sign pattern some grid point has `G > 0`. -/
theorem exists_grid_pos (A : Fin m → Fin T → Fin (M + 1)) (p : Fin m → Bool)
    (hS : S (fun z => ENNReal.ofReal (B.ρ z)) A < 1) :
    ∃ N : ℕ, ∃ b : Fin T → Fin N, 0 < ∏ j, B.h (gridArg A p N b j) := by
  have hS1 : B.Sreal A < 1 := by
    rw [S_eq_ofReal] at hS
    exact ENNReal.ofReal_lt_one.1 hS
  have hδpos : 0 < 1 - B.Sreal A := by linarith
  -- a finite set carrying all but `1 - S(A)` of the weight
  obtain ⟨F, hF⟩ : ∃ F : Finset (Fin m → ℤ), ∑' a : {x // x ∉ F}, B.c a.1 < 1 - B.Sreal A :=
    ((tendsto_order.1 (tendsto_tsum_compl_atTop_zero (fun k : Fin m → ℤ => B.c k))).2 _
      hδpos).exists
  have htail : ∑' k : Fin m → ℤ, (if k ∈ F then 0 else B.c k) = ∑' a : {x // x ∉ F}, B.c a.1 := by
    rw [show (∑' a : {x // x ∉ F}, B.c a.1)
        = ∑' x, Set.indicator {x | x ∉ F} (fun k => B.c k) x
        from tsum_subtype {x | x ∉ F} (fun k => B.c k)]
    refine tsum_congr fun k => ?_
    by_cases hk : k ∈ F <;> simp [hk]
  have hs2sum : Summable (fun k : Fin m → ℤ => if k ∈ F then 0 else B.c k) :=
    Summable.of_nonneg_of_le
      (fun k => by split_ifs <;> first | exact le_rfl | exact B.c_nonneg k)
      (fun k => by split_ifs <;> first | exact B.c_nonneg k | exact le_rfl) B.summable_c
  -- the grid size
  obtain ⟨N, hN_def⟩ : ∃ N : ℕ, N = 1 + ∑ k ∈ F, ∑ i, (kerVec A k i).natAbs := ⟨_, rfl⟩
  have hN : 0 < N := by omega
  have hbig : ∀ k ∈ F, ∀ i, (kerVec A k i).natAbs < N := by
    intro k hk i
    have h1 : (kerVec A k i).natAbs ≤ ∑ i, (kerVec A k i).natAbs :=
      Finset.single_le_sum (f := fun i => (kerVec A k i).natAbs) (fun _ _ => Nat.zero_le _)
        (mem_univ i)
    have h2 : ∑ i, (kerVec A k i).natAbs ≤ ∑ k ∈ F, ∑ i, (kerVec A k i).natAbs :=
      Finset.single_le_sum (f := fun k => ∑ i, (kerVec A k i).natAbs)
        (fun _ _ => Nat.zero_le _) hk
    omega
  refine ⟨N, ?_⟩
  by_contra hcon
  push Not at hcon
  have hzero : ∀ b : Fin T → Fin N, ∏ j, B.h (gridArg A p N b j) = 0 := fun b =>
    le_antisymm (hcon b) (prod_nonneg fun j _ => B.h_nonneg _)
  have hgrid := B.sum_grid A p N hN
  simp only [hzero, sum_const_zero, ofReal_zero] at hgrid
  set term : (Fin m → ℤ) → ℂ := fun k => ((B.w ^ m * B.c k : ℝ) : ℂ)
    * e (-(∑ j, (k j : ℝ) * shift p j))
    * (if ∀ i, (N : ℤ) ∣ kerVec A k i then (N : ℂ) ^ T else 0) with hterm_def
  have hK : 0 < (N : ℝ) ^ T * B.w ^ m := mul_pos (by positivity) (pow_pos B.w_pos _)
  have hnorm : ∀ k, ‖term k‖ ≤ (N : ℝ) ^ T * B.w ^ m * B.c k := by
    intro k
    simp only [hterm_def, norm_mul, norm_e, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg B.w_pos.le m), abs_of_nonneg (B.c_nonneg k), mul_one]
    by_cases hd : ∀ i, (N : ℤ) ∣ kerVec A k i
    · rw [if_pos hd, norm_pow, Complex.norm_natCast]
      exact le_of_eq (by ring)
    · rw [if_neg hd, norm_zero, mul_zero]
      exact mul_nonneg hK.le (B.c_nonneg k)
  have hsumR : Summable (fun k : Fin m → ℤ => (N : ℝ) ^ T * B.w ^ m * B.c k) :=
    B.summable_c.mul_left _
  have hsumC : Summable term := Summable.of_norm_bounded hsumR hnorm
  have hsumRe : Summable (fun k => (term k).re) := (Complex.hasSum_re hsumC.hasSum).summable
  have hlow : ∀ k, -((N : ℝ) ^ T * B.w ^ m * B.c k) ≤ (term k).re := fun k =>
    le_trans (neg_le_neg (hnorm k)) (abs_le.1 (Complex.abs_re_le_norm (term k))).1
  have h0 : term 0 = (((N : ℝ) ^ T * B.w ^ m : ℝ) : ℂ) := by
    have hd : ∀ i, (N : ℤ) ∣ kerVec A 0 i := fun i => by simp [kerVec]
    have hs : (∑ j, (((0 : Fin m → ℤ) j : ℤ) : ℝ) * shift p j) = 0 := by simp
    simp only [hterm_def, if_pos hd, hs, neg_zero, e_zero, B.c_zero, mul_one]
    push_cast
    ring
  have hL : ∀ k : Fin m → ℤ, (N : ℝ) ^ T * B.w ^ m * ((if k = 0 then 1 else 0)
      - (if k ≠ 0 ∧ InKer A k then B.c k else 0) - (if k ∈ F then 0 else B.c k))
      ≤ (term k).re := by
    intro k
    have hs2 : 0 ≤ (if k ∈ F then 0 else B.c k) := by
      split_ifs <;> first | exact le_rfl | exact B.c_nonneg k
    have hKs2 := mul_nonneg hK.le hs2
    by_cases hk0 : k = 0
    · subst hk0
      rw [if_pos rfl, if_neg (fun h => h.1 rfl), h0, ofReal_re]
      nlinarith
    · rw [if_neg hk0]
      by_cases hker : InKer A k
      · rw [if_pos ⟨hk0, hker⟩]
        nlinarith [hlow k]
      · rw [if_neg (fun h => hker h.2)]
        by_cases hF : k ∈ F
        · rw [if_pos hF]
          have hnd : ¬ ∀ i, (N : ℤ) ∣ kerVec A k i := by
            intro hd
            apply hker
            intro i
            exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hd i) (by simpa [kerVec] using hbig k hF i)
          have : term k = 0 := by simp only [hterm_def, if_neg hnd, mul_zero]
          rw [this, zero_re]
          simp
        · rw [if_neg hF]
          nlinarith [hlow k]
  have h1 : Summable (fun k : Fin m → ℤ => (if k = 0 then (1 : ℝ) else 0)) :=
    (hasSum_ite_eq 0 1).summable
  have hsumL : Summable (fun k : Fin m → ℤ => (N : ℝ) ^ T * B.w ^ m * ((if k = 0 then 1 else 0)
      - (if k ≠ 0 ∧ InKer A k then B.c k else 0) - (if k ∈ F then 0 else B.c k))) :=
    ((h1.sub (B.summable_ite _)).sub hs2sum).mul_left _
  have hvalL : ∑' k : Fin m → ℤ, (N : ℝ) ^ T * B.w ^ m * ((if k = 0 then 1 else 0)
      - (if k ≠ 0 ∧ InKer A k then B.c k else 0) - (if k ∈ F then 0 else B.c k))
      = (N : ℝ) ^ T * B.w ^ m * (1 - B.Sreal A - ∑' a : {x // x ∉ F}, B.c a.1) := by
    rw [tsum_mul_left, Summable.tsum_sub (h1.sub (B.summable_ite _)) hs2sum,
      Summable.tsum_sub h1 (B.summable_ite _), tsum_ite_eq, htail]
    rfl
  have hre0 : ∑' k, (term k).re = 0 := by
    rw [← Complex.re_tsum hsumC, ← hgrid, zero_re]
  have hge := Summable.tsum_le_tsum hL hsumL hsumRe
  rw [hvalL, hre0] at hge
  have : 0 < (N : ℝ) ^ T * B.w ^ m * (1 - B.Sreal A - ∑' a : {x // x ∉ F}, B.c a.1) :=
    mul_pos hK (by linarith)
  linarith

/-- **All sign patterns.** If `S(A) < 1`, the rows of `A` are shattered at margin `γ`: for every
`p` there is `θ` with `p_j cos⟨A_j, θ⟩ ≥ γ` for all `j`. -/
theorem shatters (A : Fin m → Fin T → Fin (M + 1))
    (hS : S (fun z => ENNReal.ofReal (B.ρ z)) A < 1) (p : Fin m → Bool) :
    ∃ θ : Fin T → ℝ, ∀ j,
      γ ≤ (if p j then 1 else -1) * Real.cos (∑ i, ((A j i : ℕ) : ℝ) * θ i) := by
  obtain ⟨N, b, hpos⟩ := B.exists_grid_pos A p hS
  refine ⟨fun i => 2 * π * (((b i : ℕ) : ℝ) / N), fun j => ?_⟩
  have hne : B.h (gridArg A p N b j) ≠ 0 :=
    (Finset.prod_ne_zero_iff.1 hpos.ne') j (mem_univ j)
  have hγ := B.h_ne_zero _ hne
  have harg : ∑ i, ((A j i : ℕ) : ℝ) * (2 * π * (((b i : ℕ) : ℝ) / N))
      = 2 * π * gridArg A p N b j + 2 * π * shift p j := by
    rw [gridArg, mul_sub, sub_add_cancel, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [harg]
  by_cases hp : p j = true
  · have hs : shift p j = 0 := by simp [shift, hp]
    rw [if_pos hp, hs, mul_zero, add_zero, one_mul]
    exact hγ
  · have hs : shift p j = 1 / 2 := by simp [shift, hp]
    rw [if_neg hp, hs, show 2 * π * (1 / 2 : ℝ) = π by ring, Real.cos_add_pi]
    linarith

end Bump

/-- **Shattering, entries in `{0, …, M}`.** If `((1+τ)^m - 1) / (M+1)^T < 1`, where
`τ = ∑_{z ≠ 0} ρ z` for the weights of a bump, some `m × T` matrix with entries in
`{0, …, M}` has rows shattered at margin `γ` by `θ ↦ cos⟨s, θ⟩`. -/
theorem exists_shattered_reuse {γ : ℝ} (B : Bump γ) (τ : ℝ≥0∞)
    (hτ : ∑' z, (if z = 0 then 0 else ENNReal.ofReal (B.ρ z)) = τ)
    (hlt : ((1 + τ) ^ m - 1) / (M + 1 : ℝ≥0∞) ^ T < 1) :
    ∃ A : Fin m → Fin T → Fin (M + 1), ∀ p : Fin m → Bool, ∃ θ : Fin T → ℝ, ∀ j,
      γ ≤ (if p j then 1 else -1) * Real.cos (∑ i, ((A j i : ℕ) : ℝ) * θ i) := by
  obtain ⟨A, hA⟩ := exists_S_lt_one_reuse (fun z => ENNReal.ofReal (B.ρ z))
    (by simp [B.ρ_zero]) τ hτ hlt
  exact ⟨A, B.shatters A hA⟩

/-- **Shattering, entries in `{0, …, M}`, power form.** If `(1+τ)^m ≤ (M+1)^T` with `τ` finite,
some `m × T` matrix with entries in `{0, …, M}` has rows shattered at margin `γ`. With
`ℓ = log₂(1+τ)` the condition reads `m ≤ T log₂(M+1) / ℓ`. -/
theorem exists_shattered_reuse_of_pow_le {γ : ℝ} (B : Bump γ) (τ : ℝ≥0∞) (hτtop : τ ≠ ⊤)
    (hτ : ∑' z, (if z = 0 then 0 else ENNReal.ofReal (B.ρ z)) = τ)
    (hpow : (1 + τ) ^ m ≤ (M + 1 : ℝ≥0∞) ^ T) :
    ∃ A : Fin m → Fin T → Fin (M + 1), ∀ p : Fin m → Bool, ∃ θ : Fin T → ℝ, ∀ j,
      γ ≤ (if p j then 1 else -1) * Real.cos (∑ i, ((A j i : ℕ) : ℝ) * θ i) := by
  refine exists_shattered_reuse B τ hτ ?_
  have hP0 : (M + 1 : ℝ≥0∞) ^ T ≠ 0 := pow_ne_zero _ (by simp)
  have hPt : (M + 1 : ℝ≥0∞) ^ T ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  have hXt : (1 + τ) ^ m ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hτtop⟩)
  have hX0 : (1 + τ) ^ m ≠ 0 := pow_ne_zero _ (by simp)
  rw [ENNReal.div_lt_iff (Or.inl hP0) (Or.inl hPt), one_mul]
  exact lt_of_lt_of_le (ENNReal.sub_lt_self hXt hX0 one_ne_zero) hpow

/-- **Shattering, entries in `{0, 1}`.** If `∑_{v=1}^m C(m,v) τ^v q(v)^T < 1`, where
`τ = ∑_{z ≠ 0} ρ z` for the weights of a bump, some `m × T` matrix with entries in `{0, 1}` has
rows shattered at margin `γ` by `θ ↦ cos⟨s, θ⟩`. -/
theorem exists_shattered_binary {γ : ℝ} (B : Bump γ) (τ : ℝ≥0∞)
    (hτ : ∑' z, (if z = 0 then 0 else ENNReal.ofReal (B.ρ z)) = τ)
    (hlt : ∑ v ∈ Icc 1 m, (m.choose v : ℝ≥0∞) * τ ^ v * q v ^ T < 1) :
    ∃ A : Fin m → Fin T → Fin 2, ∀ p : Fin m → Bool, ∃ θ : Fin T → ℝ, ∀ j,
      γ ≤ (if p j then 1 else -1) * Real.cos (∑ i, ((A j i : ℕ) : ℝ) * θ i) := by
  obtain ⟨A, hA⟩ := exists_S_lt_one_binary (T := T) (fun z => ENNReal.ofReal (B.ρ z))
    (by simp [B.ρ_zero]) τ hτ hlt
  exact ⟨A, B.shatters A hA⟩

end

end QNNShatter
