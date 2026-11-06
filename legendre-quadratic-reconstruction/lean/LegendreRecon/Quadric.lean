import Mathlib
import LegendreRecon.Amplitude

/-!
# Fourier transform of a quadratic character on a quadric

Let `F` be a finite field of odd characteristic with `q` elements, `χ` its quadratic character with values in
`ℂ` and `ψ` a primitive additive character, `G = g(χ, ψ)` the Gauss sum. For `n` even, `a : Fin n → F` with all
`a i ≠ 0`, `D ≠ 0` and `s : Fin n → F` put

  `f(x) = Σ_i a_i (x_i + s_i)² - D`,   `Q*(k) = Σ_i k_i² / a_i`.

Then for every `x`

  `q · Σ_k Σ_{y : y² = D Q*(k)} ψ(y - Σ_i k_i (x_i + s_i)) = G^(n+2) χ(D Π_i a_i) χ(f(x))`,

and, by Fourier inversion, for every `k`

  `G^(n+2) χ(D Π_i a_i) Σ_x χ(f(x)) ψ(Σ_i k_i x_i) = q^(n+1) Σ_{y : y² = D Q*(k)} ψ(y - Σ_i k_i s_i)`.

So the Fourier coefficient at `k` is a sum of at most two characters, at `±√(D Q*(k)) - k·s`. Only Gauss sums
are used. The number of square roots of `u` is `1 + χ(u)`; this is the hypothesis `hsq`, discharged for the
quadratic character of `F` by `card_sqrts_quadraticChar`. A general nondegenerate quadratic part reduces to the
diagonal one by a linear change of variables.
-/

open Finset

namespace LegendreRecon

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
theorem psi_sum {ι : Type*} (ψ : AddChar F ℂ) (s : Finset ι) (f : ι → F) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [sum_insert hi, prod_insert hi, AddChar.map_add_eq_mul, ih]

/-- The hypothesis `hsq` holds for the quadratic character of `F`. -/
theorem card_sqrts_quadraticChar (hF : ringChar F ≠ 2) (u : F) :
    ((univ.filter fun y : F => y ^ 2 = u).card : ℂ) =
      (quadraticChar F).ringHomComp (Int.castRingHom ℂ) u + 1 := by
  have h := quadraticChar_card_sqrts hF u
  have e : (univ.filter fun y : F => y ^ 2 = u) = {x : F | x ^ 2 = u}.toFinset := by ext; simp
  simp only [e, MulChar.ringHomComp_apply, Int.coe_castRingHom]
  exact_mod_cast h

section Gauss

variable (χ : MulChar F ℂ) (hχ : χ ≠ 1) (hq : χ.IsQuadratic) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
  (hsq : ∀ u : F, ((univ.filter fun y : F => y ^ 2 = u).card : ℂ) = χ u + 1)
include hχ hq hψ hsq

omit hχ hq hsq in
theorem sum_psi_mul_eq_zero {c : F} (hc : c ≠ 0) : ∑ u, ψ (c * u) = 0 := by
  have h := AddChar.sum_mulShift (ψ := ψ) c hψ
  calc ∑ u, ψ (c * u) = ∑ x, ψ (x * c) := sum_congr rfl fun u _ => by rw [mul_comm]
    _ = 0 := by rw [h]; simp [hc]

/-- The quadratic Gauss sum: `Σ_y ψ(c y²) = χ(c) G` for `c ≠ 0`. -/
theorem sum_psi_sq {c : F} (hc : c ≠ 0) : ∑ y, ψ (c * y ^ 2) = χ c * gaussSum χ ψ := by
  have h1 : ∑ y, ψ (c * y ^ 2) =
      ∑ u, ((univ.filter fun y : F => y ^ 2 = u).card : ℂ) * ψ (c * u) := by
    rw [← sum_fiberwise univ (fun y : F => y ^ 2) (fun y => ψ (c * y ^ 2))]
    refine sum_congr rfl fun u _ => ?_
    rw [sum_congr rfl (g := fun _ => ψ (c * u)) (fun y hy => by rw [(mem_filter.mp hy).2]),
      sum_const, nsmul_eq_mul]
  rw [h1]
  simp_rw [hsq, add_mul, one_mul, sum_add_distrib]
  rw [sum_psi_mul_eq_zero ψ hψ hc, add_zero,
    sum_congr rfl fun u _ => by rw [mul_comm c u], sum_char_mul_add χ hχ ψ c, hq.inv]

/-- The shifted quadratic Gauss sum: `Σ_y ψ(c y² + b y) = χ(c) G ψ(-b²/(4c))` for `c ≠ 0`. -/
theorem sum_psi_quad (h2 : (2 : F) ≠ 0) {c : F} (hc : c ≠ 0) (b : F) :
    ∑ y, ψ (c * y ^ 2 + b * y) = χ c * gaussSum χ ψ * ψ (-(b ^ 2 / (4 * c))) := by
  have key : ∀ y, c * y ^ 2 + b * y = c * (y + b / (2 * c)) ^ 2 + -(b ^ 2 / (4 * c)) := by
    intro y
    have h4 : (4 : F) ≠ 0 := by rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
    field_simp
    ring
  simp_rw [key, AddChar.map_add_eq_mul]
  rw [← sum_mul, ← sum_psi_sq χ hχ hq ψ hψ hsq hc]
  congr 1
  exact Fintype.sum_equiv (Equiv.addRight (b / (2 * c))) _ _ fun y => rfl

omit hψ hsq in
/-- `Σ_t χ(t) ψ(α / t) = χ(α) G` for every `α`. -/
theorem sum_char_psi_inv (α : F) : ∑ t, χ t * ψ (α * t⁻¹) = χ α * gaussSum χ ψ := by
  have h : ∑ t, χ t * ψ (α * t⁻¹) = ∑ t, χ t⁻¹ * ψ (t * α) :=
    Fintype.sum_equiv (Equiv.inv F) _ _ fun t => by simp [mul_comm]
  rw [h]
  simp_rw [← MulChar.inv_apply', hq.inv]
  rw [sum_char_mul_add χ hχ ψ α, hq.inv]

omit [Fintype F] [DecidableEq F] hχ hψ hsq in
theorem chi_mul_self {u : F} (hu : u ≠ 0) : χ u * χ u = 1 := by
  rcases hq u with h | h | h
  · have h1 := map_mul χ u u⁻¹
    rw [mul_inv_cancel₀ hu, map_one, h, zero_mul] at h1
    exact absurd h1 one_ne_zero
  · rw [h, one_mul]
  · rw [h]; norm_num

omit [Fintype F] [DecidableEq F] hχ hψ hsq in
theorem chi_inv_eq (u : F) : χ u⁻¹ = χ u := by
  rw [← MulChar.inv_apply', hq.inv]

omit [Fintype F] [DecidableEq F] hχ hψ hsq in
theorem chi_pow_even {n : ℕ} (hn : Even n) {u : F} (hu : u ≠ 0) : χ u ^ n = 1 := by
  obtain ⟨m, rfl⟩ := hn
  rw [← two_mul, pow_mul, sq, chi_mul_self χ hq hu, one_pow]

variable {n : ℕ} (hn : Even n) (h2 : (2 : F) ≠ 0) (a : Fin n → F) (ha : ∀ i, a i ≠ 0) {D : F}
  (hD : D ≠ 0)
include hn h2 ha hD

/-- The factor of one value `t` of the indicator expansion. -/
theorem term_eq (z : Fin n → F) (t : F) :
    (∑ y, ψ (t * y ^ 2 + 1 * y)) * ∏ i, ∑ j, ψ (-(t * D) / a i * j ^ 2 + -z i * j) =
      gaussSum χ ψ ^ (n + 1) * (∏ i, χ (a i)) *
        (χ t * ψ ((∑ i, a i * z i ^ 2 - D) / (4 * D) * t⁻¹)) := by
  by_cases ht : t = 0
  · subst ht
    have : ∑ y : F, ψ (0 * y ^ 2 + 1 * y) = 0 := by
      simpa using sum_psi_mul_eq_zero ψ hψ (one_ne_zero (α := F))
    rw [this, zero_mul, MulChar.map_zero, zero_mul, mul_zero]
  have hc : ∀ i, -(t * D) / a i ≠ 0 := fun i =>
    div_ne_zero (neg_ne_zero.mpr (mul_ne_zero ht hD)) (ha i)
  have h4 : (4 : F) ≠ 0 := by rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  rw [sum_psi_quad χ hχ hq ψ hψ hsq h2 ht]
  simp_rw [sum_psi_quad χ hχ hq ψ hψ hsq h2 (hc _)]
  rw [prod_mul_distrib, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, ← psi_sum]
  have hchi : ∏ i, χ (-(t * D) / a i) = ∏ i, χ (a i) := by
    simp_rw [div_eq_mul_inv, map_mul, chi_inv_eq χ hq]
    rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin,
      chi_pow_even χ hq hn (neg_ne_zero.mpr (mul_ne_zero ht hD)), one_mul]
  have hexp : ∑ i, -((-z i) ^ 2 / (4 * (-(t * D) / a i))) = (∑ i, a i * z i ^ 2) / (4 * D) * t⁻¹ := by
    rw [sum_div, sum_mul]
    refine sum_congr rfl fun i _ => ?_
    have := ha i
    field_simp
  rw [hchi, hexp, mul_comm (χ t * gaussSum χ ψ * _), ← mul_assoc]
  have hy : -((1 : F) ^ 2 / (4 * t)) + (∑ i, a i * z i ^ 2) / (4 * D) * t⁻¹ =
      (∑ i, a i * z i ^ 2 - D) / (4 * D) * t⁻¹ := by
    field_simp
    ring
  rw [← hy, AddChar.map_add_eq_mul, pow_succ]
  ring

/-- The dual cone identity: the inverse Fourier transform of `k ↦ Σ_{y² = D Q*(k)} ψ(y - k·s)` is
`χ(f)` up to the factor `G^(n+2) χ(D Π a_i) / q`. -/
theorem dual_cone (s x : Fin n → F) :
    (Fintype.card F : ℂ) * ∑ k : Fin n → F, ∑ y ∈ univ.filter (fun y : F => y ^ 2 = D * ∑ i, k i ^ 2 / a i),
        ψ (y - ∑ i, k i * (x i + s i)) =
      gaussSum χ ψ ^ (n + 2) * χ (D * ∏ i, a i) * χ (∑ i, a i * (x i + s i) ^ 2 - D) := by
  set z : Fin n → F := fun i => x i + s i with hz
  have expand : ∀ (k : Fin n → F) (y t : F),
      t * (y ^ 2 - D * ∑ i, k i ^ 2 / a i) + (y - ∑ i, k i * z i) =
        (t * y ^ 2 + 1 * y) + ∑ i, (-(t * D) / a i * k i ^ 2 + -z i * k i) := by
    intro k y t
    rw [sum_add_distrib]
    have e1 : ∑ i, -(t * D) / a i * k i ^ 2 = -(t * D) * ∑ i, k i ^ 2 / a i := by
      rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
    have e2 : ∑ i, -z i * k i = -∑ i, k i * z i := by
      rw [← sum_neg_distrib]; exact sum_congr rfl fun i _ => by ring
    rw [e1, e2]
    ring
  calc (Fintype.card F : ℂ) * ∑ k : Fin n → F, ∑ y ∈ univ.filter (fun y : F => y ^ 2 = D * ∑ i, k i ^ 2 / a i),
        ψ (y - ∑ i, k i * (x i + s i))
      = ∑ k : Fin n → F, ∑ y, ∑ t, ψ (t * (y ^ 2 - D * ∑ i, k i ^ 2 / a i)) * ψ (y - ∑ i, k i * z i) := by
        rw [mul_sum]
        refine sum_congr rfl fun k _ => ?_
        rw [sum_filter, mul_sum]
        refine sum_congr rfl fun y _ => ?_
        rw [← sum_mul, AddChar.sum_mulShift _ hψ]
        by_cases h : y ^ 2 = D * ∑ i, k i ^ 2 / a i
        · simp [h, hz]
        · simp [h, sub_eq_zero]
    _ = ∑ t, (∑ y, ψ (t * y ^ 2 + 1 * y)) * ∏ i, ∑ j, ψ (-(t * D) / a i * j ^ 2 + -z i * j) := by
        simp_rw [Fintype.prod_sum, sum_mul_sum, ← psi_sum, ← AddChar.map_add_eq_mul, ← expand]
        conv_lhs => enter [2, k]; rw [sum_comm]
        rw [sum_comm]
        exact sum_congr rfl fun t _ => sum_comm
    _ = gaussSum χ ψ ^ (n + 1) * (∏ i, χ (a i)) * ∑ t, χ t * ψ ((∑ i, a i * z i ^ 2 - D) / (4 * D) * t⁻¹) := by
        rw [mul_sum]
        exact sum_congr rfl fun t _ => term_eq χ hχ hq ψ hψ hsq hn h2 a ha hD z t
    _ = _ := by
        rw [sum_char_psi_inv χ hχ hq ψ, div_eq_mul_inv, map_mul, chi_inv_eq χ hq, map_mul, map_mul,
          map_prod, show (4 : F) = 2 * 2 by norm_num, map_mul, chi_mul_self χ hq h2, pow_succ]
        ring


omit hn h2 ha hD hχ hq hsq in
/-- Orthogonality on `F^n`. -/
theorem sum_psi_dot (c : Fin n → F) :
    ∑ x : Fin n → F, ψ (∑ i, c i * x i) = if c = 0 then (Fintype.card F : ℂ) ^ n else 0 := by
  simp_rw [psi_sum]
  rw [← Fintype.prod_sum (fun i j => ψ (c i * j))]
  have h : ∀ i, ∑ j, ψ (c i * j) = if c i = 0 then (Fintype.card F : ℂ) else 0 := fun i => by
    calc ∑ j, ψ (c i * j) = ∑ j, ψ (j * c i) := sum_congr rfl fun j _ => by rw [mul_comm]
      _ = _ := by rw [AddChar.sum_mulShift _ hψ]; split_ifs <;> simp
  simp_rw [h]
  rw [Fintype.prod_ite_zero]
  simp [funext_iff]

/-- The Fourier coefficient of `χ(f)` at `k`: a sum of at most two characters. -/
theorem fourier_coeff (s k : Fin n → F) :
    gaussSum χ ψ ^ (n + 2) * χ (D * ∏ i, a i) *
        ∑ x : Fin n → F, χ (∑ i, a i * (x i + s i) ^ 2 - D) * ψ (∑ i, k i * x i) =
      (Fintype.card F : ℂ) ^ (n + 1) *
        ∑ y ∈ univ.filter (fun y : F => y ^ 2 = D * ∑ i, k i ^ 2 / a i), ψ (y - ∑ i, k i * s i) := by
  have inner : ∀ (k' : Fin n → F) (y : F),
      ∑ x : Fin n → F, ψ (y - ∑ i, k' i * (x i + s i)) * ψ (∑ i, k i * x i) =
        if k = k' then (Fintype.card F : ℂ) ^ n * ψ (y - ∑ i, k i * s i) else 0 := by
    intro k' y
    have e : ∀ x : Fin n → F, (y - ∑ i, k' i * (x i + s i)) + ∑ i, k i * x i =
        (y - ∑ i, k' i * s i) + ∑ i, (k - k') i * x i := by
      intro x
      simp only [Pi.sub_apply, sub_mul, mul_add, sum_add_distrib, sum_sub_distrib]
      ring
    simp_rw [← AddChar.map_add_eq_mul, e, AddChar.map_add_eq_mul]
    rw [← mul_sum, sum_psi_dot ψ hψ]
    by_cases h : k = k'
    · subst h; simp [mul_comm]
    · simp [sub_eq_zero, h]
  calc _ = ∑ x : Fin n → F, ((Fintype.card F : ℂ) * ∑ k' : Fin n → F,
          ∑ y ∈ univ.filter (fun y : F => y ^ 2 = D * ∑ i, k' i ^ 2 / a i),
            ψ (y - ∑ i, k' i * (x i + s i))) * ψ (∑ i, k i * x i) := by
        rw [mul_sum]
        refine sum_congr rfl fun x _ => ?_
        rw [dual_cone χ hχ hq ψ hψ hsq hn h2 a ha hD s x]
        ring
    _ = (Fintype.card F : ℂ) * ∑ k' : Fin n → F,
          ∑ y ∈ univ.filter (fun y : F => y ^ 2 = D * ∑ i, k' i ^ 2 / a i),
            ∑ x : Fin n → F, ψ (y - ∑ i, k' i * (x i + s i)) * ψ (∑ i, k i * x i) := by
        simp_rw [mul_assoc, sum_mul]
        rw [← mul_sum, sum_comm]
        congr 1
        refine sum_congr rfl fun k' _ => ?_
        rw [sum_comm]
    _ = _ := by
        simp_rw [inner]
        rw [Fintype.sum_eq_single k fun x hx => sum_eq_zero fun y _ => by simp [Ne.symm hx]]
        simp only [ite_true]
        rw [← mul_sum, ← mul_assoc, pow_succ']


end Gauss

/-! ### The line through a measured direction -/

omit [Fintype F] [DecidableEq F] in
/-- On the line `k = λ k₀`, `λ ≠ 0`, with `r² = D Q*(k₀)`, `r ≠ 0`, the coefficient is
`ψ(λ (r - k₀·s)) + ψ(λ (-r - k₀·s))`. -/
theorem line_coeff [Fintype F] [DecidableEq F] (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ) {n : ℕ}
    (a : Fin n → F) (D : F) (s k₀ : Fin n → F) {r l : F} (hr : r ^ 2 = D * ∑ i, k₀ i ^ 2 / a i)
    (hr0 : r ≠ 0) (hl : l ≠ 0) :
    ∑ y ∈ univ.filter (fun y : F => y ^ 2 = D * ∑ i, (l * k₀ i) ^ 2 / a i), ψ (y - ∑ i, l * k₀ i * s i) =
      ψ (l * (r - ∑ i, k₀ i * s i)) + ψ (l * (-r - ∑ i, k₀ i * s i)) := by
  have hQ : D * ∑ i, (l * k₀ i) ^ 2 / a i = (l * r) ^ 2 := by
    rw [mul_pow, hr, mul_sum, mul_sum, mul_sum]
    exact sum_congr rfl fun i _ => by ring
  have hne : l * r ≠ -(l * r) := by
    intro h
    have : (2 : F) * (l * r) = 0 := by linear_combination h
    exact mul_ne_zero h2 (mul_ne_zero hl hr0) this
  have hset : univ.filter (fun y : F => y ^ 2 = D * ∑ i, (l * k₀ i) ^ 2 / a i) = {l * r, -(l * r)} := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, hQ]
    constructor
    · intro h
      have : (y - l * r) * (y + l * r) = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h1 | h1
      · left; linear_combination h1
      · right; linear_combination h1
    · rintro (h | h) <;> rw [h]; ring
  have hs : ∑ i, l * k₀ i * s i = l * ∑ i, k₀ i * s i := by
    rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
  rw [hset, sum_pair hne, hs]
  congr 1 <;> congr 1 <;> ring

omit [Fintype F] [DecidableEq F] in
/-- Fourier transform over `λ ∈ F^×` of the line state: the amplitude at `w = u` is `q - 2` when `u ≠ v`. -/
theorem line_peak [Fintype F] [DecidableEq F] (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) {u v : F}
    (huv : u ≠ v) :
    ∑ l ∈ univ.erase (0 : F), (ψ (l * u) + ψ (l * v)) * ψ (-(l * u)) = (Fintype.card F : ℂ) - 2 := by
  have h : ∀ l : F, (ψ (l * u) + ψ (l * v)) * ψ (-(l * u)) = 1 + ψ (l * (v - u)) := by
    intro l
    rw [add_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_neg_cancel,
      AddChar.map_zero_eq_one]
    congr 2; ring
  simp_rw [h]
  rw [sum_add_distrib, sum_const, card_erase_of_mem (mem_univ _), card_univ, nsmul_eq_mul, mul_one]
  have hs := AddChar.sum_mulShift (ψ := ψ) (v - u) hψ
  have hvu : v - u ≠ 0 := sub_ne_zero.mpr huv.symm
  simp only [hvu, ↓reduceIte] at hs
  rw [← add_sum_erase _ _ (mem_univ (0 : F))] at hs
  simp only [zero_mul, AddChar.map_zero_eq_one] at hs
  have : ∑ l ∈ univ.erase (0 : F), ψ (l * (v - u)) = -1 := by
    have := hs; push_cast at this ⊢; linear_combination this
  rw [this, Nat.cast_sub (Fintype.card_pos)]
  push_cast
  ring

/-- The equation of one sample, `(w + k₀·s)² = Q_B(k₀)`, is linear in `s` and `M = s sᵀ - B`. -/
theorem sample_linear {R : Type*} [CommRing R] {n : ℕ} (w : R) (k₀ s : Fin n → R)
    (B : Fin n → Fin n → R) :
    (w + ∑ i, k₀ i * s i) ^ 2 - ∑ i, ∑ j, k₀ i * B i j * k₀ j =
      w ^ 2 + 2 * w * ∑ i, k₀ i * s i + ∑ i, ∑ j, k₀ i * (s i * s j - B i j) * k₀ j := by
  have : (∑ i, k₀ i * s i) ^ 2 = ∑ i, ∑ j, k₀ i * (s i * s j) * k₀ j := by
    rw [sq, sum_mul_sum]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  simp_rw [mul_sub, sub_mul, sum_sub_distrib]
  rw [← this]
  ring

/-- If the linear form of a sample vanishes for both signs of the root, then `k₀·s' = 0` and
`k₀ᵀ M' k₀ = 0`; so each sample cuts a fixed nonzero direction of the solution space with probability
at least about one half. -/
theorem both_signs {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {r c u m : K} (hr : r ≠ 0)
    (hp : 2 * (r - c) * u + m = 0) (hm : 2 * (-r - c) * u + m = 0) : u = 0 ∧ m = 0 := by
  have hu : u = 0 := by
    have : (2 * 2 * r) * u = 0 := by linear_combination hp - hm
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero (mul_ne_zero h2 h2) hr)
  refine ⟨hu, ?_⟩
  rw [hu, mul_zero, zero_add] at hp
  exact hp

end LegendreRecon
