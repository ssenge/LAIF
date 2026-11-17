import Mathlib

/-!
# Kernel energies of isotropic finite laws on the sphere

A finite law with atoms `xⱼ` on the sphere of radius `√K` and weights `pⱼ` has normalized inner products
`ρⱼₖ = ⟨xⱼ, xₖ⟩ / K ∈ [-1, 1]`. A rotation-invariant kernel discrepancy evaluates the energy
`∑ⱼ ∑ₖ pⱼ pₖ H(ρⱼₖ)`. If the law has mean zero and identity covariance, then `∑ pⱼ pₖ ρⱼₖ = 0` and
`∑ pⱼ pₖ ρⱼₖ² = 1/K`, whatever the number and position of the atoms. Hence every kernel profile `H` with a
cubic Taylor remainder `C |ρ|³` on `[-1, 1]` gives an energy within `C/K` of `H(0) + H''(0)/(2K)`:
isotropic laws concentrated on few atoms are separated from each other by `O(1/K)` only.

A sharp profile escapes this: if `H ≥ 0` and `H(1) = 1`, the energy of a law with `m` atoms is at least `1/m`.
-/

open Finset

namespace SigregDim

variable {K m : ℕ}

/-- Normalized inner product `⟨x, y⟩ / K`. -/
noncomputable def nip (K : ℕ) (x y : Fin K → ℝ) : ℝ := (∑ i, x i * y i) / K

/-- A finite law on the sphere of radius `√K` with mean zero and identity covariance. -/
structure IsoAtoms (K m : ℕ) (x : Fin m → Fin K → ℝ) (p : Fin m → ℝ) : Prop where
  nonneg : ∀ j, 0 ≤ p j
  sum_one : ∑ j, p j = 1
  sphere : ∀ j, ∑ i, x j i ^ 2 = K
  mean : ∀ i, ∑ j, p j * x j i = 0
  cov : ∀ i l, ∑ j, p j * (x j i * x j l) = if i = l then 1 else 0

/-- Kernel energy `∑ⱼ ∑ₖ pⱼ pₖ H(ρⱼₖ)`. -/
noncomputable def energy (K : ℕ) (x : Fin m → Fin K → ℝ) (p : Fin m → ℝ) (H : ℝ → ℝ) : ℝ :=
  ∑ j, ∑ k, p j * p k * H (nip K (x j) (x k))

lemma sum_pp {p : Fin m → ℝ} (h : ∑ j, p j = 1) : ∑ j, ∑ k, p j * p k = 1 := by
  rw [← Finset.sum_mul_sum, h, one_mul]

/-- Cauchy–Schwarz on the sphere: `|ρ| ≤ 1`. -/
lemma abs_nip_le_one (hK : 0 < K) {x y : Fin K → ℝ} (hx : ∑ i, x i ^ 2 = K)
    (hy : ∑ i, y i ^ 2 = K) : |nip K x y| ≤ 1 := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hcs : (∑ i, x i * y i) ^ 2 ≤ (∑ i, x i ^ 2) * (∑ i, y i ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  rw [hx, hy] at hcs
  unfold nip
  rw [abs_div, abs_of_pos hKr, div_le_one hKr]
  exact abs_le_of_sq_le_sq' (by nlinarith) hKr.le |>.elim (fun h1 h2 => abs_le.2 ⟨h1, h2⟩)

lemma nip_self (hK : 0 < K) {x : Fin K → ℝ} (hx : ∑ i, x i ^ 2 = K) : nip K x x = 1 := by
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  unfold nip
  simp_rw [← sq]
  rw [hx, div_self hKr]

/-- First moment: `∑ pⱼ pₖ ρⱼₖ = 0`. -/
lemma energy_lin {x : Fin m → Fin K → ℝ} {p : Fin m → ℝ} (h : IsoAtoms K m x p) :
    ∑ j, ∑ k, p j * p k * nip K (x j) (x k) = 0 := by
  have e : ∀ j k, p j * p k * nip K (x j) (x k) =
      (∑ i, (p j * x j i) * (p k * x k i)) / K := by
    intro j k
    unfold nip
    rw [mul_div_assoc', Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp_rw [e, ← Finset.sum_div]
  rw [Finset.sum_comm]
  have : ∀ k, ∑ j, ∑ i, p j * x j i * (p k * x k i) =
      ∑ i, (∑ j, p j * x j i) * (p k * x k i) := by
    intro k
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
  simp_rw [this, h.mean, zero_mul, Finset.sum_const_zero, zero_div]

/-- Second moment: `∑ pⱼ pₖ ρⱼₖ² = 1/K`. -/
lemma energy_sq (hK : 0 < K) {x : Fin m → Fin K → ℝ} {p : Fin m → ℝ} (h : IsoAtoms K m x p) :
    ∑ j, ∑ k, p j * p k * nip K (x j) (x k) ^ 2 = 1 / K := by
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have e : ∀ j k, p j * p k * nip K (x j) (x k) ^ 2 =
      (∑ i, ∑ l, (p j * (x j i * x j l)) * (p k * (x k i * x k l))) / (K : ℝ) ^ 2 := by
    intro j k
    unfold nip
    rw [div_pow, mul_div_assoc', sq (∑ i, x j i * x k i), Finset.sum_mul_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  simp_rw [e, ← Finset.sum_div]
  have step : ∑ j, ∑ k, ∑ i, ∑ l, p j * (x j i * x j l) * (p k * (x k i * x k l)) =
      ∑ i, ∑ l, (∑ j, p j * (x j i * x j l)) * (∑ k, p k * (x k i * x k l)) := by
    calc ∑ j, ∑ k, ∑ i, ∑ l, p j * (x j i * x j l) * (p k * (x k i * x k l))
        = ∑ j, ∑ i, ∑ k, ∑ l, p j * (x j i * x j l) * (p k * (x k i * x k l)) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ j, ∑ i, ∑ l, ∑ k, p j * (x j i * x j l) * (p k * (x k i * x k l)) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ l, ∑ k, p j * (x j i * x j l) * (p k * (x k i * x k l)) := Finset.sum_comm
      _ = ∑ i, ∑ l, ∑ j, ∑ k, p j * (x j i * x j l) * (p k * (x k i * x k l)) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ =>
          (Finset.sum_mul_sum _ _ _ _).symm
  rw [step]
  simp_rw [h.cov]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **Blindness of smooth kernel energies.** If `|H ρ - (H₀ + H₁ ρ + c₂ ρ²)| ≤ C |ρ|³` on `[-1, 1]`, the
energy of every isotropic finite law on the sphere lies within `C/K` of `H₀ + c₂/K`. -/
theorem energy_near (hK : 0 < K) {x : Fin m → Fin K → ℝ} {p : Fin m → ℝ} (h : IsoAtoms K m x p)
    {H : ℝ → ℝ} {H₀ H₁ c₂ C : ℝ} (hC : 0 ≤ C)
    (hH : ∀ ρ, |ρ| ≤ 1 → |H ρ - (H₀ + H₁ * ρ + c₂ * ρ ^ 2)| ≤ C * |ρ| ^ 3) :
    |energy K x p H - (H₀ + c₂ / K)| ≤ C / K := by
  set ρ := fun j k => nip K (x j) (x k)
  have hρ : ∀ j k, |ρ j k| ≤ 1 := fun j k => abs_nip_le_one hK (h.sphere j) (h.sphere k)
  have hpp : ∀ j k, 0 ≤ p j * p k := fun j k => mul_nonneg (h.nonneg j) (h.nonneg k)
  have hdecomp : energy K x p H - (H₀ + c₂ / K) =
      ∑ j, ∑ k, p j * p k * (H (ρ j k) - (H₀ + H₁ * ρ j k + c₂ * ρ j k ^ 2)) := by
    have l1 := energy_lin h
    have l2 := energy_sq hK h
    have expand : ∀ j k, p j * p k * (H (ρ j k) - (H₀ + H₁ * ρ j k + c₂ * ρ j k ^ 2)) =
        p j * p k * H (ρ j k) - H₀ * (p j * p k) - H₁ * (p j * p k * ρ j k) -
          c₂ * (p j * p k * ρ j k ^ 2) := by
      intro j k; ring
    simp_rw [expand, Finset.sum_sub_distrib, ← Finset.mul_sum]
    unfold energy
    simp only [ρ] at l1 l2 ⊢
    rw [l1, l2]
    simp only [h.sum_one, mul_one]
    ring
  rw [hdecomp]
  calc |∑ j, ∑ k, p j * p k * (H (ρ j k) - (H₀ + H₁ * ρ j k + c₂ * ρ j k ^ 2))|
      ≤ ∑ j, ∑ k, |p j * p k * (H (ρ j k) - (H₀ + H₁ * ρ j k + c₂ * ρ j k ^ 2))| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ j, ∑ k, C * (p j * p k * ρ j k ^ 2) := by
        refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul, abs_of_nonneg (hpp j k)]
        have h3 : |ρ j k| ^ 3 ≤ ρ j k ^ 2 := by
          rw [← sq_abs (ρ j k), pow_succ]
          have := hρ j k
          nlinarith [abs_nonneg (ρ j k), sq_nonneg (|ρ j k|)]
        calc p j * p k * |H (ρ j k) - (H₀ + H₁ * ρ j k + c₂ * ρ j k ^ 2)|
            ≤ p j * p k * (C * |ρ j k| ^ 3) := mul_le_mul_of_nonneg_left (hH _ (hρ j k)) (hpp j k)
          _ ≤ p j * p k * (C * ρ j k ^ 2) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hC) (hpp j k)
          _ = C * (p j * p k * ρ j k ^ 2) := by ring
    _ = C / K := by
        simp_rw [← Finset.mul_sum]
        rw [show (∑ j, ∑ k, p j * p k * ρ j k ^ 2) = 1 / K from energy_sq hK h]
        ring

/-- Two isotropic finite laws on the sphere have energies within `2C/K` of each other. -/
theorem energy_diff (hK : 0 < K) {m' : ℕ} {x : Fin m → Fin K → ℝ} {p : Fin m → ℝ}
    {y : Fin m' → Fin K → ℝ} {q : Fin m' → ℝ} (hx : IsoAtoms K m x p) (hy : IsoAtoms K m' y q)
    {H : ℝ → ℝ} {H₀ H₁ c₂ C : ℝ} (hC : 0 ≤ C)
    (hH : ∀ ρ, |ρ| ≤ 1 → |H ρ - (H₀ + H₁ * ρ + c₂ * ρ ^ 2)| ≤ C * |ρ| ^ 3) :
    |energy K x p H - energy K y q H| ≤ 2 * C / K := by
  have h1 := energy_near hK hx hC hH
  have h2 := energy_near hK hy hC hH
  calc |energy K x p H - energy K y q H|
      = |(energy K x p H - (H₀ + c₂ / K)) - (energy K y q H - (H₀ + c₂ / K))| := by ring_nf
    _ ≤ |energy K x p H - (H₀ + c₂ / K)| + |energy K y q H - (H₀ + c₂ / K)| := abs_sub _ _
    _ ≤ C / K + C / K := add_le_add h1 h2
    _ = 2 * C / K := by ring

/-- Remainder of a power series with nonnegative coefficients: on `[-1, 1]` the cubic remainder is at most
`(∑ₙ βₙ₊₃) |ρ|³`. -/
theorem remainder_le_of_series {β : ℕ → ℝ} (hβ : ∀ n, 0 ≤ β n) (hs : Summable β) {H : ℝ → ℝ}
    (hH : ∀ ρ, |ρ| ≤ 1 → HasSum (fun n => β n * ρ ^ n) (H ρ)) :
    ∀ ρ, |ρ| ≤ 1 → |H ρ - (β 0 + β 1 * ρ + β 2 * ρ ^ 2)| ≤ (∑' n, β (n + 3)) * |ρ| ^ 3 := by
  intro ρ hρ
  have htail : HasSum (fun n => β (n + 3) * ρ ^ (n + 3)) (H ρ - (β 0 + β 1 * ρ + β 2 * ρ ^ 2)) := by
    have := (hasSum_nat_add_iff' 3).2 (hH ρ hρ)
    simpa [Finset.sum_range_succ, add_assoc] using this
  have hg : HasSum (fun n => β (n + 3) * |ρ| ^ 3) ((∑' n, β (n + 3)) * |ρ| ^ 3) :=
    ((summable_nat_add_iff 3).2 hs).hasSum.mul_right _
  have hbound : ∀ n, |β (n + 3) * ρ ^ (n + 3)| ≤ β (n + 3) * |ρ| ^ 3 := by
    intro n
    rw [abs_mul, abs_of_nonneg (hβ _), abs_pow]
    refine mul_le_mul_of_nonneg_left ?_ (hβ _)
    rw [pow_add]
    calc |ρ| ^ n * |ρ| ^ 3 ≤ 1 * |ρ| ^ 3 :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (abs_nonneg _) hρ) (by positivity)
      _ = |ρ| ^ 3 := one_mul _
  rw [abs_le]
  constructor
  · have := hasSum_le (fun n => (abs_le.1 (hbound n)).1) hg.neg htail
    linarith
  · exact hasSum_le (fun n => (abs_le.1 (hbound n)).2) htail hg

/-- **Sharp energies see atoms.** For any finite law on the sphere with `m` atoms and a profile `H ≥ 0` on
`[-1, 1]` with `H 1 = 1`, the energy is at least `∑ pⱼ² ≥ 1/m`. -/
theorem energy_ge_inv_card (hK : 0 < K) (hm : 0 < m) {x : Fin m → Fin K → ℝ} {p : Fin m → ℝ}
    (hp : ∀ j, 0 ≤ p j) (h1 : ∑ j, p j = 1) (hx : ∀ j, ∑ i, x j i ^ 2 = K) {H : ℝ → ℝ}
    (hH0 : ∀ ρ, |ρ| ≤ 1 → 0 ≤ H ρ) (hH1 : H 1 = 1) :
    1 / (m : ℝ) ≤ energy K x p H := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hdiag : ∑ j, p j ^ 2 ≤ energy K x p H := by
    unfold energy
    refine Finset.sum_le_sum fun j _ => ?_
    have hterm : ∀ k, 0 ≤ p j * p k * H (nip K (x j) (x k)) := fun k =>
      mul_nonneg (mul_nonneg (hp j) (hp k)) (hH0 _ (abs_nip_le_one hK (hx j) (hx k)))
    calc p j ^ 2 = p j * p j * H (nip K (x j) (x j)) := by
          rw [nip_self hK (hx j), hH1]; ring
      _ ≤ ∑ k, p j * p k * H (nip K (x j) (x k)) :=
          Finset.single_le_sum (f := fun k => p j * p k * H (nip K (x j) (x k)))
            (fun k _ => hterm k) (Finset.mem_univ j)
  have hcs : (∑ j, p j) ^ 2 ≤ (Finset.univ : Finset (Fin m)).card * ∑ j, p j ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [h1, Finset.card_univ, Fintype.card_fin] at hcs
  have : 1 / (m : ℝ) ≤ ∑ j, p j ^ 2 := by
    rw [div_le_iff₀ hmr]; linarith
  linarith

end SigregDim
