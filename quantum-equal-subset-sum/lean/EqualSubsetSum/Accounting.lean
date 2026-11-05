import EqualSubsetSum.Filter
import EqualSubsetSum.Model
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Basic

/-!
# The accounting

`SoftO c e` says `c n ≤ C (n + 1)^k 2^{e n}`, that is `c = Õ(2^{e n})`, with a calculus for sums,
products and real powers. With it:

* the balance: `σ = (4 u - 10 a₀) / 7` makes `a₀ + σ` and `σ / 2 + (2/3)(u - a₀ - σ)` equal, both to
  `(4 u - 3 a₀) / 7`, and no other `σ` does better;
* the composition: table, unranking, claw finding, Grover and amplitude amplification, under the
  hypotheses of `EqualSubsetSum.Model`, cost `Õ(2^{L n})` with
  `L = a / 2 + max (a₀ + σ, σ / 2 + (2/3)(u - a₀ - σ))`;
* the probability that a coin succeeds, from the lemmas on the filter and the cap;
* `K = Nat.choose ν ⌊ν/2⌋ = 2^{a₀ n} / poly(n)` when `|ν - a₀ n| ≤ 2`, which is proved;
* the empty label: `a₁ = a₀ = 0` gives `u = (h(p) + 1 - p) / 2`, and `σ = 4 u / 7` gives inner cost
  `4 u / 7 = S(p) = (2/7)(h(p) + 1 - p)`.

The exponents `a` and `u` enter as hypotheses on the probability of a good partition and on the list
sizes. Whether the resulting `L` stays below a given number is not addressed here.
-/

open Finset

namespace EqualSubsetSum

/-! ## The calculus -/

/-- `c n ≤ C (n + 1)^k 2^{e n}` for all `n`. -/
def SoftO (c : ℕ → ℝ) (e : ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ n, c n ≤ C * ((n : ℝ) + 1) ^ k * (2 : ℝ) ^ (e * n)

namespace SoftO

variable {c d : ℕ → ℝ} {e e₁ e₂ : ℝ}

theorem mono (h : SoftO d e) (hcd : ∀ n, c n ≤ d n) : SoftO c e := by
  obtain ⟨C, k, hC, hb⟩ := h
  exact ⟨C, k, hC, fun n => (hcd n).trans (hb n)⟩

theorem congr_exp (h : SoftO c e₁) (he : e₁ = e₂) : SoftO c e₂ := he ▸ h

private theorem term_le {C e e' : ℝ} {k k' : ℕ} (hC : 0 ≤ C) (hk : k ≤ k') (he : e ≤ e') (n : ℕ) :
    C * ((n : ℝ) + 1) ^ k * (2 : ℝ) ^ (e * n) ≤ C * ((n : ℝ) + 1) ^ k' * (2 : ℝ) ^ (e' * n) := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := by positivity
    linarith
  have h2 : ((n : ℝ) + 1) ^ k ≤ ((n : ℝ) + 1) ^ k' := pow_le_pow_right₀ h1 hk
  have h3 : (2 : ℝ) ^ (e * n) ≤ (2 : ℝ) ^ (e' * n) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right he (by positivity))
  have h4 : (0 : ℝ) ≤ (2 : ℝ) ^ (e * n) := by positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_left h2 hC) h3 h4 (by positivity)

theorem exp_mono (h : SoftO c e₁) (he : e₁ ≤ e₂) : SoftO c e₂ := by
  obtain ⟨C, k, hC, hb⟩ := h
  exact ⟨C, k, hC, fun n => (hb n).trans (term_le hC le_rfl he n)⟩

/-- A sum costs the larger exponent. -/
theorem add (hc : SoftO c e₁) (hd : SoftO d e₂) : SoftO (fun n => c n + d n) (max e₁ e₂) := by
  obtain ⟨C₁, k₁, hC₁, h₁⟩ := hc
  obtain ⟨C₂, k₂, hC₂, h₂⟩ := hd
  refine ⟨C₁ + C₂, k₁ + k₂, by linarith, fun n => ?_⟩
  have h3 := (h₁ n).trans (term_le hC₁ (Nat.le_add_right k₁ k₂) (le_max_left e₁ e₂) n)
  have h4 := (h₂ n).trans (term_le hC₂ (Nat.le_add_left k₂ k₁) (le_max_right e₁ e₂) n)
  calc c n + d n ≤ _ := add_le_add h3 h4
    _ = _ := by ring

/-- A product of nonnegative terms adds the exponents. -/
theorem mul (hc : SoftO c e₁) (hd : SoftO d e₂) (hc0 : ∀ n, 0 ≤ c n) (hd0 : ∀ n, 0 ≤ d n) :
    SoftO (fun n => c n * d n) (e₁ + e₂) := by
  obtain ⟨C₁, k₁, hC₁, h₁⟩ := hc
  obtain ⟨C₂, k₂, hC₂, h₂⟩ := hd
  refine ⟨C₁ * C₂, k₁ + k₂, by positivity, fun n => ?_⟩
  have h3 : (2 : ℝ) ^ ((e₁ + e₂) * n) = (2 : ℝ) ^ (e₁ * n) * (2 : ℝ) ^ (e₂ * n) := by
    rw [add_mul, Real.rpow_add (by norm_num)]
  rw [h3, pow_add]
  calc c n * d n ≤ (C₁ * ((n : ℝ) + 1) ^ k₁ * (2 : ℝ) ^ (e₁ * n))
        * (C₂ * ((n : ℝ) + 1) ^ k₂ * (2 : ℝ) ^ (e₂ * n)) :=
        mul_le_mul (h₁ n) (h₂ n) (hd0 n) ((hc0 n).trans (h₁ n))
    _ = _ := by ring

/-- A power `r ∈ [0, 1]` scales the exponent. -/
theorem rpow (hc : SoftO c e) (hc0 : ∀ n, 0 ≤ c n) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    SoftO (fun n => c n ^ r) (r * e) := by
  obtain ⟨C, k, hC, h⟩ := hc
  refine ⟨C ^ r, k, by positivity, fun n => ?_⟩
  have hx : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ k := by
    apply one_le_pow₀
    have : (0 : ℝ) ≤ n := by positivity
    linarith
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (e * n) := by positivity
  have h3 : (((n : ℝ) + 1) ^ k) ^ r ≤ ((n : ℝ) + 1) ^ k := by
    calc (((n : ℝ) + 1) ^ k) ^ r ≤ (((n : ℝ) + 1) ^ k) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx hr1
      _ = _ := Real.rpow_one _
  have h4 : ((2 : ℝ) ^ (e * n)) ^ r = (2 : ℝ) ^ (r * e * n) := by
    rw [← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  calc c n ^ r ≤ (C * ((n : ℝ) + 1) ^ k * (2 : ℝ) ^ (e * n)) ^ r :=
        Real.rpow_le_rpow (hc0 n) (h n) hr0
    _ = C ^ r * (((n : ℝ) + 1) ^ k) ^ r * ((2 : ℝ) ^ (e * n)) ^ r := by
        rw [Real.mul_rpow (by positivity) h2.le, Real.mul_rpow hC (by positivity)]
    _ ≤ C ^ r * ((n : ℝ) + 1) ^ k * (2 : ℝ) ^ (r * e * n) := by
        rw [h4]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by positivity))
          (by positivity)

/-- A square root halves the exponent. -/
theorem sqrt (hc : SoftO c e) (hc0 : ∀ n, 0 ≤ c n) : SoftO (fun n => √(c n)) (e / 2) := by
  have h := rpow hc hc0 (r := 1 / 2) (by norm_num) (by norm_num)
  refine (h.congr_exp (by ring)).mono fun n => ?_
  rw [Real.sqrt_eq_rpow]

/-- Polynomial factors have exponent zero. -/
theorem of_isPoly {π : ℕ → ℝ} (h : IsPoly π) : SoftO π 0 := by
  obtain ⟨C, k, hC, hb⟩ := h
  exact ⟨C, k, hC, fun n => by simpa using hb n⟩

theorem const {x : ℝ} (hx : 0 ≤ x) : SoftO (fun _ => x) 0 :=
  ⟨x, 0, hx, fun n => by simp⟩

theorem exp (e : ℝ) : SoftO (fun n => (2 : ℝ) ^ (e * n)) e :=
  ⟨1, 0, by norm_num, fun n => by simp⟩

end SoftO

/-! ## The balance -/

/-- The cost of the table, `2^{(a₀ + σ) n}`. -/
noncomputable def tableExp (a₀ σ : ℝ) : ℝ := a₀ + σ

/-- The cost of the search, `2^{(σ / 2 + (2/3)(u - a₀ - σ)) n}`. -/
noncomputable def searchExp (u a₀ σ : ℝ) : ℝ := σ / 2 + (2 / 3) * (u - a₀ - σ)

/-- The total exponent `L = a / 2 + max (a₀ + σ, σ / 2 + (2/3)(u - a₀ - σ))`. -/
noncomputable def totalExp (a u a₀ σ : ℝ) : ℝ := a / 2 + max (tableExp a₀ σ) (searchExp u a₀ σ)

/-- The balancing value of `σ`. -/
noncomputable def sigmaStar (u a₀ : ℝ) : ℝ := (4 * u - 10 * a₀) / 7

/-- **The balance.** At `σ = (4 u - 10 a₀) / 7` both inner terms equal `(4 u - 3 a₀) / 7`. -/
theorem balance (u a₀ : ℝ) :
    tableExp a₀ (sigmaStar u a₀) = (4 * u - 3 * a₀) / 7 ∧
      searchExp u a₀ (sigmaStar u a₀) = (4 * u - 3 * a₀) / 7 := by
  unfold tableExp searchExp sigmaStar
  constructor <;> ring

/-- At the balance the total exponent is `a / 2 + (4 u - 3 a₀) / 7`. -/
theorem totalExp_balanced (a u a₀ : ℝ) :
    totalExp a u a₀ (sigmaStar u a₀) = a / 2 + (4 * u - 3 * a₀) / 7 := by
  unfold totalExp
  rw [(balance u a₀).1, (balance u a₀).2, max_self]

/-- The balance is optimal: every `σ` has inner cost at least `(4 u - 3 a₀) / 7`, the first term
increasing and the second decreasing in `σ`. -/
theorem balance_optimal (u a₀ σ : ℝ) :
    (4 * u - 3 * a₀) / 7 ≤ max (tableExp a₀ σ) (searchExp u a₀ σ) := by
  unfold tableExp searchExp
  by_cases h : σ ≤ (4 * u - 10 * a₀) / 7
  · exact le_max_of_le_right (by linarith)
  · exact le_max_of_le_left (by linarith [not_le.mp h])

/-- At the balance the window has exponent `3 (u + a₀) / 7`, so `T ≥ 1` is consistent as soon as
`u + a₀ ≥ 0`. -/
theorem window_exp_balanced (u a₀ : ℝ) :
    u - a₀ - sigmaStar u a₀ = 3 * (u + a₀) / 7 := by
  unfold sigmaStar
  ring

/-! ## The composition -/

variable {G : Primitives} {π Λ : ℕ → ℝ}

/-- The base procedure for a fixed coin: build the table, then search over the residues, each check
being claw finding on two windows with queries through the table. -/
noncomputable def baseCost (G : Primitives) (n : ℕ) (P T J : ℝ) : ℝ :=
  G.table n P + G.grover n J (G.claw n T (G.unrank n))

/-- The total: amplitude amplification over the coin, with success probability `q`. -/
noncomputable def totalCost (G : Primitives) (n : ℕ) (q P T J : ℝ) : ℝ :=
  G.amplify n q (baseCost G n P T J)

theorem baseCost_nonneg (G : Primitives) (n : ℕ) (P T J : ℝ) : 0 ≤ baseCost G n P T J :=
  add_nonneg (G.table_nonneg n P) (G.grover_nonneg n J _)

/-- The base procedure costs at most `π P + 8 π³ J T^{2/3}`. -/
theorem baseCost_le (hπ1 : ∀ n, 1 ≤ π n) (hTb : TableBuild G π Λ) (hUn : Unranking G π)
    (hCl : ClawWindows G π Λ) (hGr : GroverResidues G π Λ) {n : ℕ} {P T J : ℝ} (hP : 1 ≤ P)
    (hT : 1 ≤ T) (hJ : 1 ≤ J) (hPΛ : P ≤ Λ n) (hTΛ : T ≤ Λ n) (hJΛ : J ≤ Λ n) :
    baseCost G n P T J ≤ π n * P + 8 * (π n * π n * π n) * J * T ^ ((2 : ℝ) / 3) := by
  unfold baseCost
  have hπ := hπ1 n
  have hT0 : 1 ≤ T ^ ((2 : ℝ) / 3) := Real.one_le_rpow hT (by norm_num)
  have hU := hUn n
  have hc := hCl n T (G.unrank n) hT hTΛ (G.unrank_nonneg n)
  set c := G.claw n T (G.unrank n) with hcdef
  have hc0 : 0 ≤ c := G.claw_nonneg _ _ _
  have hg := hGr n J c (by linarith) hJΛ hc0
  have hc1 : c + 1 ≤ 4 * (π n * π n) * T ^ ((2 : ℝ) / 3) := by
    have h1 : c ≤ π n * T ^ ((2 : ℝ) / 3) * (π n + 1) :=
      hc.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    have h2 : π n * T ^ ((2 : ℝ) / 3) * (π n + 1) ≤ 2 * (π n * π n) * T ^ ((2 : ℝ) / 3) := by
      have : 0 ≤ π n * T ^ ((2 : ℝ) / 3) := by positivity
      nlinarith
    have h3 : 1 ≤ π n * π n * T ^ ((2 : ℝ) / 3) := by
      have : 1 ≤ π n * π n := by nlinarith
      nlinarith
    linarith
  have hJ1 : J + 1 ≤ 2 * J := by linarith
  have hgr : G.grover n J c ≤ 8 * (π n * π n * π n) * J * T ^ ((2 : ℝ) / 3) := by
    calc G.grover n J c ≤ π n * (J + 1) * (c + 1) := hg
      _ ≤ π n * (2 * J) * (4 * (π n * π n) * T ^ ((2 : ℝ) / 3)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hJ1 (by linarith)) hc1 (by linarith) (by positivity)
      _ = _ := by ring
  exact add_le_add (hTb n P hP hPΛ) hgr

/-- **The composition.** Under the hypotheses of `EqualSubsetSum.Model`, if the modulus bound, the
window and the number of iterations have exponents `eP`, `eT`, `eJ`, and the success probability of
a coin is `2^{-a n} / poly(n)`, the total cost is `Õ(2^{(a / 2 + max (eP, eJ + (2/3) eT)) n})`. -/
theorem total_softO (hπ : IsPoly π) (hπ1 : ∀ n, 1 ≤ π n) (hTb : TableBuild G π Λ)
    (hUn : Unranking G π) (hCl : ClawWindows G π Λ) (hGr : GroverResidues G π Λ)
    (hAA : AmplitudeAmplification G π Λ) {P T J q : ℕ → ℝ}
    (hP : ∀ n, 1 ≤ P n) (hT : ∀ n, 1 ≤ T n) (hJ : ∀ n, 1 ≤ J n) (hq0 : ∀ n, 0 < q n)
    (hq1 : ∀ n, q n ≤ 1) (hPΛ : ∀ n, P n ≤ Λ n) (hTΛ : ∀ n, T n ≤ Λ n) (hJΛ : ∀ n, J n ≤ Λ n)
    (hqΛ : ∀ n, 1 / q n ≤ Λ n) {eP eT eJ a : ℝ} (hPe : SoftO P eP) (hTe : SoftO T eT) (hJe : SoftO J eJ)
    (hqe : SoftO (fun n => 1 / q n) a) :
    SoftO (fun n => totalCost G n (q n) (P n) (T n) (J n))
      (a / 2 + max eP (eJ + (2 / 3) * eT)) := by
  have hπ0 : ∀ n, 0 ≤ π n := fun n => by linarith [hπ1 n]
  have hπe := SoftO.of_isPoly hπ
  have hT0 : ∀ n, 0 ≤ T n := fun n => by linarith [hT n]
  have hJ0 : ∀ n, 0 ≤ J n := fun n => by linarith [hJ n]
  have hP0 : ∀ n, 0 ≤ P n := fun n => by linarith [hP n]
  -- the bound on the base procedure
  have hπ3 : SoftO (fun n => π n * π n * π n) 0 :=
    ((hπe.mul hπe hπ0 hπ0).mul hπe (fun n => mul_nonneg (hπ0 n) (hπ0 n)) hπ0).congr_exp (by ring)
  have hT23 : SoftO (fun n => T n ^ ((2 : ℝ) / 3)) ((2 / 3) * eT) :=
    hTe.rpow hT0 (by norm_num) (by norm_num)
  have hterm1 : SoftO (fun n => π n * P n) eP :=
    (hπe.mul hPe hπ0 hP0).congr_exp (by ring)
  have hc8 : SoftO (fun n => 8 * (π n * π n * π n)) 0 :=
    ((SoftO.const (x := 8) (by norm_num)).mul hπ3 (fun _ => by norm_num)
      (fun n => by have := hπ0 n; positivity)).congr_exp (by ring)
  have hterm2 : SoftO (fun n => 8 * (π n * π n * π n) * J n * T n ^ ((2 : ℝ) / 3))
      (eJ + (2 / 3) * eT) := by
    have h8nn : ∀ n, 0 ≤ 8 * (π n * π n * π n) := fun n => by have := hπ0 n; positivity
    have h1 := (hc8.mul hJe h8nn hJ0).mul hT23 (fun n => mul_nonneg (h8nn n) (hJ0 n))
      (fun n => by have := hT0 n; positivity)
    exact h1.congr_exp (by ring)
  have hB := hterm1.add hterm2
  have hBnn : ∀ n, 0 ≤ π n * P n + 8 * (π n * π n * π n) * J n * T n ^ ((2 : ℝ) / 3) := fun n => by
    have := hπ0 n
    have := hP0 n
    have := hJ0 n
    have := hT0 n
    positivity
  have hqs : SoftO (fun n => √(1 / q n)) (a / 2) :=
    hqe.sqrt fun n => by have := hq0 n; positivity
  have htot := ((((SoftO.const (x := 2) (by norm_num)).mul hπe (fun _ => by norm_num) hπ0).mul hB
    (fun n => mul_nonneg (by norm_num) (hπ0 n)) hBnn).mul hqs
    (fun n => mul_nonneg (mul_nonneg (by norm_num) (hπ0 n)) (hBnn n))
    (fun n => Real.sqrt_nonneg _)).congr_exp
      (e₂ := a / 2 + max eP (eJ + (2 / 3) * eT)) (by ring)
  refine htot.mono fun n => ?_
  have hAAn := (hAA n (q n) (baseCost G n (P n) (T n) (J n)) (hq0 n) (hq1 n) (hqΛ n)
    (baseCost_nonneg _ _ _ _ _)).1
  have hb := baseCost_le hπ1 hTb hUn hCl hGr (n := n) (hP n) (hT n) (hJ n) (hPΛ n) (hTΛ n) (hJΛ n)
  have hB1 : 1 ≤ π n * P n + 8 * (π n * π n * π n) * J n * T n ^ ((2 : ℝ) / 3) := by
    have h1 : 1 ≤ π n * P n := one_le_mul_of_one_le_of_one_le (hπ1 n) (hP n)
    have h2 : (0 : ℝ) ≤ 8 * (π n * π n * π n) * J n * T n ^ ((2 : ℝ) / 3) := by
      have := hπ0 n
      have := hJ0 n
      have := hT0 n
      positivity
    linarith
  have hb1 : baseCost G n (P n) (T n) (J n) + 1
      ≤ 2 * (π n * P n + 8 * (π n * π n * π n) * J n * T n ^ ((2 : ℝ) / 3)) := by linarith
  have hsqrt : (1 : ℝ) / √(q n) = √(1 / q n) := by
    rw [Real.sqrt_div zero_le_one, Real.sqrt_one]
  have hsq0 : 0 ≤ √(1 / q n) := Real.sqrt_nonneg _
  unfold totalCost
  calc G.amplify n (q n) (baseCost G n (P n) (T n) (J n))
      ≤ π n * ((baseCost G n (P n) (T n) (J n) + 1) / √(q n)) := hAAn
    _ = π n * (baseCost G n (P n) (T n) (J n) + 1) * √(1 / q n) := by
        rw [← hsqrt]
        ring
    _ ≤ π n * (2 * (π n * P n + 8 * (π n * π n * π n) * J n * T n ^ ((2 : ℝ) / 3))) * √(1 / q n) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb1 (hπ0 n)) hsq0
    _ = _ := by ring

/-! ## The parameters of the schedule -/

/-- **The size of `K`.** `2^ν ≤ (ν + 1) K` and `K ≤ 2^ν` for `K = Nat.choose ν ⌊ν/2⌋`. -/
theorem choose_half_bounds (ν : ℕ) :
    2 ^ ν ≤ (ν + 1) * ν.choose (ν / 2) ∧ ν.choose (ν / 2) ≤ 2 ^ ν := by
  constructor
  · rw [← Nat.sum_range_choose ν]
    calc ∑ m ∈ range (ν + 1), ν.choose m ≤ ∑ _m ∈ range (ν + 1), ν.choose (ν / 2) :=
          sum_le_sum fun m _ => Nat.choose_le_middle m ν
      _ = (ν + 1) * ν.choose (ν / 2) := by simp
  · rw [← Nat.sum_range_choose ν]
    exact single_le_sum (f := fun m => ν.choose m) (fun _ _ => Nat.zero_le _)
      (mem_range.mpr (by have := Nat.div_le_self ν 2; omega))

/-- **`K = 2^{a₀ n} / poly(n)`.** If `|ν n - a₀ n| ≤ 2`, then `K = Nat.choose ν ⌊ν/2⌋` has exponent
`a₀` and `1 / K` has exponent `-a₀`. -/
theorem softO_choose {ν : ℕ → ℕ} {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hν : ∀ n, |(ν n : ℝ) - a₀ * n| ≤ 2) :
    SoftO (fun n => ((ν n).choose (ν n / 2) : ℝ)) a₀ ∧
      SoftO (fun n => 1 / ((ν n).choose (ν n / 2) : ℝ)) (-a₀) := by
  have hpow : ∀ n, (2 : ℝ) ^ (ν n) = (2 : ℝ) ^ ((ν n : ℝ)) := fun n => (Real.rpow_natCast _ _).symm
  have hup : ∀ n, (ν n : ℝ) ≤ a₀ * n + 2 := fun n => by linarith [(abs_le.mp (hν n)).2]
  have hlo : ∀ n, a₀ * n - 2 ≤ (ν n : ℝ) := fun n => by linarith [(abs_le.mp (hν n)).1]
  constructor
  · refine ⟨4, 0, by norm_num, fun n => ?_⟩
    have h1 : ((ν n).choose (ν n / 2) : ℝ) ≤ (2 : ℝ) ^ (ν n) := by
      exact_mod_cast (choose_half_bounds (ν n)).2
    have h2 : (2 : ℝ) ^ ((ν n : ℝ)) ≤ (2 : ℝ) ^ (a₀ * n + 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (hup n)
    have h3 : (2 : ℝ) ^ (a₀ * n + 2) = 4 * (2 : ℝ) ^ (a₀ * n) := by
      rw [Real.rpow_add (by norm_num), mul_comm]
      norm_num
    rw [hpow] at h1
    simp only [pow_zero, mul_one]
    linarith
  · refine ⟨4 * (a₀ + 3), 1, by positivity, fun n => ?_⟩
    have hk := choose_half_bounds (ν n)
    have h1 : (2 : ℝ) ^ (ν n) ≤ ((ν n : ℝ) + 1) * ((ν n).choose (ν n / 2) : ℝ) := by
      exact_mod_cast hk.1
    have hK : (0 : ℝ) < ((ν n).choose (ν n / 2) : ℝ) := by
      have : 0 < (ν n).choose (ν n / 2) := Nat.choose_pos (Nat.div_le_self _ _)
      exact_mod_cast this
    have hn : (0 : ℝ) ≤ n := by positivity
    have h2 : (2 : ℝ) ^ (a₀ * n - 2) ≤ (2 : ℝ) ^ ((ν n : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (hlo n)
    have h3 : (2 : ℝ) ^ (a₀ * n - 2) = (2 : ℝ) ^ (a₀ * n) / 4 := by
      rw [Real.rpow_sub (by norm_num)]
      norm_num
    have h4 : (2 : ℝ) ^ (-a₀ * n) * (2 : ℝ) ^ (a₀ * n) = 1 := by
      rw [← Real.rpow_add (by norm_num)]
      simp
    have hE : (0 : ℝ) < (2 : ℝ) ^ (a₀ * n) := by positivity
    have hE' : (0 : ℝ) < (2 : ℝ) ^ (-a₀ * n) := by positivity
    rw [hpow] at h1
    have h5 : (2 : ℝ) ^ (a₀ * n) ≤ 4 * (((ν n : ℝ) + 1) * ((ν n).choose (ν n / 2) : ℝ)) := by
      linarith
    have h6 : (ν n : ℝ) + 1 ≤ (a₀ + 3) * ((n : ℝ) + 1) := by
      have := hup n
      nlinarith
    rw [div_le_iff₀ hK, pow_one]
    have h7 : (2 : ℝ) ^ (a₀ * n) ≤ 4 * ((a₀ + 3) * ((n : ℝ) + 1)) * ((ν n).choose (ν n / 2) : ℝ) := by
      refine h5.trans ?_
      have := mul_le_mul_of_nonneg_right h6 hK.le
      linarith
    calc (1 : ℝ) = (2 : ℝ) ^ (-a₀ * n) * (2 : ℝ) ^ (a₀ * n) := h4.symm
      _ ≤ (2 : ℝ) ^ (-a₀ * n) * (4 * ((a₀ + 3) * ((n : ℝ) + 1)) * ((ν n).choose (ν n / 2) : ℝ)) :=
          mul_le_mul_of_nonneg_left h7 hE'.le
      _ = _ := by ring

/-- **The exponents of the schedule.** Let `K`, `1 / K` and `U` have exponents `a₀`, `-a₀` and `u`,
let `s = 2^{σ n}` with `σ ≥ 0`, `P₀ = K s`, `T ≤ c (n + 1) U / P₀ + 1` with `u - a₀ - σ ≥ 0`, and
`J ≤ √(c (n + 1) s) + 1`. Then `2 P₀`, `T` and `J` have exponents `a₀ + σ`, `u - a₀ - σ` and `σ / 2`.
So the rounding `T = ⌈c n U / P₀⌉` and `J = ⌈√(c n s)⌉` is covered. -/
theorem schedule_exponents {K U T J : ℕ → ℝ} {a₀ u σ c : ℝ} (hK0 : ∀ n, 0 < K n)
    (hU0 : ∀ n, 0 ≤ U n) (hσ : 0 ≤ σ) (hc : 0 ≤ c) (hTexp : 0 ≤ u - a₀ - σ) (hKe : SoftO K a₀)
    (hKi : SoftO (fun n => 1 / K n) (-a₀)) (hUe : SoftO U u)
    (hT : ∀ n, T n ≤ c * ((n : ℝ) + 1) * U n / (K n * (2 : ℝ) ^ (σ * n)) + 1)
    (hJ : ∀ n, J n ≤ √(c * ((n : ℝ) + 1) * (2 : ℝ) ^ (σ * n)) + 1) :
    SoftO (fun n => 2 * (K n * (2 : ℝ) ^ (σ * n))) (a₀ + σ) ∧
      SoftO T (u - a₀ - σ) ∧ SoftO J (σ / 2) := by
  have hE : ∀ e : ℝ, ∀ n : ℕ, (0 : ℝ) ≤ (2 : ℝ) ^ (e * n) := fun e n => by positivity
  have hKnn : ∀ n, 0 ≤ K n := fun n => (hK0 n).le
  have hpoly : SoftO (fun n : ℕ => c * ((n : ℝ) + 1)) 0 :=
    ⟨c, 1, hc, fun n => by simp⟩
  have hpnn : ∀ n : ℕ, 0 ≤ c * ((n : ℝ) + 1) := fun n => by positivity
  refine ⟨?_, ?_, ?_⟩
  · have h1 := hKe.mul (SoftO.exp σ) hKnn (hE σ)
    have h2 := (SoftO.const (x := 2) (by norm_num)).mul h1 (fun _ => by norm_num)
      (fun n => mul_nonneg (hKnn n) (hE σ n))
    exact h2.congr_exp (by ring)
  · have h1 := (hpoly.mul hUe hpnn hU0).mul hKi (fun n => mul_nonneg (hpnn n) (hU0 n))
      (fun n => by have := hK0 n; positivity)
    have h2 := h1.mul (SoftO.exp (-σ)) (fun n => by
      have := hpnn n
      have := hU0 n
      have := hK0 n
      positivity) (hE (-σ))
    have h3 : SoftO (fun n : ℕ => c * ((n : ℝ) + 1) * U n / (K n * (2 : ℝ) ^ (σ * n)))
        (u - a₀ - σ) := by
      refine (h2.congr_exp (by ring)).mono fun n => ?_
      have hinv : (2 : ℝ) ^ (-σ * n) = 1 / (2 : ℝ) ^ (σ * n) := by
        rw [neg_mul, Real.rpow_neg (by norm_num), one_div]
      have hk := hK0 n
      have hs : (0 : ℝ) < (2 : ℝ) ^ (σ * n) := by positivity
      rw [hinv]
      apply le_of_eq
      field_simp
    have h4 := h3.add (SoftO.const (x := 1) (by norm_num))
    exact (h4.congr_exp (max_eq_left hTexp)).mono hT
  · have h1 := hpoly.mul (SoftO.exp σ) hpnn (hE σ)
    have h2 := h1.sqrt (fun n => mul_nonneg (hpnn n) (hE σ n))
    have h3 := h2.add (SoftO.const (x := 1) (by norm_num))
    have hmax : max ((0 + σ) / 2) 0 = σ / 2 := by
      rw [zero_add]
      exact max_eq_left (by linarith)
    exact (h3.congr_exp hmax).mono hJ

/-- **The total exponent.** Under the hypotheses of `EqualSubsetSum.Model` and for the schedule of
`schedule_exponents`, with `T, J ≥ 1`, and a success probability `q` of a coin with `1 / q` of exponent
`a`, the total cost has exponent
`L = a / 2 + max (a₀ + σ, σ / 2 + (2/3)(u - a₀ - σ))`. -/
theorem total_exponent (hπ : IsPoly π) (hπ1 : ∀ n, 1 ≤ π n) (hTb : TableBuild G π Λ)
    (hUn : Unranking G π) (hCl : ClawWindows G π Λ) (hGr : GroverResidues G π Λ)
    (hAA : AmplitudeAmplification G π Λ) {K U T J q : ℕ → ℝ} {a a₀ u σ c : ℝ} (hK1 : ∀ n, 1 ≤ K n)
    (hU0 : ∀ n, 0 ≤ U n) (hσ : 0 ≤ σ) (hc : 0 ≤ c) (hTexp : 0 ≤ u - a₀ - σ) (hKe : SoftO K a₀)
    (hKi : SoftO (fun n => 1 / K n) (-a₀)) (hUe : SoftO U u)
    (hT : ∀ n, T n ≤ c * ((n : ℝ) + 1) * U n / (K n * (2 : ℝ) ^ (σ * n)) + 1) (hT1 : ∀ n, 1 ≤ T n)
    (hJ : ∀ n, J n ≤ √(c * ((n : ℝ) + 1) * (2 : ℝ) ^ (σ * n)) + 1) (hJ1 : ∀ n, 1 ≤ J n)
    (hq0 : ∀ n, 0 < q n) (hq1 : ∀ n, q n ≤ 1) (hqe : SoftO (fun n => 1 / q n) a)
    (hPΛ : ∀ n : ℕ, 2 * (K n * (2 : ℝ) ^ (σ * n)) ≤ Λ n)
    (hTΛ : ∀ n, T n ≤ Λ n) (hJΛ : ∀ n, J n ≤ Λ n) (hqΛ : ∀ n, 1 / q n ≤ Λ n) :
    SoftO (fun n => totalCost G n (q n) (2 * (K n * (2 : ℝ) ^ (σ * n))) (T n) (J n))
      (totalExp a u a₀ σ) := by
  have hK0 : ∀ n, 0 < K n := fun n => by linarith [hK1 n]
  obtain ⟨hP, hTe, hJe⟩ := schedule_exponents hK0 hU0 hσ hc hTexp hKe hKi hUe hT hJ
  have hP1 : ∀ n : ℕ, 1 ≤ 2 * (K n * (2 : ℝ) ^ (σ * n)) := fun n => by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (σ * n) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg hσ (by positivity))
    have h2 : 1 ≤ K n * (2 : ℝ) ^ (σ * n) := one_le_mul_of_one_le_of_one_le (hK1 n) h1
    linarith
  have h := total_softO hπ hπ1 hTb hUn hCl hGr hAA
    (P := fun n => 2 * (K n * (2 : ℝ) ^ (σ * n))) (T := T) (J := J) (q := q)
    hP1 hT1 hJ1 hq0 hq1 hPΛ hTΛ hJΛ hqΛ hP hTe hJe hqe
  exact h.congr_exp (by simp [totalExp, tableExp, searchExp])

/-- **The total exponent at the balance.** With `σ = (4 u - 10 a₀) / 7`, assumed nonnegative, the total
cost has exponent `a / 2 + (4 u - 3 a₀) / 7`. -/
theorem total_exponent_balanced (hπ : IsPoly π) (hπ1 : ∀ n, 1 ≤ π n) (hTb : TableBuild G π Λ)
    (hUn : Unranking G π) (hCl : ClawWindows G π Λ) (hGr : GroverResidues G π Λ)
    (hAA : AmplitudeAmplification G π Λ) {K U T J q : ℕ → ℝ} {a a₀ u c : ℝ} (hK1 : ∀ n, 1 ≤ K n)
    (hU0 : ∀ n, 0 ≤ U n) (hσ : 0 ≤ sigmaStar u a₀) (hc : 0 ≤ c) (hua : 0 ≤ u + a₀)
    (hKe : SoftO K a₀) (hKi : SoftO (fun n => 1 / K n) (-a₀)) (hUe : SoftO U u)
    (hT : ∀ n, T n ≤ c * ((n : ℝ) + 1) * U n / (K n * (2 : ℝ) ^ (sigmaStar u a₀ * n)) + 1)
    (hT1 : ∀ n, 1 ≤ T n)
    (hJ : ∀ n, J n ≤ √(c * ((n : ℝ) + 1) * (2 : ℝ) ^ (sigmaStar u a₀ * n)) + 1)
    (hJ1 : ∀ n, 1 ≤ J n)
    (hq0 : ∀ n, 0 < q n) (hq1 : ∀ n, q n ≤ 1) (hqe : SoftO (fun n => 1 / q n) a)
    (hPΛ : ∀ n : ℕ, 2 * (K n * (2 : ℝ) ^ (sigmaStar u a₀ * n)) ≤ Λ n)
    (hTΛ : ∀ n, T n ≤ Λ n) (hJΛ : ∀ n, J n ≤ Λ n) (hqΛ : ∀ n, 1 / q n ≤ Λ n) :
    SoftO (fun n => totalCost G n (q n) (2 * (K n * (2 : ℝ) ^ (sigmaStar u a₀ * n))) (T n) (J n))
      (a / 2 + (4 * u - 3 * a₀) / 7) := by
  have hTexp : 0 ≤ u - a₀ - sigmaStar u a₀ := by
    rw [window_exp_balanced]
    positivity
  have h := total_exponent hπ hπ1 hTb hUn hCl hGr hAA hK1 hU0 hσ hc hTexp hKe hKi hUe hT hT1 hJ hJ1
    hq0 hq1 hqe hPΛ hTΛ hJΛ hqΛ
  exact h.congr_exp (totalExp_balanced a u a₀)

/-! ## The empty label -/

/-- The binary entropy `h(p)`, in bits. -/
noncomputable def binEnt (p : ℝ) : ℝ := -(p * Real.logb 2 p) - (1 - p) * Real.logb 2 (1 - p)

/-- The entropy of three weights, in bits. -/
noncomputable def ent3 (x y z : ℝ) : ℝ :=
  -(x * Real.logb 2 x) - (y * Real.logb 2 y) - (z * Real.logb 2 z)

/-- The exponent `u = c_A + c_B H(b₁ / c_B, b₀ / c_B, b₁ / c_B)` of the lists, for an array with
`c_A = 2 a₁ + a₀` and `c_B = 2 b₁ + b₀`. -/
noncomputable def listExp (a₁ a₀ b₁ b₀ : ℝ) : ℝ :=
  (2 * a₁ + a₀) + (2 * b₁ + b₀) *
    ent3 (b₁ / (2 * b₁ + b₀)) (b₀ / (2 * b₁ + b₀)) (b₁ / (2 * b₁ + b₀))

/-- `S(p) = (2/7)(h(p) + 1 - p)`. -/
noncomputable def emptyExp (p : ℝ) : ℝ := (2 / 7) * (binEnt p + 1 - p)

/-- **The list exponent of the empty label.** With `a₁ = a₀ = 0`, the conditions `4 b₁ = 1 - p` and
`2 b₀ = p` give `u = (h(p) + 1 - p) / 2`, for `p < 1`. -/
theorem listExp_empty {p : ℝ} (hp : p < 1) :
    listExp 0 0 ((1 - p) / 4) (p / 2) = (binEnt p + 1 - p) / 2 := by
  have hq : 1 - p ≠ 0 := by linarith
  have hc : 2 * ((1 - p) / 4) + p / 2 = 1 / 2 := by ring
  have h1 : (1 - p) / 4 / (1 / 2) = (1 - p) / 2 := by ring
  have h2 : p / 2 / (1 / 2) = p := by ring
  have hlog : Real.logb 2 ((1 - p) / 2) = Real.logb 2 (1 - p) - 1 := by
    rw [Real.logb_div hq (by norm_num), Real.logb_self_eq_one (by norm_num)]
  unfold listExp ent3 binEnt
  rw [hc, h1, h2, hlog]
  ring

/-- **The exponent of the empty label.** For `a₀ = 0` and `u = (h(p) + 1 - p) / 2`, the balance is
`σ = 4 u / 7`, both inner terms equal `4 u / 7`, and this is
`S(p) = (2/7)(h(p) + 1 - p)`. With `a = 0` this is the total exponent. -/
theorem empty_label_exponent (p : ℝ) :
    let u := (binEnt p + 1 - p) / 2
    sigmaStar u 0 = 4 * u / 7 ∧ tableExp 0 (4 * u / 7) = 4 * u / 7 ∧
      searchExp u 0 (4 * u / 7) = 4 * u / 7 ∧ 4 * u / 7 = emptyExp p ∧
      totalExp 0 u 0 (4 * u / 7) = emptyExp p := by
  intro u
  have hu : u = (binEnt p + 1 - p) / 2 := rfl
  have h1 : sigmaStar u 0 = 4 * u / 7 := by
    unfold sigmaStar
    ring
  have h2 : tableExp 0 (4 * u / 7) = 4 * u / 7 := by
    unfold tableExp
    ring
  have h3 : searchExp u 0 (4 * u / 7) = 4 * u / 7 := by
    unfold searchExp
    ring
  have h4 : 4 * u / 7 = emptyExp p := by
    unfold emptyExp
    rw [hu]
    ring
  refine ⟨h1, h2, h3, h4, ?_⟩
  unfold totalExp
  rw [h2, h3, max_self, h4]
  ring

/-- `S(1/3) = (2/7) log₂ 3`. -/
theorem emptyExp_one_third : emptyExp (1 / 3) = (2 / 7) * Real.logb 2 3 := by
  have h3 : Real.logb 2 (1 / 3) = - Real.logb 2 3 := by
    rw [one_div, Real.logb_inv]
  have h4 : Real.logb 2 (2 / 3) = 1 - Real.logb 2 3 := by
    rw [Real.logb_div (by norm_num) (by norm_num), Real.logb_self_eq_one (by norm_num)]
  have h5 : (1 : ℝ) - 1 / 3 = 2 / 3 := by norm_num
  unfold emptyExp binEnt
  rw [h5, h3, h4]
  ring

/-- **The total cost of the empty label.** With `K = 1`, `U` of exponent `u = (h(p) + 1 - p) / 2 ≥ 0`
and `σ = 4 u / 7`, and a success probability `q` of a coin with `1 / q` of exponent `0`, the total
cost has exponent `S(p)`. -/
theorem total_exponent_empty (hπ : IsPoly π) (hπ1 : ∀ n, 1 ≤ π n) (hTb : TableBuild G π Λ)
    (hUn : Unranking G π) (hCl : ClawWindows G π Λ) (hGr : GroverResidues G π Λ)
    (hAA : AmplitudeAmplification G π Λ) {U T J q : ℕ → ℝ} {p c : ℝ}
    (hu : 0 ≤ (binEnt p + 1 - p) / 2) (hU0 : ∀ n, 0 ≤ U n) (hc : 0 ≤ c)
    (hUe : SoftO U ((binEnt p + 1 - p) / 2))
    (hT : ∀ n, T n ≤ c * ((n : ℝ) + 1) * U n /
      (1 * (2 : ℝ) ^ (4 * ((binEnt p + 1 - p) / 2) / 7 * n)) + 1) (hT1 : ∀ n, 1 ≤ T n)
    (hJ : ∀ n, J n ≤ √(c * ((n : ℝ) + 1) * (2 : ℝ) ^ (4 * ((binEnt p + 1 - p) / 2) / 7 * n)) + 1)
    (hJ1 : ∀ n, 1 ≤ J n)
    (hq0 : ∀ n, 0 < q n) (hq1 : ∀ n, q n ≤ 1) (hqe : SoftO (fun n => 1 / q n) 0)
    (hPΛ : ∀ n : ℕ, 2 * (1 * (2 : ℝ) ^ (4 * ((binEnt p + 1 - p) / 2) / 7 * n)) ≤ Λ n)
    (hTΛ : ∀ n, T n ≤ Λ n) (hJΛ : ∀ n, J n ≤ Λ n) (hqΛ : ∀ n, 1 / q n ≤ Λ n) :
    SoftO (fun n => totalCost G n (q n)
        (2 * (1 * (2 : ℝ) ^ (4 * ((binEnt p + 1 - p) / 2) / 7 * n))) (T n) (J n))
      (emptyExp p) := by
  have h := total_exponent (K := fun _ => 1) (U := U) (T := T) (J := J) (q := q) (a := 0) (a₀ := 0)
    (u := (binEnt p + 1 - p) / 2) (σ := 4 * ((binEnt p + 1 - p) / 2) / 7) (c := c)
    hπ hπ1 hTb hUn hCl hGr hAA (fun _ => le_rfl) hU0 (by positivity) hc (by linarith)
    (SoftO.const (by norm_num)) ((SoftO.const (x := 1 / 1) (by norm_num)).congr_exp (by simp)) hUe
    hT hT1 hJ hJ1 hq0 hq1 hqe hPΛ hTΛ hJΛ hqΛ
  exact h.congr_exp (empty_label_exponent p).2.2.2.2

/-! ## The probability of a good coin -/

/-- **The search succeeds for a uniform `j`.** If the marked fraction `φ` satisfies `J² φ ≥ 1`, the
mean over `j < J` of the success probability is at least `1/4 - ε`. -/
theorem grover_uniform {ε : ℕ → ℝ} (hG : GroverSuccess G ε Λ) (n : ℕ) {φ : ℝ} {J : ℕ}
    (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) (hJ : 1 ≤ (J : ℝ) ^ 2 * φ) (hJΛ : (J : ℝ) ≤ Λ n) :
    (1 : ℝ) / 4 - ε n ≤ mean (range J) (G.groverSucc n φ) := by
  have h := grover_average hφ0 hφ1 hJ
  have hJpos : (0 : ℝ) < #(range J) := by
    rw [card_range]
    rcases Nat.eq_zero_or_pos J with rfl | h
    · norm_num at hJ
    · exact_mod_cast h
  unfold mean at h ⊢
  rw [le_div_iff₀ hJpos] at h ⊢
  have h2 : ∑ j ∈ range J, (groverProb φ j - ε n) ≤ ∑ j ∈ range J, G.groverSucc n φ j :=
    sum_le_sum fun j hj => hG n φ j hφ0.le hφ1
      (le_trans (by exact_mod_cast (mem_range.mp hj).le) hJΛ)
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul] at h2
  nlinarith

/-- **The coin.** The three independent choices of the coin: the partition, the prime and the number
of iterations. If a fraction `q` of partitions is good, for a good partition at least `3/4` of the
primes are good, and for those the mean success over `j` is at least `β`, then the mean success over
all coins is at least `q (3/4) β`. -/
theorem coin_success {Lab Mod Itr : Type*} (ΩL : Finset Lab) (ΩP : Finset Mod) (Ωj : Finset Itr)
    (good : Lab → Prop) (goodP : Lab → Mod → Prop) (succ : Lab → Mod → Itr → ℝ) {q β : ℝ}
    (hq0 : 0 ≤ q) (hβ0 : 0 ≤ β)
    (hsucc : ∀ x₁ ∈ ΩL, ∀ x₂ ∈ ΩP, ∀ x₃ ∈ Ωj, 0 ≤ succ x₁ x₂ x₃)
    (hgood : q ≤ prob ΩL good)
    (hP : ∀ x₁ ∈ ΩL, good x₁ → (3 : ℝ) / 4 ≤ prob ΩP (goodP x₁))
    (hj : ∀ x₁ ∈ ΩL, good x₁ → ∀ x₂ ∈ ΩP, goodP x₁ x₂ → β ≤ mean Ωj (succ x₁ x₂)) :
    q * ((3 / 4) * β) ≤ mean (ΩL ×ˢ (ΩP ×ˢ Ωj)) (fun x => succ x.1 x.2.1 x.2.2) := by
  refine mean_chain ΩL (ΩP ×ˢ Ωj) good (fun x₁ y => succ x₁ y.1 y.2) hgood hq0
    (by positivity) ?_ ?_
  · rintro x₁ h₁ ⟨x₂, x₃⟩ hy
    simp only [mem_product] at hy
    exact hsucc x₁ h₁ x₂ hy.1 x₃ hy.2
  intro x₁ h₁ hg
  exact mean_chain ΩP Ωj (goodP x₁) (fun x₂ y => succ x₁ x₂ y) (hP x₁ h₁ hg)
    (by norm_num) hβ0 (fun x₂ h₂ x₃ h₃ => hsucc x₁ h₁ x₂ h₂ x₃ h₃) (hj x₁ h₁ hg)

/-- A constant factor in the success probability does not change its exponent. -/
theorem softO_inv_const {q : ℕ → ℝ} {a κ : ℝ} (hκ : 0 < κ) (hq : ∀ n, 0 < q n)
    (hqe : SoftO (fun n => 1 / q n) a) : SoftO (fun n => 1 / (q n * κ)) a := by
  have h := (SoftO.const (x := 1 / κ) (by positivity)).mul hqe (fun _ => by positivity)
    (fun n => by have := hq n; positivity)
  refine (h.congr_exp (by ring)).mono fun n => ?_
  have := hq n
  apply le_of_eq
  field_simp

/-! ## The parameters of the filter -/

/-- With `PrimeCount`, the primes of `[P₀, 2 P₀]` have `PrimeHit` with `δ = r C log₂ P₀ / P₀`, for a
bound `B < P₀^{r + 1}` on the differences. -/
theorem primeHit_of_primeCount {C : ℝ} (hC : PrimeCount C) {P₀ r : ℕ} (hP₀ : 2 ≤ P₀) {B : ℤ}
    (hB : B < (P₀ : ℤ) ^ (r + 1)) :
    PrimeHit ((Icc P₀ (2 * P₀)).filter Nat.Prime) B
      ((r : ℝ) * (C * (Nat.log 2 P₀ : ℝ)) / P₀) := by
  set Ps := (Icc P₀ (2 * P₀)).filter Nat.Prime with hPs
  have hcount := hC P₀ hP₀
  rw [← hPs] at hcount
  have hP₀r : (0 : ℝ) < P₀ := by exact_mod_cast (by omega : 0 < P₀)
  have hpos : 0 < #Ps := by
    rcases Nat.eq_zero_or_pos #Ps with h0 | h
    · rw [h0] at hcount
      simp only [Nat.cast_zero, mul_zero] at hcount
      linarith
    · exact h
  have hhit := primeHit_of_card (Ps := Ps)
    (fun P hP => (mem_filter.mp hP).2) (P₀ := P₀) (r := r) (N := #Ps)
    (fun P hP => (mem_Icc.mp (mem_filter.mp hP).1).1) (by omega) hpos le_rfl hB
  intro d hd hdB
  have h1 := hhit d hd hdB
  have hpr : (0 : ℝ) < #Ps := by exact_mod_cast hpos
  have h2 : (r : ℝ) / #Ps * #Ps = r := by field_simp
  have h3 : (r : ℝ) ≤ (r : ℝ) * (C * (Nat.log 2 P₀ : ℝ)) / P₀ * #Ps := by
    have h4 : (r : ℝ) * P₀ ≤ (r : ℝ) * (C * (Nat.log 2 P₀ : ℝ) * #Ps) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    have h5 : (r : ℝ) * (C * (Nat.log 2 P₀ : ℝ)) / P₀ * #Ps
        = (r : ℝ) * (C * (Nat.log 2 P₀ : ℝ) * #Ps) / P₀ := by ring
    rw [h5, le_div_iff₀ hP₀r]
    exact h4
  rw [h2] at h1
  exact h1.trans h3

/-- The parameters of the filter at `P₀ = K s`, with `s ≥ 1` and `δ = w / P₀`: `K δ ≤ w`, so `b = w`
works, and the size `T = 64 w U / P₀` satisfies `64 U δ ≤ T`. In the setting of the lemma `w` is
`r C log₂ P₀ = O(n)`. -/
theorem filter_parameters {K s w U : ℝ} (hK : 0 < K) (hs : 1 ≤ s) (hw : 0 ≤ w) :
    K * (w / (K * s)) ≤ w ∧ 64 * U * (w / (K * s)) ≤ 64 * w * U / (K * s) := by
  have hs0 : 0 < s := by linarith
  constructor
  · have h1 : K * (w / (K * s)) = w / s := by field_simp
    rw [h1]
    exact div_le_self hw hs
  · apply le_of_eq
    ring

end EqualSubsetSum
