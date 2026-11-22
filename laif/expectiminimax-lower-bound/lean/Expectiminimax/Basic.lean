import Mathlib.Tactic

/-!
# Expectiminimax lower bound: the combinatorial part

The hard instance has Boolean leaves, OR at maximum nodes, AND at minimum nodes, and at a chance
node exactly `t` or exactly `t + Δ` high children. This file proves that every node takes one of two
values, computes the gap at a chance node, checks the choice of the parameters, and proves the
arithmetic behind the weighted adversary bound of the exact-weight function.
-/

namespace Expectiminimax

open Finset

variable {d : ℕ}

/-- If every child takes the value `l` or `h` with `l ≤ h`, the maximum takes the value `h` exactly
when some child does, and `l` otherwise. -/
theorem max_two (f : Fin d → ℚ) (hne : (univ : Finset (Fin d)).Nonempty) (l h : ℚ) (hlh : l ≤ h)
    (hf : ∀ i, f i = l ∨ f i = h) :
    univ.sup' hne f = (if ∃ i, f i = h then h else l) := by
  obtain ⟨j, -, hj⟩ := exists_mem_eq_sup' hne f
  split_ifs with hex
  · obtain ⟨i, hi⟩ := hex
    apply le_antisymm
    · exact sup'_le hne f (fun k _ => by rcases hf k with hk | hk <;> rw [hk] <;> linarith)
    · rw [← hi]; exact le_sup' f (mem_univ i)
  · push_neg at hex
    rw [hj]; rcases hf j with hk | hk
    · exact hk
    · exact absurd hk (hex j)

/-- The minimum takes the value `l` exactly when some child does, and `h` otherwise. -/
theorem min_two (f : Fin d → ℚ) (hne : (univ : Finset (Fin d)).Nonempty) (l h : ℚ) (hlh : l ≤ h)
    (hf : ∀ i, f i = l ∨ f i = h) :
    univ.inf' hne f = (if ∃ i, f i = l then l else h) := by
  obtain ⟨j, -, hj⟩ := exists_mem_eq_inf' hne f
  split_ifs with hex
  · obtain ⟨i, hi⟩ := hex
    apply le_antisymm
    · rw [← hi]; exact inf'_le f (mem_univ i)
    · exact le_inf' hne f (fun k _ => by rcases hf k with hk | hk <;> rw [hk] <;> linarith)
  · push_neg at hex
    rw [hj]; rcases hf j with hk | hk
    · exact absurd hk (hex j)
    · exact hk

/-- A chance node with `k` high children takes the value `l + (h - l) k / d`. -/
theorem mean_two (f : Fin d → ℚ) (hd : 0 < d) (l h : ℚ) (hf : ∀ i, f i = l ∨ f i = h) :
    (∑ i, f i) / d = l + (h - l) * (univ.filter (fun i => f i = h)).card / d := by
  have key : ∀ i, f i = l + (h - l) * (if f i = h then 1 else 0) := by
    intro i; rcases hf i with hi | hi
    · by_cases hlh : l = h
      · simp [hi, hlh]
      · have : f i ≠ h := by rw [hi]; exact hlh
        rw [if_neg this, hi]; ring
    · simp [hi]
  have hsum : ∑ i, f i = d * l + (h - l) * (univ.filter (fun i => f i = h)).card := by
    rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_boole]
    simp
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [hsum]; field_simp

/-- The two values of a chance node layer with parameters `t` and `t + Δ` differ by
`(h - l) Δ / d`. -/
theorem chance_gap (l h : ℚ) (t Δ : ℕ) (hd : 0 < d) :
    (l + (h - l) * ((t + Δ : ℕ) : ℚ) / d) - (l + (h - l) * (t : ℚ) / d) = (h - l) * Δ / d := by
  push_cast; ring

/-- The two root values of the layered instance: start from `(0, 1)` at the leaves and apply the
chance layers from the bottom; deterministic layers keep the pair. -/
def twoValues (d : ℕ) : List (ℕ × ℕ) → ℚ × ℚ
  | [] => (0, 1)
  | (t, Δ) :: rest =>
      let p := twoValues d rest
      (p.1 + (p.2 - p.1) * t / d, p.1 + (p.2 - p.1) * (t + Δ) / d)

/-- The root gap is the product of `Δ_j / d` over the chance layers. -/
theorem twoValues_gap (L : List (ℕ × ℕ)) :
    (twoValues d L).2 - (twoValues d L).1 = (L.map (fun p => (p.2 : ℚ) / d)).prod := by
  induction L with
  | nil => simp [twoValues]
  | cons p rest ih =>
    obtain ⟨t, Δ⟩ := p
    simp only [twoValues, List.map_cons, List.prod_cons]
    rw [← ih]; ring

/-- Choice of the parameters: if `a` is least with `d^{-a} ≤ 4ε`, then `Δ = ⌈4ε d^a⌉` satisfies
`1 ≤ Δ ≤ d`, and the gap `Δ / d^a` lies between `4ε` and `8ε`. -/
theorem params (d a : ℕ) (hd : 2 ≤ d) (ε : ℚ) (hε : 0 < ε)
    (hlow : 1 ≤ 4 * ε * (d : ℚ) ^ a) (hhigh : 4 * ε * (d : ℚ) ^ a < d) :
    1 ≤ ⌈4 * ε * (d : ℚ) ^ a⌉ ∧ ⌈4 * ε * (d : ℚ) ^ a⌉ ≤ d ∧
      4 * ε ≤ (⌈4 * ε * (d : ℚ) ^ a⌉ : ℚ) / (d : ℚ) ^ a ∧
      (⌈4 * ε * (d : ℚ) ^ a⌉ : ℚ) / (d : ℚ) ^ a ≤ 8 * ε := by
  have hpos : (0 : ℚ) < (d : ℚ) ^ a := by positivity
  have hc1 := Int.le_ceil (4 * ε * (d : ℚ) ^ a)
  have hc2 := Int.ceil_lt_add_one (4 * ε * (d : ℚ) ^ a)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Int.one_le_ceil_iff.mpr (by linarith)
  · exact Int.ceil_le.mpr (by exact_mod_cast hhigh.le)
  · rw [le_div_iff₀ hpos]; linarith
  · rw [div_le_iff₀ hpos]; linarith

/-- Ratio of the binomial counts in the weighted adversary relation:
`C(m, Δ) · Δ = C(m - 1, Δ - 1) · m`. -/
theorem choose_ratio (m Δ : ℕ) (hm : 1 ≤ m) (hΔ : 1 ≤ Δ) :
    m.choose Δ * Δ = (m - 1).choose (Δ - 1) * m := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨Δ', rfl⟩ : ∃ Δ', Δ = Δ' + 1 := ⟨Δ - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have := Nat.add_one_mul_choose_eq m' Δ'
  linarith [mul_comm (m'.choose Δ') (m' + 1)]

/-- With `t = ⌊(N - Δ)/2⌋`, the product `(N - t)(t + Δ)` is at least `N^2 / 4`, so the weighted
adversary bound `√((N - t)(t + Δ)) / Δ` is at least `N / (2Δ)`. -/
theorem ew_product (N Δ : ℕ) (hΔ : 1 ≤ Δ) (hN : Δ ≤ N) :
    N ^ 2 ≤ 4 * ((N - (N - Δ) / 2) * ((N - Δ) / 2 + Δ)) := by
  obtain ⟨s, rfl⟩ : ∃ s, N = Δ + s := ⟨N - Δ, by omega⟩
  have h1 : Δ + s - s / 2 = Δ + (s - s / 2) := by omega
  simp only [Nat.add_sub_cancel_left, h1]
  rcases Nat.even_or_odd s with ⟨r, hr⟩ | ⟨r, hr⟩
  · subst hr
    have e1 : (r + r) / 2 = r := by omega
    have e2 : r + r - r = r := by omega
    rw [e1, e2]; nlinarith
  · subst hr
    have e1 : (2 * r + 1) / 2 = r := by omega
    have e2 : 2 * r + 1 - r = r + 1 := by omega
    rw [e1, e2]; nlinarith

end Expectiminimax
