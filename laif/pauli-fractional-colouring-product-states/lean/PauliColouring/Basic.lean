import Mathlib

/-!
# Counting steps of the product-basis colouring

A Pauli string on `n` qubits is `P : Fin n → Option (Fin 3)`, with `none` the identity and
`some σ` one of the three single-qubit Pauli matrices. A basis choice is `s : Fin n → Fin 3`, and
`P` lies in the commuting set of `s` if every non-identity coordinate of `P` equals that of `s`.
Qubit `i` has expectation vector `e i : Fin 3 → ℝ` of squared length at most `1`.

* `compat_commute`: two strings in the commuting set of the same basis choice agree on every
  coordinate where both are not the identity, so they commute.
* `total_weight`: the basis probabilities `q (e i)` give total weight `1`.
* `cover_ge`: a string `P` is covered with probability at least the product of the squared
  expectations `e i (P i) ^ 2` over its support, which is `tr(ρ P) ^ 2` for a product state.
-/

namespace PauliColouring

open Finset

/-- Basis probabilities of one qubit: squared expectations, normalized, or uniform if all vanish. -/
noncomputable def q (e : Fin 3 → ℝ) (σ : Fin 3) : ℝ :=
  if ∑ τ, e τ ^ 2 = 0 then 1 / 3 else e σ ^ 2 / ∑ τ, e τ ^ 2

theorem q_nonneg (e : Fin 3 → ℝ) (σ : Fin 3) : 0 ≤ q e σ := by
  unfold q; split_ifs <;> positivity

theorem q_sum (e : Fin 3 → ℝ) : ∑ σ, q e σ = 1 := by
  unfold q
  split_ifs with h
  · simp
  · rw [← sum_div]; exact div_self h

theorem q_ge (e : Fin 3 → ℝ) (he : ∑ τ, e τ ^ 2 ≤ 1) (σ : Fin 3) : e σ ^ 2 ≤ q e σ := by
  have hle : e σ ^ 2 ≤ ∑ τ, e τ ^ 2 :=
    single_le_sum (f := fun τ => e τ ^ 2) (fun τ _ => sq_nonneg _) (mem_univ σ)
  unfold q
  split_ifs with h
  · rw [h] at hle; linarith
  · have hS : 0 < ∑ τ, e τ ^ 2 := lt_of_le_of_ne (sum_nonneg fun τ _ => sq_nonneg _) (Ne.symm h)
    rw [le_div_iff₀ hS]
    nlinarith [sq_nonneg (e σ)]

/-- Membership of a string in the commuting set of a basis choice. -/
def compat (s : Fin n → Fin 3) (P : Fin n → Option (Fin 3)) : Prop :=
  ∀ i, P i = none ∨ P i = some (s i)

theorem compat_commute (s : Fin n → Fin 3) (P Q : Fin n → Option (Fin 3))
    (hP : compat s P) (hQ : compat s Q) (i : Fin n) (a b : Fin 3)
    (ha : P i = some a) (hb : Q i = some b) : a = b := by
  rcases hP i with h | h <;> rcases hQ i with h' | h' <;> simp_all

theorem total_weight (e : Fin n → Fin 3 → ℝ) :
    ∑ s : Fin n → Fin 3, ∏ i, q (e i) (s i) = 1 := by
  rw [← Fintype.prod_sum]
  simp [q_sum]

theorem cover_ge (e : Fin n → Fin 3 → ℝ) (he : ∀ i, ∑ τ, e i τ ^ 2 ≤ 1)
    (P : Fin n → Option (Fin 3)) :
    ∏ i, (match P i with | none => 1 | some σ => e i σ ^ 2)
      ≤ ∑ s : Fin n → Fin 3,
          ∏ i, (q (e i) (s i) * (if P i = none ∨ P i = some (s i) then 1 else 0)) := by
  rw [← Fintype.prod_sum (fun i σ => q (e i) σ * (if P i = none ∨ P i = some σ then 1 else 0))]
  apply prod_le_prod₀
  · intro i _
    cases P i <;> simp [sq_nonneg]
  · intro i _
    cases h : P i with
    | none => simp [q_sum]
    | some σ0 =>
        simp only [reduceCtorEq, false_or, Option.some.injEq, mul_ite, mul_one, mul_zero]
        rw [sum_ite_eq]
        simpa using q_ge (e i) (he i) σ0

end PauliColouring
