import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Alternating projections in one block

In a block of Jordan's lemma, the two projectors have rank one in a plane, with `cos² θ = p` between
their images. `vec k o` is the unit vector of the plane reached after a test: the test `k` alternates
between the two projectors, and the outcome `o` says whether the vector lies in the image.

`agree_prob` is the fact in the plane: the probability that the next outcome agrees with the current
one is `p`, whichever the current outcome and whichever the test.

`pathProb` is the probability of a sequence of bits `X_i`, where `X_i` holds iff outcome `i` equals
outcome `i - 1`, computed by the Born rule along the tests. `pathProb_eq` shows that it is the product
form `bernoulli p`, so the bits are independent with mean `p`. `bernoulli_sum` shows that this is a
probability distribution on the strings of a given length, and `bernoulli_mean_head` gives the mean of
a bit, since the position of a bit plays no role in the product.

Jordan's lemma itself, which reduces the two projectors to such planes, and the fact that the initial
state lies in one plane since its projector has rank one, are not formalized.
-/

namespace QuantumBranching

open Real

/-- The unit vector of the plane after a test: the test of parity `false` uses the first basis,
the test of parity `true` the basis rotated by `θ`. The outcome selects a vector of the basis. -/
noncomputable def vec (θ : ℝ) : Bool → Bool → ℝ × ℝ
  | false, true => (1, 0)
  | false, false => (0, 1)
  | true, true => (cos θ, sin θ)
  | true, false => (-sin θ, cos θ)

/-- The probability of moving between two unit vectors. -/
noncomputable def born (u v : ℝ × ℝ) : ℝ := (u.1 * v.1 + u.2 * v.2) ^ 2

/-- **The plane.** With `p = cos² θ`, the next outcome agrees with the current one with probability
`p`, and differs with probability `1 - p`, for both tests and both current outcomes. -/
theorem agree_prob (θ : ℝ) (k cur : Bool) :
    born (vec θ k cur) (vec θ (!k) cur) = cos θ ^ 2 ∧
      born (vec θ k cur) (vec θ (!k) (!cur)) = 1 - cos θ ^ 2 := by
  have h := Real.sin_sq_add_cos_sq θ
  cases k <;> cases cur <;> simp only [vec, born, Bool.not_false, Bool.not_true] <;>
    constructor <;> nlinarith

/-- The probability of a string of agreement bits, from the outcome `cur` of a test of parity `k`,
by the Born rule along the tests. -/
noncomputable def pathProb (θ : ℝ) : Bool → Bool → List Bool → ℝ
  | _, _, [] => 1
  | k, cur, x :: xs =>
    let next := if x then cur else !cur
    born (vec θ k cur) (vec θ (!k) next) * pathProb θ (!k) next xs

/-- The product form: independent bits with mean `p`. -/
noncomputable def bernoulli (p : ℝ) : List Bool → ℝ
  | [] => 1
  | x :: xs => (if x then p else 1 - p) * bernoulli p xs

/-- **Independence, by product form.** The probability of a string of agreement bits does not depend
on the start, and it is the product of `p` over the agreements and `1 - p` over the others. -/
theorem pathProb_eq (θ : ℝ) (k cur : Bool) (xs : List Bool) :
    pathProb θ k cur xs = bernoulli (cos θ ^ 2) xs := by
  induction xs generalizing k cur with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨h1, h2⟩ := agree_prob θ k cur
    cases x
    · simp only [pathProb, bernoulli, Bool.false_eq_true, ite_false, ih, h2]
    · simp only [pathProb, bernoulli, ite_true, ih, h1]

/-- All the strings of bits of a given length. -/
def allStrings : ℕ → List (List Bool)
  | 0 => [[]]
  | r + 1 => (allStrings r).map (List.cons true) ++ (allStrings r).map (List.cons false)

theorem sum_map_cons (p : ℝ) (b : Bool) (l : List (List Bool)) :
    ((l.map (List.cons b)).map (bernoulli p)).sum =
      (if b then p else 1 - p) * (l.map (bernoulli p)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, bernoulli] at ih ⊢
    rw [ih]
    ring

/-- The product form is a probability distribution. -/
theorem bernoulli_sum (p : ℝ) (r : ℕ) : ((allStrings r).map (bernoulli p)).sum = 1 := by
  induction r with
  | zero => simp [allStrings, bernoulli]
  | succ r ih =>
    simp only [allStrings, List.map_append, List.sum_append]
    rw [sum_map_cons, sum_map_cons, ih]
    simp

/-- The first bit has mean `p`, and the others follow by the product form. -/
theorem bernoulli_mean_head (p : ℝ) (r : ℕ) :
    (((allStrings r).map (List.cons true)).map (bernoulli p)).sum = p := by
  rw [sum_map_cons, bernoulli_sum]
  simp

end QuantumBranching
