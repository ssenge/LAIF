import Mathlib

/-!
# Directions of hidden subgroups in the unitriangular group U₄(F_p)

An element `g` of U₄(F_p) is stored by its six entries above the diagonal: first row (1, b1, b2, a), second row
(0, 1, z, c1), third row (0, 0, 1, c2). `mul` is the matrix product in these coordinates (`mul_eq_matrix` checks it
against `Matrix.mul`).

* `mul_b1`, `mul_z`, `mul_c2`: the superdiagonal is additive, and `pw_b1`, `pw_c2`: the k-th power has superdiagonal
  k times that of g.
* `inF_mul`: the preimage `inF s` of the line through (1, s) in the (b1, c2) plane is closed under multiplication.
* `pw_inF_iff`: if b1 ≠ 0 and k ≠ 0 in F_p, then g ^ k lies in `inF s` exactly when s * b1 = c2 (Lemma 2).
* `sigma_mul`, `sigma_inF`: conjugation by diag(1, 1, 1, r) with r ≠ 0 respects `mul` and maps `inF r` onto `inF 1`
  (Lemma 3).
* `inF_mul_K`: multiplying by an element of K does not change the direction (case 2).
* `example_instance`: for p = 5 a concrete element lies in `inF 3` and not in `inF 2`.
-/

namespace UnitriHSP

variable {p : ℕ} [Fact p.Prime]

/-- Entries of an upper unitriangular 4 × 4 matrix above the diagonal. -/
@[ext] structure U4 (p : ℕ) where
  b1 : ZMod p
  z : ZMod p
  c2 : ZMod p
  b2 : ZMod p
  c1 : ZMod p
  a : ZMod p

/-- The matrix of an element. -/
def toMatrix (g : U4 p) : Matrix (Fin 4) (Fin 4) (ZMod p) :=
  !![1, g.b1, g.b2, g.a; 0, 1, g.z, g.c1; 0, 0, 1, g.c2; 0, 0, 0, 1]

/-- The product in coordinates. -/
def mul (g h : U4 p) : U4 p :=
  ⟨g.b1 + h.b1, g.z + h.z, g.c2 + h.c2, g.b2 + h.b2 + g.b1 * h.z, g.c1 + h.c1 + g.z * h.c2,
    g.a + h.a + g.b1 * h.c1 + g.b2 * h.c2⟩

/-- The coordinate product is the matrix product. -/
theorem mul_eq_matrix (g h : U4 p) : toMatrix (mul g h) = toMatrix g * toMatrix h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, mul, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/-- The identity. -/
def one : U4 p := ⟨0, 0, 0, 0, 0, 0⟩

/-- Powers. -/
def pw (g : U4 p) : ℕ → U4 p
  | 0 => one
  | k + 1 => mul (pw g k) g

theorem mul_b1 (g h : U4 p) : (mul g h).b1 = g.b1 + h.b1 := rfl
theorem mul_z (g h : U4 p) : (mul g h).z = g.z + h.z := rfl
theorem mul_c2 (g h : U4 p) : (mul g h).c2 = g.c2 + h.c2 := rfl

theorem pw_b1 (g : U4 p) (k : ℕ) : (pw g k).b1 = k * g.b1 := by
  induction k with
  | zero => simp [pw, one]
  | succ k ih => simp [pw, mul_b1, ih]; ring

theorem pw_c2 (g : U4 p) (k : ℕ) : (pw g k).c2 = k * g.c2 := by
  induction k with
  | zero => simp [pw, one]
  | succ k ih => simp [pw, mul_c2, ih]; ring

/-- Membership in the preimage of the line through (1, s) in the (b1, c2) plane. -/
def inF (s : ZMod p) (g : U4 p) : Prop := g.c2 = s * g.b1

theorem inF_mul {s : ZMod p} {g h : U4 p} (hg : inF s g) (hh : inF s h) : inF s (mul g h) := by
  unfold inF at *; rw [mul_b1, mul_c2, hg, hh]; ring

/-- Lemma 2: a nontrivial power of g lies in `inF s` exactly when `s * b1 = c2`. -/
theorem pw_inF_iff (g : U4 p) (s : ZMod p) (k : ℕ) (hk : (k : ZMod p) ≠ 0) :
    inF s (pw g k) ↔ s * g.b1 = g.c2 := by
  unfold inF; rw [pw_b1, pw_c2]
  constructor
  · intro h
    have : (k : ZMod p) * (g.c2 - s * g.b1) = 0 := by rw [mul_sub, h]; ring
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hk
    · exact (sub_eq_zero.mp h0).symm
  · intro h; rw [← h]; ring

/-- The direction is unique: for b1 ≠ 0 at most one s works. -/
theorem direction_unique (g : U4 p) (hb : g.b1 ≠ 0) {s t : ZMod p} (hs : s * g.b1 = g.c2)
    (ht : t * g.b1 = g.c2) : s = t :=
  mul_right_cancel₀ hb (hs.trans ht.symm)

/-- Conjugation by diag(1, 1, 1, r). -/
noncomputable def sigma (r : ZMod p) (g : U4 p) : U4 p :=
  ⟨g.b1, g.z, g.c2 / r, g.b2, g.c1 / r, g.a / r⟩

/-- Lemma 3, first part: `sigma r` respects the product. -/
theorem sigma_mul (r : ZMod p) (g h : U4 p) : sigma r (mul g h) = mul (sigma r g) (sigma r h) := by
  ext <;> simp [sigma, mul] <;> ring

/-- `sigma r` is the conjugation by diag(1, 1, 1, r) on matrices. -/
theorem sigma_eq_conj (r : ZMod p) (hr : r ≠ 0) (g : U4 p) :
    toMatrix (sigma r g) * Matrix.diagonal ![1, 1, 1, r] = Matrix.diagonal ![1, 1, 1, r] * toMatrix g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, sigma, Matrix.mul_apply, Matrix.diagonal, hr]

/-- Lemma 3, second part: `sigma r` maps `inF r` onto `inF 1`. -/
theorem sigma_inF (r : ZMod p) (hr : r ≠ 0) (g : U4 p) : inF 1 (sigma r g) ↔ inF r g := by
  unfold inF sigma; simp only [one_mul]
  constructor
  · intro h; field_simp at h; rw [h]
  · intro h; rw [h]; field_simp

/-- Case 2 of Lemma 2: multiplying by an element of K = {b1 = c2 = 0} (which contains U₄′) does not change the
direction. -/
theorem inF_mul_K (s : ZMod p) (g x : U4 p) (hx1 : x.b1 = 0) (hx2 : x.c2 = 0) :
    inF s (mul g x) ↔ inF s g := by
  unfold inF; rw [mul_b1, mul_c2, hx1, hx2, add_zero, add_zero]

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Non-vacuity: for p = 5 the element with b1 = 2, z = 1, c2 = 1 lies in `inF 3` (3 * 2 = 1 in F_5) and not in
`inF 2`, and its square is still in `inF 3`. -/
theorem example_instance :
    let g : U4 5 := ⟨2, 1, 1, 0, 0, 0⟩
    inF 3 g ∧ ¬ inF 2 g ∧ inF 3 (pw g 2) := by
  intro g
  have h1 : inF 3 g := show (1 : ZMod 5) = 3 * 2 by decide
  refine ⟨h1, show ¬ ((1 : ZMod 5) = 2 * 2) by decide, ?_⟩
  exact (pw_inF_iff g 3 2 (show ((2 : ℕ) : ZMod 5) ≠ 0 by decide)).mpr h1.symm

end UnitriHSP
