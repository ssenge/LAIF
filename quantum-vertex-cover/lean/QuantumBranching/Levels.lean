import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The quadratic bound

Fix a real `N ≥ 4` and a natural `q ≥ 1`, and put `W q = 22 * q + 3` and
`A q = 7 * q + 4 * W q + 1`, so that `A q = 95 * q + 13` and `(W q - q) / 3 = 7 * q + 1`.

The time `Q m` bounds the search on every instance with `log (B x) ≤ m`. A value call at a node `v` is
padded to the budget `Q (padLevel N q (B v))`, where `padLevel N q b = (3/4) * log b + q * log N`.

`quadratic_bound` concludes `Q m ^ 2 ≤ N ^ A q * exp m`. No monotonicity of `Q` is used, and the family
of instances carries no well founded relation: `padLevel_drop` shows that the level drops by at least
`log N` above the base, and the induction runs on the natural number of drops. The conclusion needs a
lower bound on `m`, since the base is flat: `base_fails_below` shows that it fails for
`m = -(6 * q + 2) * log N` when the base is attained. Since `B ≥ 2`, only `m > 0` occurs.

The sum of the terms is `2 * N ^ (5 * q) + N ^ (7 * q + 4 * W q) + N ^ (A q + 7 * q - (7 * q + 1))`, and
each of the four powers is at most `N ^ (A q - 1)`.

`decrease_condition` gives the exact condition for the decrease of the level, `7 * q ≤ w`, and
`decrease_sharp` shows that it cannot be lowered.
-/

open Real

namespace QuantumBranching

/-- The threshold of the base case, in powers of `N`. -/
def W (q : ℕ) : ℕ := 22 * q + 3

/-- The exponent of the bound. -/
def A (q : ℕ) : ℕ := 7 * q + 4 * W q + 1

theorem A_eq (q : ℕ) : A q = 95 * q + 13 := by simp only [A, W]; ring

/-- `(W q - q) / 3` is a natural number. -/
theorem W_sub_div (q : ℕ) : ((W q : ℝ) - q) / 3 = ((7 * q + 1 : ℕ) : ℝ) := by
  simp only [W]; push_cast; ring

/-- The last exponent is exactly `A q - 1`: this is the choice of `W`. -/
theorem exponent_identity (q : ℕ) : A q + 7 * q - (7 * q + 1) = A q - 1 := by
  rw [A_eq]; omega

/-- The condition behind the choice of `W`: `7 * q + 1 ≤ (w - q) / 3` iff `22 * q + 3 ≤ w`. -/
theorem W_condition (q w : ℕ) : 3 * (7 * q + 1) + q ≤ w ↔ 22 * q + 3 ≤ w := by omega

theorem W_gt (q : ℕ) : 8 * q < W q := by simp only [W]; omega

/-- The level of a value call at a node of measure `b`. -/
noncomputable def padLevel (N : ℝ) (q : ℕ) (b : ℝ) : ℝ := (3 / 4) * log b + q * log N

section Estimates

variable {N : ℝ} {q : ℕ}

theorem log_N_pos (hN : 4 ≤ N) : 0 < log N := Real.log_pos (by linarith)

theorem N_pos (hN : 4 ≤ N) : 0 < N := by linarith

theorem one_le_pow_N (hN : 4 ≤ N) (k : ℕ) : 1 ≤ N ^ k := one_le_pow₀ (by linarith)

theorem pow_mono_N (hN : 4 ≤ N) {a b : ℕ} (h : a ≤ b) : N ^ a ≤ N ^ b :=
  pow_le_pow_right₀ (by linarith) h

theorem pow_eq_exp (hN : 4 ≤ N) (k : ℕ) : N ^ k = exp (k * log N) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (N_pos hN)]
  ring_nf

/-- **The inner estimate.** A level above the threshold `w` forces `B v` to be large, which gains the
factor `B v ^ (-1/4) ≤ N ^ (-(w - q) / 3)`. -/
theorem inner_estimate {w : ℝ} (hN : 4 ≤ N) {Bv : ℝ} (hBv : 0 < Bv)
    (hw : w * log N < padLevel N q Bv) :
    Bv ^ ((3 : ℝ) / 4) ≤ Bv * N ^ (-(w - q) / 3) := by
  unfold padLevel at hw
  have hgain : (w - q) * log N < (3 / 4) * log Bv := by linarith
  rw [Real.rpow_def_of_pos hBv, Real.rpow_def_of_pos (N_pos hN)]
  have : Bv = exp (log Bv) := (Real.exp_log hBv).symm
  conv_rhs => rw [this]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h3 : log N * (-(w - q) / 3) = -(((w - q) * log N) / 3) := by ring
  rw [h3]
  linarith

/-- The inner estimate in natural powers, for `W q`. -/
theorem inner_estimate_pow (hN : 4 ≤ N) {Bv : ℝ} (hBv : 0 < Bv)
    (hw : (W q : ℝ) * log N < padLevel N q Bv) :
    N ^ (7 * q + 1) * Bv ^ ((3 : ℝ) / 4) ≤ Bv := by
  unfold padLevel at hw
  have hgain : ((W q : ℝ) - q) * log N < (3 / 4) * log Bv := by linarith
  rw [pow_eq_exp hN, Real.rpow_def_of_pos hBv, ← Real.exp_add]
  have : Bv = exp (log Bv) := (Real.exp_log hBv).symm
  conv_rhs => rw [this]
  apply Real.exp_le_exp.mpr
  have hW : ((W q : ℝ) - q) = 3 * ((7 * q + 1 : ℕ) : ℝ) := by
    simp only [W]; push_cast; ring
  rw [hW] at hgain
  nlinarith

/-- The exponential of a level. -/
theorem exp_padLevel (hN : 4 ≤ N) {Bv : ℝ} (hBv : 0 < Bv) :
    exp (padLevel N q Bv) = N ^ q * Bv ^ ((3 : ℝ) / 4) := by
  unfold padLevel
  rw [pow_eq_exp hN, Real.rpow_def_of_pos hBv, ← Real.exp_add]
  congr 1
  ring

/-- **The exact condition for the decrease.** If `7 * q ≤ w`, the level of a node of an instance of
measure at most `m`, above the threshold `w`, is below `m`. -/
theorem decrease_condition (hN : 4 ≤ N) {w m Bv : ℝ} (hw : 7 * (q : ℝ) ≤ w)
    (hm : w * log N < m) (hv : log Bv ≤ m + q * log N) : padLevel N q Bv < m := by
  have hl : 0 < log N := log_N_pos hN
  have : 7 * (q : ℝ) * log N ≤ w * log N := mul_le_mul_of_nonneg_right hw hl.le
  unfold padLevel
  linarith

/-- The condition `7 * q ≤ w` cannot be lowered: below it, there are values with no decrease. -/
theorem decrease_sharp (hN : 4 ≤ N) {w : ℝ} (hw : w < 7 * (q : ℝ)) :
    ∃ m lv : ℝ, w * log N < m ∧ lv ≤ m + q * log N ∧ m ≤ (3 / 4) * lv + q * log N := by
  have hl : 0 < log N := log_N_pos hN
  refine ⟨7 * q * log N, 8 * q * log N, by nlinarith, by linarith, ?_⟩
  linarith

/-- With `W q`, the level drops by at least `log N`, uniformly. -/
theorem padLevel_drop (hN : 4 ≤ N) (hq : 1 ≤ q) {m Bv : ℝ} (hm : (W q : ℝ) * log N < m)
    (hv : log Bv ≤ m + q * log N) : padLevel N q Bv ≤ m - log N := by
  have hl : 0 < log N := log_N_pos hN
  have hW : (W q : ℝ) = 22 * q + 3 := by simp only [W]; push_cast; ring
  rw [hW] at hm
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq2 : log N ≤ q * log N := by nlinarith
  unfold padLevel
  nlinarith

/-- A flat base cannot give the conclusion for arbitrarily small `m`. -/
theorem base_fails_below (hN : 4 ≤ N) :
    N ^ A q * exp (-((6 * q + 2 : ℕ) * log N)) < N ^ (q + 4 * W q) := by
  have hN0 := N_pos hN
  have h1 : exp (-((6 * q + 2 : ℕ) * log N)) = (N ^ (6 * q + 2))⁻¹ := by
    rw [Real.exp_neg, ← pow_eq_exp hN]
  have hA : A q = (q + 4 * W q) + (6 * q + 1) := by simp only [A]; ring
  have hpos : 0 < N ^ (q + 4 * W q) := pow_pos hN0 _
  rw [h1, hA, pow_add, show 6 * q + 2 = (6 * q + 1) + 1 by ring, pow_add N (6 * q + 1) 1, pow_one]
  have hpos2 : 0 < N ^ (6 * q + 1) := pow_pos hN0 _
  rw [mul_inv]
  field_simp
  linarith

end Estimates

section Lists

variable {α : Type*}

theorem list_sum_le_mul {l : List ℝ} {u M : ℝ} (hu : 0 ≤ u) (hlen : (l.length : ℝ) ≤ M)
    (h : ∀ a ∈ l, a ≤ u) : l.sum ≤ M * u := by
  have : l.sum ≤ l.length * u := by
    clear hlen
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      have h1 := h a (by simp)
      have h2 := ih (fun b hb => h b (by simp [hb]))
      nlinarith
  exact this.trans (mul_le_mul_of_nonneg_right hlen hu)

theorem list_map_sum_le {l : List α} {f g : α → ℝ} (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

theorem list_sum_affine (l : List α) (B : α → ℝ) (a b : ℝ) :
    (l.map fun v => a + b * B v).sum = a * l.length + b * (l.map B).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, ih]
    ring

theorem list_map_sum_nonneg {l : List α} {f : α → ℝ} (h : ∀ a ∈ l, 0 ≤ f a) :
    0 ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_nonneg (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

end Lists

section Sum

variable {I : Type*} {N : ℝ} {q : ℕ}

/-- The coefficient of `B x` in the sum over all children. -/
noncomputable def coef (N : ℝ) (q : ℕ) : ℝ :=
  2 * N ^ (3 * q) + N ^ (5 * q + 4 * W q) + N ^ (A q + 5 * q - (7 * q + 1))

theorem coef_pos (hN : 4 ≤ N) : 0 < coef N q := by
  have := N_pos hN
  unfold coef
  positivity

theorem one_le_coef (hN : 4 ≤ N) : 1 ≤ coef N q := by
  have h1 := one_le_pow_N hN (3 * q)
  have h2 := one_le_pow_N hN (5 * q + 4 * W q)
  have h3 := one_le_pow_N hN (A q + 5 * q - (7 * q + 1))
  unfold coef
  linarith

/-- The sum over all children, for a fixed list of nodes. It holds as soon as the budget of the calls
at each node is at most the two terms of the estimate. `Y v` is `N ^ q` times the squared budget. -/
theorem sum_estimate (hN : 4 ≤ N) (B : I → ℝ) (hB : ∀ x, 2 ≤ B x)
    (V : List I) (Bx : ℝ) (hM1 : (V.map B).sum ≤ N ^ q * Bx)
    (kids : I → List ℝ) (Y : I → ℝ)
    (hkidlen : ∀ v, ((kids v).length : ℝ) ≤ N ^ q)
    (hkid : ∀ v ∈ V, ∀ c ∈ kids v, c ≤ N ^ q * (1 + Y v + B v))
    (hY0 : ∀ v ∈ V, 0 ≤ Y v)
    (hY : ∀ v ∈ V, Y v ≤ N ^ q * (N ^ (q + 4 * W q) + N ^ (A q + q - (7 * q + 1)) * B v)) :
    (V.map fun v => (kids v).sum).sum ≤ Bx * coef N q := by
  have hN0 := N_pos hN
  set e1 := q + 4 * W q with he1
  set e2 := A q + q - (7 * q + 1) with he2
  set α := N ^ q * N ^ q * (1 + N ^ q * N ^ e1) with hα
  set β := N ^ q * N ^ q * (1 + N ^ q * N ^ e2) with hβ
  have hαnn : 0 ≤ α := by positivity
  have hβnn : 0 ≤ β := by positivity
  have hone : ∀ v ∈ V, (kids v).sum ≤ α + β * B v := by
    intro v hv
    have hBv : (0 : ℝ) < B v := by linarith [hB v]
    have hu0 : 0 ≤ N ^ q * (1 + Y v + B v) := by
      have := hY0 v hv
      positivity
    have h1 := list_sum_le_mul hu0 (hkidlen v) (hkid v hv)
    have h2 := hY v hv
    have h3 : N ^ q * (N ^ q * (1 + Y v + B v)) ≤
        N ^ q * (N ^ q * (1 + N ^ q * (N ^ e1 + N ^ e2 * B v) + B v)) := by
      gcongr
    refine h1.trans (h3.trans (le_of_eq ?_))
    simp only [hα, hβ]
    ring
  have hlen : (V.length : ℝ) ≤ N ^ q * Bx := by
    have : (V.length : ℝ) ≤ (V.map B).sum := by
      have h := list_map_sum_le (l := V) (f := fun _ => (1 : ℝ)) (g := B)
        (fun a _ => by linarith [hB a])
      simpa using h
    linarith
  have hsum := list_map_sum_le (l := V) hone
  rw [list_sum_affine] at hsum
  have h1 : α * V.length ≤ α * (N ^ q * Bx) := mul_le_mul_of_nonneg_left hlen hαnn
  have h2 : β * (V.map B).sum ≤ β * (N ^ q * Bx) := mul_le_mul_of_nonneg_left hM1 hβnn
  have he3 : A q + 5 * q - (7 * q + 1) = q + q + q + q + e2 := by
    simp only [he2, A_eq]; omega
  have he4 : 5 * q + 4 * W q = q + q + q + q + e1 := by simp only [he1]; ring
  refine hsum.trans ((add_le_add h1 h2).trans (le_of_eq ?_))
  unfold coef
  rw [he3, he4, show 3 * q = q + q + q by ring]
  simp only [hα, hβ, pow_add]
  ring

/-- The terms of the sum, after the factor of the walk, are at most `N ^ A q`. -/
theorem four_terms (hN : 4 ≤ N) : N ^ (2 * q) * coef N q ≤ N ^ A q := by
  have hA1 : A q = (A q - 1) + 1 := by rw [A_eq]; omega
  have ht1 : N ^ (2 * q) * N ^ (3 * q) ≤ N ^ (A q - 1) := by
    rw [← pow_add]; exact pow_mono_N hN (by rw [A_eq]; omega)
  have ht2 : N ^ (2 * q) * N ^ (5 * q + 4 * W q) ≤ N ^ (A q - 1) := by
    rw [← pow_add]; exact pow_mono_N hN (by rw [A_eq]; simp only [W]; omega)
  have ht3 : N ^ (2 * q) * N ^ (A q + 5 * q - (7 * q + 1)) ≤ N ^ (A q - 1) := by
    rw [← pow_add]; exact pow_mono_N hN (by rw [A_eq]; omega)
  have hpos : 0 < N ^ (A q - 1) := pow_pos (N_pos hN) _
  unfold coef
  calc N ^ (2 * q) * (2 * N ^ (3 * q) + N ^ (5 * q + 4 * W q) + N ^ (A q + 5 * q - (7 * q + 1)))
      ≤ 4 * N ^ (A q - 1) := by nlinarith
    _ ≤ N * N ^ (A q - 1) := by nlinarith
    _ = N ^ A q := by
      conv_rhs => rw [hA1, pow_succ]
      ring

/-- The budget of a call, from the base below the threshold and the bound above it. -/
theorem budget_bound (hN : 4 ≤ N) {Bv Qv : ℝ} (hBv : 0 < Bv)
    (hbase : padLevel N q Bv ≤ (W q : ℝ) * log N → Qv ^ 2 ≤ N ^ (q + 4 * W q))
    (hind : (W q : ℝ) * log N < padLevel N q Bv → Qv ^ 2 ≤ N ^ A q * exp (padLevel N q Bv)) :
    Qv ^ 2 ≤ N ^ (q + 4 * W q) + N ^ (A q + q - (7 * q + 1)) * Bv := by
  have hN0 := N_pos hN
  have hp1 : 0 ≤ N ^ (q + 4 * W q) := by positivity
  have hp2 : 0 ≤ N ^ (A q + q - (7 * q + 1)) * Bv := by positivity
  by_cases hc : padLevel N q Bv ≤ (W q : ℝ) * log N
  · linarith [hbase hc]
  · push Not at hc
    have hin := inner_estimate_pow (q := q) hN hBv hc
    have hA : A q + q = (A q + q - (7 * q + 1)) + (7 * q + 1) := by rw [A_eq]; omega
    calc Qv ^ 2 ≤ N ^ A q * exp (padLevel N q Bv) := hind hc
      _ = N ^ (A q + q) * Bv ^ ((3 : ℝ) / 4) := by
          rw [exp_padLevel hN hBv, pow_add]; ring
      _ = N ^ (A q + q - (7 * q + 1)) * (N ^ (7 * q + 1) * Bv ^ ((3 : ℝ) / 4)) := by
          conv_lhs => rw [hA, pow_add]
          ring
      _ ≤ N ^ (A q + q - (7 * q + 1)) * Bv := mul_le_mul_of_nonneg_left hin (by positivity)
      _ ≤ _ := by linarith

end Sum

/-- The hypotheses of the quadratic bound, over an abstract family of instances. `R` selects the
instances that are searched, `V x` lists the nodes of the tree of `x`, and `kids v` the squared step
counts of the children of `v`.

`walk` is the bound of the walk for any upper bound `S` on the sum of the squared step counts over
the searched instances of measure at most `m`. It says that `Q m ^ 2` is at most `N ^ (2 * q)` times
the least such bound, without taking a supremum. -/
structure LevelHyp {I : Type*} (N : ℝ) (q : ℕ) (B : I → ℝ) (R : I → Prop) (Q : ℝ → ℝ)
    (V : I → List I) (kids : I → List ℝ) : Prop where
  N_ge : 4 ≤ N
  q_pos : 1 ≤ q
  B_ge : ∀ x, 2 ≤ B x
  /-- The bound of the walk, above the base. -/
  walk : ∀ m, (W q : ℝ) * log N < m → ∀ S, 0 ≤ S →
    (∀ x, R x → log (B x) ≤ m → ((V x).map fun v => (kids v).sum).sum ≤ S) →
      Q m ^ 2 ≤ N ^ (2 * q) * S
  /-- The cost of a child, with the calls at `v` padded to the level of `v`. -/
  kid_le : ∀ v, ∀ c ∈ kids v, c ≤ N ^ q * (1 + N ^ q * Q (padLevel N q (B v)) ^ 2 + B v)
  /-- The number of children. -/
  kids_length : ∀ v, ((kids v).length : ℝ) ≤ N ^ q
  /-- (M1) across depths. -/
  M1 : ∀ x, R x → ((V x).map B).sum ≤ N ^ q * B x
  /-- The base case. -/
  base : ∀ m, m ≤ (W q : ℝ) * log N → Q m ^ 2 ≤ N ^ (q + 4 * W q)

namespace LevelHyp

variable {I : Type*} {N : ℝ} {q : ℕ} {B : I → ℝ} {R : I → Prop} {Q : ℝ → ℝ} {V : I → List I}
  {kids : I → List ℝ}

theorem B_pos (h : LevelHyp N q B R Q V kids) (x : I) : 0 < B x := by linarith [h.B_ge x]

theorem padLevel_pos (h : LevelHyp N q B R Q V kids) (x : I) : 0 ≤ padLevel N q (B x) := by
  have hl := log_N_pos h.N_ge
  have h1 : 0 ≤ log (B x) := Real.log_nonneg (by linarith [h.B_ge x])
  unfold padLevel
  positivity

/-- A node has measure at most that of the root, up to the constant in (M1). -/
theorem B_node_le (h : LevelHyp N q B R Q V kids) {x v : I} (hR : R x) (hv : v ∈ V x) :
    B v ≤ N ^ q * B x := by
  refine le_trans ?_ (h.M1 x hR)
  have hnn : ∀ a ∈ (V x).map B, 0 ≤ a := by
    intro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    exact (h.B_pos b).le
  exact List.single_le_sum hnn _ (List.mem_map_of_mem hv)

/-- The bound on `log (B v)` from (M1). -/
theorem log_node_le (h : LevelHyp N q B R Q V kids) {x v : I} (hR : R x) (hv : v ∈ V x) :
    log (B v) ≤ log (B x) + q * log N := by
  have hN := h.N_ge
  have hN0 := N_pos hN
  have h1 := Real.log_le_log (h.B_pos v) (h.B_node_le hR hv)
  rw [Real.log_mul (by positivity) (h.B_pos x).ne', Real.log_pow] at h1
  linarith

/-- The base bound as a bound by `exp m`. -/
theorem base_le (h : LevelHyp N q B R Q V kids) {m : ℝ} (hm : m ≤ (W q : ℝ) * log N)
    (hlow : -((6 * q + 1 : ℕ) * log N) ≤ m) : Q m ^ 2 ≤ N ^ A q * exp m := by
  have hN := h.N_ge
  have hN0 := N_pos hN
  have hb := h.base m hm
  have hA : A q = (q + 4 * W q) + (6 * q + 1) := by simp only [A]; ring
  have h1 : (1 : ℝ) ≤ N ^ (6 * q + 1) * exp m := by
    rw [pow_eq_exp hN, ← Real.exp_add]
    exact Real.one_le_exp (by linarith)
  have hp : 0 < N ^ (q + 4 * W q) := pow_pos hN0 _
  calc Q m ^ 2 ≤ N ^ (q + 4 * W q) := hb
    _ ≤ N ^ (q + 4 * W q) * (N ^ (6 * q + 1) * exp m) := le_mul_of_one_le_right hp.le h1
    _ = N ^ A q * exp m := by rw [hA, pow_add]; ring

/-- The induction on the natural number of drops. -/
theorem bound_of_drops (h : LevelHyp N q B R Q V kids) (j : ℕ) :
    ∀ m, -((6 * q + 1 : ℕ) * log N) ≤ m → m ≤ ((W q : ℝ) + j) * log N →
      Q m ^ 2 ≤ N ^ A q * exp m := by
  have hN := h.N_ge
  have hN0 := N_pos hN
  have hl := log_N_pos hN
  induction j with
  | zero =>
    intro m hlow hm
    exact h.base_le (by simpa using hm) hlow
  | succ j ih =>
    intro m hlow hm
    by_cases hbase : m ≤ (W q : ℝ) * log N
    · exact h.base_le hbase hlow
    · push Not at hbase
      have hlev0 : ∀ v, -((6 * q + 1 : ℕ) * log N) ≤ padLevel N q (B v) := by
        intro v
        have h0 := h.padLevel_pos v
        have : (0 : ℝ) ≤ ((6 * q + 1 : ℕ) : ℝ) * log N := by positivity
        linarith
      have hS : ∀ x, R x → log (B x) ≤ m →
          ((V x).map fun v => (kids v).sum).sum ≤ exp m * coef N q := by
        intro x hR hx
        have hBx : B x ≤ exp m := by
          rw [← Real.exp_log (h.B_pos x)]
          exact Real.exp_le_exp.mpr hx
        have hbudget : ∀ v ∈ V x, Q (padLevel N q (B v)) ^ 2 ≤
            N ^ (q + 4 * W q) + N ^ (A q + q - (7 * q + 1)) * B v := by
          intro v hv
          refine budget_bound hN (h.B_pos v) (h.base _) fun hc => ih _ (hlev0 v) ?_
          have hdrop := padLevel_drop hN h.q_pos hbase
            ((h.log_node_le hR hv).trans (by linarith))
          push_cast at hm
          nlinarith
        have hNq : 0 ≤ N ^ q := by positivity
        have hsum := sum_estimate (q := q) hN B h.B_ge (V x) (B x) (h.M1 x hR) kids
          (fun v => N ^ q * Q (padLevel N q (B v)) ^ 2) h.kids_length
          (fun v _ c hc => h.kid_le v c hc) (fun v _ => by positivity)
          (fun v hv => mul_le_mul_of_nonneg_left (hbudget v hv) hNq)
        exact hsum.trans (mul_le_mul_of_nonneg_right hBx (coef_pos hN).le)
      have hS0 : 0 ≤ exp m * coef N q := mul_nonneg (Real.exp_pos _).le (coef_pos hN).le
      calc Q m ^ 2 ≤ N ^ (2 * q) * (exp m * coef N q) := h.walk m hbase _ hS0 hS
        _ = (N ^ (2 * q) * coef N q) * exp m := by ring
        _ ≤ N ^ A q * exp m := mul_le_mul_of_nonneg_right (four_terms hN) (Real.exp_pos _).le

end LevelHyp

/-- **The quadratic bound.** `Q m ^ 2 ≤ N ^ A q * exp m` for every `m ≥ -(6 * q + 1) * log N`, in
particular for every `m ≥ 0`. -/
theorem quadratic_bound {I : Type*} {N : ℝ} {q : ℕ} {B : I → ℝ} {R : I → Prop} {Q : ℝ → ℝ}
    {V : I → List I} {kids : I → List ℝ} (h : LevelHyp N q B R Q V kids) {m : ℝ}
    (hlow : -((6 * q + 1 : ℕ) * log N) ≤ m) :
    Q m ^ 2 ≤ N ^ A q * exp m := by
  have hl := log_N_pos h.N_ge
  obtain ⟨j, hj⟩ := exists_nat_ge (m / log N)
  refine h.bound_of_drops j m hlow ?_
  have h1 : m ≤ j * log N := by rwa [div_le_iff₀ hl] at hj
  have h2 : (0 : ℝ) ≤ (W q : ℝ) * log N := mul_nonneg (Nat.cast_nonneg _) hl.le
  nlinarith

/-- From the square to the time, at the level of an instance. -/
theorem time_of_sq {N Qx Bx : ℝ} {a : ℕ} (hN : 4 ≤ N) (hBx : 0 < Bx)
    (h : Qx ^ 2 ≤ N ^ a * exp (log Bx)) : Qx ≤ N ^ ((a : ℝ) / 2) * √Bx := by
  have hN0 := N_pos hN
  rw [Real.exp_log hBx] at h
  have h1 : √(N ^ a * Bx) = N ^ ((a : ℝ) / 2) * √Bx := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow (N ^ a), ← Real.rpow_natCast,
      ← Real.rpow_mul hN0.le]
    congr 2
    ring
  rw [← h1]
  exact Real.le_sqrt_of_sq_le h

/-- The bound for finite sets of nodes. -/
theorem quadratic_bound_finset {I : Type*} {N : ℝ} {q : ℕ} {B : I → ℝ} {Q : ℝ → ℝ}
    (V : I → Finset I) (kids : I → List ℝ) (hN : 4 ≤ N) (hq : 1 ≤ q) (hB : ∀ x, 2 ≤ B x)
    (hwalk : ∀ m, (W q : ℝ) * log N < m → ∀ S, 0 ≤ S →
      (∀ x, log (B x) ≤ m → ∑ v ∈ V x, (kids v).sum ≤ S) → Q m ^ 2 ≤ N ^ (2 * q) * S)
    (hkid : ∀ v, ∀ c ∈ kids v, c ≤ N ^ q * (1 + N ^ q * Q (padLevel N q (B v)) ^ 2 + B v))
    (hkids : ∀ v, ((kids v).length : ℝ) ≤ N ^ q)
    (hM1 : ∀ x, ∑ v ∈ V x, B v ≤ N ^ q * B x)
    (hbase : ∀ m, m ≤ (W q : ℝ) * log N → Q m ^ 2 ≤ N ^ (q + 4 * W q))
    {m : ℝ} (hm : 0 ≤ m) :
    Q m ^ 2 ≤ N ^ A q * exp m := by
  have hl := log_N_pos hN
  refine quadratic_bound (B := B) (R := fun _ => True) (V := fun x => (V x).toList)
    (kids := kids) ?_ ?_
  · refine ⟨hN, hq, hB, ?_, hkid, hkids, ?_, hbase⟩
    · intro m hm S hS hx
      exact hwalk m hm S hS fun x hxm => by simpa [Finset.sum_toList] using hx x trivial hxm
    · intro x _
      simpa [Finset.sum_toList] using hM1 x
  · have : (0 : ℝ) ≤ ((6 * q + 1 : ℕ) : ℝ) * log N := by positivity
    linarith

end QuantumBranching
