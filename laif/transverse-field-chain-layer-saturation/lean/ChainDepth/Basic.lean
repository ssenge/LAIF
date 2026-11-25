import Mathlib

/-!
# Pseudospin picture of the transverse-field chain ansatz: depth bound and rigidity

A pseudospin is a unit vector of `ℝ³`, starting at `ex = (1, 0, 0)`. Layer `j` rotates it by
`4 γ j` about `nk k = (cos k, 0, sin k)` and then by `4 β j` about `ex`. For a ring of `L` qubits the
momenta are `k = (2j + 1) π / L`, and the pseudospin of `k* = π - π / L` has its axis at angle
`π / L` from `em = (-1, 0, 0)`.

Main statements:
* `depth_bound`: after `p` layers the pseudospin of `k*` has angle at least `π - 2 p π / L` from
  `em`, so `not_flipped` shows it is not at `em` when `2 p < L`.
* `rigidity`: if `2 p = L` and the pseudospin of `k*` ends at `em`, then every rotation angle
  `4 γ j` and every intermediate `4 β j` has cosine `-1`.
* `all_flip`: under the conclusion of `rigidity` every pseudospin `(2j + 1) π / L` ends at `em`.
* `not_prepared`: at depth at most `L / 2` no circuit puts the pseudospin of `k*` at `em` while the
  pseudospin of `π / L` stays at `ex`.
-/

open Real

namespace ChainDepth

/-- A vector of `ℝ³` in coordinates. -/
@[ext] structure V3 where
  x : ℝ
  y : ℝ
  z : ℝ

/-- Inner product. -/
def dot (u v : V3) : ℝ := u.x * v.x + u.y * v.y + u.z * v.z

/-- Vector product. -/
def cross (u v : V3) : V3 :=
  ⟨u.y * v.z - u.z * v.y, u.z * v.x - u.x * v.z, u.x * v.y - u.y * v.x⟩

/-- Triple product. -/
def triple (u v w : V3) : ℝ := dot u (cross v w)

/-- Rotation by `θ` about the unit axis `n`. -/
noncomputable def rot (n : V3) (θ : ℝ) (w : V3) : V3 :=
  ⟨cos θ * w.x + sin θ * (cross n w).x + (1 - cos θ) * dot n w * n.x,
   cos θ * w.y + sin θ * (cross n w).y + (1 - cos θ) * dot n w * n.y,
   cos θ * w.z + sin θ * (cross n w).z + (1 - cos θ) * dot n w * n.z⟩

/-- The start direction `(1, 0, 0)`. -/
def ex : V3 := ⟨1, 0, 0⟩

/-- The flipped direction `(-1, 0, 0)`. -/
def em : V3 := ⟨-1, 0, 0⟩

/-- The axis of momentum `k`. -/
noncomputable def nk (k : ℝ) : V3 := ⟨cos k, 0, sin k⟩

/-- A direction of the `xz`-plane by its angle from `ex`. -/
noncomputable def polar (φ : ℝ) : V3 := ⟨cos φ, 0, sin φ⟩

/-- The pseudospin of momentum `k` after `j` layers with angles `γ, β`. -/
noncomputable def state (k : ℝ) (γ β : ℕ → ℝ) : ℕ → V3
  | 0 => ex
  | j + 1 => rot ex (4 * β j) (rot (nk k) (4 * γ j) (state k γ β j))

theorem dot_comm (u v : V3) : dot u v = dot v u := by unfold dot; ring

/-- The determinant of the matrix of inner products of three vectors is the square of their
triple product. -/
theorem det_identity (u v w : V3) :
    dot u u * dot v v * dot w w + 2 * dot u v * dot v w * dot u w
      - dot u v ^ 2 * dot w w - dot v w ^ 2 * dot u u - dot u w ^ 2 * dot v v
      = triple u v w ^ 2 := by
  unfold triple dot cross; ring

theorem dot_mem {u v : V3} (hu : dot u u = 1) (hv : dot v v = 1) :
    -1 ≤ dot u v ∧ dot u v ≤ 1 := by
  have h : dot u u * dot v v - dot u v ^ 2
      = (cross u v).x ^ 2 + (cross u v).y ^ 2 + (cross u v).z ^ 2 := by
    unfold dot cross; ring
  rw [hu, hv] at h
  have h2 : dot u v ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (cross u v).x, sq_nonneg (cross u v).y, sq_nonneg (cross u v).z]
  exact abs_le.mp ((sq_le_one_iff_abs_le_one _).mp h2)

/-- Triangle inequality for angles between unit vectors. -/
theorem tri {u v w : V3} (hu : dot u u = 1) (hv : dot v v = 1) (hw : dot w w = 1) :
    arccos (dot u w) ≤ arccos (dot u v) + arccos (dot v w) := by
  have hg := det_identity u v w
  rw [hu, hv, hw] at hg
  obtain ⟨ha1, ha2⟩ := dot_mem hu hv
  obtain ⟨hb1, hb2⟩ := dot_mem hv hw
  by_cases hs : π ≤ arccos (dot u v) + arccos (dot v w)
  · linarith [arccos_le_pi (dot u w)]
  · replace hs := not_le.mp hs
    have hA : 0 ≤ 1 - dot u v ^ 2 := by nlinarith
    have hB : 0 ≤ 1 - dot v w ^ 2 := by nlinarith
    have key : cos (arccos (dot u v) + arccos (dot v w)) ≤ dot u w := by
      rw [cos_add, cos_arccos ha1 ha2, cos_arccos hb1 hb2, sin_arccos, sin_arccos]
      have hsq : (dot u w - dot u v * dot v w) ^ 2 ≤ (1 - dot u v ^ 2) * (1 - dot v w ^ 2) := by
        nlinarith [sq_nonneg (triple u v w)]
      have habs : |dot u w - dot u v * dot v w| ≤ √(1 - dot u v ^ 2) * √(1 - dot v w ^ 2) := by
        rw [← Real.sqrt_mul hA, ← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt hsq
      linarith [neg_abs_le (dot u w - dot u v * dot v w)]
    calc arccos (dot u w) ≤ arccos (cos (arccos (dot u v) + arccos (dot v w))) :=
          arccos_le_arccos key
      _ = arccos (dot u v) + arccos (dot v w) :=
          arccos_cos (add_nonneg (arccos_nonneg _) (arccos_nonneg _)) hs.le

/-- Equality in the triangle inequality forces the triple product to vanish. -/
theorem tri_eq {u v w : V3} (hu : dot u u = 1) (hv : dot v v = 1) (hw : dot w w = 1)
    (h : arccos (dot u w) = arccos (dot u v) + arccos (dot v w)) : triple u v w = 0 := by
  have hg := det_identity u v w
  rw [hu, hv, hw] at hg
  obtain ⟨ha1, ha2⟩ := dot_mem hu hv
  obtain ⟨hb1, hb2⟩ := dot_mem hv hw
  obtain ⟨hc1, hc2⟩ := dot_mem hu hw
  have hA : 0 ≤ 1 - dot u v ^ 2 := by nlinarith
  have hB : 0 ≤ 1 - dot v w ^ 2 := by nlinarith
  have hc := congrArg cos h
  rw [cos_arccos hc1 hc2, cos_add, cos_arccos ha1 ha2, cos_arccos hb1 hb2, sin_arccos,
    sin_arccos] at hc
  have h1 : dot u w - dot u v * dot v w = -(√(1 - dot u v ^ 2) * √(1 - dot v w ^ 2)) := by
    linarith
  have hsq : (dot u w - dot u v * dot v w) ^ 2 = (1 - dot u v ^ 2) * (1 - dot v w ^ 2) := by
    rw [h1, neg_sq, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]
  have hT : triple u v w ^ 2 = 0 := by linear_combination -hg - hsq
  exact pow_eq_zero_iff (by norm_num) |>.mp hT

theorem rot_dot_axis {n : V3} (hn : dot n n = 1) (θ : ℝ) (w : V3) :
    dot (rot n θ w) n = dot w n := by
  simp only [dot, rot, cross] at *
  linear_combination (1 - cos θ) * (n.x * w.x + n.y * w.y + n.z * w.z) * hn

theorem rot_unit {n w : V3} (hn : dot n n = 1) (hw : dot w w = 1) (θ : ℝ) :
    dot (rot n θ w) (rot n θ w) = 1 := by
  have hcs := sin_sq_add_cos_sq θ
  simp only [dot, rot, cross] at *
  linear_combination hw
    + (sin θ ^ 2 * (w.x * w.x + w.y * w.y + w.z * w.z)
        + (1 - cos θ) ^ 2 * (n.x * w.x + n.y * w.y + n.z * w.z) ^ 2) * hn
    + ((w.x * w.x + w.y * w.y + w.z * w.z) - (n.x * w.x + n.y * w.y + n.z * w.z) ^ 2) * hcs

/-- A rotation about an axis of the `xz`-plane that moves a vector of the `xz`-plane to a
different vector of the `xz`-plane has angle `π` modulo `2π`. -/
theorem rot_cos_neg_one {n w : V3} (hn : dot n n = 1) (hny : n.y = 0) (hwy : w.y = 0) {θ : ℝ}
    (hr : (rot n θ w).y = 0) (hne : rot n θ w ≠ w) : cos θ = -1 := by
  obtain ⟨nx, ny, nz⟩ := n
  obtain ⟨wx, wy, wz⟩ := w
  simp only at hny hwy
  subst hny hwy
  simp only [dot] at hn
  have hy : sin θ * (nz * wx - nx * wz) = 0 := by
    simp only [rot, cross, dot] at hr; linear_combination hr
  rcases mul_eq_zero.mp hy with hs | hq
  · have h2 : (cos θ - 1) * (cos θ + 1) = 0 := by
      linear_combination sin_sq_add_cos_sq θ - sin θ * hs
    rcases mul_eq_zero.mp h2 with h1 | h1
    · exfalso; apply hne
      have hc1 : cos θ = 1 := by linarith
      ext <;> simp [rot, cross, dot, hc1, hs]
    · linarith
  · exfalso; apply hne
    ext
    · simp only [rot, cross, dot]
      linear_combination (1 - cos θ) * (wx * hn - nz * hq)
    · simp only [rot, cross, dot]
      linear_combination sin θ * hq
    · simp only [rot, cross, dot]
      linear_combination (1 - cos θ) * (wz * hn + nx * hq)

theorem dot_ex_ex : dot ex ex = 1 := by simp [dot, ex]
theorem dot_em_em : dot em em = 1 := by simp [dot, em]
theorem dot_nk (k : ℝ) : dot (nk k) (nk k) = 1 := by
  simp only [dot, nk]; linear_combination sin_sq_add_cos_sq k

theorem rot_ex_dot_em (θ : ℝ) (w : V3) : dot (rot ex θ w) em = dot w em := by
  simp only [dot, rot, cross, ex, em]; ring

theorem state_unit (k : ℝ) (γ β : ℕ → ℝ) : ∀ j, dot (state k γ β j) (state k γ β j) = 1
  | 0 => dot_ex_ex
  | j + 1 => by
      simp only [state]
      exact rot_unit dot_ex_ex (rot_unit (dot_nk k) (state_unit k γ β j) _) _

theorem dot_nk_em (a : ℝ) : dot (nk (π - a)) em = cos a := by
  simp [dot, nk, em, cos_pi_sub]

/-- One layer moves the pseudospin of `π - a` by at most `2a` towards `em`. -/
theorem step {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ π) {w : V3} (hw : dot w w = 1) (θ : ℝ) :
    arccos (dot w em) ≤ arccos (dot (rot (nk (π - a)) θ w) em) + 2 * a := by
  have hn := dot_nk (π - a)
  have hne : arccos (dot (nk (π - a)) em) = a := by rw [dot_nk_em, arccos_cos ha0 ha1]
  have h1 := tri hw hn dot_em_em
  have h2 := tri (rot_unit hn hw θ) dot_em_em hn
  rw [dot_comm em, hne] at h2
  rw [hne] at h1
  rw [rot_dot_axis hn θ w] at h2
  linarith

theorem dot_ex_em : dot ex em = -1 := by simp [dot, ex, em]

/-- Forward form of the distance bound. -/
theorem forward {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ π) (γ β : ℕ → ℝ) (j : ℕ) :
    ∀ i : ℕ, arccos (dot (state (π - a) γ β j) em) - 2 * i * a
      ≤ arccos (dot (state (π - a) γ β (j + i)) em)
  | 0 => by simp
  | i + 1 => by
      have ih := forward ha0 ha1 γ β j i
      have hs := step ha0 ha1 (state_unit (π - a) γ β (j + i)) (4 * γ (j + i))
      rw [show j + (i + 1) = (j + i) + 1 by omega]
      simp only [state, rot_ex_dot_em]
      push_cast
      linarith

/-- Distance bound: after `j` layers the angle from `em` is at least `π - 2 j a`. -/
theorem depth_bound {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ π) (γ β : ℕ → ℝ) (j : ℕ) :
    π - 2 * j * a ≤ arccos (dot (state (π - a) γ β j) em) := by
  have h := forward ha0 ha1 γ β 0 j
  simp only [zero_add] at h
  have h0 : arccos (dot (state (π - a) γ β 0) em) = π := by
    simp only [state]; rw [dot_ex_em, arccos_neg_one]
  linarith

theorem arccos_em : arccos (dot em em) = 0 := by rw [dot_em_em, arccos_one]

theorem a_bounds {L : ℕ} (hL : 1 ≤ L) : 0 ≤ π / L ∧ π / L ≤ π := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  exact ⟨div_nonneg pi_pos.le (by linarith), div_le_self pi_pos.le hL'⟩

/-- Below depth `L / 2` the pseudospin of `π - π / L` cannot reach `em`. -/
theorem not_flipped (L p : ℕ) (hp : 2 * p < L) (γ β : ℕ → ℝ) :
    state (π - π / L) γ β p ≠ em := by
  intro h
  have hL : 1 ≤ L := by omega
  obtain ⟨ha0, ha1⟩ := a_bounds hL
  have hb := depth_bound ha0 ha1 γ β p
  rw [h, arccos_em] at hb
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hlt : (2 * p : ℝ) / L < 1 := (div_lt_one hLpos).mpr (by exact_mod_cast hp)
  have : 2 * (p : ℝ) * (π / L) = (2 * p) / L * π := by ring
  nlinarith [pi_pos]

/-- At depth `L / 2` every layer that brings the pseudospin of `π - a` to `em` is tight. -/
theorem tight {a : ℝ} (ha0 : 0 < a) (ha1 : a < π) (γ β : ℕ → ℝ) (p : ℕ)
    (hpa : 2 * p * a = π) (h : state (π - a) γ β p = em) (j : ℕ) (hj : j < p) :
    let w := state (π - a) γ β j
    let v := rot (nk (π - a)) (4 * γ j) w
    w.y = 0 ∧ v.y = 0 ∧ v ≠ w ∧
      arccos (dot w em) = arccos (dot w (nk (π - a))) + a ∧
      arccos (dot v (nk (π - a))) = arccos (dot v em) + a := by
  intro w v
  have hn := dot_nk (π - a)
  have hw : dot w w = 1 := state_unit _ γ β j
  have hv : dot v v = 1 := rot_unit hn hw _
  have hne : arccos (dot (nk (π - a)) em) = a := by
    rw [dot_nk_em, arccos_cos ha0.le ha1.le]
  -- exact values at `j` and `j + 1`
  have hval : ∀ i, i ≤ p → arccos (dot (state (π - a) γ β i) em) = π - 2 * i * a := by
    intro i hi
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hi
    have hf := forward ha0.le ha1.le γ β i r
    rw [h, arccos_em] at hf
    have hl := depth_bound ha0.le ha1.le γ β i
    push_cast at hpa
    nlinarith
  have hwj := hval j hj.le
  have hwj1 := hval (j + 1) hj
  have hvj : arccos (dot v em) = arccos (dot (state (π - a) γ β (j + 1)) em) := by
    show arccos (dot v em) = arccos (dot (rot ex (4 * β j) v) em)
    rw [rot_ex_dot_em]
  push_cast at hwj1
  have h1 := tri hw hn dot_em_em
  have h2 := tri hv dot_em_em hn
  rw [dot_comm em, hne] at h2
  rw [hne] at h1
  have h3 : dot v (nk (π - a)) = dot w (nk (π - a)) := rot_dot_axis hn _ w
  have e1 : arccos (dot w em) = arccos (dot w (nk (π - a))) + a := by
    rw [h3] at h2; linarith
  have e2 : arccos (dot v (nk (π - a))) = arccos (dot v em) + a := by
    rw [h3] at h2 ⊢; linarith
  have hsin : 0 < sin (π - a) := by rw [sin_pi_sub]; exact sin_pos_of_pos_of_lt_pi ha0 ha1
  refine ⟨?_, ?_, ?_, e1, e2⟩
  · have ht := tri_eq hw hn dot_em_em (by rw [hne]; exact e1)
    have : triple w (nk (π - a)) em = -(w.y * sin (π - a)) := by
      simp only [triple, dot, cross, nk, em]; ring
    rw [this, neg_eq_zero] at ht
    rcases mul_eq_zero.mp ht with h0 | h0
    · exact h0
    · linarith
  · have ht := tri_eq hv dot_em_em hn (by rw [dot_comm em, hne]; exact e2)
    have : triple v em (nk (π - a)) = v.y * sin (π - a) := by
      simp only [triple, dot, cross, nk, em]; ring
    rw [this] at ht
    rcases mul_eq_zero.mp ht with h0 | h0
    · exact h0
    · linarith
  · intro hvw
    have : arccos (dot v em) = arccos (dot w em) := by rw [hvw]
    linarith

/-- Rigidity at depth `L / 2`: flipping the pseudospin of `π - π / L` forces every angle `4 γ j`
and every intermediate angle `4 β j` to have cosine `-1`. -/
theorem rigidity (L p : ℕ) (hL : 2 * p = L) (hp : 1 ≤ p) (γ β : ℕ → ℝ)
    (h : state (π - π / L) γ β p = em) :
    (∀ j, j < p → cos (4 * γ j) = -1) ∧ (∀ j, j + 1 < p → cos (4 * β j) = -1) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  have ha0 : 0 < π / L := div_pos pi_pos hLpos
  have ha1 : π / L < π := div_lt_self pi_pos (by linarith)
  have hpa : 2 * (p : ℝ) * (π / L) = π := by
    have h2 : (2 * p : ℝ) = L := by exact_mod_cast hL
    calc 2 * (p : ℝ) * (π / L) = (2 * p) / L * π := by ring
      _ = π := by rw [h2, div_self hLpos.ne', one_mul]
  constructor
  · intro j hj
    obtain ⟨hwy, hvy, hne, -, -⟩ := tight ha0 ha1 γ β p hpa h j hj
    exact rot_cos_neg_one (dot_nk _) rfl hwy hvy hne
  · intro j hj
    obtain ⟨-, hvy, -, -, e2⟩ := tight ha0 ha1 γ β p hpa h j (by omega)
    obtain ⟨hwy', -, -, e1', -⟩ := tight ha0 ha1 γ β p hpa h (j + 1) hj
    have hne : rot ex (4 * β j) (rot (nk (π - π / L)) (4 * γ j) (state (π - π / L) γ β j))
        ≠ rot (nk (π - π / L)) (4 * γ j) (state (π - π / L) γ β j) := by
      intro heq
      have : state (π - π / L) γ β (j + 1)
          = rot (nk (π - π / L)) (4 * γ j) (state (π - π / L) γ β j) := by
        simp only [state]; exact heq
      simp only [this] at e1'
      linarith
    have hr : (rot ex (4 * β j) (rot (nk (π - π / L)) (4 * γ j)
        (state (π - π / L) γ β j))).y = 0 := by
      have : state (π - π / L) γ β (j + 1)
          = rot ex (4 * β j) (rot (nk (π - π / L)) (4 * γ j) (state (π - π / L) γ β j)) := by
        simp only [state]
      rw [← this]; exact hwy'
    exact rot_cos_neg_one dot_ex_ex rfl hvy hr hne

theorem sin_of_cos {θ : ℝ} (h : cos θ = -1) : sin θ = 0 := by
  have h2 : sin θ ^ 2 = 0 := by nlinarith [sin_sq_add_cos_sq θ]
  exact pow_eq_zero_iff (by norm_num) |>.mp h2

/-- A rotation by `π` about `nk k` reflects the `xz`-plane across the axis. -/
theorem rot_pi_nk {θ : ℝ} (h : cos θ = -1) (k φ : ℝ) :
    rot (nk k) θ (polar φ) = polar (2 * k - φ) := by
  have hs := sin_of_cos h
  ext
  · simp only [rot, cross, dot, nk, polar, h, hs]
    rw [cos_sub, cos_two_mul, sin_two_mul]; ring
  · simp only [rot, cross, dot, nk, polar, h, hs]; ring
  · simp only [rot, cross, dot, nk, polar, h, hs]
    rw [sin_sub, cos_two_mul, sin_two_mul]
    linear_combination 2 * sin φ * sin_sq_add_cos_sq k

/-- A rotation by `π` about `ex` reflects the `xz`-plane across `ex`. -/
theorem rot_pi_ex {θ : ℝ} (h : cos θ = -1) (φ : ℝ) : rot ex θ (polar φ) = polar (-φ) := by
  have hs := sin_of_cos h
  ext <;> simp only [rot, cross, dot, ex, polar, h, hs, cos_neg, sin_neg] <;> ring

theorem rot_ex_em (θ : ℝ) : rot ex θ em = em := by
  ext <;> simp only [rot, cross, dot, ex, em] <;> ring

/-- Under the angle conditions of `rigidity`, the pseudospin of every momentum `k` sits at
`polar (-(2 m k))` after `m < p` layers. -/
theorem state_polar (k : ℝ) (γ β : ℕ → ℝ) (p : ℕ)
    (hγ : ∀ j, j < p → cos (4 * γ j) = -1) (hβ : ∀ j, j + 1 < p → cos (4 * β j) = -1) :
    ∀ m, m < p → state k γ β m = polar (-(2 * m * k))
  | 0, _ => by ext <;> simp [state, ex, polar]
  | m + 1, hm => by
      simp only [state]
      rw [state_polar k γ β p hγ hβ m (by omega), rot_pi_nk (hγ m (by omega)),
        rot_pi_ex (hβ m hm)]
      congr 1; push_cast; ring

/-- Under the angle conditions of `rigidity` with `2 p = L`, every pseudospin `(2j + 1) π / L`
ends at `em`. -/
theorem all_flip (L p : ℕ) (hL : 2 * p = L) (hp : 1 ≤ p) (γ β : ℕ → ℝ)
    (hγ : ∀ j, j < p → cos (4 * γ j) = -1) (hβ : ∀ j, j + 1 < p → cos (4 * β j) = -1)
    (j : ℕ) : state ((2 * j + 1) * π / L) γ β p = em := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  simp only [state]
  rw [state_polar _ γ β (q + 1) hγ hβ q (by omega), rot_pi_nk (hγ q (by omega))]
  have hang : 2 * ((2 * j + 1) * π / L) - -(2 * (q : ℝ) * ((2 * j + 1) * π / L))
      = ((2 * j + 1 : ℕ) : ℝ) * π := by
    have hL' : (L : ℝ) = 2 * ((q : ℝ) + 1) := by rw [← hL]; push_cast; ring
    have hq1 : (2 * ((q : ℝ) + 1)) ≠ 0 := by positivity
    rw [hL']; push_cast; field_simp; ring
  have hpol : polar (((2 * j + 1 : ℕ) : ℝ) * π) = em := by
    ext <;> simp only [polar, em, cos_nat_mul_pi, sin_nat_mul_pi]
    · rw [pow_succ, pow_mul]; norm_num
  rw [hang, hpol, rot_ex_em]

/-- Rigidity and all-flip together: if the pseudospin of `π - π / L` ends at `em` after `L / 2`
layers, then so does every pseudospin `(2j + 1) π / L`. -/
theorem rigid_all_flip (L p : ℕ) (hL : 2 * p = L) (hp : 1 ≤ p) (γ β : ℕ → ℝ)
    (h : state (π - π / L) γ β p = em) (j : ℕ) : state ((2 * j + 1) * π / L) γ β p = em := by
  obtain ⟨hγ, hβ⟩ := rigidity L p hL hp γ β h
  exact all_flip L p hL hp γ β hγ hβ j

/-- No circuit of depth at most `L / 2` flips the pseudospin of `π - π / L` while the pseudospin
of `π / L` stays at `ex`. -/
theorem not_prepared (L p q : ℕ) (hL : 2 * p = L) (hp : 2 ≤ p) (hq : q ≤ p) (γ β : ℕ → ℝ) :
    ¬ (state (π - π / L) γ β q = em ∧ state (π / L) γ β q = ex) := by
  rintro ⟨h1, h2⟩
  rcases lt_or_eq_of_le hq with hlt | rfl
  · exact not_flipped L q (by omega) γ β h1
  · have h0 := rigid_all_flip L q hL (by omega) γ β h1 0
    have hk : ((2 * ((0 : ℕ) : ℝ) + 1) * π / L) = π / L := by push_cast; ring
    rw [hk, h2] at h0
    have hx := congrArg V3.x h0
    norm_num [em, ex] at hx

/-! ## Non-vacuity -/

theorem rot_zero (n : V3) (w : V3) : rot n 0 w = w := by
  ext <;> simp [rot]

/-- The zero circuit keeps every pseudospin at `ex`. -/
theorem zero_keeps (k : ℝ) (p : ℕ) : state k (fun _ => 0) (fun _ => 0) p = ex := by
  induction p with
  | zero => rfl
  | succ p ih => simp only [state, mul_zero, rot_zero, ih]

/-- The all-`π` circuit of depth `2` on a ring of `4` qubits flips the pseudospin of
`π - π / 4`: the hypothesis of `rigidity` can hold, and the distance bound of `depth_bound` is
attained (angle `0 = π - 2 · 2 · π / 4`). -/
theorem allpi_flips :
    state (π - π / ((4 : ℕ) : ℝ)) (fun _ => π / 4) (fun _ => π / 4) 2 = em := by
  have hc : cos (4 * (π / 4)) = -1 := by rw [show 4 * (π / 4) = π by ring, cos_pi]
  have h := all_flip 4 2 rfl (by norm_num) (fun _ => π / 4) (fun _ => π / 4)
    (fun _ _ => hc) (fun _ _ => hc) 1
  convert h using 2
  push_cast; ring

/-- The distance bound of `depth_bound` is attained by the all-`π` circuit at `L = 4`, `p = 2`. -/
theorem depth_bound_attained :
    arccos (dot (state (π - π / ((4 : ℕ) : ℝ)) (fun _ => π / 4) (fun _ => π / 4) 2) em)
      = π - 2 * ((2 : ℕ) : ℝ) * (π / ((4 : ℕ) : ℝ)) := by
  rw [allpi_flips, arccos_em]; push_cast; ring

/-- Each condition excluded by `not_prepared` can hold on its own at depth `L / 2` (here
`L = 4`): the all-`π` circuit flips the pseudospin of `π - π / 4`, and the zero circuit keeps
the pseudospin of `π / 4` at `ex`. -/
theorem not_prepared_parts :
    state (π - π / ((4 : ℕ) : ℝ)) (fun _ => π / 4) (fun _ => π / 4) 2 = em ∧
    state (π / ((4 : ℕ) : ℝ)) (fun _ => 0) (fun _ => 0) 2 = ex :=
  ⟨allpi_flips, zero_keeps _ 2⟩

end ChainDepth
