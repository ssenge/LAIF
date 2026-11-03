import Mathlib

/-!
# Algebraic core of the sparsity lemma for cut relations

Notation follows `QC/cutquery/RESULTS.md`, Section 3. `A` is an abelian group, in the application `ℝ/ℤ`.
Vectors `c v` carry a form with coefficients `H`; a dependency among them forces `λ_u • D_u` to vanish,
or to be small in the normed case.
-/

open Finset

namespace CutQuery

variable {V W ι A : Type*}

section Form

variable [Fintype W] [Fintype ι] [AddCommGroup A]

/-- The form `⟨c_u, c_v⟩_H = Σ_s c_u(s) c_v(s) H_s`. -/
def pr (c : W → ι → ℤ) (H : ι → A) (u v : W) : A :=
  ∑ s, (c u s * c v s) • H s

/-- `lam` is an integer dependency among the vectors `c v`. -/
def IsDep (c : W → ι → ℤ) (lam : W → ℤ) : Prop :=
  ∀ s, ∑ v, lam v * c v s = 0

/-- Pairing a dependency with any vector gives zero. -/
theorem sum_smul_pr_eq_zero (c : W → ι → ℤ) (H : ι → A) (lam : W → ℤ) (hl : IsDep c lam) (u : W) :
    ∑ v, lam v • pr c H u v = 0 := by
  unfold pr
  simp_rw [smul_sum, smul_smul]
  rw [sum_comm]
  apply sum_eq_zero
  intro s _
  have h : ∑ v, (lam v * (c u s * c v s)) • H s = (c u s * ∑ v, lam v * c v s) • H s := by
    rw [mul_sum, sum_smul]
    exact sum_congr rfl fun v _ => by rw [mul_left_comm]
  rw [h, hl s, mul_zero, zero_smul]

variable [DecidableEq W]

/-- Exact case: the off-diagonal entries vanish, so `λ_u • D_u = 0`. -/
theorem smul_diag_eq_zero (c : W → ι → ℤ) (H : ι → A) (D : W → A) (lam : W → ℤ) (hl : IsDep c lam)
    (hd : ∀ u, pr c H u u = D u) (ho : ∀ u v, u ≠ v → pr c H u v = 0) (u : W) : lam u • D u = 0 := by
  have h := sum_smul_pr_eq_zero c H lam hl u
  rw [← add_sum_erase _ _ (mem_univ u), sum_eq_zero, add_zero, hd] at h
  · exact h
  · intro v hv
    rw [ho u v (ne_of_mem_erase hv).symm, smul_zero]

end Form

section Norm

variable [Fintype W] [Fintype ι] [DecidableEq W] [SeminormedAddCommGroup A]

/-- Near case: with off-diagonal entries of norm at most `η`, `‖λ_u • D_u‖ ≤ ‖λ‖₁ η`. -/
theorem norm_smul_diag_le (c : W → ι → ℤ) (H : ι → A) (D : W → A) (lam : W → ℤ) (η : ℝ) (hη : 0 ≤ η)
    (hl : IsDep c lam) (hd : ∀ u, pr c H u u = D u) (ho : ∀ u v, u ≠ v → ‖pr c H u v‖ ≤ η) (u : W) :
    ‖lam u • D u‖ ≤ (∑ v, |(lam v : ℝ)|) * η := by
  have h := sum_smul_pr_eq_zero c H lam hl u
  rw [← add_sum_erase _ _ (mem_univ u), hd] at h
  have h' : lam u • D u = -∑ v ∈ univ.erase u, lam v • pr c H u v := eq_neg_of_add_eq_zero_left h
  rw [h', norm_neg]
  calc ‖∑ v ∈ univ.erase u, lam v • pr c H u v‖
      ≤ ∑ v ∈ univ.erase u, ‖lam v • pr c H u v‖ := norm_sum_le _ _
    _ ≤ ∑ v ∈ univ.erase u, |(lam v : ℝ)| * η := by
        refine sum_le_sum fun v hv => ?_
        have h1 : ‖lam v • pr c H u v‖ ≤ |(lam v : ℝ)| * ‖pr c H u v‖ := by
          have := norm_zsmul_le (lam v) (pr c H u v)
          simpa [Int.norm_eq_abs] using this
        exact h1.trans (mul_le_mul_of_nonneg_left (ho u v (ne_of_mem_erase hv).symm) (abs_nonneg _))
    _ ≤ ∑ v, |(lam v : ℝ)| * η :=
        sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ =>
          mul_nonneg (abs_nonneg _) hη
    _ = (∑ v, |(lam v : ℝ)|) * η := by rw [sum_mul]

end Norm

section TwoGroup

variable [Fintype W] [Fintype ι] [DecidableEq W] [AddCommGroup A]

/-- An odd multiple and a power of 2 both killing `g` force `g = 0`. -/
theorem eq_zero_of_odd_smul {a : ℤ} (ha : Odd a) {k : ℕ} {g : A} (h1 : a • g = 0)
    (h2 : ((2 : ℤ) ^ k) • g = 0) : g = 0 := by
  obtain ⟨b, hb⟩ := ha
  have hc : IsCoprime a (2 : ℤ) := ⟨1, -b, by rw [hb]; ring⟩
  obtain ⟨p, q, hpq⟩ := hc.pow_right (n := k)
  calc g = (p * a + q * (2 : ℤ) ^ k) • g := by rw [hpq, one_smul]
    _ = p • (a • g) + q • (((2 : ℤ) ^ k) • g) := by rw [add_smul, mul_smul, mul_smul]
    _ = 0 := by rw [h1, h2, smul_zero, smul_zero, add_zero]

/-- Exact case over a 2-group: the vectors `c v` admit no nonzero dependency. -/
theorem dep_eq_zero_of_two_power (c : W → ι → ℤ) (H : ι → A) (D : W → A)
    (hd : ∀ u, pr c H u u = D u) (ho : ∀ u v, u ≠ v → pr c H u v = 0)
    (hne : ∀ u, D u ≠ 0) (hpow : ∀ u, ∃ k : ℕ, ((2 : ℤ) ^ k) • D u = 0)
    (lam : W → ℤ) (hl : IsDep c lam) : lam = 0 := by
  have key : ∀ (k : ℕ) (l : W → ℤ), IsDep c l → ∀ u, (2 : ℤ) ^ k ∣ l u := by
    intro k
    induction k with
    | zero => intro l _ u; simp
    | succ k ih =>
      intro l hl' u
      have heven : ∀ v, 2 ∣ l v := by
        intro v
        rcases Int.even_or_odd (l v) with he | ho'
        · exact he.two_dvd
        · obtain ⟨j, hj⟩ := hpow v
          exact absurd
            (eq_zero_of_odd_smul ho' (smul_diag_eq_zero c H D l hl' hd ho v) hj) (hne v)
      choose l' hl'' using heven
      have hdep : IsDep c l' := by
        intro s
        have hs := hl' s
        have : (2 : ℤ) * ∑ v, l' v * c v s = 0 := by
          rw [mul_sum, ← hs]
          exact sum_congr rfl fun v _ => by rw [hl'' v]; ring
        simpa using this
      obtain ⟨w, hw⟩ := ih l' hdep u
      exact ⟨w, by rw [hl'' u, hw]; ring⟩
  funext u
  have h := key ((lam u).natAbs + 1) lam hl u
  by_contra hu
  have hu' : lam u ≠ 0 := hu
  have hle := Int.le_of_dvd (abs_pos.mpr hu') ((dvd_abs _ _).mpr h)
  have hlt : ((lam u).natAbs : ℤ) < (2 : ℤ) ^ ((lam u).natAbs + 1) := by
    have := Nat.lt_two_pow_self (n := (lam u).natAbs + 1)
    have h3 : (lam u).natAbs < 2 ^ ((lam u).natAbs + 1) := by omega
    exact_mod_cast h3
  rw [Int.abs_eq_natAbs] at hle
  omega

/-- Exact case over a 2-group: at most `dim` vectors, where `dim` is the length of the vectors. -/
theorem card_le_of_two_power (c : W → ι → ℤ) (H : ι → A) (D : W → A)
    (hd : ∀ u, pr c H u u = D u) (ho : ∀ u v, u ≠ v → pr c H u v = 0)
    (hne : ∀ u, D u ≠ 0) (hpow : ∀ u, ∃ k : ℕ, ((2 : ℤ) ^ k) • D u = 0) :
    Fintype.card W ≤ Fintype.card ι := by
  have hli : LinearIndependent ℤ c := by
    rw [Fintype.linearIndependent_iff]
    intro g hg u
    have hdep : IsDep c g := by
      intro s
      have := congrFun hg s
      simpa [Finset.sum_apply, smul_eq_mul] using this
    exact congrFun (dep_eq_zero_of_two_power c H D hd ho hne hpow g hdep) u
  have := hli.fintype_card_le_finrank
  simpa [Module.finrank_fintype_fun_eq_card] using this

end TwoGroup

section CutForm

variable [Fintype ι] [AddCommGroup A]

/-- `F_uv = Σ_s (x_u + x_v - 2 x_u x_v) • t_s`; on binary `x` the coefficient is the indicator of `x_u ≠ x_v`. -/
def cutSum (x : ι → V → ℤ) (t : ι → A) (u v : V) : A :=
  ∑ s, (x s u + x s v - 2 * (x s u * x s v)) • t s

/-- The vectors `ŷ_v = (x_v - x_o, 1)`, with the extra coordinate at `none`. -/
def yhat (x : ι → V → ℤ) (o v : V) : Option ι → ℤ
  | some s => x s v - x s o
  | none => 1

/-- The coefficients `Ĥ = (2 t, -2 β_o)`. -/
def Hhat (t : ι → A) (βo : A) : Option ι → A
  | some s => (2 : ℤ) • t s
  | none => -((2 : ℤ) • βo)

/-- `⟨ŷ_u, ŷ_v⟩ = F_uo + F_vo - F_uv - 2 β_o` for binary `x`. -/
theorem pr_yhat (x : ι → V → ℤ) (t : ι → A) (βo : A) (o : V) (hx : ∀ s, x s o = 0 ∨ x s o = 1)
    (u v : V) :
    pr (yhat x o) (Hhat t βo) u v
      = cutSum x t u o + cutSum x t v o - cutSum x t u v - (2 : ℤ) • βo := by
  unfold pr cutSum
  rw [Fintype.sum_option]
  simp only [yhat, Hhat, mul_one, one_smul]
  rw [← sum_add_distrib, ← sum_sub_distrib, add_comm, sub_eq_add_neg]
  congr 1
  refine sum_congr rfl fun s _ => ?_
  rw [smul_smul, ← add_smul, ← sub_smul]
  congr 1
  rcases hx s with h | h <;> rw [h] <;> ring

/-- The off-diagonal identity: `⟨ŷ_u, ŷ_v⟩ = ε_uo + ε_vo - ε_uv`, from `F = β_u + β_v + ε`. -/
theorem pr_yhat_offdiag (x : ι → V → ℤ) (t : ι → A) (β : V → A) (ε : V → V → A) (o : V)
    (hx : ∀ s, x s o = 0 ∨ x s o = 1)
    (hF : ∀ a b, a ≠ b → cutSum x t a b = β a + β b + ε a b)
    {u v : V} (huv : u ≠ v) (huo : u ≠ o) (hvo : v ≠ o) :
    pr (yhat x o) (Hhat t (β o)) u v = ε u o + ε v o - ε u v := by
  rw [pr_yhat x t (β o) o hx, hF u o huo, hF v o hvo, hF u v huv, two_smul]
  abel

/-- The diagonal identity: `⟨ŷ_v, ŷ_v⟩ = 2 β_v + 2 ε_vo`. -/
theorem pr_yhat_diag (x : ι → V → ℤ) (t : ι → A) (β : V → A) (ε : V → V → A) (o : V)
    (hx : ∀ s v, x s v = 0 ∨ x s v = 1)
    (hF : ∀ a b, a ≠ b → cutSum x t a b = β a + β b + ε a b)
    {v : V} (hvo : v ≠ o) :
    pr (yhat x o) (Hhat t (β o)) v v = (2 : ℤ) • β v + (2 : ℤ) • ε v o := by
  have hself : cutSum x t v v = 0 := by
    unfold cutSum
    refine sum_eq_zero fun s _ => ?_
    rcases hx s v with h | h <;> simp [h]
  rw [pr_yhat x t (β o) o (fun s => hx s o), hself, hF v o hvo, two_smul, two_smul, two_smul]
  abel

/-- Decomposition (1): choosing `β_v = F_ov - β_o` with `2 β_o = F_o1 + F_o2 - F_12` gives
`F_uv = β_u + β_v + ε_uv`, where `ε_uv = F_uv - F_ou - F_ov + F_o1 + F_o2 - F_12` is the label of `b_uv`. -/
theorem decomposition (F : V → V → A) (o p q : V) (βo : A) (h : (2 : ℤ) • βo = F o p + F o q - F p q)
    (u v : V) :
    F u v = (F o u - βo) + (F o v - βo) + (F u v - F o u - F o v + F o p + F o q - F p q) := by
  have h' : βo + βo = F o p + F o q - F p q := by rw [← two_smul ℤ βo]; exact h
  have : F u v = F u v - F o u - F o v + (F o u + F o v) := by abel
  calc F u v = F u v - F o u - F o v + F o u + F o v := by abel
    _ = (F o u - βo) + (F o v - βo) + (F u v - F o u - F o v + (βo + βo)) := by abel
    _ = _ := by rw [h']; abel

end CutForm

/-- Exact 2-group case of the sparsity lemma. If all labels vanish, the vertices `Y` other than the
base with `2 β_v ≠ 0` number at most `R + 1`. -/
theorem exact_sparsity_two_group [Fintype ι] [AddCommGroup A] [DecidableEq V]
    (x : ι → V → ℤ) (t : ι → A) (β : V → A) (o : V) (hx : ∀ s v, x s v = 0 ∨ x s v = 1)
    (hF : ∀ a b, a ≠ b → cutSum x t a b = β a + β b)
    (Y : Finset V) (hYo : o ∉ Y) (hne : ∀ v ∈ Y, (2 : ℤ) • β v ≠ 0)
    (hpow : ∀ v ∈ Y, ∃ k : ℕ, ((2 : ℤ) ^ k) • ((2 : ℤ) • β v) = 0) :
    Y.card ≤ Fintype.card ι + 1 := by
  have hF' : ∀ a b, a ≠ b → cutSum x t a b = β a + β b + (fun _ _ => (0 : A)) a b := by
    intro a b hab; simpa using hF a b hab
  have hvo : ∀ v : Y, (v : V) ≠ o := fun v h => hYo (h ▸ v.2)
  have := card_le_of_two_power (W := Y) (ι := Option ι)
    (fun v => yhat x o (v : V)) (Hhat t (β o)) (fun v => (2 : ℤ) • β (v : V))
    (fun u => by
      have := pr_yhat_diag x t β (fun _ _ => (0 : A)) o hx hF' (hvo u)
      simpa [pr] using this)
    (fun u v huv => by
      have hne' : (u : V) ≠ v := fun h => huv (Subtype.ext h)
      have := pr_yhat_offdiag x t β (fun _ _ => (0 : A)) o (fun s => hx s o) hF' hne' (hvo u) (hvo v)
      simpa [pr] using this)
    (fun u => hne u u.2) (fun u => hpow u u.2)
  simpa [Fintype.card_option] using this

/-- Near case of the sparsity lemma. With `F = β_u + β_v + ε`, labels of norm at most `η` and `ε_vo = 0`,
any dependency among the `ŷ_v` satisfies `‖λ_u • 2 β_u‖ ≤ ‖λ‖₁ η`. -/
theorem near_divisibility [Fintype ι] [SeminormedAddCommGroup A] [DecidableEq V]
    (x : ι → V → ℤ) (t : ι → A) (β : V → A) (ε : V → V → A) (o : V) (η : ℝ) (hη : 0 ≤ η)
    (hx : ∀ s v, x s v = 0 ∨ x s v = 1)
    (hF : ∀ a b, a ≠ b → cutSum x t a b = β a + β b + ε a b)
    (hε : ∀ a b, ‖ε a b‖ ≤ η) (hεo : ∀ a, ε a o = 0)
    (Y : Finset V) (hYo : o ∉ Y) (lam : Y → ℤ)
    (hl : IsDep (fun v : Y => yhat x o (v : V)) lam) (u : Y) :
    ‖lam u • ((2 : ℤ) • β (u : V))‖ ≤ (∑ v, |(lam v : ℝ)|) * η := by
  have hvo : ∀ v : Y, (v : V) ≠ o := fun v h => hYo (h ▸ v.2)
  refine norm_smul_diag_le (fun v : Y => yhat x o (v : V)) (Hhat t (β o))
    (fun v => (2 : ℤ) • β (v : V)) lam η hη hl ?_ ?_ u
  · intro w
    have := pr_yhat_diag x t β ε o hx hF (hvo w)
    rw [hεo, smul_zero, add_zero] at this
    exact this
  · intro a b hab
    have hne' : (a : V) ≠ b := fun h => hab (Subtype.ext h)
    have := pr_yhat_offdiag x t β ε o (fun s => hx s o) hF hne' (hvo a) (hvo b)
    rw [hεo, hεo, zero_add, zero_sub] at this
    have h2 : ‖pr (fun v : Y => yhat x o (v : V)) (Hhat t (β o)) a b‖ = ‖ε a b‖ := by
      have h3 : pr (fun v : Y => yhat x o (v : V)) (Hhat t (β o)) a b
          = pr (yhat x o) (Hhat t (β o)) a b := rfl
      rw [h3, this, norm_neg]
    exact h2.le.trans (hε _ _)

/-- Passing from a divisor `g` of `G` to `G`: `‖G • a‖ ≤ |G| ‖g • a‖`. This is the step `g_u ≤ m` in Lemma 2. -/
theorem norm_smul_of_dvd [SeminormedAddCommGroup A] {g G : ℤ} (hg : g ∣ G) (hG : G ≠ 0) (a : A) :
    ‖G • a‖ ≤ |(G : ℝ)| * ‖g • a‖ := by
  obtain ⟨k, rfl⟩ := hg
  have hg0 : g ≠ 0 := left_ne_zero_of_mul hG
  have hk0 : k ≠ 0 := right_ne_zero_of_mul hG
  have h1 : ‖(g * k) • a‖ ≤ |(k : ℝ)| * ‖g • a‖ := by
    rw [mul_comm, mul_smul]
    have := norm_zsmul_le k (g • a)
    simpa [Int.norm_eq_abs] using this
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have hg1 : (1 : ℝ) ≤ |(g : ℝ)| := by exact_mod_cast Int.one_le_abs hg0
  push_cast
  rw [abs_mul]
  nlinarith [abs_nonneg (k : ℝ)]

end CutQuery
