import Mathlib

/-!
# Classical simulation of bounded low-degree polynomials on most inputs

Let `p` be a real polynomial of total degree at most `d ≥ 1` with `0 ≤ p ≤ 1` on `{0,1}^N`. For
`ε, δ > 0` there is a deterministic decision tree of depth at most `⌈2d/(δφ)⌉`, where
`φ = (8 √15 / (125 π^4)) (ε²δ/2)^{5/2} / d^6`, whose output is within `ε` of `p(X)` on all but a
`δ` fraction of the inputs `X` (`simulation`). The tree queries a variable of influence at least `φ`
as long as the variance of the restricted polynomial is at least `ε²δ/2`, and outputs the mean of
the restriction otherwise.

The two hypotheses are stated as propositions:

* `ExplicitBound`: the influence bound for bounded low-degree polynomials with the explicit
  constant, copied verbatim from `AaronsonAmbainis/Conjecture.lean` of
  https://github.com/physical-superintelligence/aaronson-ambainis (commit
  `2a6ceaef872ae993708950f951989134084b851a`), where it is the statement of the theorem
  `AaronsonAmbainis.aaronson_ambainis_explicit`; the paper is arXiv:2611.09773.
* `TotalInfluenceBound`: the folklore bound `Σ_i Inf_i[p] ≤ d` for a polynomial of degree at most
  `d` with values in `[0,1]` on `{0,1}^N`, Lemma 20 of arXiv:0911.0996v3 (Lemma 3.1 of the journal
  version, Theory of Computing 10 (2014) 133–166), in the same encoding.

The reduction (the potential argument with the total influence, the restriction identities and the
tree construction) is proved here.
-/

namespace AASimulation

open Finset MvPolynomial

/-- The influence bound with an explicit constant, verbatim from `AaronsonAmbainis/Conjecture.lean`
(commit `2a6ceaef872ae993708950f951989134084b851a` of
https://github.com/physical-superintelligence/aaronson-ambainis), where it is the statement of
`AaronsonAmbainis.aaronson_ambainis_explicit`: a polynomial `p` of total degree at most `d` with
`0 ≤ p ≤ 1` on `{0,1}^N` and variance at least `ε > 0` has a variable `i` with
`E[(p(X) − p(X^i))²] ≥ (8 √15 / (125 π^4)) ε^{5/2} / d^6`. -/
def ExplicitBound : Prop :=
  ∀ (N d : ℕ) (p : MvPolynomial (Fin N) ℝ), p.totalDegree ≤ d →
    (∀ X : Fin N → Bool,
      0 ≤ MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ∧
        MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ≤ 1) →
    ∀ ε : ℝ, 0 < ε →
      (∑ X : Fin N → Bool,
          (MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p
            - (∑ Y : Fin N → Bool, MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else 0) p)
                / 2 ^ N) ^ 2) / 2 ^ N ≥ ε →
      ∃ i : Fin N,
        (∑ X : Fin N → Bool,
          (MvPolynomial.eval (fun k => if X k then (1 : ℝ) else 0) p
            - MvPolynomial.eval
                (fun k => if Function.update X i (!X i) k then (1 : ℝ) else 0) p) ^ 2) / 2 ^ N
          ≥ 8 * Real.sqrt 15 / (125 * Real.pi ^ 4) * ε ^ ((5 : ℝ) / 2) / (d : ℝ) ^ 6

/-- The total influence bound, Lemma 20 of arXiv:0911.0996v3 (Lemma 3.1 of the journal version):
for a polynomial `p` of total degree at most `d` with `0 ≤ p ≤ 1` on `{0,1}^N`,
`Σ_i E[(p(X) − p(X^i))²] ≤ d`. -/
def TotalInfluenceBound : Prop :=
  ∀ (N d : ℕ) (p : MvPolynomial (Fin N) ℝ), p.totalDegree ≤ d →
    (∀ X : Fin N → Bool,
      0 ≤ MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ∧
        MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ≤ 1) →
    ∑ i : Fin N,
        (∑ X : Fin N → Bool,
          (MvPolynomial.eval (fun k => if X k then (1 : ℝ) else 0) p
            - MvPolynomial.eval
                (fun k => if Function.update X i (!X i) k then (1 : ℝ) else 0) p) ^ 2) / 2 ^ N
      ≤ d

variable {N : ℕ}

/-- The mean over the uniform distribution on `{0,1}^N`. -/
noncomputable def mean (f : (Fin N → Bool) → ℝ) : ℝ := (∑ X, f X) / 2 ^ N

/-- The variance. -/
noncomputable def var (f : (Fin N → Bool) → ℝ) : ℝ := mean fun X => (f X - mean f) ^ 2

/-- The influence `E[(f(X) − f(X^i))²]` of the variable `i`. -/
noncomputable def inf (i : Fin N) (f : (Fin N → Bool) → ℝ) : ℝ :=
  mean fun X => (f X - f (Function.update X i (!X i))) ^ 2

/-- The total influence. -/
noncomputable def totInf (f : (Fin N → Bool) → ℝ) : ℝ := ∑ i, inf i f

/-- The restriction `x_i = b`, as a function on the whole cube. -/
def restrict (i : Fin N) (b : Bool) (f : (Fin N → Bool) → ℝ) : (Fin N → Bool) → ℝ :=
  fun X => f (Function.update X i b)

theorem mean_le_mean {f g : (Fin N → Bool) → ℝ} (h : ∀ X, f X ≤ g X) : mean f ≤ mean g :=
  div_le_div_of_nonneg_right (sum_le_sum fun X _ => h X) (by positivity)

theorem mean_nonneg {f : (Fin N → Bool) → ℝ} (h : ∀ X, 0 ≤ f X) : 0 ≤ mean f :=
  div_nonneg (sum_nonneg fun X _ => h X) (by positivity)

theorem mean_div (f : (Fin N → Bool) → ℝ) (c : ℝ) : mean (fun X => f X / c) = mean f / c := by
  unfold mean; rw [← sum_div]; ring

theorem sum_flip (i : Fin N) (F : (Fin N → Bool) → ℝ) :
    ∑ X, F (Function.update X i (!X i)) = ∑ X, F X := by
  let e : (Fin N → Bool) ≃ (Fin N → Bool) :=
    { toFun := fun X => Function.update X i (!X i)
      invFun := fun X => Function.update X i (!X i)
      left_inv := fun X => by simp
      right_inv := fun X => by simp }
  exact e.sum_comp F

/-- Averaging over the value of one coordinate. -/
theorem mean_restrict (i : Fin N) (F : (Fin N → Bool) → ℝ) :
    mean (restrict i true F) + mean (restrict i false F) = 2 * mean F := by
  have h : ∀ X, restrict i true F X + restrict i false F X =
      F X + F (Function.update X i (!X i)) := by
    intro X
    cases hX : X i
    · have e : Function.update X i false = X := by rw [← hX]; exact Function.update_eq_self i X
      simp only [restrict, e, Bool.not_false]; ring
    · have e : Function.update X i true = X := by rw [← hX]; exact Function.update_eq_self i X
      simp only [restrict, e, Bool.not_true]
  unfold mean
  rw [← add_div, ← sum_add_distrib, sum_congr rfl fun X _ => h X, sum_add_distrib, sum_flip]
  ring

theorem restrict_update (i : Fin N) (b c : Bool) (f : (Fin N → Bool) → ℝ) (X : Fin N → Bool) :
    restrict i b f (Function.update X i c) = restrict i b f X := by
  simp [restrict]

theorem inf_restrict_self (i : Fin N) (b : Bool) (f : (Fin N → Bool) → ℝ) :
    inf i (restrict i b f) = 0 := by
  simp [inf, restrict, mean]

theorem inf_restrict_ne {i j : Fin N} (hji : j ≠ i) (f : (Fin N → Bool) → ℝ) :
    inf j (restrict i true f) + inf j (restrict i false f) = 2 * inf j f := by
  have key : ∀ b, inf j (restrict i b f) =
      mean (restrict i b fun Y => (f Y - f (Function.update Y j (!Y j))) ^ 2) := by
    intro b
    unfold inf
    congr 1
    funext X
    simp only [restrict]
    rw [Function.update_of_ne hji, Function.update_comm hji]
  rw [key, key]
  exact mean_restrict i _

theorem inf_nonneg (i : Fin N) (f : (Fin N → Bool) → ℝ) : 0 ≤ inf i f :=
  mean_nonneg fun X => sq_nonneg _

theorem totInf_nonneg (f : (Fin N → Bool) → ℝ) : 0 ≤ totInf f :=
  sum_nonneg fun i _ => inf_nonneg i f

/-- Restricting the variable `i` removes its influence and keeps the others on average. -/
theorem totInf_restrict (i : Fin N) (f : (Fin N → Bool) → ℝ) :
    totInf (restrict i true f) + totInf (restrict i false f) = 2 * (totInf f - inf i f) := by
  have h : ∀ j, inf j (restrict i true f) + inf j (restrict i false f) =
      2 * inf j f - if j = i then 2 * inf i f else 0 := by
    intro j
    by_cases hj : j = i
    · subst hj; simp [inf_restrict_self]
    · rw [inf_restrict_ne hj, if_neg hj, sub_zero]
  unfold totInf
  rw [← sum_add_distrib, sum_congr rfl fun j _ => h j, sum_sub_distrib, ← mul_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- Decision trees on `{0,1}^N` with real leaves. -/
inductive DTree (N : ℕ) where
  | leaf : ℝ → DTree N
  | node : Fin N → DTree N → DTree N → DTree N

namespace DTree

/-- The output on an input: at `node i t0 t1` the tree queries `X i` and goes to `t1` on `true`. -/
def eval : DTree N → (Fin N → Bool) → ℝ
  | leaf r, _ => r
  | node i t0 t1, X => if X i then t1.eval X else t0.eval X

/-- The depth, the largest number of queries on an input. -/
def depth : DTree N → ℕ
  | leaf _ => 0
  | node _ t0 t1 => max t0.depth t1.depth + 1

/-- The tree read with `x_i = b`: every query of `i` is answered by `b`. -/
def fix (i : Fin N) (b : Bool) : DTree N → DTree N
  | leaf r => leaf r
  | node j t0 t1 =>
    if j = i then (if b then fix i b t1 else fix i b t0) else node j (fix i b t0) (fix i b t1)

theorem eval_fix (i : Fin N) (b : Bool) (t : DTree N) (X : Fin N → Bool) :
    (t.fix i b).eval X = t.eval (Function.update X i b) := by
  induction t with
  | leaf r => rfl
  | node j t0 t1 ih0 ih1 =>
    by_cases hj : j = i
    · subst hj
      cases b <;> simp [fix, eval, ih0, ih1]
    · simp [fix, eval, hj, ih0, ih1, Function.update_of_ne hj]

theorem depth_fix (i : Fin N) (b : Bool) (t : DTree N) : (t.fix i b).depth ≤ t.depth := by
  induction t with
  | leaf r => simp [fix, depth]
  | node j t0 t1 ih0 ih1 =>
    simp only [fix]
    split_ifs <;> simp only [depth] <;> omega

theorem eval_fix_update (i : Fin N) (b c : Bool) (t : DTree N) (X : Fin N → Bool) :
    (t.fix i b).eval (Function.update X i c) = (t.fix i b).eval X := by
  rw [eval_fix, eval_fix, Function.update_idem]

end DTree

open DTree

/-- The fraction of inputs on which the tree `t` is more than `ε` away from `f`. -/
noncomputable def bad (ε : ℝ) (t : DTree N) (f : (Fin N → Bool) → ℝ) : ℝ :=
  mean fun X => if ε < |t.eval X - f X| then 1 else 0

theorem bad_nonneg (ε : ℝ) (t : DTree N) (f : (Fin N → Bool) → ℝ) : 0 ≤ bad ε t f :=
  mean_nonneg fun X => by split_ifs <;> norm_num

theorem bad_le_one (ε : ℝ) (t : DTree N) (f : (Fin N → Bool) → ℝ) : bad ε t f ≤ 1 := by
  have h : bad ε t f ≤ mean fun _ => (1 : ℝ) := mean_le_mean fun X => by split_ifs <;> norm_num
  simpa [mean] using h

theorem ind_le_sq {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    (if ε < |a| then (1 : ℝ) else 0) ≤ a ^ 2 / ε ^ 2 := by
  split_ifs with h
  · have h2 := mul_self_lt_mul_self hε.le h
    rw [abs_mul_abs_self] at h2
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  · positivity

/-- A leaf with the mean: the inequality of the second moment. -/
theorem bad_leaf_le {ε : ℝ} (hε : 0 < ε) (f : (Fin N → Bool) → ℝ) :
    bad ε (leaf (mean f)) f ≤ var f / ε ^ 2 := by
  unfold bad var
  rw [← mean_div]
  refine mean_le_mean fun X => ?_
  have := ind_le_sq hε (mean f - f X)
  simp only [DTree.eval]
  calc (if ε < |mean f - f X| then (1 : ℝ) else 0) ≤ (mean f - f X) ^ 2 / ε ^ 2 := this
    _ = (f X - mean f) ^ 2 / ε ^ 2 := by ring

/-- One of the two readings `x_i = c` of a tree is as good as the tree, for a function that
ignores `x_i`. -/
theorem exists_fix_le (ε : ℝ) (i : Fin N) (t : DTree N) (g : (Fin N → Bool) → ℝ)
    (hg : ∀ c X, g (Function.update X i c) = g X) :
    ∃ c, bad ε (t.fix i c) g ≤ bad ε t g := by
  set K : (Fin N → Bool) → ℝ := fun X => if ε < |t.eval X - g X| then 1 else 0
  have h : ∀ c, bad ε (t.fix i c) g = mean (restrict i c K) := by
    intro c
    unfold bad
    congr 1
    funext X
    simp only [K, restrict, eval_fix, hg]
  have hm := mean_restrict i K
  have hK : bad ε t g = mean K := rfl
  rw [← h, ← h, ← hK] at hm
  by_cases h1 : bad ε (t.fix i true) g ≤ bad ε t g
  · exact ⟨true, h1⟩
  · exact ⟨false, by linarith⟩

/-- The error of a tree that queries `i` first, with subtrees that ignore `x_i`. -/
theorem bad_node (ε : ℝ) (i : Fin N) (s0 s1 : DTree N) (f : (Fin N → Bool) → ℝ)
    (h0 : ∀ c X, s0.eval (Function.update X i c) = s0.eval X)
    (h1 : ∀ c X, s1.eval (Function.update X i c) = s1.eval X) :
    2 * bad ε (node i s0 s1) f = bad ε s1 (restrict i true f) + bad ε s0 (restrict i false f) := by
  unfold bad
  rw [← mean_restrict i]
  congr 1 <;> (congr 1; funext X; simp [restrict, DTree.eval, h0, h1]; try exact if_congr Iff.rfl rfl rfl)

/-- The potential argument: for a class of functions closed under restrictions in which every
function of variance at least `τ` has a variable of influence at least `φ`, every function of the
class has, for every `k`, a tree of depth at most `k` with
`k φ · bad ≤ k φ τ/ε² + totInf f`. -/
theorem exists_tree (C : ((Fin N → Bool) → ℝ) → Prop)
    (hC : ∀ f i b, C f → C (restrict i b f))
    {ε τ φ : ℝ} (hε : 0 < ε) (hτ : 0 ≤ τ) (hφ : 0 ≤ φ)
    (hAA : ∀ f, C f → τ ≤ var f → ∃ i, φ ≤ inf i f) :
    ∀ k : ℕ, ∀ f, C f → ∃ t : DTree N, t.depth ≤ k ∧
      (k : ℝ) * φ * bad ε t f ≤ (k : ℝ) * φ * (τ / ε ^ 2) + totInf f := by
  intro k
  induction k with
  | zero =>
    intro f _
    exact ⟨leaf (mean f), le_rfl, by simpa using totInf_nonneg f⟩
  | succ k ih =>
    intro f hf
    have hτ' : 0 ≤ τ / ε ^ 2 := by positivity
    by_cases hv : var f < τ
    · refine ⟨leaf (mean f), Nat.zero_le _, ?_⟩
      have h1 := bad_leaf_le hε f
      have h2 : var f / ε ^ 2 ≤ τ / ε ^ 2 := div_le_div_of_nonneg_right hv.le (by positivity)
      have h3 := totInf_nonneg f
      have hk : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * φ := by positivity
      have := mul_le_mul_of_nonneg_left (h1.trans h2) hk
      linarith
    · push_neg at hv
      obtain ⟨i, hi⟩ := hAA f hf hv
      obtain ⟨t1, hd1, hb1⟩ := ih _ (hC f i true hf)
      obtain ⟨t0, hd0, hb0⟩ := ih _ (hC f i false hf)
      obtain ⟨c1, hc1⟩ := exists_fix_le ε i t1 (restrict i true f) (restrict_update i true · f)
      obtain ⟨c0, hc0⟩ := exists_fix_le ε i t0 (restrict i false f) (restrict_update i false · f)
      refine ⟨node i (t0.fix i c0) (t1.fix i c1), ?_, ?_⟩
      · have := depth_fix i c0 t0
        have := depth_fix i c1 t1
        simp only [depth]
        omega
      · have hn := bad_node ε i (t0.fix i c0) (t1.fix i c1) f
          (eval_fix_update i c0 · t0) (eval_fix_update i c1 · t1)
        have hI := totInf_restrict i f
        set a := bad ε (t1.fix i c1) (restrict i true f)
        set b := bad ε (t0.fix i c0) (restrict i false f)
        have ha1 : a ≤ 1 := bad_le_one _ _ _
        have hb1' : b ≤ 1 := bad_le_one _ _ _
        have hK : (0 : ℝ) ≤ (k : ℝ) * φ := by positivity
        have e1 := mul_le_mul_of_nonneg_left hc1 hK
        have e0 := mul_le_mul_of_nonneg_left hc0 hK
        have f1 := mul_le_mul_of_nonneg_left ha1 hφ
        have f0 := mul_le_mul_of_nonneg_left hb1' hφ
        have g := mul_nonneg hφ hτ'
        have hbad : bad ε (node i (t0.fix i c0) (t1.fix i c1)) f = (a + b) / 2 := by linarith
        rw [hbad]
        push_cast
        nlinarith

/-- **Simulation on most inputs.** Assuming the influence bound `ExplicitBound` and the total
influence bound `TotalInfluenceBound`, a polynomial `p` of total degree at most `d ≥ 1` with
`0 ≤ p ≤ 1` on `{0,1}^N` is computed to within `ε` on all but at most `δ 2^N` inputs by a decision
tree of depth at most `⌈2d/(δφ)⌉` with `φ = (8 √15 / (125 π^4)) (ε²δ/2)^{5/2} / d^6`. -/
theorem simulation (hAA : ExplicitBound) (hTI : TotalInfluenceBound) (N d : ℕ) (hd : 1 ≤ d)
    (p : MvPolynomial (Fin N) ℝ) (hp : p.totalDegree ≤ d)
    (hb : ∀ X : Fin N → Bool,
      0 ≤ MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ∧
        MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ≤ 1)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ t : DTree N,
      t.depth ≤ ⌈2 * d / (δ * (8 * Real.sqrt 15 / (125 * Real.pi ^ 4) *
          (ε ^ 2 * δ / 2) ^ ((5 : ℝ) / 2) / (d : ℝ) ^ 6))⌉₊ ∧
      ((univ.filter fun X : Fin N → Bool =>
          ε < |t.eval X - MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p|).card : ℝ)
        ≤ δ * 2 ^ N := by
  set τ : ℝ := ε ^ 2 * δ / 2 with hτdef
  set φ : ℝ := 8 * Real.sqrt 15 / (125 * Real.pi ^ 4) * τ ^ ((5 : ℝ) / 2) / (d : ℝ) ^ 6 with hφdef
  have hτ : 0 < τ := by positivity
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hφ : 0 < φ := by positivity
  set C : ((Fin N → Bool) → ℝ) → Prop := fun f => ∃ q : MvPolynomial (Fin N) ℝ,
    q.totalDegree ≤ d ∧
    (∀ X : Fin N → Bool, 0 ≤ MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) q ∧
      MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) q ≤ 1) ∧
    ∀ X, f X = MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) q with hCdef
  have hC : ∀ f i b, C f → C (restrict i b f) := by
    rintro f i b ⟨q, hq, hqb, hfq⟩
    let s : Fin N → MvPolynomial (Fin N) ℝ :=
      fun k => if k = i then MvPolynomial.C (if b then 1 else 0) else MvPolynomial.X k
    have hev : ∀ (r : MvPolynomial (Fin N) ℝ) (X : Fin N → Bool),
        MvPolynomial.eval (fun k => if X k then (1 : ℝ) else 0) (bind₁ s r) =
          MvPolynomial.eval (fun k => if Function.update X i b k then (1 : ℝ) else 0) r := by
      intro r X
      have hpt : (fun k => if Function.update X i b k then (1 : ℝ) else 0) =
          fun k => MvPolynomial.eval (fun k => if X k then (1 : ℝ) else 0) (s k) := by
        funext k
        by_cases hk : k = i
        · subst hk; simp [s]
        · simp [s, hk, Function.update_of_ne hk]
      rw [hpt]
      induction r using MvPolynomial.induction_on with
      | C a => simp
      | add p q hp hq => simp [hp, hq]
      | mul_X p k hp => simp [hp]
    refine ⟨bind₁ s q, ?_, fun X => ?_, fun X => ?_⟩
    · conv_lhs => rw [q.as_sum]
      rw [map_sum]
      refine totalDegree_finsetSum_le fun m hm => ?_
      rw [bind₁_monomial]
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      refine (totalDegree_finsetProd _ _).trans ?_
      have hs : ∀ k, (s k).totalDegree ≤ 1 := by
        intro k
        by_cases hk : k = i
        · rw [show s k = MvPolynomial.C (if b then 1 else 0) from if_pos hk, totalDegree_C]
          exact Nat.zero_le _
        · rw [show s k = MvPolynomial.X k from if_neg hk, totalDegree_X]
      refine le_trans (sum_le_sum fun k _ => (totalDegree_pow _ _).trans
        (Nat.mul_le_mul_left _ (hs k))) ?_
      simp only [mul_one]
      exact (le_totalDegree hm).trans hq
    · rw [hev]; exact hqb _
    · show f (Function.update X i b) = _
      rw [hev]; exact hfq _
  have hAA' : ∀ f, C f → τ ≤ var f → ∃ i, φ ≤ inf i f := by
    rintro f ⟨q, hq, hqb, hfq⟩ hv
    have hf : f = fun X => MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) q := funext hfq
    subst hf
    obtain ⟨i, hi⟩ := hAA N d q hq hqb τ hτ hv
    exact ⟨i, hi⟩
  set f : (Fin N → Bool) → ℝ := fun X => MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p
  have hCf : C f := ⟨p, hp, hb, fun X => rfl⟩
  have hTf : totInf f ≤ d := hTI N d p hp hb
  set k : ℕ := ⌈2 * d / (δ * φ)⌉₊ with hkdef
  obtain ⟨t, htd, htb⟩ := exists_tree C hC hε hτ.le hφ.le hAA' k f hCf
  refine ⟨t, htd, ?_⟩
  have hk : 2 * (d : ℝ) / (δ * φ) ≤ k := Nat.le_ceil _
  have hk2 : 2 * (d : ℝ) ≤ k * (δ * φ) := by
    rwa [div_le_iff₀ (by positivity)] at hk
  have hkpos : (0 : ℝ) < k * φ := by
    have : (0 : ℝ) < k * (δ * φ) := lt_of_lt_of_le (by positivity) hk2
    have hk0 : (0 : ℝ) < k := by
      rcases (Nat.cast_nonneg k : (0 : ℝ) ≤ k).lt_or_eq with h0 | h0
      · exact h0
      · rw [← h0, zero_mul] at this; exact absurd this (lt_irrefl 0)
    positivity
  have hτe : τ / ε ^ 2 = δ / 2 := by rw [hτdef]; field_simp
  rw [hτe] at htb
  have hbad : bad ε t f ≤ δ := by
    have : (k : ℝ) * φ * bad ε t f ≤ k * φ * δ := by nlinarith
    exact le_of_mul_le_mul_left this hkpos
  have hcard : bad ε t f = ((univ.filter fun X : Fin N → Bool =>
      ε < |t.eval X - f X|).card : ℝ) / 2 ^ N := by
    unfold bad mean
    rw [Finset.sum_boole]
  rw [hcard, div_le_iff₀ (by positivity)] at hbad
  exact hbad

end AASimulation
