import SigregDim.Basic

/-!
# A discrete law with the sphere moments

The hypotheses collected in `SphereLike` are satisfiable in every dimension `K ≥ 1`. The law
`(2/(K(K+2))) ∑ₖ δ(eₖ) + (K/(K+2)) δ(𝟙/√K)` lies on the unit sphere, has the second and fourth
moments of the uniform law on the sphere, and is invariant under transpositions of coordinates.
-/

open MeasureTheory Finset

namespace SigregDim

variable {K : ℕ}

/-- Atoms: the diagonal point `𝟙/√K` and the unit vectors `eₖ`. -/
noncomputable def atom : Option (Fin K) → (Fin K → ℝ)
  | none => fun _ => (Real.sqrt K)⁻¹
  | some k => Pi.single k 1

/-- Weights of the atoms. -/
noncomputable def wt (K : ℕ) : Option (Fin K) → ℝ
  | none => K / (K + 2)
  | some _ => 2 / (K * (K + 2))

/-- The discrete law. -/
noncomputable def witness (K : ℕ) : Measure (Fin K → ℝ) :=
  Measure.sum fun o : Option (Fin K) => ENNReal.ofReal (wt K o) • Measure.dirac (atom o)

lemma wt_nonneg (o : Option (Fin K)) : 0 ≤ wt K o := by
  cases o <;> simp only [wt] <;> positivity

lemma integral_witness (f : (Fin K → ℝ) → ℝ) :
    ∫ x, f x ∂witness K = wt K none * f (atom none) + ∑ k, wt K (some k) * f (atom (some k)) := by
  unfold witness
  rw [integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top), tsum_fintype, Fintype.sum_option]
  simp only [ENNReal.toReal_ofReal (wt_nonneg _), smul_eq_mul]

lemma sqrt_inv_sq (hK : 0 < K) : ((Real.sqrt K)⁻¹) ^ 2 = 1 / K := by
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _), one_div]

lemma sum_single_pow (k l : Fin K) (n : ℕ) (hn : n ≠ 0) :
    (Pi.single k (1 : ℝ) : Fin K → ℝ) l ^ n = if l = k then 1 else 0 := by
  by_cases h : l = k
  · subst h; simp
  · simp [Pi.single_apply, h, hn]

theorem sphereLike_witness (hK : 0 < K) : SphereLike K (witness K) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hKne : (K : ℝ) ≠ 0 := hKr.ne'
  have hs := sqrt_inv_sq hK
  have hs4 : ((Real.sqrt K)⁻¹) ^ 4 = 1 / K ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hs]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- total mass one
    rw [isProbabilityMeasure_iff]
    unfold witness
    rw [Measure.sum_apply _ MeasurableSet.univ, tsum_fintype, Fintype.sum_option]
    simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul,
      mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => wt_nonneg _),
      ← ENNReal.ofReal_add (wt_nonneg _) (Finset.sum_nonneg fun k _ => wt_nonneg _)]
    rw [← ENNReal.ofReal_one]
    congr 1
    simp only [wt, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · -- support on the sphere
    unfold witness
    rw [Measure.ae_sum_iff]
    intro o
    refine Measure.ae_smul_measure ?_ _
    rw [ae_dirac_iff (measurableSet_eq_fun (by fun_prop) measurable_const)]
    cases o with
    | none =>
      simp only [atom, hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    | some k =>
      simp only [atom, sum_single_pow _ _ 2 two_ne_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
  · intro k
    rw [integral_witness]
    simp only [atom, hs, sum_single_pow _ _ 2 two_ne_zero, wt, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    field_simp
  · intro k
    rw [integral_witness]
    simp only [atom, hs4, sum_single_pow _ _ 4 four_ne_zero, wt, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    field_simp
    ring
  · intro k l hkl
    rw [integral_witness]
    have hz : ∀ m : Fin K, (Pi.single m (1 : ℝ) : Fin K → ℝ) k ^ 2 *
        (Pi.single m (1 : ℝ) : Fin K → ℝ) l ^ 2 = 0 := by
      intro m
      rw [sum_single_pow _ _ 2 two_ne_zero, sum_single_pow _ _ 2 two_ne_zero]
      by_cases h : k = m
      · subst h; simp [Ne.symm hkl]
      · simp [h]
    simp only [atom, hs, hz, wt, mul_zero, Finset.sum_const_zero, add_zero]
    field_simp
  · intro i j
    have hmeas : Measurable fun x : Fin K → ℝ => x ∘ Equiv.swap i j :=
      measurable_pi_iff.2 fun k => measurable_pi_apply (Equiv.swap i j k)
    unfold witness
    rw [Measure.map_sum hmeas.aemeasurable]
    have hterm : ∀ o : Option (Fin K),
        Measure.map (fun x : Fin K → ℝ => x ∘ Equiv.swap i j)
          (ENNReal.ofReal (wt K o) • Measure.dirac (atom o)) =
        ENNReal.ofReal (wt K (Equiv.optionCongr (Equiv.swap i j) o)) •
          Measure.dirac (atom (Equiv.optionCongr (Equiv.swap i j) o)) := by
      intro o
      rw [Measure.map_smul _ hmeas.aemeasurable, Measure.map_dirac' hmeas]
      cases o with
      | none => rfl
      | some k =>
        simp only [Equiv.optionCongr_apply, Option.map_some, wt, atom]
        congr 2
        funext l
        simp only [Function.comp_apply, Pi.single_apply, Equiv.swap_apply_eq_iff]
    simp_rw [hterm]
    exact Measure.sum_comp_equiv (Equiv.optionCongr (Equiv.swap i j))
      (fun o => ENNReal.ofReal (wt K o) • Measure.dirac (atom o))

end SigregDim
