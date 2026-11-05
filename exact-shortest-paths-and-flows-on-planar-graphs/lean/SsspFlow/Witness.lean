import SsspFlow.Hubs

/-!
# From a decomposition to labels

For a decomposition with levels `Γ`, `topLevel` lists the levels from the top: all darts, then the levels
of `Γ` from the deepest one upwards. Values along these levels, with the bounds of `LevelMetric`, give
`bagVal`, the values between the hubs of each bag, with the bounds of `bagVal_lo` and `bagVal_hi`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal

namespace SsspFlow

open FourColor

/-- A list without repetitions in a finite set is at most as long as the set is large. -/
theorem length_le_of_forall_mem {α : Type*} [DecidableEq α] {l : List α} (hn : l.Nodup) {S : Finset α}
    (h : ∀ y ∈ l, y ∈ S) : l.length ≤ S.card := by
  rw [← List.toFinset_card_of_nodup hn]
  exact Finset.card_le_card fun y hy => h y (List.mem_toFinset.1 hy)

namespace RotSystem

variable {D : Type*} [Fintype D] [DecidableEq D] {R : RotSystem D}

/-- The first return to all darts is the permutation. -/
theorem firstReturn_univ (f : Equiv.Perm D) : firstReturn f Finset.univ = f := by
  ext x
  rw [firstReturn_eq_of_trail f (Finset.mem_univ x) (Trail.here (Finset.mem_univ _))]

/-- At all darts, `ψ` is the reversal. -/
theorem psi_univ_apply (M : RotSystem D) (x : D) : M.psi Finset.univ x = M.rev x := by
  show firstReturn M.rot Finset.univ (firstReturn M.facePerm Finset.univ x) = M.rev x
  rw [firstReturn_univ, firstReturn_univ]
  exact M.rot.apply_symm_apply _

/-- The cycles of `ψ` at all darts have two elements. -/
theorem fconnect_psi_univ (M : RotSystem D) {x y : D} (h : fconnect (M.psi Finset.univ) x y) :
    y = x ∨ y = M.rev x := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail e c _ hec ih =>
    obtain rfl : M.psi Finset.univ e = c := hec
    rw [psi_univ_apply]
    rcases ih with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (M.rev_rev _)

namespace RootedTree

variable {V : Type*} [Fintype V] [DecidableEq V] {t : R.RootedTree V}

/-- The levels from the top: all darts, then the levels of `Γ` from depth `H` upwards. -/
noncomputable def topLevel (Γ : ℕ → Finset (D × Bool)) (H i : ℕ) : Finset (D × Bool) :=
  if i = 0 then Finset.univ else Γ (H + 1 - i)

theorem topLevel_zero (Γ : ℕ → Finset (D × Bool)) (H : ℕ) : topLevel Γ H 0 = Finset.univ := rfl

theorem topLevel_succ (Γ : ℕ → Finset (D × Bool)) (H i : ℕ) : topLevel Γ H (i + 1) = Γ (H - i) := by
  simp only [topLevel, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
  congr 1
  omega

section Decomp

variable {code : D × Bool → ℕ} {Γ C : ℕ → Finset (D × Bool)} {w₀ : D × Bool} {H : ℕ}

namespace Decomp

variable (hD : t.Decomp w₀ Γ C)

include hD

/-- All darts form a level. -/
theorem level_univ : t.IsLevel Finset.univ := by
  have h1 : t.next {w₀} Finset.univ = Finset.univ := by
    ext z
    simp only [mem_next, Finset.mem_univ, iff_true]
    exact Or.inr ⟨z, trivial, Or.inl rfl⟩
  have h2 := hD.level₀.next (C := Finset.univ) fun d _ => by
    rw [h1]
    exact Finset.mem_univ _
  rwa [h1] at h2

theorem topLevel_level (i : ℕ) : t.IsLevel (topLevel Γ H i) := by
  cases i with
  | zero => exact hD.level_univ
  | succ i =>
    rw [topLevel_succ]
    exact hD.level _

theorem topLevel_sub (i : ℕ) : topLevel Γ H (i + 1) ⊆ topLevel Γ H i := by
  cases i with
  | zero => exact Finset.subset_univ _
  | succ i =>
    rw [topLevel_succ, topLevel_succ]
    exact hD.mono (by omega)

/-- The corners of a cycle of `ψ` on a level from the top are few. -/
theorem cycOf_length_le {h : ℕ} (hdep : ∀ v, t.dep v ≤ h) (i : ℕ) (x : D × Bool) :
    (cycOf (R.double.psi (topLevel Γ H i)) code x).length ≤ 2 + H * (2 + 4 * h) := by
  classical
  cases i with
  | zero =>
    rw [topLevel_zero]
    refine (length_le_of_forall_mem (S := {x, R.double.rev x}) (cycOf_nodup _ _) ?_).trans ?_
    · intro y hy
      rcases R.double.fconnect_psi_univ ((mem_cycOf _).1 hy) with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · have := Finset.card_le_two (a := x) (b := R.double.rev x)
      omega
  | succ i =>
    rw [topLevel_succ]
    by_cases hx : x ∈ Γ (H - i)
    · refine (length_le_of_forall_mem (S := R.portsOf (Γ (H - i)) x) (cycOf_nodup _ _) ?_).trans ?_
      · intro y hy
        have h1 := (mem_cycOf _).1 hy
        exact mem_portsOf.2 ⟨mem_of_fconnect_psi hx h1, R.double.gcomp_split_of_fconnect_psi h1⟩
      · have h1 := hD.card_ports hdep (H - i) x
        have h2 : (H - i) * (2 + 4 * h) ≤ H * (2 + 4 * h) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
    · have h1 : (cycOf (R.double.psi (Γ (H - i))) code x).length ≤ 1 := by
        have h2 : cycOf (R.double.psi (Γ (H - i))) code x = [x] := by
          have h3 : ∀ y, fconnect (R.double.psi (Γ (H - i))) x y → y = x := by
            intro y hy
            exact eq_of_fconnect_of_fixed ((R.double.fixesOff_psi _) x hx) hy
          have h4 : ∀ y ∈ cycOf (R.double.psi (Γ (H - i))) code x, y = x :=
            fun y hy => h3 y ((mem_cycOf _).1 hy)
          have hn : (cycOf (R.double.psi (Γ (H - i))) code x).Nodup := cycOf_nodup _ _
          have hm := self_mem_cycOf (R.double.psi (Γ (H - i))) (code := code) x
          rcases hl : cycOf (R.double.psi (Γ (H - i))) code x with _ | ⟨a, l⟩
          · rw [hl] at hm
            simp at hm
          · rw [hl] at h4 hn
            have ha := h4 a (List.mem_cons_self ..)
            subst ha
            cases l with
            | nil => rfl
            | cons b l =>
              have hb := h4 b (by simp)
              subst hb
              simp at hn
        rw [h2]
        simp
      omega

end Decomp

/-! ### The values of the bags -/

variable (R) in
/-- The darts of the bag named `x`. -/
def bagDarts (code : D × Bool → ℕ) (Γ : ℕ → Finset (D × Bool)) (H x : ℕ) : Set (D × Bool) :=
  {z | R.InBag code Γ H x z}

/-- The level of the corners of the hubs of the bag named `x`. -/
noncomputable def hubLevel (Γ : ℕ → Finset (D × Bool)) (H x : ℕ) : Finset (D × Bool) :=
  topLevel Γ H (H - (Nat.unpair x).1)

variable (t) in
/-- The values between the hubs of the bag named `x`, from values along the levels from the top. -/
noncomputable def bagVal (code : D × Bool → ℕ) (Γ : ℕ → Finset (D × Bool)) (H : ℕ)
    (vals : ℕ → D × Bool → D × Bool → ℝ≥0∞) (x : ℕ) (a b : V) : ℝ≥0∞ :=
  bagDist t (hubLevel Γ H x) (bagDarts R code Γ H x) (vals (H - (Nat.unpair x).1)) a b

namespace Decomp

variable (hD : t.Decomp w₀ Γ C) (hc : R.Connected) (hinj : Function.Injective code)
  {adj : V → V → Prop} (hadj : ∀ a b, adj a b → ∃ d, t.vert d = a ∧ t.vert (R.rev d) = b)
  (hsurj : ∀ v, ∃ d, t.vert d = v) (hH : ∀ v, ¬ t.NP (Γ H) v)

include hD

theorem sub_hubLevel {x : ℕ} (hx : (Nat.unpair x).1 ≤ H) : Γ (Nat.unpair x).1 ⊆ hubLevel Γ H x := by
  unfold hubLevel
  rcases Nat.lt_or_ge (Nat.unpair x).1 H with h | h
  · obtain ⟨i, hi⟩ : ∃ i, H - (Nat.unpair x).1 = i + 1 := ⟨H - (Nat.unpair x).1 - 1, by omega⟩
    rw [hi, topLevel_succ]
    exact hD.mono (by omega)
  · have : H - (Nat.unpair x).1 = 0 := by omega
    rw [this, topLevel_zero]
    exact Finset.subset_univ _

/-- The darts of a bag form components of the split at its corners. -/
theorem bagDarts_closed (x : ℕ) (z z' : D × Bool) (hz : z ∈ bagDarts R code Γ H x)
    (h : (R.double.split (hubLevel Γ H x)).toHypermap.gcomp z z') : z' ∈ bagDarts R code Γ H x :=
  InBag.same hz (gcomp_split_mono (hD.sub_hubLevel hz.1) h)

include hc hinj hadj hsurj hH

/-- The hubs of a bag are the vertices of its corners. -/
theorem hub_eq (x : ℕ) : (hD.hierarchy hc hinj hadj hsurj hH).hub x =
    (bagHubs t (hubLevel Γ H x) (bagDarts R code Γ H x) : Set V) := by
  ext a
  simp only [Finset.mem_coe, mem_bagHubs]
  constructor
  · rintro ⟨g, hg, hgm, rfl⟩
    refine ⟨g, ?_, hg, rfl⟩
    unfold hubLevel
    rcases Nat.lt_or_ge (Nat.unpair x).1 H with h | h
    · obtain ⟨i, hi⟩ : ∃ i, H - (Nat.unpair x).1 = i + 1 := ⟨H - (Nat.unpair x).1 - 1, by omega⟩
      rw [hi, topLevel_succ]
      have : H - i = (Nat.unpair x).1 + 1 := by omega
      rwa [this]
    · have : H - (Nat.unpair x).1 = 0 := by omega
      rw [this, topLevel_zero]
      exact Finset.mem_univ _
  · rintro ⟨p, hp, hpx, rfl⟩
    rcases Nat.lt_or_ge (Nat.unpair x).1 H with h | h
    · obtain ⟨i, hi⟩ : ∃ i, H - (Nat.unpair x).1 = i + 1 := ⟨H - (Nat.unpair x).1 - 1, by omega⟩
      unfold hubLevel at hp
      rw [hi, topLevel_succ] at hp
      have h1 : H - i = (Nat.unpair x).1 + 1 := by omega
      rw [h1] at hp
      exact ⟨p, hpx, hp, rfl⟩
    · have hd := hpx.1
      have h2 : (Nat.unpair x).1 = H := by omega
      obtain ⟨g, hg, hgp, hs⟩ := exists_corner_of_not_NP (t := t) (Γ := Γ H) (u := p) (hH _)
      refine ⟨g, hpx.same (by rw [h2]; exact hs), ?_, hgp⟩
      rw [h2]
      exact hD.sub_succ H hg

/-- An arc of a bag from a vertex off the hubs lies in the child of the vertex. -/
theorem hedge_out (x : ℕ) (a b : V) (h : (hD.hierarchy hc hinj hadj hsurj hH).arc x a b)
    (ha : a ∉ (hD.hierarchy hc hinj hadj hsurj hH).hub x) :
    ∃ c', (hD.hierarchy hc hinj hadj hsurj hH).kid c' x ∧
      (hD.hierarchy hc hinj hadj hsurj hH).arc c' a b := by
  obtain ⟨z, hz, rfl, rfl⟩ := h
  have hnp := hD.np_of_not_hub hc hinj hz ha
  have hlt := hD.depth_lt_of_np hc hinj hH hz.1 hnp
  exact ⟨R.bagName code Γ ((Nat.unpair x).1 + 1) z, ⟨bagName_fst _ _, z, inBag_name hlt z, hz⟩,
    ⟨z, inBag_name hlt z, rfl, rfl⟩⟩

/-- An arc of a bag to a vertex off the hubs lies in the child of the vertex. -/
theorem hedge_in (x : ℕ) (a b : V) (h : (hD.hierarchy hc hinj hadj hsurj hH).arc x a b)
    (hb : b ∉ (hD.hierarchy hc hinj hadj hsurj hH).hub x) :
    ∃ c', (hD.hierarchy hc hinj hadj hsurj hH).kid c' x ∧
      (hD.hierarchy hc hinj hadj hsurj hH).arc c' a b := by
  obtain ⟨z, hz, rfl, rfl⟩ := h
  have hz' : R.InBag code Γ H x (R.double.rev z) := hz.same (same_rev _ z)
  have hnp := hD.np_of_not_hub hc hinj hz' hb
  have hlt := hD.depth_lt_of_np hc hinj hH hz.1 hnp
  exact ⟨R.bagName code Γ ((Nat.unpair x).1 + 1) z, ⟨bagName_fst _ _, z, inBag_name hlt z, hz⟩,
    ⟨z, inBag_name hlt z, rfl, rfl⟩⟩

/-- A hub of a bag in a child is a hub of the child. -/
theorem hub_kid (x c' : ℕ) (a : V) (hk : (hD.hierarchy hc hinj hadj hsurj hH).kid c' x)
    (ha : a ∈ (hD.hierarchy hc hinj hadj hsurj hH).hub x)
    (hac : a ∈ (hD.hierarchy hc hinj hadj hsurj hH).bag c') :
    a ∈ (hD.hierarchy hc hinj hadj hsurj hH).hub c' := by
  obtain ⟨h1, -⟩ := hk
  obtain ⟨g, -, hg, rfl⟩ := ha
  obtain ⟨z, hz, hzg⟩ := hac
  have hnp : ¬ t.NP (Γ ((Nat.unpair x).1 + 1)) (t.vertM z) := by
    rw [hzg]
    exact fun hn => hn g hg rfl
  obtain ⟨g', hg', hgz, hs⟩ := exists_corner_of_not_NP hnp
  refine ⟨g', hz.same (by rw [h1]; exact hs), ?_, hgz.trans hzg⟩
  rw [h1]
  exact hD.sub_succ _ hg'

variable {g : D × Bool → ℕ} {w : V → V → ℝ≥0∞} {U s : ℕ}
  {vals : ℕ → D × Bool → D × Bool → ℝ≥0∞}

omit hc hinj hadj hsurj hH in
/-- **Lower bound for the values of a bag.** -/
theorem bagVal_lo (hadj' : ∀ z, adj (t.vertM z) (t.vertM (R.double.rev z)))
    (hgw : ∀ z, (g z : ℝ≥0∞) = w (t.vertM z) (t.vertM (R.double.rev z)))
    (hvals : ∀ i, i ≤ H → ∃ μ, LevelMetric R.double g code U s (topLevel Γ H i)
      (cU U ^ (2 * i)) μ (vals i)) (x : ℕ) (a b : V) :
    (U : ℝ≥0∞) * dist adj w Set.univ a b ≤ bagVal t code Γ H vals x a b := by
  obtain ⟨μ, hμ⟩ := hvals (H - (Nat.unpair x).1) (by omega)
  unfold bagVal
  refine bagDist_lo hadj' hgw (fun p hp q hq => ?_) a b
  have hp' := (mem_bagCorners.1 hp).1
  have hq' := (mem_bagCorners.1 hq).1
  exact (hμ.lo p hp' q hq').trans (hμ.val_lo p hp' q hq')

/-- **Upper bound for the values of a bag.** -/
theorem bagVal_hi (hgw : ∀ z, (g z : ℝ≥0∞) = w (t.vertM z) (t.vertM (R.double.rev z))) (hU : 1 ≤ U)
    (hvals : ∀ i, i ≤ H → ∃ μ, LevelMetric R.double g code U s (topLevel Γ H i)
      (cU U ^ (2 * i)) μ (vals i)) (x : ℕ) (a b : V)
    (ha : a ∈ (hD.hierarchy hc hinj hadj hsurj hH).hub x)
    (hb : b ∈ (hD.hierarchy hc hinj hadj hsurj hH).hub x) :
    bagVal t code Γ H vals x a b ≤ (cU U ^ (2 * H + 1) * (U : ℝ≥0∞)) *
      distR adj w ((hD.hierarchy hc hinj hadj hsurj hH).arc x) a b := by
  obtain ⟨μ, hμ⟩ := hvals (H - (Nat.unpair x).1) (by omega)
  have hsub : (hD.hierarchy hc hinj hadj hsurj hH).hub x = _ := hD.hub_eq hc hinj hadj hsurj hH x
  rw [hsub] at ha hb
  have hc1 : 1 ≤ cU U := one_le_cU hU
  have hκ0 : cU U ^ (2 * H + 1) ≠ 0 := by
    exact (lt_of_lt_of_le one_pos (one_le_pow₀ hc1)).ne'
  have hκT : cU U ^ (2 * H + 1) ≠ ⊤ := ENNReal.pow_ne_top (cU_ne_top hU)
  refine bagDist_hi (hD.bagDarts_closed x) hgw (fun p hp q hq => ?_) hκ0 hκT hU ha hb
  have hp' := (mem_bagCorners.1 hp).1
  have hq' := (mem_bagCorners.1 hq).1
  have h1 := (hμ.val_hi p hp' q hq').trans (mul_le_mul_right (hμ.hi p hp' q hq') _)
  refine h1.trans ?_
  rw [← mul_assoc, ← pow_succ']
  refine mul_le_mul_left (pow_le_pow_right₀ hc1 (by omega)) _

end Decomp

end Decomp

end RootedTree

end RotSystem

end SsspFlow
