import SsspFlow.Tables

/-!
# The cut of a bag from its table

A dart with the numbers of itself and of its reverse, together with the table of the corners of its bag,
determines the masses and positions on the tour of the bag (`massXY_eq`, `posXY_eq`), whether it is heavy
(`hvT_iff`), and whether it is a candidate for the cut, with its value (`candA_eq`, `candY_eq`). The next level
follows from the selected darts and their positions on the tour through all darts (`mem_next_iff`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SsspFlow

namespace RotSystem

open FourColor

variable {D : Type*} [Fintype D] [DecidableEq D] {R : RotSystem D}

namespace RootedTree

variable {V : Type*} [Fintype V] [DecidableEq V] {t : R.RootedTree V}

/-- The numbers of a dart: its code, its position on the tour through all darts, and its numbers on the first
tour with the marks and with all darts as weights. -/
abbrev View := ℕ × ℕ × ℕ × ℕ

section Pure

variable (W : ℕ) (tab : ℕ → ℕ) (c₀ : ℕ)

/-- The mass of the marks from the first corner. -/
noncomputable def mFT (x : View) : ℕ := massT W tab c₀ 1 3 x.1 x.2.1 x.2.2.1

/-- The position on the tour of the bag from the first corner. -/
noncomputable def pUT (x : View) : ℕ := massT W tab c₀ 2 4 x.1 x.2.1 x.2.2.2

/-- The number of marks of the bag. -/
noncomputable def cycFT : ℕ := ∑ c ∈ portsT W tab, fldT tab 1 c

/-- The length of the tour of the bag. -/
noncomputable def cycUT : ℕ := ∑ c ∈ portsT W tab, fldT tab 2 c

/-- The mass of the marks between two darts. -/
noncomputable def massXY (x y : View) : ℕ :=
  massBy (mFT W tab c₀) (pUT W tab c₀) (cycFT W tab) x y

/-- The position of a dart on the tour of the bag seen from another dart. -/
noncomputable def posXY (x y : View) : ℕ :=
  massBy (pUT W tab c₀) (pUT W tab c₀) (cycUT W tab) x y

/-- The dart `x` with reverse `y` is heavy. -/
def hvT (x y : View) : Prop := 3 * cycFT W tab < 4 * massXY W tab c₀ x y + 2

open Classical in
/-- The value of a start of a cut. -/
noncomputable def startValT (x y : View) : ℕ :=
  if hvT W tab c₀ x y then (posXY W tab c₀ x y + 1) * W + x.1 else 0 * W + x.1

open Classical in
/-- The value of a dart as the first dart of a cut, if it is a candidate. -/
noncomputable def candA (x y : View) (mk sm : Prop) : Option ℕ :=
  if cycFT W tab = 0 then none
  else if cycFT W tab < 4 then (if sm then some x.1 else none)
  else if ¬ mk ∧ (hvT W tab c₀ x y ∨ ¬ hvT W tab c₀ y x) then some (startValT W tab c₀ x y) else none

/-- The mass of the marks from a dart with mass `ma` and position `pa` on the tour of the bag. -/
noncomputable def massFromT (pa ma : ℕ) (x : View) : ℕ :=
  if pa ≤ pUT W tab c₀ x then mFT W tab c₀ x - ma else cycFT W tab - (ma - mFT W tab c₀ x)

open Classical in
/-- The value of a dart with face `fz` as the second dart of a cut, if it is a candidate. -/
noncomputable def candY (hasA : Prop) (pa ma fa fz : ℕ) (x : View) : Option ℕ :=
  if 4 ≤ cycFT W tab ∧ hasA ∧ fz = fa ∧ cycFT W tab + 2 ≤ 4 * massFromT W tab c₀ pa ma x then
    some (massFromT W tab c₀ pa ma x * W + x.1)
  else none

end Pure

variable (t) in
/-- The numbers of a dart. -/
noncomputable def viewOf (code : D × Bool → ℕ) (w₀ z : D × Bool) : View :=
  (code z, pos (t.tau w₀) w₀ z, t.phi (t.marks {w₀}) w₀ z, t.phi Finset.univ w₀ z)

/-- The table of the corners of a bag. -/
structure PortTab (t : R.RootedTree V) (W : ℕ) (tab : ℕ → ℕ) (Γ : Finset (D × Bool))
    (g₀ : D × Bool) (code : D × Bool → ℕ) (w₀ : D × Bool) : Prop where
  f0 : ∀ p ∈ R.portsOf Γ g₀, tab (Nat.pair (code p) 0) = pos (t.tau w₀) w₀ p + 1
  f1 : ∀ p ∈ R.portsOf Γ g₀, tab (Nat.pair (code p) 1) = t.arcV Γ (t.marks {w₀}) (t.marks Γ) w₀ p + 1
  f2 : ∀ p ∈ R.portsOf Γ g₀, tab (Nat.pair (code p) 2) = t.arcV Γ Finset.univ Finset.univ w₀ p + 1
  f3 : ∀ p ∈ R.portsOf Γ g₀, tab (Nat.pair (code p) 3) =
    t.phiB (t.marks {w₀}) (t.marks Γ) w₀ ((R.double.nodeReturn Γ)⁻¹ p) + 1
  f4 : ∀ p ∈ R.portsOf Γ g₀, tab (Nat.pair (code p) 4) =
    t.phiB Finset.univ Finset.univ w₀ ((R.double.nodeReturn Γ)⁻¹ p) + 1
  none : ∀ c, (∀ p ∈ R.portsOf Γ g₀, code p ≠ c) → tab (Nat.pair c 0) = 0

variable {w₀ : D × Bool} {Γ : Finset (D × Bool)} {W : ℕ} {tab : ℕ → ℕ} {g₀ : D × Bool}
  {code : D × Bool → ℕ} {fid : D × Bool → ℕ}

theorem PortTab.toF (h : t.PortTab W tab Γ g₀ code w₀) :
    TabOK W tab (R.portsOf Γ g₀) code (pos (t.tau w₀) w₀) (t.arcV Γ (t.marks {w₀}) (t.marks Γ) w₀)
      (fun p => t.phiB (t.marks {w₀}) (t.marks Γ) w₀ ((R.double.nodeReturn Γ)⁻¹ p)) 1 3 :=
  ⟨h.f0, h.f1, h.f3, h.none⟩

theorem PortTab.toU (h : t.PortTab W tab Γ g₀ code w₀) :
    TabOK W tab (R.portsOf Γ g₀) code (pos (t.tau w₀) w₀) (t.arcV Γ Finset.univ Finset.univ w₀)
      (fun p => t.phiB Finset.univ Finset.univ w₀ ((R.double.nodeReturn Γ)⁻¹ p)) 2 4 :=
  ⟨h.f0, h.f2, h.f4, h.none⟩

variable (hL : t.IsLevel Γ) (hw : w₀ ∈ Γ) (h₀ : t.vertM w₀ = t.root) (h₁ : w₀.2 = true)
  (hL₀ : t.IsLevel {w₀}) (hR : R.Planar) (hc : R.Connected) (hg₀ : g₀ ∈ Γ)
  (hinj : Function.Injective code) (hcW : ∀ z, code z < W) (hW : Fintype.card (D × Bool) ≤ W)
  (hTab : t.PortTab W tab Γ g₀ code w₀)

include hw in
theorem marks_sub_first : ∀ y ∈ t.marks Γ, y ∈ t.marks {w₀} :=
  fun _ hy => marks_mono (Finset.singleton_subset_iff.2 hw) hy

include hL h₀ in
theorem marks_of_first : ∀ y, y ∉ Γ → (∀ u, u ≠ t.root → y = t.c1 u → t.NP Γ u) →
    y ∈ t.marks {w₀} → y ∈ t.marks Γ := fun y hy hc hm => by
  obtain ⟨v, hv, hyv⟩ := (mem_marks_singleton h₀).1 hm
  rcases hyv with rfl | rfl
  · exact t.mem_marks.2 ⟨v, hc v hv rfl, Or.inl rfl⟩
  · exact t.mem_marks.2 ⟨v, np_of_c0_not_mem hL hv hy, Or.inr rfl⟩

include hL hR hc in
theorem fconnect_of_same {x y : D × Bool} (h : R.Same Γ x y) : fconnect (t.tourL Γ) x y :=
  ((hL.spanForest hR hc).fconnect_tour_iff _ _).2 ((R.double.cone_gcomp_iff Γ _ _).2 h)

include hL hR hc in
theorem same_of_fconnect {x y : D × Bool} (h : fconnect (t.tourL Γ) x y) : R.Same Γ x y :=
  (R.double.cone_gcomp_iff Γ _ _).1 (((hL.spanForest hR hc).fconnect_tour_iff _ _).1 h)

include hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab in
theorem mFT_eq {z : D × Bool} (hs : R.Same Γ g₀ z) :
    mFT W tab (code g₀) (t.viewOf code w₀ z) = mass (t.tourL Γ) (t.marks Γ) g₀ z :=
  massT_eq hL hw h₀ h₁ hL₀ hR hc (marks_sub_first hw) (marks_of_first hL h₀) hg₀ hinj hcW hW hTab.toF hs

include hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab in
theorem pUT_eq {z : D × Bool} (hs : R.Same Γ g₀ z) :
    pUT W tab (code g₀) (t.viewOf code w₀ z) = pos (t.tourL Γ) g₀ z :=
  (massT_eq hL hw h₀ h₁ hL₀ hR hc (fun _ _ => Finset.mem_univ _) (fun _ _ _ _ => Finset.mem_univ _)
    hg₀ hinj hcW hW hTab.toU hs).trans (mass_univ (fconnect_of_same hL hR hc hs))

include hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab in
theorem cycFT_eq : cycFT W tab = t.npOf Γ g₀ :=
  (cycT_eq hL hw h₀ h₁ hL₀ hR hc (marks_sub_first hw) (marks_of_first hL h₀) hg₀ hinj hcW hW
    hTab.toF).trans (cycMass_eq_npOf hL hR hc g₀)

include hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab in
theorem cycUT_eq : cycUT W tab = cycMass (t.tourL Γ) Finset.univ g₀ :=
  cycT_eq hL hw h₀ h₁ hL₀ hR hc (fun _ _ => Finset.mem_univ _) (fun _ _ _ _ => Finset.mem_univ _)
    hg₀ hinj hcW hW hTab.toU

include hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab in
/-- **The mass between two darts of a bag.** -/
theorem massXY_eq {x y : D × Bool} (hx : R.Same Γ g₀ x) (hy : R.Same Γ g₀ y) :
    massXY W tab (code g₀) (t.viewOf code w₀ x) (t.viewOf code w₀ y) =
      mass (t.tourL Γ) (t.marks Γ) x y := by
  have h := mass_eq_massBy (f := t.tourL Γ) (g := g₀) (t.marks Γ)
    (m := fun z => mFT W tab (code g₀) (t.viewOf code w₀ z))
    (p := fun z => pUT W tab (code g₀) (t.viewOf code w₀ z))
    (fun z hz => mFT_eq hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab (same_of_fconnect hL hR hc hz))
    (fun z hz => pUT_eq hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab (same_of_fconnect hL hR hc hz))
    (fconnect_of_same hL hR hc hx) (fconnect_of_same hL hR hc hy)
  rw [h, cycMass_eq_npOf hL hR hc g₀, ← cycFT_eq hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab]
  rfl

include hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab in
/-- **The position of a dart of a bag seen from another dart.** -/
theorem posXY_eq {x y : D × Bool} (hx : R.Same Γ g₀ x) (hy : R.Same Γ g₀ y) :
    posXY W tab (code g₀) (t.viewOf code w₀ x) (t.viewOf code w₀ y) = pos (t.tourL Γ) x y := by
  have hxy : fconnect (t.tourL Γ) x y := fconnect_of_same hL hR hc (Same.trans (Same.symm hx) hy)
  have hup : ∀ z, fconnect (t.tourL Γ) g₀ z →
      pUT W tab (code g₀) (t.viewOf code w₀ z) = mass (t.tourL Γ) Finset.univ g₀ z := fun z hz => by
    rw [pUT_eq hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab (same_of_fconnect hL hR hc hz), mass_univ hz]
  have h := mass_eq_massBy (f := t.tourL Γ) (g := g₀) Finset.univ
    (m := fun z => pUT W tab (code g₀) (t.viewOf code w₀ z))
    (p := fun z => pUT W tab (code g₀) (t.viewOf code w₀ z)) hup
    (fun z hz => pUT_eq hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab (same_of_fconnect hL hR hc hz))
    (fconnect_of_same hL hR hc hx) (fconnect_of_same hL hR hc hy)
  rw [mass_univ hxy] at h
  rw [h, ← cycUT_eq hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab]
  rfl

include hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab in
theorem hvT_iff {z : D × Bool} (hs : R.Same Γ g₀ z) :
    hvT W tab (code g₀) (t.viewOf code w₀ z) (t.viewOf code w₀ (R.double.rev z)) ↔ t.Hv Γ z := by
  unfold hvT
  rw [massXY_eq hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab hs (Same.trans hs (same_rev Γ z)),
    cycFT_eq hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab]
  show _ ↔ 3 * cycMass (t.tourL Γ) (t.marks Γ) z <
    4 * mass (t.tourL Γ) (t.marks Γ) z (R.double.rev z) + 2
  rw [cycMass_eq_npOf hL hR hc z, npOf_congr (t := t) hs]

include hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab in
theorem hvT_rev_iff {z : D × Bool} (hs : R.Same Γ g₀ z) :
    hvT W tab (code g₀) (t.viewOf code w₀ (R.double.rev z)) (t.viewOf code w₀ z) ↔
      t.Hv Γ (R.double.rev z) := by
  have h := hvT_iff hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab (Same.trans hs (same_rev Γ z))
  rwa [R.double.rev_rev] at h

include hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab in
theorem startValT_eq {z : D × Bool} (hs : R.Same Γ g₀ z) :
    startValT W tab (code g₀) (t.viewOf code w₀ z) (t.viewOf code w₀ (R.double.rev z)) =
      t.startVal code W Γ z := by
  classical
  have hh := hvT_iff hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab hs
  unfold startValT startVal
  by_cases h : t.Hv Γ z
  · rw [if_pos (hh.2 h), if_pos h,
      posXY_eq hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab hs (Same.trans hs (same_rev Γ z))]
    rfl
  · rw [if_neg (fun h' => h (hh.1 h')), if_neg h]
    rfl

variable (t) in
open Classical in
/-- The candidates for the first dart of the cut of a bag. -/
noncomputable def aSet (Γ : Finset (D × Bool)) (u : D × Bool) : Finset (D × Bool) :=
  if t.npOf Γ u = 0 then ∅ else if t.npOf Γ u < 4 then t.smallSet Γ u else t.startSet Γ u

variable (t) in
/-- The value of a candidate for the first dart of the cut of a bag. -/
noncomputable def aVal (code : D × Bool → ℕ) (W : ℕ) (Γ : Finset (D × Bool)) (u z : D × Bool) : ℕ :=
  if t.npOf Γ u < 4 then code z else t.startVal code W Γ z

variable (t) in
/-- The first dart of the cut of a bag. -/
noncomputable def selA (code : D × Bool → ℕ) (W : ℕ) (Γ : Finset (D × Bool)) (u : D × Bool) :
    Finset (D × Bool) :=
  argminF (t.aSet Γ u) (t.aVal code W Γ u)

variable (t) in
open Classical in
/-- The second dart of the cut of a bag. -/
noncomputable def selY (code : D × Bool → ℕ) (W : ℕ) (fid : D × Bool → ℕ) (Γ : Finset (D × Bool))
    (u : D × Bool) : Finset (D × Bool) :=
  if t.npOf Γ u < 4 then ∅
  else (t.startOfBag code W Γ u).biUnion fun a => argminF (t.endSet fid Γ u a) (t.endVal code W Γ a)

theorem selOf_eq (u : D × Bool) :
    t.selOf code W fid Γ u = t.selA code W Γ u ∪ t.selY code W fid Γ u := by
  classical
  unfold selOf selA selY aSet aVal
  by_cases h0 : t.npOf Γ u = 0
  · rw [if_pos h0, if_pos h0, if_pos (by omega)]
    simp [argminF]
  · rw [if_neg h0, if_neg h0]
    by_cases h4 : t.npOf Γ u < 4
    · rw [if_pos h4, if_pos h4, if_pos h4, Finset.union_empty]
      exact congrArg _ (by funext z; rw [if_pos h4])
    · rw [if_neg h4, if_neg h4, if_neg h4]
      unfold startOfBag
      congr 1
      exact congrArg _ (by funext z; rw [if_neg h4])

include hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab in
/-- **A dart decides whether it is a candidate for the first dart of a cut, and its value.** -/
theorem candA_eq {z : D × Bool} (hs : R.Same Γ g₀ z) {mk sm : Prop} (hmk : mk ↔ z ∈ t.marks Γ)
    (hsm : sm ↔ ∃ v, t.NP Γ v ∧ z = t.r0 v) :
    candA W tab (code g₀) (t.viewOf code w₀ z) (t.viewOf code w₀ (R.double.rev z)) mk sm =
      if z ∈ t.aSet Γ g₀ then some (t.aVal code W Γ g₀ z) else none := by
  classical
  have hcy := cycFT_eq hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab
  have hz : z ∈ R.dartsOf Γ g₀ := mem_dartsOf.2 hs
  unfold candA aSet aVal
  rw [hcy]
  by_cases h0 : t.npOf Γ g₀ = 0
  · rw [if_pos h0, if_pos h0]
    simp
  · rw [if_neg h0, if_neg h0]
    by_cases h4 : t.npOf Γ g₀ < 4
    · rw [if_pos h4, if_pos h4, if_pos h4]
      have hiff : sm ↔ z ∈ t.smallSet Γ g₀ := by
        rw [hsm]
        unfold smallSet
        simp [Finset.mem_filter, hz]
      by_cases hsm' : sm
      · rw [if_pos hsm', if_pos (hiff.1 hsm')]
        rfl
      · rw [if_neg hsm', if_neg (fun h => hsm' (hiff.2 h))]
    · rw [if_neg h4, if_neg h4, if_neg h4]
      have hiff : (¬ mk ∧ (hvT W tab (code g₀) (t.viewOf code w₀ z) (t.viewOf code w₀ (R.double.rev z)) ∨
          ¬ hvT W tab (code g₀) (t.viewOf code w₀ (R.double.rev z)) (t.viewOf code w₀ z))) ↔
          z ∈ t.startSet Γ g₀ := by
        rw [hmk, hvT_iff hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab hs,
          hvT_rev_iff hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab hs]
        unfold startSet
        simp [Finset.mem_filter, hz]
      by_cases hc' : z ∈ t.startSet Γ g₀
      · rw [if_pos (hiff.2 hc'), if_pos hc', startValT_eq hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab hs]
      · rw [if_neg (fun h => hc' (hiff.1 h)), if_neg hc']

/-- The value of a candidate for the first dart determines its code. -/
theorem aVal_mod (hcW : ∀ z, code z < W) (u z : D × Bool) : t.aVal code W Γ u z % W = code z := by
  classical
  unfold aVal
  by_cases h4 : t.npOf Γ u < 4
  · rw [if_pos h4, Nat.mod_eq_of_lt (hcW z)]
  · rw [if_neg h4]
    unfold startVal
    by_cases h : t.Hv Γ z
    · rw [if_pos h, lex_mod (hcW z)]
    · rw [if_neg h, lex_mod (hcW z)]

theorem mem_selA_unique (hinj : Function.Injective code) (hcW : ∀ z, code z < W) {u a a' : D × Bool}
    (ha : a ∈ t.selA code W Γ u) (ha' : a' ∈ t.selA code W Γ u) : a = a' :=
  argminF_unique (fun z _ z' _ e => hinj (by rw [← aVal_mod (t := t) (Γ := Γ) hcW u z, e, aVal_mod hcW]))
    ha ha'

include hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab in
/-- The mass from a dart with known numbers. -/
theorem massFromT_eq {a z : D × Bool} (ha : R.Same Γ g₀ a) (hs : R.Same Γ g₀ z) :
    massFromT W tab (code g₀) (pUT W tab (code g₀) (t.viewOf code w₀ a))
      (mFT W tab (code g₀) (t.viewOf code w₀ a)) (t.viewOf code w₀ z) =
      mass (t.tourL Γ) (t.marks Γ) a z :=
  massXY_eq hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab ha hs

include hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab in
/-- **A dart decides whether it is a candidate for the second dart of a cut, and its value.** -/
theorem candY_eq {a z : D × Bool} (ha : R.Same Γ g₀ a) (hs : R.Same Γ g₀ z) (hn : 4 ≤ t.npOf Γ g₀) :
    candY W tab (code g₀) True (pUT W tab (code g₀) (t.viewOf code w₀ a))
        (mFT W tab (code g₀) (t.viewOf code w₀ a)) (fid a) (fid z) (t.viewOf code w₀ z) =
      if z ∈ t.endSet fid Γ g₀ a then some (t.endVal code W Γ a z) else none := by
  classical
  have hcy := cycFT_eq hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab
  have hm := massFromT_eq hL hw h₀ h₁ hL₀ hR hc hg₀ hinj hcW hW hTab ha hs
  unfold candY
  rw [hm, hcy]
  have hz : z ∈ R.dartsOf Γ g₀ := mem_dartsOf.2 hs
  by_cases h : z ∈ t.endSet fid Γ g₀ a
  · rw [if_pos h]
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 h
    rw [if_pos ⟨hn, trivial, h1, h2⟩]
    rfl
  · rw [if_neg h, if_neg]
    rintro ⟨-, -, h1, h2⟩
    exact h (Finset.mem_filter.2 ⟨hz, h1, h2⟩)

theorem endVal_mod (hcW : ∀ z, code z < W) (a z : D × Bool) : t.endVal code W Γ a z % W = code z :=
  lex_mod (hcW z)

include hL h₀ h₁ in
/-- **The next level.** A dart belongs to it if it is a corner, selected in its bag, or a rail of a vertex
whose interval on the tour through all darts holds a selected dart of its bag. -/
theorem mem_next_iff (z : D × Bool) :
    z ∈ t.next Γ (t.sel code W fid Γ) ↔
      z ∈ Γ ∨ z ∈ t.selOf code W fid Γ z ∨
        ∃ u, u ≠ t.root ∧ (z = t.r0 u ∨ z = t.c0 u) ∧ ∃ c ∈ t.selOf code W fid Γ z,
          pos (t.tau w₀) w₀ (t.c1 u) ≤ pos (t.tau w₀) w₀ c ∧
            pos (t.tau w₀) w₀ c ≤ pos (t.tau w₀) w₀ (t.r0 u) := by
  rw [mem_next]
  constructor
  · rintro (h | ⟨c, hc, rfl | h⟩)
    · exact Or.inl h
    · obtain ⟨u, hu⟩ := mem_sel.1 hc
      refine Or.inr (Or.inl ?_)
      rwa [← selOf_congr (selOf_same hu)]
    · obtain ⟨u, hu⟩ := mem_sel.1 hc
      obtain ⟨w, hwn, ha, hz⟩ := mem_railsUp.1 h
      have hne := hwn.ne_root hL
      have hcz : R.Same Γ c z := gcomp_of_mem_railsUp hL h
      have huz : R.Same Γ u z := Same.trans (selOf_same hu) hcz
      refine Or.inr (Or.inr ⟨w, hne, hz, c, ?_, (anc_iff_interval h₀ h₁ hne c).1 ha⟩)
      rwa [← selOf_congr huz]
  · rintro (h | h | ⟨u, hu, hz, c, hcs, hi⟩)
    · exact Or.inl h
    · exact Or.inr ⟨z, mem_sel.2 ⟨z, h⟩, Or.inl rfl⟩
    · by_cases hzΓ : z ∈ Γ
      · exact Or.inl hzΓ
      · have hn : t.NP Γ u := by
          rcases hz with rfl | rfl
          · exact np_of_r0_not_mem hL hu hzΓ
          · exact np_of_c0_not_mem hL hu hzΓ
        exact Or.inr ⟨c, mem_sel.2 ⟨z, hcs⟩, Or.inr
          (mem_railsUp.2 ⟨u, hn, (anc_iff_interval h₀ h₁ hu c).2 hi, hz⟩)⟩

end RootedTree

end RotSystem

end SsspFlow
