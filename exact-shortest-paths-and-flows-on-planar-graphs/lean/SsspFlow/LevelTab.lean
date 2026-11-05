import SsspFlow.NetFlood

/-!
# The answers of the calls of one level

For one level of a decomposition, the calls of the aggregation primitive have answers that do not depend on the
memories of the nodes. The tables are `ptOf` for the corners of a bag, `aOf` for the least first candidate, `raOf`
for the record of the first dart of the cut, `yOf` for the least second candidate, and `ryOf` for the record of
the second dart. A dart reads from them whether it is selected (`isA_iff`, `isY_iff`), and whether it belongs to
the next level (`mem_next`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SsspFlow.Congest

open Cslib.Congest Cslib.Congest.Algorithm FourColor RotSystem RotSystem.RootedTree

variable {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] {R : RotSystem D}

section Sets

variable {t : R.RootedTree V} {Γ : Finset (D × Bool)} {code : D × Bool → ℕ} {W : ℕ} {fid : D × Bool → ℕ}

theorem aSet_same {u z : D × Bool} (h : z ∈ t.aSet Γ u) : R.Same Γ u z := by
  classical
  unfold aSet at h
  split_ifs at h
  · simp at h
  · exact mem_dartsOf.1 (Finset.mem_filter.1 h).1
  · exact mem_dartsOf.1 (Finset.mem_filter.1 h).1

theorem aSet_congr {u u' : D × Bool} (hs : R.Same Γ u u') : t.aSet Γ u = t.aSet Γ u' := by
  unfold aSet smallSet startSet
  rw [npOf_congr (t := t) hs, dartsOf_congr hs]

theorem aVal_congr {u u' : D × Bool} (hs : R.Same Γ u u') : t.aVal code W Γ u = t.aVal code W Γ u' := by
  funext z
  unfold aVal
  rw [npOf_congr (t := t) hs]

theorem selA_congr {u u' : D × Bool} (hs : R.Same Γ u u') : t.selA code W Γ u = t.selA code W Γ u' := by
  unfold selA
  rw [aSet_congr hs, aVal_congr hs]

theorem selA_same {u z : D × Bool} (h : z ∈ t.selA code W Γ u) : R.Same Γ u z :=
  aSet_same (mem_argminF.1 h).1

theorem endSet_congr {u u' : D × Bool} (hs : R.Same Γ u u') (a : D × Bool) :
    t.endSet fid Γ u a = t.endSet fid Γ u' a := by
  unfold endSet
  rw [dartsOf_congr hs, npOf_congr (t := t) hs]

theorem endSet_same {u a z : D × Bool} (h : z ∈ t.endSet fid Γ u a) : R.Same Γ u z :=
  mem_dartsOf.1 (Finset.mem_filter.1 h).1

theorem startOfBag_congr {u u' : D × Bool} (hs : R.Same Γ u u') :
    t.startOfBag code W Γ u = t.startOfBag code W Γ u' := by
  unfold startOfBag startSet
  rw [dartsOf_congr hs]

theorem selY_congr {u u' : D × Bool} (hs : R.Same Γ u u') :
    t.selY code W fid Γ u = t.selY code W fid Γ u' := by
  unfold selY startOfBag startSet endSet
  rw [dartsOf_congr hs, npOf_congr (t := t) hs]

theorem selA_eq_start {u : D × Bool} (h0 : t.npOf Γ u ≠ 0) (h4 : ¬ t.npOf Γ u < 4) :
    t.selA code W Γ u = t.startOfBag code W Γ u := by
  classical
  unfold selA aSet startOfBag
  rw [if_neg h0, if_neg h4]
  exact congrArg _ (by funext z; unfold aVal; rw [if_neg h4])

theorem selOf_same' {u z : D × Bool} (h : z ∈ t.selY code W fid Γ u) : R.Same Γ u z :=
  selOf_same (t := t) (by rw [selOf_eq]; exact Finset.mem_union_right _ h)

end Sets

theorem mem_optItems {o : Option ℕ} {κ a : ℕ} :
    (κ, a) ∈ o.toList.map (fun a => ((0 : ℕ), a)) ↔ κ = 0 ∧ o = some a := by
  cases o with
  | none => simp
  | some b =>
    simp only [Option.toList_some, List.map_cons, List.map_nil, List.mem_singleton, Prod.mk.injEq,
      Option.some.injEq]
    exact and_congr_right fun _ => eq_comm

variable (R V) in
/-- The data of a decomposition. -/
structure LevelData where
  t : R.RootedTree V
  code : D × Bool → ℕ
  W : ℕ
  fid : D × Bool → ℕ
  w₀ : D × Bool

namespace LevelData

variable (L : LevelData V R)

/-- The levels. -/
noncomputable def Γs : ℕ → Finset (D × Bool) := L.t.levelSeq L.code L.W L.fid L.w₀

/-- The name of the bag of a dart. -/
noncomputable def nm (d : ℕ) (z : D × Bool) : ℕ := R.bagName L.code L.Γs d z

/-- The fields of a corner. -/
noncomputable def portField (Γ : Finset (D × Bool)) (j : ℕ) (z : D × Bool) : ℕ :=
  match j with
  | 0 => pos (L.t.tau L.w₀) L.w₀ z
  | 1 => L.t.arcV Γ (L.t.marks {L.w₀}) (L.t.marks Γ) L.w₀ z
  | 2 => L.t.arcV Γ Finset.univ Finset.univ L.w₀ z
  | 3 => L.t.phiB (L.t.marks {L.w₀}) (L.t.marks Γ) L.w₀ ((R.double.nodeReturn Γ)⁻¹ z)
  | _ => L.t.phiB Finset.univ Finset.univ L.w₀ ((R.double.nodeReturn Γ)⁻¹ z)

/-- The pairs of a dart in the call for the corners. -/
noncomputable def portItems (d : ℕ) (z : D × Bool) : List (ℕ × ℕ) :=
  if z ∈ L.Γs d then
    (List.range 5).map fun j => (Nat.pair (L.code z) j, L.portField (L.Γs d) j z)
  else []

/-- The table of the corners of the bag of a dart. -/
noncomputable def ptOf (d : ℕ) (z : D × Bool) (κ : ℕ) : ℕ :=
  tabD (L.nm d) (L.portItems d) (L.nm d z) κ

/-- The least code of a corner of the bag of a dart. -/
noncomputable def mcOf (d : ℕ) (z : D × Bool) : ℕ := R.minCode L.code (L.Γs d) z

/-- The numbers of a dart. -/
noncomputable abbrev view (z : D × Bool) : View := L.t.viewOf L.code L.w₀ z

/-- The value of a dart as the first dart of a cut. -/
noncomputable def aCand (d : ℕ) (z : D × Bool) : Option ℕ :=
  candA L.W (L.ptOf d z) (L.mcOf d z) (L.view z) (L.view (R.double.rev z))
    (z ∈ L.t.marks (L.Γs d)) (∃ v, L.t.NP (L.Γs d) v ∧ z = L.t.r0 v)

/-- The pairs of a dart in the call for the first dart. -/
noncomputable def aItems (d : ℕ) (z : D × Bool) : List (ℕ × ℕ) :=
  (L.aCand d z).toList.map fun a => (0, a)

/-- The least value of a first dart in the bag of a dart. -/
noncomputable def aOf (d : ℕ) (z : D × Bool) : ℕ := tabD (L.nm d) (L.aItems d) (L.nm d z) 0

/-- The dart is the first dart of the cut of its bag. -/
def isA (d : ℕ) (z : D × Bool) : Prop := ∃ a, L.aCand d z = some a ∧ L.aOf d z = a + 1

/-- The fields of the first dart of a cut. -/
noncomputable def raFields (d : ℕ) (z : D × Bool) : List (ℕ × ℕ) :=
  [(0, pos (L.t.tau L.w₀) L.w₀ z), (1, mFT L.W (L.ptOf d z) (L.mcOf d z) (L.view z)),
    (2, pUT L.W (L.ptOf d z) (L.mcOf d z) (L.view z)), (3, L.fid z)]

open Classical in
/-- The pairs of a dart in the call for the record of the first dart. -/
noncomputable def raItems (d : ℕ) (z : D × Bool) : List (ℕ × ℕ) :=
  if L.isA d z then L.raFields d z else []

/-- The record of the first dart of the cut of the bag of a dart. -/
noncomputable def raOf (d : ℕ) (z : D × Bool) (κ : ℕ) : ℕ :=
  tabD (L.nm d) (L.raItems d) (L.nm d z) κ

/-- The value of a dart as the second dart of a cut. -/
noncomputable def yCand (d : ℕ) (z : D × Bool) : Option ℕ :=
  candY L.W (L.ptOf d z) (L.mcOf d z) (L.raOf d z 0 ≠ 0) (L.raOf d z 2 - 1) (L.raOf d z 1 - 1)
    (L.raOf d z 3 - 1) (L.fid z) (L.view z)

/-- The pairs of a dart in the call for the second dart. -/
noncomputable def yItems (d : ℕ) (z : D × Bool) : List (ℕ × ℕ) :=
  (L.yCand d z).toList.map fun a => (0, a)

/-- The least value of a second dart in the bag of a dart. -/
noncomputable def yOf (d : ℕ) (z : D × Bool) : ℕ := tabD (L.nm d) (L.yItems d) (L.nm d z) 0

/-- The dart is the second dart of the cut of its bag. -/
def isY (d : ℕ) (z : D × Bool) : Prop := ∃ a, L.yCand d z = some a ∧ L.yOf d z = a + 1

open Classical in
/-- The pairs of a dart in the call for the record of the second dart. -/
noncomputable def ryItems (d : ℕ) (z : D × Bool) : List (ℕ × ℕ) :=
  if L.isY d z then [(0, pos (L.t.tau L.w₀) L.w₀ z)] else []

/-- The record of the second dart of the cut of the bag of a dart. -/
noncomputable def ryOf (d : ℕ) (z : D × Bool) : ℕ := tabD (L.nm d) (L.ryItems d) (L.nm d z) 0

/-- A dart of a cut lies in an interval of positions on the tour through all darts. -/
def ivOf (d : ℕ) (z : D × Bool) (lo hi : ℕ) : Prop :=
  (L.raOf d z 0 ≠ 0 ∧ lo ≤ L.raOf d z 0 - 1 ∧ L.raOf d z 0 - 1 ≤ hi) ∨
    (L.ryOf d z ≠ 0 ∧ lo ≤ L.ryOf d z - 1 ∧ L.ryOf d z - 1 ≤ hi)

/-- The hypotheses on the data. -/
structure OK : Prop where
  h₀ : L.t.vertM L.w₀ = L.t.root
  h₁ : L.w₀.2 = true
  hR : R.Planar
  hc : R.Connected
  hinj : Function.Injective L.code
  hcW : ∀ z, L.code z < L.W
  hW : Fintype.card (D × Bool) ≤ L.W
  hfid : ∀ x y, L.fid x = L.fid y ↔ fconnect R.double.facePerm x y

variable {L}

theorem nm_congr {d : ℕ} {u u' : D × Bool} (hs : R.Same (L.Γs d) u u') : L.nm d u = L.nm d u' :=
  bagName_congr hs

theorem ptOf_congr {d : ℕ} {u u' : D × Bool} (hs : R.Same (L.Γs d) u u') : L.ptOf d u = L.ptOf d u' := by
  funext κ
  unfold ptOf
  rw [nm_congr hs]

theorem mcOf_congr {d : ℕ} {u u' : D × Bool} (hs : R.Same (L.Γs d) u u') : L.mcOf d u = L.mcOf d u' :=
  minCode_congr hs

theorem mem_portItems {d : ℕ} {z : D × Bool} {κ a : ℕ} :
    (κ, a) ∈ L.portItems d z ↔
      z ∈ L.Γs d ∧ ∃ j, j < 5 ∧ κ = Nat.pair (L.code z) j ∧ a = L.portField (L.Γs d) j z := by
  unfold portItems
  by_cases hz : z ∈ L.Γs d
  · rw [if_pos hz, List.mem_map]
    simp only [List.mem_range, Prod.mk.injEq, hz, true_and]
    constructor
    · rintro ⟨j, hj, h1, h2⟩
      exact ⟨j, hj, h1.symm, h2.symm⟩
    · rintro ⟨j, hj, h1, h2⟩
      exact ⟨j, hj, h1.symm, h2.symm⟩
  · rw [if_neg hz]
    simp [hz]

theorem mem_aItems {d : ℕ} {z : D × Bool} {κ a : ℕ} :
    (κ, a) ∈ L.aItems d z ↔ κ = 0 ∧ L.aCand d z = some a := mem_optItems

theorem mem_yItems {d : ℕ} {z : D × Bool} {κ a : ℕ} :
    (κ, a) ∈ L.yItems d z ↔ κ = 0 ∧ L.yCand d z = some a := mem_optItems

namespace OK

variable (h : L.OK)

include h

theorem decomp : L.t.Decomp L.w₀ L.Γs (fun d => L.t.sel L.code L.W L.fid (L.Γs d)) :=
  decomp_levelSeq h.h₀ h.h₁ h.hR h.hc h.hinj h.hcW h.hfid

theorem level (d : ℕ) : L.t.IsLevel (L.Γs d) := h.decomp.level d

theorem w₀_mem (d : ℕ) : L.w₀ ∈ L.Γs d := h.decomp.w₀_mem d

theorem hL₀ : L.t.IsLevel {L.w₀} := isLevel_singleton h.h₀ h.h₁

theorem hne (d : ℕ) (u : D × Bool) : ∃ g ∈ L.Γs d, R.Same (L.Γs d) u g :=
  h.decomp.exists_port h.hc d u

theorem nm_eq_iff {d : ℕ} {u u' : D × Bool} : L.nm d u = L.nm d u' ↔ R.Same (L.Γs d) u u' :=
  bagName_eq_iff (fun d u => h.hne d u) h.hinj

theorem exists_minPort (d : ℕ) (z : D × Bool) :
    ∃ g ∈ L.Γs d, R.Same (L.Γs d) z g ∧ L.code g = L.mcOf d z := by
  obtain ⟨g₁, hg₁, hs₁⟩ := h.hne d z
  have hnon : (L.code '' (R.portsOf (L.Γs d) z : Set (D × Bool))).Nonempty :=
    ⟨_, g₁, mem_portsOf.2 ⟨hg₁, hs₁⟩, rfl⟩
  obtain ⟨g, hg, hgc⟩ := Nat.sInf_mem hnon
  obtain ⟨hgΓ, hs⟩ := mem_portsOf.1 hg
  exact ⟨g, hgΓ, hs, hgc⟩

theorem ptOf_field {d : ℕ} {g₀ p : D × Bool} {j : ℕ} (hp : p ∈ R.portsOf (L.Γs d) g₀) (hj : j < 5) :
    L.ptOf d g₀ (Nat.pair (L.code p) j) = L.portField (L.Γs d) j p + 1 := by
  obtain ⟨hpΓ, hs⟩ := mem_portsOf.1 hp
  refine tabD_of_unique ⟨p, (h.nm_eq_iff.2 hs).symm, mem_portItems.2 ⟨hpΓ, j, hj, rfl, rfl⟩⟩ ?_
  intro z a hz hm
  obtain ⟨hzΓ, j', hj', he, rfl⟩ := mem_portItems.1 hm
  obtain ⟨e1, rfl⟩ := Nat.pair_eq_pair.1 he
  obtain rfl := h.hinj e1
  rfl

/-- **The table of the corners of a bag.** -/
theorem portTab {d : ℕ} {g₀ : D × Bool} :
    L.t.PortTab L.W (L.ptOf d g₀) (L.Γs d) g₀ L.code L.w₀ where
  f0 _ hp := h.ptOf_field hp (j := 0) (by norm_num)
  f1 _ hp := h.ptOf_field hp (j := 1) (by norm_num)
  f2 _ hp := h.ptOf_field hp (j := 2) (by norm_num)
  f3 _ hp := h.ptOf_field hp (j := 3) (by norm_num)
  f4 _ hp := h.ptOf_field hp (j := 4) (by norm_num)
  none c hc := tabD_none fun z a hz hm => by
    obtain ⟨hzΓ, j, _, he, _⟩ := mem_portItems.1 hm
    exact hc z (mem_portsOf.2 ⟨hzΓ, h.nm_eq_iff.1 hz.symm⟩) (Nat.pair_eq_pair.1 he).1.symm

theorem aCand_eq {d : ℕ} {g₀ z : D × Bool} (hg : g₀ ∈ L.Γs d) (hgc : L.code g₀ = L.mcOf d g₀)
    (hs : R.Same (L.Γs d) g₀ z) :
    L.aCand d z = if z ∈ L.t.aSet (L.Γs d) g₀ then some (L.t.aVal L.code L.W (L.Γs d) g₀ z) else none := by
  unfold aCand
  rw [← ptOf_congr hs, ← mcOf_congr hs, ← hgc]
  exact candA_eq (h.level d) (h.w₀_mem d) h.h₀ h.h₁ h.hL₀ h.hR h.hc hg h.hinj h.hcW h.hW h.portTab hs
    Iff.rfl Iff.rfl

/-- **A dart reads whether it is the first dart of the cut of its bag.** -/
theorem isA_iff {d : ℕ} {z : D × Bool} : L.isA d z ↔ z ∈ L.t.selA L.code L.W (L.Γs d) z := by
  classical
  obtain ⟨g₀, hg, hzg, hgc⟩ := h.exists_minPort d z
  have hgz : R.Same (L.Γs d) g₀ z := Same.symm hzg
  have hgc' : L.code g₀ = L.mcOf d g₀ := hgc.trans (mcOf_congr hzg)
  have key := fun {z' : D × Bool} (hs' : R.Same (L.Γs d) g₀ z') => h.aCand_eq hg hgc' hs'
  rw [selA_congr hzg]
  unfold RotSystem.RootedTree.selA
  rw [mem_argminF]
  constructor
  · rintro ⟨a, hca, hta⟩
    rw [key hgz] at hca
    by_cases hm : z ∈ L.t.aSet (L.Γs d) g₀
    · rw [if_pos hm] at hca
      obtain rfl := Option.some.inj hca
      refine ⟨hm, fun z' hz' => ?_⟩
      have hs' := aSet_same hz'
      have hn : L.nm d z' = L.nm d z := nm_congr (Same.trans (Same.symm hs') hgz)
      have hmem : ((0 : ℕ), L.t.aVal L.code L.W (L.Γs d) g₀ z') ∈ L.aItems d z' :=
        mem_aItems.2 ⟨rfl, by rw [key hs', if_pos hz']⟩
      have h1 := tabD_le hn hmem
      unfold aOf at hta
      omega
    · rw [if_neg hm] at hca
      simp at hca
  · rintro ⟨hm, hl⟩
    have hc : L.aCand d z = some (L.t.aVal L.code L.W (L.Γs d) g₀ z) := by rw [key hgz, if_pos hm]
    refine ⟨_, hc, tabD_of_least ⟨z, rfl, mem_aItems.2 ⟨rfl, hc⟩⟩ ?_⟩
    intro z' a' hn hm'
    obtain ⟨-, hc'⟩ := mem_aItems.1 hm'
    have hs' : R.Same (L.Γs d) g₀ z' := Same.trans hgz (h.nm_eq_iff.1 hn.symm)
    rw [key hs'] at hc'
    by_cases hmz : z' ∈ L.t.aSet (L.Γs d) g₀
    · rw [if_pos hmz] at hc'
      obtain rfl := Option.some.inj hc'
      exact hl z' hmz
    · rw [if_neg hmz] at hc'
      simp at hc'

theorem raFields_unique {d : ℕ} {κ x y : ℕ} {z : D × Bool} (hx : (κ, x) ∈ L.raFields d z)
    (hy : (κ, y) ∈ L.raFields d z) : x = y := by
  simp only [raFields, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hx hy
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases hy with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega

/-- The record of the first dart of a cut. -/
theorem raOf_eq {d : ℕ} {z a : D × Bool} {κ x : ℕ} (ha : a ∈ L.t.selA L.code L.W (L.Γs d) z)
    (hv : (κ, x) ∈ L.raFields d a) : L.raOf d z κ = x + 1 := by
  classical
  have hsame := selA_same ha
  have hA : L.isA d a := h.isA_iff.2 (by rw [← selA_congr hsame]; exact ha)
  refine tabD_of_unique ⟨a, (nm_congr hsame).symm, by unfold raItems; rw [if_pos hA]; exact hv⟩ ?_
  intro z' a' hn hm
  unfold raItems at hm
  by_cases hA' : L.isA d z'
  · rw [if_pos hA'] at hm
    have hz' := h.isA_iff.1 hA'
    rw [← selA_congr (h.nm_eq_iff.1 hn.symm)] at hz'
    obtain rfl : z' = a := mem_selA_unique h.hinj h.hcW hz' ha
    exact h.raFields_unique hm hv
  · rw [if_neg hA'] at hm
    simp at hm

theorem raOf_none {d : ℕ} {z : D × Bool} (hn : L.t.selA L.code L.W (L.Γs d) z = ∅) (κ : ℕ) :
    L.raOf d z κ = 0 := by
  classical
  refine tabD_none fun z' a hz' hm => ?_
  unfold raItems at hm
  by_cases hA : L.isA d z'
  · have hz := h.isA_iff.1 hA
    rw [← selA_congr (h.nm_eq_iff.1 hz'.symm), hn] at hz
    simp at hz
  · rw [if_neg hA] at hm
    simp at hm

theorem yCand_eq {d : ℕ} {g₀ a z : D × Bool} (hg : g₀ ∈ L.Γs d) (hgc : L.code g₀ = L.mcOf d g₀)
    (ha : a ∈ L.t.selA L.code L.W (L.Γs d) g₀) (hs : R.Same (L.Γs d) g₀ z)
    (hn : 4 ≤ L.t.npOf (L.Γs d) g₀) :
    L.yCand d z = if z ∈ L.t.endSet L.fid (L.Γs d) g₀ a then
      some (L.t.endVal L.code L.W (L.Γs d) a z) else none := by
  have hsa : R.Same (L.Γs d) g₀ a := selA_same ha
  have hP : L.ptOf d a = L.ptOf d g₀ := (ptOf_congr hsa).symm
  have hM : L.mcOf d a = L.code g₀ := by rw [hgc]; exact (mcOf_congr hsa).symm
  have hsel : a ∈ L.t.selA L.code L.W (L.Γs d) z := by rw [← selA_congr hs]; exact ha
  have h0 : L.raOf d z 0 = pos (L.t.tau L.w₀) L.w₀ a + 1 := h.raOf_eq hsel (by simp [raFields])
  have h1 : L.raOf d z 1 = mFT L.W (L.ptOf d g₀) (L.code g₀) (L.view a) + 1 := by
    have := h.raOf_eq hsel (κ := 1) (x := mFT L.W (L.ptOf d a) (L.mcOf d a) (L.view a))
      (by simp [raFields])
    rwa [hP, hM] at this
  have h2 : L.raOf d z 2 = pUT L.W (L.ptOf d g₀) (L.code g₀) (L.view a) + 1 := by
    have := h.raOf_eq hsel (κ := 2) (x := pUT L.W (L.ptOf d a) (L.mcOf d a) (L.view a))
      (by simp [raFields])
    rwa [hP, hM] at this
  have h3 : L.raOf d z 3 = L.fid a + 1 := h.raOf_eq hsel (by simp [raFields])
  have hT : (L.raOf d z 0 ≠ 0) = True := by
    rw [h0]
    simp
  unfold yCand
  rw [hT, h1, h2, h3, ← ptOf_congr hs, ← mcOf_congr hs, ← hgc]
  simp only [Nat.add_sub_cancel]
  exact candY_eq (h.level d) (h.w₀_mem d) h.h₀ h.h₁ h.hL₀ h.hR h.hc hg h.hinj h.hcW h.hW h.portTab hsa hs hn

/-- **A dart reads whether it is the second dart of the cut of its bag.** -/
theorem isY_iff {d : ℕ} {z : D × Bool} : L.isY d z ↔ z ∈ L.t.selY L.code L.W L.fid (L.Γs d) z := by
  classical
  obtain ⟨g₀, hg, hzg, hgc⟩ := h.exists_minPort d z
  have hgz : R.Same (L.Γs d) g₀ z := Same.symm hzg
  have hgc' : L.code g₀ = L.mcOf d g₀ := hgc.trans (mcOf_congr hzg)
  by_cases h4 : L.t.npOf (L.Γs d) z < 4
  · have hnone : L.yCand d z = none := by
      unfold yCand candY
      rw [if_neg]
      rintro ⟨h5, -⟩
      have h6 := cycFT_eq (h.level d) (h.w₀_mem d) h.h₀ h.h₁ h.hL₀ h.hR h.hc hg h.hinj h.hcW h.hW
        (h.portTab (d := d) (g₀ := g₀))
      rw [ptOf_congr hzg, h6, ← npOf_congr hzg] at h5
      omega
    unfold RotSystem.RootedTree.selY
    rw [if_pos h4]
    constructor
    · rintro ⟨a, hc, -⟩
      rw [hnone] at hc
      simp at hc
    · intro hz
      simp at hz
  · have h0 : L.t.npOf (L.Γs d) z ≠ 0 := by omega
    have hn : 4 ≤ L.t.npOf (L.Γs d) g₀ := by
      rw [← npOf_congr hzg]
      omega
    obtain ⟨a, ha⟩ := argminF_nonempty (f := L.t.startVal L.code L.W (L.Γs d))
      (startSet_nonempty (h.level d) h.hc g₀)
    have hsel : a ∈ L.t.selA L.code L.W (L.Γs d) g₀ := by
      rw [selA_eq_start (by rw [← npOf_congr hzg]; exact h0) (by rw [← npOf_congr hzg]; exact h4)]
      exact ha
    have key := fun {z' : D × Bool} (hs' : R.Same (L.Γs d) g₀ z') => h.yCand_eq hg hgc' hsel hs' hn
    have hY : z ∈ L.t.selY L.code L.W L.fid (L.Γs d) z ↔
        z ∈ argminF (L.t.endSet L.fid (L.Γs d) g₀ a) (L.t.endVal L.code L.W (L.Γs d) a) := by
      unfold RotSystem.RootedTree.selY
      rw [if_neg h4, Finset.mem_biUnion]
      constructor
      · rintro ⟨a', ha', hz⟩
        have ha'' : a' ∈ L.t.selA L.code L.W (L.Γs d) g₀ := by
          rw [selA_eq_start (by rw [← npOf_congr hzg]; exact h0) (by rw [← npOf_congr hzg]; exact h4),
            ← startOfBag_congr hzg]
          exact ha'
        obtain rfl : a' = a := mem_selA_unique h.hinj h.hcW ha'' hsel
        rwa [endSet_congr hzg] at hz
      · intro hz
        exact ⟨a, by rw [startOfBag_congr hzg]; exact ha, by rwa [endSet_congr hzg]⟩
    rw [hY, mem_argminF]
    constructor
    · rintro ⟨b, hca, hta⟩
      rw [key hgz] at hca
      by_cases hm : z ∈ L.t.endSet L.fid (L.Γs d) g₀ a
      · rw [if_pos hm] at hca
        obtain rfl := Option.some.inj hca
        refine ⟨hm, fun z' hz' => ?_⟩
        have hs' := endSet_same hz'
        have hn' : L.nm d z' = L.nm d z := nm_congr (Same.trans (Same.symm hs') hgz)
        have hmem : ((0 : ℕ), L.t.endVal L.code L.W (L.Γs d) a z') ∈ L.yItems d z' :=
          mem_yItems.2 ⟨rfl, by rw [key hs', if_pos hz']⟩
        have h1 := tabD_le hn' hmem
        unfold yOf at hta
        omega
      · rw [if_neg hm] at hca
        simp at hca
    · rintro ⟨hm, hl⟩
      have hc : L.yCand d z = some (L.t.endVal L.code L.W (L.Γs d) a z) := by rw [key hgz, if_pos hm]
      refine ⟨_, hc, tabD_of_least ⟨z, rfl, mem_yItems.2 ⟨rfl, hc⟩⟩ ?_⟩
      intro z' a' hn' hm'
      obtain ⟨-, hc'⟩ := mem_yItems.1 hm'
      have hs' : R.Same (L.Γs d) g₀ z' := Same.trans hgz (h.nm_eq_iff.1 hn'.symm)
      rw [key hs'] at hc'
      by_cases hmz : z' ∈ L.t.endSet L.fid (L.Γs d) g₀ a
      · rw [if_pos hmz] at hc'
        obtain rfl := Option.some.inj hc'
        exact hl z' hmz
      · rw [if_neg hmz] at hc'
        simp at hc'

theorem selY_unique {d : ℕ} {z y y' : D × Bool} (hy : y ∈ L.t.selY L.code L.W L.fid (L.Γs d) z)
    (hy' : y' ∈ L.t.selY L.code L.W L.fid (L.Γs d) z) : y = y' := by
  classical
  unfold RotSystem.RootedTree.selY at hy hy'
  by_cases h4 : L.t.npOf (L.Γs d) z < 4
  · rw [if_pos h4] at hy
    simp at hy
  · rw [if_neg h4, Finset.mem_biUnion] at hy hy'
    obtain ⟨a, ha, h1⟩ := hy
    obtain ⟨a', ha', h2⟩ := hy'
    have h0 : L.t.npOf (L.Γs d) z ≠ 0 := by omega
    have e1 : a ∈ L.t.selA L.code L.W (L.Γs d) z := by rw [selA_eq_start h0 h4]; exact ha
    have e2 : a' ∈ L.t.selA L.code L.W (L.Γs d) z := by rw [selA_eq_start h0 h4]; exact ha'
    obtain rfl : a = a' := mem_selA_unique h.hinj h.hcW e1 e2
    refine argminF_unique (fun u _ u' _ e => h.hinj ?_) h1 h2
    rw [← endVal_mod (t := L.t) (Γ := L.Γs d) (a := a) h.hcW u, e, endVal_mod h.hcW]

/-- The record of the second dart of a cut. -/
theorem ryOf_eq {d : ℕ} {z y : D × Bool} (hy : y ∈ L.t.selY L.code L.W L.fid (L.Γs d) z) :
    L.ryOf d z = pos (L.t.tau L.w₀) L.w₀ y + 1 := by
  classical
  have hsame := selOf_same' hy
  have hA : L.isY d y := h.isY_iff.2 (by rw [← selY_congr hsame]; exact hy)
  refine tabD_of_unique ⟨y, (nm_congr hsame).symm, by unfold ryItems; rw [if_pos hA]; simp⟩ ?_
  intro z' a' hn hm
  unfold ryItems at hm
  by_cases hA' : L.isY d z'
  · rw [if_pos hA'] at hm
    have hz' := h.isY_iff.1 hA'
    rw [← selY_congr (h.nm_eq_iff.1 hn.symm)] at hz'
    obtain rfl : z' = y := h.selY_unique hz' hy
    simpa using hm
  · rw [if_neg hA'] at hm
    simp at hm

theorem ryOf_none {d : ℕ} {z : D × Bool} (hn : L.t.selY L.code L.W L.fid (L.Γs d) z = ∅) :
    L.ryOf d z = 0 := by
  classical
  refine tabD_none fun z' a hz' hm => ?_
  unfold ryItems at hm
  by_cases hA : L.isY d z'
  · have hz := h.isY_iff.1 hA
    rw [← selY_congr (h.nm_eq_iff.1 hz'.symm), hn] at hz
    simp at hz
  · rw [if_neg hA] at hm
    simp at hm

theorem iv_iff {d : ℕ} {z : D × Bool} {lo hi : ℕ} :
    L.ivOf d z lo hi ↔ ∃ c ∈ L.t.selOf L.code L.W L.fid (L.Γs d) z,
      lo ≤ pos (L.t.tau L.w₀) L.w₀ c ∧ pos (L.t.tau L.w₀) L.w₀ c ≤ hi := by
  classical
  have hA : ∀ {a}, a ∈ L.t.selA L.code L.W (L.Γs d) z →
      L.raOf d z 0 = pos (L.t.tau L.w₀) L.w₀ a + 1 := fun ha => h.raOf_eq ha (by simp [raFields])
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · obtain ⟨a, ha⟩ : (L.t.selA L.code L.W (L.Γs d) z).Nonempty := by
        by_contra hne
        exact h1 (h.raOf_none (Finset.not_nonempty_iff_eq_empty.1 hne) 0)
      rw [hA ha] at h2 h3
      exact ⟨a, by rw [selOf_eq]; exact Finset.mem_union_left _ ha, by simpa using h2, by simpa using h3⟩
    · obtain ⟨y, hy⟩ : (L.t.selY L.code L.W L.fid (L.Γs d) z).Nonempty := by
        by_contra hne
        exact h1 (h.ryOf_none (Finset.not_nonempty_iff_eq_empty.1 hne))
      rw [h.ryOf_eq hy] at h2 h3
      exact ⟨y, by rw [selOf_eq]; exact Finset.mem_union_right _ hy, by simpa using h2, by simpa using h3⟩
  · rintro ⟨c, hc, h2, h3⟩
    rw [selOf_eq, Finset.mem_union] at hc
    rcases hc with hc | hc
    · refine Or.inl ?_
      rw [hA hc]
      simpa using ⟨h2, h3⟩
    · refine Or.inr ?_
      rw [h.ryOf_eq hc]
      simpa using ⟨h2, h3⟩

/-- **A dart reads whether it belongs to the next level.** -/
theorem mem_next {d : ℕ} {z : D × Bool} :
    z ∈ L.Γs (d + 1) ↔ z ∈ L.Γs d ∨ L.isA d z ∨ L.isY d z ∨
      ∃ u, u ≠ L.t.root ∧ (z = L.t.r0 u ∨ z = L.t.c0 u) ∧
        L.ivOf d z (pos (L.t.tau L.w₀) L.w₀ (L.t.c1 u)) (pos (L.t.tau L.w₀) L.w₀ (L.t.r0 u)) := by
  have e : z ∈ L.Γs (d + 1) ↔ z ∈ L.t.next (L.Γs d) (L.t.sel L.code L.W L.fid (L.Γs d)) := Iff.rfl
  have e2 : z ∈ L.t.selOf L.code L.W L.fid (L.Γs d) z ↔ L.isA d z ∨ L.isY d z := by
    rw [selOf_eq, Finset.mem_union, h.isA_iff, h.isY_iff]
  rw [e, mem_next_iff (h.level d) h.h₀ h.h₁ z, e2]
  simp only [h.iv_iff, or_assoc]

/-! ### Bounds of the values and of the keys -/

theorem mcOf_lt (d : ℕ) (z : D × Bool) : L.mcOf d z < L.W := by
  obtain ⟨g, -, -, hgc⟩ := h.exists_minPort d z
  rw [← hgc]
  exact h.hcW g

theorem nm_lt {H d : ℕ} (hH : H ≤ L.W) (hd : d ≤ H) (z : D × Bool) : L.nm d z < (L.W + 1) ^ 2 := by
  have h1 := h.mcOf_lt d z
  have h2 : L.nm d z = Nat.pair d (L.mcOf d z) := rfl
  rw [h2]
  refine (Nat.pair_lt_max_add_one_sq _ _).trans_le (Nat.pow_le_pow_left ?_ 2)
  have : max d (L.mcOf d z) ≤ L.W := max_le (hd.trans hH) h1.le
  omega

theorem pos_le_W (f : Equiv.Perm (D × Bool)) (x y : D × Bool) : pos f x y ≤ L.W := by
  by_cases hc : fconnect f x y
  · have h1 := pos_lt_card f hc (S := Finset.univ) (fun _ _ => Finset.mem_univ _)
    have h2 := h.hW
    rw [Finset.card_univ] at h1
    omega
  · rw [pos_of_not_fconnect hc]
    exact Nat.zero_le _

theorem card_le_W (T : Finset (D × Bool)) : T.card ≤ L.W :=
  (Finset.card_le_univ _).trans h.hW

theorem phi_le (T₀ : Finset (D × Bool)) (w₀ z : D × Bool) : L.t.phi T₀ w₀ z ≤ L.W :=
  (phi_le_card _ _ _ _).trans (h.card_le_W _)

theorem phiB_le (T₀ T : Finset (D × Bool)) (w₀ e : D × Bool) : L.t.phiB T₀ T w₀ e ≤ L.W := by
  unfold RotSystem.RootedTree.phiB
  split_ifs
  · exact (Nat.sub_le _ _).trans (h.phi_le _ _ _)
  · exact h.phi_le _ _ _

theorem arcV_le (Γ T₀ T : Finset (D × Bool)) (w₀ x : D × Bool) : L.t.arcV Γ T₀ T w₀ x ≤ L.W + 1 := by
  have hi : ind T x ≤ 1 := by
    unfold ind
    split_ifs <;> omega
  unfold RotSystem.RootedTree.arcV
  split_ifs
  · have := h.card_le_W T
    omega
  · have h1 := h.phi_le T₀ w₀ (R.double.rot⁻¹ x)
    have h2 := Nat.sub_le (L.t.phi T₀ w₀ (R.double.rot⁻¹ x))
      (L.t.phiB T₀ T w₀ ((R.double.nodeReturn Γ)⁻¹ x))
    omega

theorem portField_le (Γ : Finset (D × Bool)) (j : ℕ) (z : D × Bool) : L.portField Γ j z ≤ L.W + 1 := by
  rcases j with _ | _ | _ | _ | j
  · exact (h.pos_le_W _ _ _).trans (Nat.le_succ _)
  · exact h.arcV_le _ _ _ _ _
  · exact h.arcV_le _ _ _ _ _
  · exact (h.phiB_le _ _ _ _).trans (Nat.le_succ _)
  · exact (h.phiB_le _ _ _ _).trans (Nat.le_succ _)

theorem portItems_lt {d κ a : ℕ} {z : D × Bool} (h5 : 5 ≤ L.W) (hm : (κ, a) ∈ L.portItems d z) :
    κ < (L.W + 1) ^ 2 ∧ a ≤ L.W + 1 := by
  obtain ⟨-, j, hj, rfl, rfl⟩ := mem_portItems.1 hm
  refine ⟨(Nat.pair_lt_max_add_one_sq _ _).trans_le (Nat.pow_le_pow_left ?_ 2), h.portField_le _ _ _⟩
  have := h.hcW z
  have : max (L.code z) j ≤ L.W := max_le (by omega) (by omega)
  omega

theorem exists_port_keys {hh : ℕ} (hdep : ∀ v, L.t.dep v ≤ hh) (d : ℕ) (z : D × Bool) :
    ∃ K : Finset ℕ, K.card ≤ 5 * (1 + d * (2 + 4 * hh)) ∧
      ∀ z', L.nm d z' = L.nm d z → ∀ p ∈ L.portItems d z', p.1 ∈ K := by
  classical
  refine ⟨(R.portsOf (L.Γs d) z).biUnion fun p => (Finset.range 5).image (Nat.pair (L.code p)), ?_, ?_⟩
  · refine (Finset.card_biUnion_le_card_mul _ _ 5 fun p _ => ?_).trans ?_
    · exact Finset.card_image_le.trans (by simp)
    · have := h.decomp.card_ports hdep d z
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left 5 this
  · rintro z' hn ⟨κ, a⟩ hm
    obtain ⟨hz', j, hj, rfl, -⟩ := mem_portItems.1 hm
    refine Finset.mem_biUnion.2 ⟨z', mem_portsOf.2 ⟨hz', h.nm_eq_iff.1 hn.symm⟩,
      Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, rfl⟩⟩

theorem mass_le_W (f : Equiv.Perm (D × Bool)) (T : Finset (D × Bool)) (x y : D × Bool) :
    mass f T x y ≤ L.W := by
  classical
  unfold mass
  exact (Finset.card_filter_le _ _).trans (h.card_le_W _)

theorem aCand_lt {d a : ℕ} {z : D × Bool} (hc : L.aCand d z = some a) : a < (L.W + 2) * (L.W + 2) := by
  obtain ⟨g₀, hg, hzg, hgc⟩ := h.exists_minPort d z
  rw [h.aCand_eq hg (hgc.trans (mcOf_congr hzg)) (Same.symm hzg)] at hc
  split_ifs at hc with hm
  obtain rfl := Option.some.inj hc
  have hz := h.hcW z
  have hp := h.pos_le_W (L.t.tourL (L.Γs d)) z (R.double.rev z)
  have h1 : (pos (L.t.tourL (L.Γs d)) z (R.double.rev z) + 1) * L.W ≤ (L.W + 1) * L.W :=
    Nat.mul_le_mul_right _ (by omega)
  unfold RotSystem.RootedTree.aVal RotSystem.RootedTree.startVal
  split_ifs <;> nlinarith

theorem mFT_view (d : ℕ) (z : D × Bool) :
    mFT L.W (L.ptOf d z) (L.mcOf d z) (L.view z) ≤ L.W ∧
      pUT L.W (L.ptOf d z) (L.mcOf d z) (L.view z) ≤ L.W ∧ cycFT L.W (L.ptOf d z) ≤ L.W := by
  obtain ⟨g₀, hg, hzg, hgc⟩ := h.exists_minPort d z
  have hgc' := hgc.trans (mcOf_congr hzg)
  rw [ptOf_congr hzg, mcOf_congr hzg, ← hgc']
  have e1 := mFT_eq (h.level d) (h.w₀_mem d) h.h₀ h.h₁ h.hL₀ h.hR h.hc hg h.hinj h.hcW h.hW
    (h.portTab (d := d) (g₀ := g₀)) (Same.symm hzg)
  have e2 := pUT_eq (h.level d) (h.w₀_mem d) h.h₀ h.h₁ h.hL₀ h.hR h.hc hg h.hinj h.hcW h.hW
    (h.portTab (d := d) (g₀ := g₀)) (Same.symm hzg)
  have e3 := cycFT_eq (h.level d) (h.w₀_mem d) h.h₀ h.h₁ h.hL₀ h.hR h.hc hg h.hinj h.hcW h.hW
    (h.portTab (d := d) (g₀ := g₀))
  refine ⟨?_, ?_, ?_⟩
  · rw [show L.view z = L.t.viewOf L.code L.w₀ z from rfl, e1]
    exact h.mass_le_W _ _ _ _
  · rw [show L.view z = L.t.viewOf L.code L.w₀ z from rfl, e2]
    exact h.pos_le_W _ _ _
  · rw [e3]
    classical
    unfold RotSystem.RootedTree.npOf
    exact (Finset.card_filter_le _ _).trans (h.card_le_W _)

theorem yCand_lt {d a : ℕ} {z : D × Bool} (hc : L.yCand d z = some a) : a < (L.W + 2) * (L.W + 2) := by
  obtain ⟨h1, -, h3⟩ := h.mFT_view d z
  have hz := h.hcW z
  unfold yCand candY at hc
  split_ifs at hc
  obtain rfl := Option.some.inj hc
  have h2 : massFromT L.W (L.ptOf d z) (L.mcOf d z) (L.raOf d z 2 - 1) (L.raOf d z 1 - 1) (L.view z) ≤ L.W := by
    unfold massFromT
    split_ifs <;> omega
  have h4 := Nat.mul_le_mul_right L.W h2
  have h5 : (L.view z).1 = L.code z := rfl
  rw [h5]
  nlinarith

theorem raFields_lt {d κ a : ℕ} {z : D × Bool} (hm : (κ, a) ∈ L.raFields d z) :
    κ < 4 ∧ (a < (L.W + 2) * (L.W + 2) ∨ a = L.fid z) := by
  obtain ⟨h1, h2, -⟩ := h.mFT_view d z
  have h0 := h.pos_le_W (L.t.tau L.w₀) L.w₀ z
  simp only [raFields, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨by norm_num, Or.inl (by nlinarith)⟩
  · exact ⟨by norm_num, Or.inl (by nlinarith)⟩
  · exact ⟨by norm_num, Or.inl (by nlinarith)⟩
  · exact ⟨by norm_num, Or.inr rfl⟩

/-- **The diameter of a bag, in terms of the darts of the bag.** -/
theorem span {hh H d : ℕ} (hdep : ∀ v, L.t.dep v ≤ hh) (hd : d ≤ H) {z z' : D × Bool}
    (hn : L.nm d z = L.nm d z') :
    ReachLE (fun a c => ∃ y, L.nm d y = L.nm d z ∧ L.t.vertM y = a ∧ L.t.vertM (R.double.rev y) = c)
      ((2 * H + 2) * (2 * (hh + (1 + H * (2 + 4 * hh))) + 1)) (L.t.vertM z) (L.t.vertM z') := by
  have hs := h.nm_eq_iff.1 hn
  have hJ : (R.portsOf (L.Γs d) z).card ≤ 1 + H * (2 + 4 * hh) := by
    have h1 := h.decomp.card_ports hdep d z
    have h2 : d * (2 + 4 * hh) ≤ H * (2 + 4 * hh) := Nat.mul_le_mul_right _ hd
    omega
  have hG : (R.gapsOf (L.Γs d) z).card ≤ 2 * H + 1 := by
    have h1 := h.decomp.card_gaps d z
    omega
  have hdiam := bag_diam (h.level d) h.hR h.hc hdep hJ hG (u := z) ⟨z, connect_refl z, rfl⟩ ⟨z', hs, rfl⟩
  refine ReachLE.mono_adj ?_ hdiam
  rintro a' b' ⟨w, hw, rfl, rfl⟩
  exact ⟨w, (nm_congr hw).symm, rfl, rfl⟩

end OK

end LevelData

end SsspFlow.Congest
