import SsspFlow.NetLevels
import SsspFlow.EdgeBound

/-!
# The tables of the value calls

One call per bag gathers the records of the corners of the bag in a table. A record holds the name of the cycle of
the corner, the name of its sector, its position on the tour through all darts, a flag for the corners of the next
level, and its label. The readers `deltaT`, `dataT`, `labPT`, `bagT` are functions of the table alone. Given a table
with the records of a set of corners (`VT`), they agree with the values and labels on these corners.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal

namespace SsspFlow

open FourColor RotSystem RotSystem.RootedTree

/-! ### Records -/

/-- The field `j` of a record. -/
def fieldVal (cy sec ps fl : ℕ) (lab : List ℕ) : ℕ → ℕ
  | 0 => cy
  | 1 => sec
  | 2 => ps
  | 3 => fl
  | 4 => lab.length
  | j + 5 => lab.getD j 0

/-- The pairs of a record of the corner with code `c`. -/
def fieldItems (c cy sec ps fl : ℕ) (lab : List ℕ) : List (ℕ × ℕ) :=
  (List.range (5 + lab.length)).map fun j => (Nat.pair c j, fieldVal cy sec ps fl lab j)

theorem mem_fieldItems {c cy sec ps fl κ a : ℕ} {lab : List ℕ} :
    (κ, a) ∈ fieldItems c cy sec ps fl lab ↔
      ∃ j, j < 5 + lab.length ∧ κ = Nat.pair c j ∧ a = fieldVal cy sec ps fl lab j := by
  unfold fieldItems
  rw [List.mem_map]
  simp only [List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨j, hj, h1, h2⟩
    exact ⟨j, hj, h1.symm, h2.symm⟩
  · rintro ⟨j, hj, h1, h2⟩
    exact ⟨j, hj, h1.symm, h2.symm⟩

/-! ### Readers -/

/-- The label of a corner in a table. -/
def labT (tab : ℕ → ℕ) (c : ℕ) : List ℕ :=
  (List.range (fldT tab 4 c)).map fun j => fldT tab (j + 5) c

/-- The value between two corners in a table: zero on the diagonal, `⊤` between cycles, and within a cycle `dec` of
the labels. -/
noncomputable def deltaT (dec : List ℕ → List ℕ → ℝ≥0∞) (tab : ℕ → ℕ) (c c' : ℕ) : ℝ≥0∞ :=
  if c = c' then 0 else if fldT tab 0 c = fldT tab 0 c' then dec (labT tab c) (labT tab c') else ⊤

/-- A step between two corners in a table: zero within a sector. -/
noncomputable def stepT (dec : List ℕ → List ℕ → ℝ≥0∞) (tab : ℕ → ℕ) (c c' : ℕ) : ℝ≥0∞ :=
  if fldT tab 1 c = fldT tab 1 c' then 0 else deltaT dec tab c c'

/-- The least total value of a walk of steps between corners in a table. -/
noncomputable def dataT (W : ℕ) (dec : List ℕ → List ℕ → ℝ≥0∞) (tab : ℕ → ℕ) : ℕ → ℕ → ℝ≥0∞ :=
  hubDist (portsT W tab) (stepT dec tab)

open Classical in
/-- The list of the elements of `S` in the order of `key`, if there is one. -/
noncomputable def sortedBy (key : ℕ → ℕ) (S : Finset ℕ) : List ℕ :=
  if h : ∃ l : List ℕ, l.Nodup ∧ (∀ c, c ∈ l ↔ c ∈ S) ∧ l.Pairwise (fun a b => key a ≤ key b) then
    h.choose
  else []

theorem sortedBy_eq {key : ℕ → ℕ} {S : Finset ℕ} {l : List ℕ} (hn : l.Nodup) (hm : ∀ c, c ∈ l ↔ c ∈ S)
    (hp : l.Pairwise (fun a b => key a ≤ key b)) (hk : ∀ a ∈ S, ∀ b ∈ S, key a = key b → a = b) :
    sortedBy key S = l := by
  have h : ∃ l : List ℕ, l.Nodup ∧ (∀ c, c ∈ l ↔ c ∈ S) ∧ l.Pairwise (fun a b => key a ≤ key b) :=
    ⟨l, hn, hm, hp⟩
  unfold sortedBy
  rw [dite_eq_left h]
  obtain ⟨hn', hm', hp'⟩ := h.choose_spec
  refine List.Perm.eq_of_pairwise (le := fun a b => key a ≤ key b) ?_ hp' hp
    ((List.perm_ext_iff_of_nodup hn' hn).2 fun c => (hm' c).trans (hm c).symm)
  intro a b ha hb h1 h2
  exact hk a ((hm' a).1 ha) b ((hm b).1 hb) (le_antisymm h1 h2)

/-- The flagged corners in a table, in the order of the tour from the corner with code `mc`. -/
noncomputable def cycT (W : ℕ) (tab : ℕ → ℕ) (mc : ℕ) : List ℕ :=
  sortedBy (fun c => keyMod W (fldT tab 2 mc) (fldT tab 2 c))
    ((portsT W tab).filter fun c => fldT tab 3 c = 1)

/-- The label of a flagged corner, from a table. -/
noncomputable def labPT (bag : ∀ k, (Fin k → Fin k → ℝ≥0∞) → Fin k → List ℕ) (W : ℕ)
    (dec : List ℕ → List ℕ → ℝ≥0∞) (tab : ℕ → ℕ) (mc c : ℕ) : List ℕ :=
  labOn bag (dataT W dec tab) (cycT W tab mc) c

section Hubs

variable {V : Type*} [DecidableEq V] (vx : ℕ → V) (W : ℕ) (dec : List ℕ → List ℕ → ℝ≥0∞) (tab : ℕ → ℕ)

/-- The hubs in a table. -/
noncomputable def hubsT : Finset V := (portsT W tab).image vx

/-- A step between hubs in a table: the least value between their corners. -/
noncomputable def hstepT (a b : V) : ℝ≥0∞ :=
  ⨅ (c : ℕ) (c' : ℕ) (_ : c ∈ portsT W tab ∧ c' ∈ portsT W tab ∧ vx c = a ∧ vx c' = b), deltaT dec tab c c'

/-- The least total value of a walk of steps between hubs in a table. -/
noncomputable def bagT : V → V → ℝ≥0∞ := hubDist (hubsT vx W tab) (hstepT vx W dec tab)

end Hubs

/-! ### Lists along a bijection -/

/-- A family of functions on `Fin k` does not see how the length is written. -/
theorem bag_cast {α : Type*} (bag : ∀ k, (Fin k → Fin k → ℝ≥0∞) → Fin k → α) {k k' : ℕ} (h : k = k')
    {m : Fin k → Fin k → ℝ≥0∞} {m' : Fin k' → Fin k' → ℝ≥0∞} (hm : ∀ i j, m' (Fin.cast h i) (Fin.cast h j) = m i j)
    (a : Fin k) : bag k' m' (Fin.cast h a) = bag k m a := by
  subst h
  have : m' = m := by
    funext i j
    exact hm i j
  rw [this]
  rfl

section Map

variable {D : Type*} [DecidableEq D] {code : D → ℕ}

/-- Labels along an injective code. -/
theorem labOn_map (bag : ∀ k, (Fin k → Fin k → ℝ≥0∞) → Fin k → List ℕ) {w : D → D → ℝ≥0∞}
    {w' : ℕ → ℕ → ℝ≥0∞} {c : List D} (hc : c.Nodup) (hinj : Function.Injective code)
    (hw : ∀ a ∈ c, ∀ b ∈ c, w' (code a) (code b) = w a b) {x : D} (hx : x ∈ c) :
    labOn bag w' (c.map code) (code x) = labOn bag w c x := by
  obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hx
  have hl : c.length = (c.map code).length := (List.length_map code).symm
  have hn : (c.map code).Nodup := hc.map hinj
  have h1 : code c[a] = (c.map code)[(Fin.cast hl ⟨a, ha⟩ : Fin (c.map code).length)] := by
    simp
  rw [h1, labOn_getElem bag w' hn (Fin.cast hl ⟨a, ha⟩)]
  have h2 := labOn_getElem bag w hc ⟨a, ha⟩
  have h3 : c[a] = c[(⟨a, ha⟩ : Fin c.length)] := rfl
  rw [h3, h2]
  refine bag_cast bag hl (fun i j => ?_) _
  simp only [Fin.val_cast, List.getElem_map, Fin.getElem_fin]
  exact hw _ (List.getElem_mem _) _ (List.getElem_mem _)

/-- The equivalence between a set and its image under an injective code. -/
noncomputable def imageEquiv (hinj : Function.Injective code) (P : Finset D) : ↥(P.image code) ≃ ↥P :=
  (Equiv.ofBijective (fun p : P => (⟨code p, Finset.mem_image_of_mem _ p.2⟩ : ↥(P.image code)))
    ⟨fun _ _ h => Subtype.ext (hinj (congrArg Subtype.val h)), fun ⟨c, hc⟩ => by
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hc
      exact ⟨⟨p, hp⟩, rfl⟩⟩).symm

theorem corr_imageEquiv (hinj : Function.Injective code) {P : Finset D} {p : D} (hp : p ∈ P) :
    Corr (imageEquiv hinj P) (code p) p := by
  refine ⟨Finset.mem_image_of_mem _ hp, ?_⟩
  have h1 : (⟨code p, Finset.mem_image_of_mem _ hp⟩ : ↥(P.image code)) =
      (Equiv.ofBijective (fun p : P => (⟨code p, Finset.mem_image_of_mem _ p.2⟩ : ↥(P.image code)))
        ⟨fun _ _ h => Subtype.ext (hinj (congrArg Subtype.val h)), fun ⟨c, hc⟩ => by
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hc
          exact ⟨⟨p, hp⟩, rfl⟩⟩) ⟨p, hp⟩ := rfl
  rw [h1]
  unfold imageEquiv
  rw [Equiv.symm_apply_apply]

theorem eq_of_corr_image (hinj : Function.Injective code) {P : Finset D} {c : ℕ} {p : D}
    (h : Corr (imageEquiv hinj P) c p) : p ∈ P ∧ c = code p := by
  obtain ⟨hc, rfl⟩ := h
  refine ⟨(imageEquiv hinj P ⟨c, hc⟩).2, ?_⟩
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hc
  have := corr_imageEquiv hinj hq
  obtain ⟨_, h2⟩ := this
  rw [h2]

end Map

/-! ### A table with the records of a set of corners -/

section Table

variable {D : Type*} [DecidableEq D]

/-- The table holds the records of the corners in `P`, and nothing at other codes. -/
structure VT (W : ℕ) (tab : ℕ → ℕ) (P : Finset D) (code : D → ℕ) (cy sec ps fl : D → ℕ)
    (lab : D → List ℕ) : Prop where
  fld : ∀ p ∈ P, ∀ j, j < 5 + (lab p).length →
    tab (Nat.pair (code p) j) = fieldVal (cy p) (sec p) (ps p) (fl p) (lab p) j + 1
  none : ∀ c, (∀ p ∈ P, code p ≠ c) → tab (Nat.pair c 0) = 0

namespace VT

variable {W : ℕ} {tab : ℕ → ℕ} {P : Finset D} {code : D → ℕ} {cy sec ps fl : D → ℕ} {lab : D → List ℕ}
  (hT : VT W tab P code cy sec ps fl lab) (hinj : Function.Injective code) (hcW : ∀ z, code z < W)

include hT

theorem fld_lt {p : D} (hp : p ∈ P) {j : ℕ} (hj : j < 5 + (lab p).length) :
    fldT tab j (code p) = fieldVal (cy p) (sec p) (ps p) (fl p) (lab p) j := by
  unfold fldT
  rw [hT.fld p hp j hj, Nat.add_sub_cancel]

theorem fld0 {p : D} (hp : p ∈ P) : fldT tab 0 (code p) = cy p := hT.fld_lt hp (by omega)

theorem fld1 {p : D} (hp : p ∈ P) : fldT tab 1 (code p) = sec p := hT.fld_lt hp (by omega)

theorem fld2 {p : D} (hp : p ∈ P) : fldT tab 2 (code p) = ps p := hT.fld_lt hp (by omega)

theorem fld3 {p : D} (hp : p ∈ P) : fldT tab 3 (code p) = fl p := hT.fld_lt hp (by omega)

theorem lab_eq {p : D} (hp : p ∈ P) : labT tab (code p) = lab p := by
  have h4 : fldT tab 4 (code p) = (lab p).length := hT.fld_lt hp (by omega)
  unfold labT
  rw [h4]
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  have hj : j < (lab p).length := by simpa using h1
  simp only [List.getElem_map, List.getElem_range]
  rw [hT.fld_lt hp (by omega)]
  show (lab p).getD j 0 = _
  simp [List.getD_eq_getElem?_getD, hj]

include hcW in
theorem ports : portsT W tab = P.image code := by
  ext c
  simp only [portsT, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨-, h⟩
    by_contra hn
    exact h (hT.none c fun p hp e => hn ⟨p, hp, e⟩)
  · rintro ⟨p, hp, rfl⟩
    refine ⟨hcW p, ?_⟩
    rw [hT.fld p hp 0 (by omega)]
    omega

variable {dec : List ℕ → List ℕ → ℝ≥0∞} {δ : D → D → ℝ≥0∞} {ν : Equiv.Perm D}

include hinj in
/-- **The values from a table.** -/
theorem delta (hδ : ∀ p ∈ P, ∀ q ∈ P, δ p q =
      if p = q then 0 else if cy p = cy q then dec (lab p) (lab q) else ⊤) {p q : D} (hp : p ∈ P)
    (hq : q ∈ P) : deltaT dec tab (code p) (code q) = δ p q := by
  rw [hδ p hp q hq]
  unfold deltaT
  simp only [hinj.eq_iff, hT.fld0 hp, hT.fld0 hq, hT.lab_eq hp, hT.lab_eq hq]

include hinj in
/-- **The steps from a table.** -/
theorem step (hδ : ∀ p ∈ P, ∀ q ∈ P, δ p q =
      if p = q then 0 else if cy p = cy q then dec (lab p) (lab q) else ⊤)
    (hν : ∀ p ∈ P, ∀ q ∈ P, sec p = sec q ↔ fconnect ν p q) {p q : D} (hp : p ∈ P) (hq : q ∈ P) :
    stepT dec tab (code p) (code q) = stepOf ν δ p q := by
  classical
  unfold stepT stepOf
  rw [hT.fld1 hp, hT.fld1 hq, hT.delta hinj hδ hp hq]
  by_cases h : fconnect ν p q
  · rw [if_pos ((hν p hp q hq).2 h), if_pos h]
  · rw [if_neg fun e => h ((hν p hp q hq).1 e), if_neg h]

include hinj hcW in
/-- **The hub walks from a table.** -/
theorem data (hδ : ∀ p ∈ P, ∀ q ∈ P, δ p q =
      if p = q then 0 else if cy p = cy q then dec (lab p) (lab q) else ⊤)
    (hν : ∀ p ∈ P, ∀ q ∈ P, sec p = sec q ↔ fconnect ν p q) {p q : D} (hp : p ∈ P) (hq : q ∈ P) :
    dataT W dec tab (code p) (code q) = hubDist P (stepOf ν δ) p q := by
  unfold dataT
  rw [hT.ports hcW]
  refine hubDist_corr (β := imageEquiv hinj P) ?_ (corr_imageEquiv hinj hp) (corr_imageEquiv hinj hq)
  intro a' a b' b ha hb
  obtain ⟨ha1, rfl⟩ := eq_of_corr_image hinj ha
  obtain ⟨hb1, rfl⟩ := eq_of_corr_image hinj hb
  exact hT.step hinj hδ hν ha1 hb1

include hcW in
/-- **The list of a cycle from a table.** -/
theorem cyc {l : List D} {g₀ : D} (hg₀ : g₀ ∈ P) (hl : l.Nodup) (hinj : Function.Injective code)
    (hm : ∀ p, p ∈ l ↔ p ∈ P ∧ fl p = 1)
    (hs : l.Pairwise fun a b => keyMod W (ps g₀) (ps a) ≤ keyMod W (ps g₀) (ps b))
    (hk : ∀ a ∈ l, ∀ b ∈ l, keyMod W (ps g₀) (ps a) = keyMod W (ps g₀) (ps b) → a = b) :
    cycT W tab (code g₀) = l.map code := by
  have hmem : ∀ c, c ∈ l.map code ↔ c ∈ (portsT W tab).filter fun c => fldT tab 3 c = 1 := by
    intro c
    rw [hT.ports hcW]
    simp only [List.mem_map, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨h1, h2⟩ := (hm p).1 hp
      exact ⟨⟨p, h1, rfl⟩, by rw [hT.fld3 h1, h2]⟩
    · rintro ⟨⟨p, hp, rfl⟩, h2⟩
      rw [hT.fld3 hp] at h2
      exact ⟨p, (hm p).2 ⟨hp, h2⟩, rfl⟩
  have hkey : ∀ p ∈ P, fldT tab 2 (code p) = ps p := fun p hp => hT.fld2 hp
  refine sortedBy_eq (hl.map hinj) hmem ?_ ?_
  · rw [List.pairwise_map]
    refine hs.imp_of_mem fun {a b} ha hb h => ?_
    rw [hkey g₀ hg₀, hkey a ((hm a).1 ha).1, hkey b ((hm b).1 hb).1]
    exact h
  · intro a ha b hb he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ((hmem a).2 ha)
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ((hmem b).2 hb)
    rw [hkey g₀ hg₀, hkey p ((hm p).1 hp).1, hkey q ((hm q).1 hq).1] at he
    rw [hk p hp q hq he]

include hcW in
/-- **The label of a flagged corner from a table.** -/
theorem lab_port (bag : ∀ k, (Fin k → Fin k → ℝ≥0∞) → Fin k → List ℕ) {w : D → D → ℝ≥0∞} {l : List D}
    {g₀ : D} (hg₀ : g₀ ∈ P) (hl : l.Nodup) (hinj : Function.Injective code)
    (hm : ∀ p, p ∈ l ↔ p ∈ P ∧ fl p = 1)
    (hs : l.Pairwise fun a b => keyMod W (ps g₀) (ps a) ≤ keyMod W (ps g₀) (ps b))
    (hk : ∀ a ∈ l, ∀ b ∈ l, keyMod W (ps g₀) (ps a) = keyMod W (ps g₀) (ps b) → a = b)
    (hw : ∀ a ∈ l, ∀ b ∈ l, dataT W dec tab (code a) (code b) = w a b) {x : D} (hx : x ∈ l) :
    labPT bag W dec tab (code g₀) (code x) = labOn bag w l x := by
  unfold labPT
  rw [hT.cyc hcW hg₀ hl hinj hm hs hk]
  exact labOn_map bag hl hinj hw hx

variable {V : Type*} [DecidableEq V] {vx : ℕ → V} {vert : D → V}

include hcW in
theorem hubs (hv : ∀ p ∈ P, vx (code p) = vert p) : hubsT vx W tab = P.image vert := by
  unfold hubsT
  rw [hT.ports hcW]
  ext a
  simp only [Finset.mem_image, exists_exists_and_eq_and]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, (hv p hp).symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, hv p hp⟩

include hinj hcW in
theorem hstep (hv : ∀ p ∈ P, vx (code p) = vert p)
    (hδ : ∀ p ∈ P, ∀ q ∈ P, δ p q =
      if p = q then 0 else if cy p = cy q then dec (lab p) (lab q) else ⊤) (a b : V) :
    hstepT vx W dec tab a b =
      ⨅ (p : D) (q : D) (_ : p ∈ P ∧ q ∈ P ∧ vert p = a ∧ vert q = b), δ p q := by
  unfold hstepT
  rw [hT.ports hcW]
  apply le_antisymm
  · refine le_iInf fun p => le_iInf fun q => le_iInf fun h => ?_
    obtain ⟨hp, hq, h1, h2⟩ := h
    rw [← hT.delta hinj hδ hp hq]
    exact (iInf_le _ (code p)).trans ((iInf_le _ (code q)).trans (iInf_le _
      ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hq, by rw [hv p hp, h1], by rw [hv q hq, h2]⟩))
  · refine le_iInf fun c => le_iInf fun c' => le_iInf fun h => ?_
    obtain ⟨h1, h2, h3, h4⟩ := h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 h2
    rw [hT.delta hinj hδ hp hq]
    exact (iInf_le _ p).trans ((iInf_le _ q).trans (iInf_le _
      ⟨hp, hq, (hv p hp).symm.trans h3, (hv q hq).symm.trans h4⟩))

include hinj hcW in
/-- **The values between hubs from a table.** -/
theorem bag (hv : ∀ p ∈ P, vx (code p) = vert p)
    (hδ : ∀ p ∈ P, ∀ q ∈ P, δ p q =
      if p = q then 0 else if cy p = cy q then dec (lab p) (lab q) else ⊤) (a b : V) :
    bagT vx W dec tab a b = hubDist (P.image vert)
      (fun a b => ⨅ (p : D) (q : D) (_ : p ∈ P ∧ q ∈ P ∧ vert p = a ∧ vert q = b), δ p q) a b := by
  unfold bagT
  rw [hT.hubs hcW hv]
  congr 1
  funext a b
  exact hT.hstep hinj hcW hv hδ a b

end VT

end Table

/-! ### Hub walks that stay in a part -/

section Restrict

variable {D : Type*} [DecidableEq D] {P Γ : Finset D} {w : D → D → ℝ≥0∞}

/-- Hub walks do not leave a part of the hubs if no finite step leaves it. -/
theorem hubDist_restrict (hsub : P ⊆ Γ) (hw : ∀ a ∈ Γ, ∀ b ∈ Γ, w a b ≠ ⊤ → (a ∈ P ↔ b ∈ P)) {p q : D}
    (hp : p ∈ P) (hq : q ∈ P) : hubDist P w p q = hubDist Γ w p q := by
  classical
  apply le_antisymm
  · let f : D → D → ℝ≥0∞ := fun a b =>
      if a ∈ P ∧ b ∈ P then hubDist P w a b else if a ∉ P ∧ b ∉ P then 0 else ⊤
    have hf : f p q = hubDist P w p q := if_pos ⟨hp, hq⟩
    rw [← hf]
    refine le_hubDist (fun a => ?_) (fun a b c => ?_) (fun a ha b hb => ?_) p q
    · by_cases ha : a ∈ P
      · show (if a ∈ P ∧ a ∈ P then _ else _) = 0
        rw [if_pos ⟨ha, ha⟩]
        exact hubDist_self_le ha
      · show (if a ∈ P ∧ a ∈ P then _ else _) = 0
        rw [if_neg (fun h => ha h.1), if_pos ⟨ha, ha⟩]
    · by_cases ha : a ∈ P <;> by_cases hb : b ∈ P <;> by_cases hc : c ∈ P <;>
        first
          | (simp only [f, ha, hb, hc, and_self, if_true]; exact hubDist_triangle _ _ _ _)
          | (simp [f, ha, hb, hc]; done)
    · by_cases ha' : a ∈ P <;> by_cases hb' : b ∈ P
      · show (if a ∈ P ∧ b ∈ P then _ else _) ≤ _
        rw [if_pos ⟨ha', hb'⟩]
        exact hubDist_le_step ha' hb'
      · have h1 : w a b = ⊤ := by
          by_contra hne
          exact hb' ((hw a ha b hb hne).1 ha')
        rw [h1]
        exact le_top
      · have h1 : w a b = ⊤ := by
          by_contra hne
          exact ha' ((hw a ha b hb hne).2 hb')
        rw [h1]
        exact le_top
      · show (if a ∈ P ∧ b ∈ P then _ else if a ∉ P ∧ b ∉ P then _ else _) ≤ _
        rw [if_neg (fun h => ha' h.1), if_pos ⟨ha', hb'⟩]
        exact zero_le
  · simp only [hubDist, dist, le_iInf_iff]
    intro c hc
    exact iInf₂_le c fun z hz => hsub (hc z hz)

end Restrict

/-! ### Distances at all darts -/

namespace RotSystem

variable {D : Type*} [Fintype D] [DecidableEq D]

theorem split_univ_tail_inj (M : RotSystem D) {p q : D}
    (h : (M.split Finset.univ).tail p = (M.split Finset.univ).tail q) : p = q :=
  eq_of_tail_eq (M.nodeReturn_split Finset.univ) (Finset.mem_univ p) (Finset.mem_univ q) h

/-- At all darts, the distance from a dart to its reverse is the weight of the dart. -/
theorem lvlT_univ_rev {M : RotSystem D} {g : D → ℕ} {U : ℕ} (p : D) :
    lvlT M g U Finset.univ p (M.rev p) = (U : ℝ≥0∞) * (g p : ℝ≥0∞) := by
  unfold lvlT
  congr 1
  apply le_antisymm
  · have hw : (M.split Finset.univ).IsWalk ((M.split Finset.univ).tail p) [p]
        ((M.split Finset.univ).tail (M.rev p)) := ⟨rfl, rfl⟩
    have h1 := walkDist_le (fun z => (g z : ℝ≥0∞)) hw
    simpa using h1
  · refine le_iInf₂ fun l hl => ?_
    cases l with
    | nil => exact absurd (M.split_univ_tail_inj hl).symm (M.rev_ne p)
    | cons z l =>
      obtain ⟨h1, -⟩ := hl
      obtain rfl := M.split_univ_tail_inj h1
      simp only [List.map_cons, List.sum_cons]
      exact le_self_add

namespace RootedTree

variable {R : RotSystem D} {V : Type*} [Fintype V] [DecidableEq V] {t : R.RootedTree V}
  {w₀ : D × Bool} {Γ : Finset (D × Bool)}

/-- Along a cycle of `ψ`, the positions from the start increase. -/
theorem orbit_pos_lt (hL : t.IsLevel Γ) (hw : w₀ ∈ Γ) (h₀ : t.vertM w₀ = t.root) (h₁ : w₀.2 = true)
    (hL₀ : t.IsLevel {w₀}) (hR : R.Planar) (hc : R.Connected) {g₀ : D × Bool} (hg₀ : g₀ ∈ Γ) :
    ∀ k, k < Function.minimalPeriod (R.double.psi Γ) g₀ → ∀ j, j < k →
      pos (t.tau w₀) g₀ ((⇑(R.double.psi Γ))^[j] g₀) < pos (t.tau w₀) g₀ ((⇑(R.double.psi Γ))^[k] g₀) := by
  intro k
  induction k with
  | zero =>
    intro _ j hj
    omega
  | succ k ih =>
    intro hk j hj
    have hgk : (⇑(R.double.psi Γ))^[k] g₀ ∈ R.portsOf Γ g₀ :=
      mem_portsOf.2 ⟨mem_of_fconnect_psi hg₀ (fconnect_iterate _ _ _),
        R.double.gcomp_split_of_fconnect_psi (fconnect_iterate _ _ _)⟩
    have h0P : g₀ ∈ R.portsOf Γ g₀ := mem_portsOf.2 ⟨hg₀, connect_refl _⟩
    have hne : R.double.psi Γ ((⇑(R.double.psi Γ))^[k] g₀) ≠ g₀ := by
      intro e
      have e1 : (⇑(R.double.psi Γ))^[k + 1] g₀ = g₀ := by
        rw [Function.iterate_succ_apply']
        exact e
      have := Function.IsPeriodicPt.minimalPeriod_le (Nat.succ_pos k) e1
      omega
    have hstep := key_step (fconnect_tau h₀ h₁) (ports_min hL hw h₀ h₁ hL₀ hR hc _ hgk) h0P
      (fun e => ports_fix hL hR hc _ hgk _ h0P e) hne
    rw [Function.iterate_succ_apply']
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hlt | rfl
    · exact (ih (by omega) j hlt).trans hstep
    · exact hstep

end RootedTree

end RotSystem

end SsspFlow

/-! ### The values along the levels -/

namespace SsspFlow.Congest

open Cslib.Congest Cslib.Congest.Algorithm FourColor RotSystem RotSystem.RootedTree
open scoped ENNReal

/-- The fixed numbers of the value calls. -/
structure ValP where
  H : ℕ
  U : ℕ
  s : ℕ
  Lb : ℕ
  Wb : ℕ
  query : List ℕ → List ℕ → ℕ∞

namespace ValP

variable (P : ValP)

/-- The labels of a bag. -/
noncomputable def bagF : ∀ k, (Fin k → Fin k → ℝ≥0∞) → Fin k → List ℕ :=
  fun k w => (bagData P.query P.U P.s P.Lb P.Wb k w).1

/-- The value from two labels of step `i`. At step `0`, the label of a dart is its weight. -/
noncomputable def dec : ℕ → List ℕ → List ℕ → ℝ≥0∞
  | 0, a, _ => (P.U : ℝ≥0∞) * ((a.headD 0 : ℕ) : ℝ≥0∞)
  | _ + 1, a, b => (decode P.s (P.query a b) : ℝ≥0∞)

end ValP

variable {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] {R : RotSystem D}

namespace LevelData

variable (L : LevelData V R) (P : ValP) (g : D × Bool → ℕ) (sec : ℕ → D × Bool → ℕ)

/-- The levels from the top. -/
noncomputable def Γt (i : ℕ) : Finset (D × Bool) := topLevel L.Γs P.H i

/-- The values along the levels. -/
noncomputable def vals : ℕ → D × Bool → D × Bool → ℝ≥0∞ :=
  valSeq R.double g L.code P.U P.query P.s P.Lb P.Wb (L.Γt P)

/-- The sectors of the next level on the corners of a level. -/
noncomputable def nuOf (i : ℕ) : Equiv.Perm (D × Bool) :=
  (R.double.split (L.Γt P (i + 1))).nodeReturn (L.Γt P i)

/-- The matrix for the bags of the next level. -/
noncomputable def wOf (i : ℕ) : D × Bool → D × Bool → ℝ≥0∞ :=
  hubDist (L.Γt P i) (stepOf (L.nuOf P i) (L.vals P g i))

/-- The labels along the levels. -/
noncomputable def labelOf : ℕ → D × Bool → List ℕ
  | 0, z => [g z]
  | i + 1, z => labOn P.bagF (L.wOf P g i) (cycOf (R.double.psi (L.Γt P (i + 1))) L.code z) z

/-- The name of the cycle of a corner at a level. -/
noncomputable def cyId (i : ℕ) (z : D × Bool) : ℕ :=
  if i = 0 then Nat.pair 0 (min (L.code z) (L.code (R.double.rev z))) else L.nm (P.H + 1 - i) z

/-- The flag of a corner of the next level. -/
noncomputable def flagOf (i : ℕ) (z : D × Bool) : ℕ := if z ∈ L.Γt P (i + 1) then 1 else 0

/-- The pairs of a dart in a value call. -/
noncomputable def vItems (i : ℕ) (z : D × Bool) : List (ℕ × ℕ) :=
  if z ∈ L.Γt P i then
    fieldItems (L.code z) (L.cyId P i z) (sec i z) (pos (L.t.tau L.w₀) L.w₀ z) (L.flagOf P i z)
      (L.labelOf P g i z)
  else []

/-- The table of a value call for the bag of a dart. -/
noncomputable def vT (i : ℕ) (z : D × Bool) (κ : ℕ) : ℕ :=
  tabD (L.nm (P.H - i)) (L.vItems P g sec i) (L.nm (P.H - i) z) κ

/-- The corners of a level in the bag of a dart at the depth of the call. -/
noncomputable def cornersIn (i : ℕ) (z : D × Bool) : Finset (D × Bool) :=
  (L.Γt P i).filter fun p => L.nm (P.H - i) p = L.nm (P.H - i) z

variable {L P g sec}

theorem Γt_succ (i : ℕ) : L.Γt P (i + 1) = L.Γs (P.H - i) := topLevel_succ _ _ _

theorem Γt_zero : L.Γt P 0 = Finset.univ := rfl

theorem mem_vItems {i : ℕ} {z : D × Bool} {κ a : ℕ} :
    (κ, a) ∈ L.vItems P g sec i z ↔ z ∈ L.Γt P i ∧ ∃ j, j < 5 + (L.labelOf P g i z).length ∧
      κ = Nat.pair (L.code z) j ∧ a = fieldVal (L.cyId P i z) (sec i z) (pos (L.t.tau L.w₀) L.w₀ z)
        (L.flagOf P i z) (L.labelOf P g i z) j := by
  unfold vItems
  by_cases hz : z ∈ L.Γt P i
  · rw [if_pos hz, mem_fieldItems]
    simp [hz]
  · rw [if_neg hz]
    simp [hz]

namespace OK

variable (h : L.OK)

include h

theorem Γt_level (i : ℕ) : L.t.IsLevel (L.Γt P i) := h.decomp.topLevel_level i

theorem Γt_sub (i : ℕ) : L.Γt P (i + 1) ⊆ L.Γt P i := h.decomp.topLevel_sub i

/-- **The table of a value call holds the records of the corners of the bag.** -/
theorem vT_ok (i : ℕ) (z₀ : D × Bool) :
    VT L.W (L.vT P g sec i z₀) (L.cornersIn P i z₀) L.code (L.cyId P i) (sec i)
      (pos (L.t.tau L.w₀) L.w₀) (L.flagOf P i) (L.labelOf P g i) where
  fld p hp j hj := by
    obtain ⟨hpΓ, hn⟩ := Finset.mem_filter.1 hp
    refine tabD_of_unique ⟨p, hn, mem_vItems.2 ⟨hpΓ, j, hj, rfl, rfl⟩⟩ ?_
    intro z a hz hm
    obtain ⟨hzΓ, j', hj', he, rfl⟩ := mem_vItems.1 hm
    obtain ⟨e1, rfl⟩ := Nat.pair_eq_pair.1 he
    obtain rfl := h.hinj e1
    rfl
  none c hc := tabD_none fun z a hz hm => by
    obtain ⟨hzΓ, j, _, he, _⟩ := mem_vItems.1 hm
    exact hc z (Finset.mem_filter.2 ⟨hzΓ, hz⟩) (Nat.pair_eq_pair.1 he).1.symm

/-- The name of a cycle tells the cycle. -/
theorem cyId_iff {i : ℕ} {p q : D × Bool} (hp : p ∈ L.Γt P i) (hq : q ∈ L.Γt P i) :
    L.cyId P i p = L.cyId P i q ↔ fconnect (R.double.psi (L.Γt P i)) p q := by
  cases i with
  | zero =>
    have hc : ∀ z, L.cyId P 0 z = Nat.pair 0 (min (L.code z) (L.code (R.double.rev z))) :=
      fun z => if_pos rfl
    rw [hc, hc]
    constructor
    · intro e
      have e' := (Nat.pair_eq_pair.1 e).2
      have hq' : q = p ∨ q = R.double.rev p := by
        rcases min_choice (L.code p) (L.code (R.double.rev p)) with h1 | h1 <;>
          rcases min_choice (L.code q) (L.code (R.double.rev q)) with h2 | h2 <;>
            rw [h1, h2] at e'
        · exact Or.inl (h.hinj e').symm
        · right
          have := h.hinj e'
          rw [this, R.double.rev_rev]
        · exact Or.inr (h.hinj e').symm
        · exact Or.inl (R.double.rev_injective (h.hinj e')).symm
      have hψ : ∀ z, R.double.psi (L.Γt P 0) z = R.double.rev z := fun z => R.double.psi_univ_apply z
      rcases hq' with rfl | rfl
      · exact connect_refl _
      · have := fconnect1 (R.double.psi (L.Γt P 0)) p
        rwa [hψ] at this
    · intro hf
      rcases R.double.fconnect_psi_univ hf with rfl | rfl
      · rfl
      · rw [R.double.rev_rev, min_comm]
  | succ i =>
    have e : P.H + 1 - (i + 1) = P.H - i := by omega
    unfold cyId
    rw [if_neg (Nat.succ_ne_zero i), if_neg (Nat.succ_ne_zero i), e, h.nm_eq_iff,
      ← Γt_succ (L := L) (P := P) i]
    constructor
    · intro hs
      exact fconnect_psi_of_same (h.Γt_level (i + 1)) h.hR h.hc hp hq hs
    · intro hf
      exact R.double.gcomp_split_of_fconnect_psi hf

/-- **The values from the labels.** -/
theorem vals_eq (hU : 1 ≤ P.U) (i : ℕ) {p q : D × Bool} (hp : p ∈ L.Γt P i) (hq : q ∈ L.Γt P i) :
    L.vals P g i p q = if p = q then 0 else
      if L.cyId P i p = L.cyId P i q then P.dec i (L.labelOf P g i p) (L.labelOf P g i q) else ⊤ := by
  classical
  rw [ite_congr rfl (fun _ => rfl) fun _ => if_congr (h.cyId_iff hp hq) rfl rfl]
  cases i with
  | zero =>
    by_cases hpq : p = q
    · subst hpq
      rw [if_pos rfl]
      exact lvlT_self _
    rw [if_neg hpq]
    by_cases hf : fconnect (R.double.psi (L.Γt P 0)) p q
    · rw [if_pos hf]
      rcases R.double.fconnect_psi_univ hf with rfl | rfl
      · exact absurd rfl hpq
      · exact lvlT_univ_rev p
    · rw [if_neg hf]
      exact lvlT_top (R.double_planar h.hR h.hc) (R.double_connected h.hc) (h.Γt_level 0).nonempty
        (h.Γt_level 0).skel hU hp hq hf
  | succ i =>
    show levelVal P.query P.U P.s P.Lb P.Wb (R.double.psi (L.Γt P (i + 1))) L.code (L.wOf P g i) p q = _
    unfold levelVal deltaStep
    by_cases hpq : p = q
    · rw [if_pos hpq, if_pos hpq]
    rw [if_neg hpq, if_neg hpq]
    by_cases hf : fconnect (R.double.psi (L.Γt P (i + 1))) p q
    · rw [if_pos hf, if_pos hf]
      show _ = (decode P.s (P.query
        (labOn P.bagF (L.wOf P g i) (cycOf (R.double.psi (L.Γt P (i + 1))) L.code p) p)
        (labOn P.bagF (L.wOf P g i) (cycOf (R.double.psi (L.Γt P (i + 1))) L.code q) q)) : ℝ≥0∞)
      rw [← cycOf_congr _ h.hinj hf]
      rfl
    · rw [if_neg hf, if_neg hf]

omit h in
/-- Corners on one vertex of the split share a sector. -/
theorem fconnect_nu_iff {i : ℕ} {p q : D × Bool} (hp : p ∈ L.Γt P i) (hq : q ∈ L.Γt P i) :
    fconnect (L.nuOf P i) p q ↔
      (R.double.split (L.Γt P (i + 1))).tail p = (R.double.split (L.Γt P (i + 1))).tail q := by
  rw [RotSystem.tail_eq_iff]
  exact fconnect_firstReturn_iff _ hp hq

/-- A finite step stays in a bag of the depth of the call. -/
theorem nm_of_step (hU : 1 ≤ P.U) {i : ℕ} {a b : D × Bool} (ha : a ∈ L.Γt P i) (hb : b ∈ L.Γt P i)
    (hne : stepOf (L.nuOf P i) (L.vals P g i) a b ≠ ⊤) : L.nm (P.H - i) a = L.nm (P.H - i) b := by
  classical
  rw [h.nm_eq_iff, ← Γt_succ (L := L) (P := P) i]
  unfold stepOf at hne
  by_cases hf : fconnect (L.nuOf P i) a b
  · exact (R.double.split (L.Γt P (i + 1))).toHypermap.gcomp_of_cnode
      (((R.double.split (L.Γt P (i + 1))).tail_eq_iff _ _).1 ((fconnect_nu_iff ha hb).1 hf))
  · rw [if_neg hf, h.vals_eq hU i ha hb] at hne
    by_cases hab : a = b
    · subst hab
      exact connect_refl _
    · rw [if_neg hab] at hne
      by_cases hc : L.cyId P i a = L.cyId P i b
      · exact gcomp_split_mono (h.Γt_sub i)
          (R.double.gcomp_split_of_fconnect_psi ((h.cyId_iff ha hb).1 hc))
      · rw [if_neg hc] at hne
        exact absurd rfl hne

variable (hU : 1 ≤ P.U)
  (hsec : ∀ i p q, p ∈ L.Γt P i → q ∈ L.Γt P i → (sec i p = sec i q ↔
    (R.double.split (L.Γt P (i + 1))).tail p = (R.double.split (L.Γt P (i + 1))).tail q))

include hU hsec

/-- **The matrix of the next level from a table.** -/
theorem data_read (i : ℕ) (z₀ : D × Bool) {p q : D × Bool} (hp : p ∈ L.cornersIn P i z₀)
    (hq : q ∈ L.cornersIn P i z₀) :
    dataT L.W (P.dec i) (L.vT P g sec i z₀) (L.code p) (L.code q) = L.wOf P g i p q := by
  have hT := h.vT_ok (P := P) (g := g) (sec := sec) i z₀
  rw [hT.data (δ := L.vals P g i) (ν := L.nuOf P i) h.hinj h.hcW
    (fun p hp q hq => h.vals_eq hU i (Finset.mem_filter.1 hp).1 (Finset.mem_filter.1 hq).1)
    (fun p hp q hq => by
      rw [fconnect_nu_iff (Finset.mem_filter.1 hp).1 (Finset.mem_filter.1 hq).1]
      exact hsec i p q (Finset.mem_filter.1 hp).1 (Finset.mem_filter.1 hq).1) hp hq]
  refine hubDist_restrict (Finset.filter_subset _ _) (fun a ha b hb hne => ?_) hp hq
  have hn := h.nm_of_step hU ha hb hne
  simp only [cornersIn, Finset.mem_filter, ha, hb, true_and, hn]

/-- **The label of a corner of the next level from a table.** -/
theorem label_read {i : ℕ} {p : D × Bool} (hp : p ∈ L.Γt P (i + 1)) :
    L.labelOf P g (i + 1) p =
      labPT P.bagF L.W (P.dec i) (L.vT P g sec i p) (L.mcOf (P.H - i) p) (L.code p) := by
  obtain ⟨g₀, hg, hs, hgc⟩ := h.exists_minPort (P.H - i) p
  have e := Γt_succ (L := L) (P := P) i
  have hgt : g₀ ∈ L.Γt P (i + 1) := e ▸ hg
  have hlev : L.t.IsLevel (L.Γt P (i + 1)) := h.Γt_level (i + 1)
  have hw₀ : L.w₀ ∈ L.Γt P (i + 1) := by
    rw [e]
    exact h.w₀_mem _
  rw [← hgc]
  have hT := h.vT_ok (P := P) (g := g) (sec := sec) i p
  have hsame : R.Same (L.Γt P (i + 1)) p g₀ := by rw [e]; exact hs
  have hfp : fconnect (R.double.psi (L.Γt P (i + 1))) p g₀ :=
    fconnect_psi_of_same hlev h.hR h.hc hp hgt hsame
  have hnm : L.nm (P.H - i) g₀ = L.nm (P.H - i) p := (h.nm_eq_iff.2 hs).symm
  have hg₀P : g₀ ∈ L.cornersIn P i p := Finset.mem_filter.2 ⟨h.Γt_sub i hgt, hnm⟩
  have hst : SsspFlow.startOf (R.double.psi (L.Γt P (i + 1))) L.code g₀ = g₀ := by
    obtain ⟨h1, h2⟩ := startOf_spec (R.double.psi (L.Γt P (i + 1))) L.code g₀
    refine h.hinj (le_antisymm (h2 _ (connect_refl _)) ?_)
    have h3 : L.code g₀ = L.mcOf (P.H - i) g₀ := hgc.trans (mcOf_congr hs)
    rw [h3]
    refine Nat.sInf_le ⟨_, mem_portsOf.2 ⟨?_, ?_⟩, rfl⟩
    · rw [← e]
      exact mem_of_fconnect_psi hgt h1
    · rw [← e]
      exact R.double.gcomp_split_of_fconnect_psi h1
  have hcyc : cycOf (R.double.psi (L.Γt P (i + 1))) L.code g₀ =
      orbitList (R.double.psi (L.Γt P (i + 1))) g₀ := by
    unfold cycOf
    rw [hst]
  have hconn := fconnect_tau (t := L.t) h.h₀ h.h₁
  have hmono := orbit_pos_lt hlev hw₀ h.h₀ h.h₁ h.hL₀ h.hR h.hc hgt
  show labOn P.bagF (L.wOf P g i) (cycOf (R.double.psi (L.Γt P (i + 1))) L.code p) p = _
  rw [cycOf_congr _ h.hinj hfp]
  refine (hT.lab_port h.hcW P.bagF hg₀P (cycOf_nodup _ _) h.hinj ?_ ?_ ?_ ?_ ?_).symm
  · intro q
    rw [mem_cycOf]
    constructor
    · intro hf
      have hq' := mem_of_fconnect_psi hgt hf
      refine ⟨Finset.mem_filter.2 ⟨h.Γt_sub i hq', ?_⟩, if_pos hq'⟩
      have h1 : R.Same (L.Γs (P.H - i)) g₀ q := by
        rw [← e]
        exact R.double.gcomp_split_of_fconnect_psi hf
      rw [← h.nm_eq_iff.2 h1, hnm]
    · rintro ⟨h1, h2⟩
      obtain ⟨-, hn⟩ := Finset.mem_filter.1 h1
      have hq' : q ∈ L.Γt P (i + 1) := by
        by_contra hc
        have h3 : L.flagOf P i q = 0 := if_neg hc
        omega
      refine fconnect_psi_of_same hlev h.hR h.hc hgt hq' ?_
      rw [e]
      exact h.nm_eq_iff.1 (hnm.trans hn.symm)
  · rw [hcyc]
    unfold orbitList
    rw [List.pairwise_map]
    refine (List.pairwise_lt_range (n := Function.minimalPeriod _ g₀)).imp_of_mem ?_
    intro a b _ hb hab
    exact (pos_le_iff_key hconn h.hW L.w₀ g₀ _ _).1 (hmono b (List.mem_range.1 hb) a hab).le
  · intro a _ b _ he
    have h1 := (pos_le_iff_key hconn h.hW L.w₀ g₀ a b).2 he.le
    have h2 := (pos_le_iff_key hconn h.hW L.w₀ g₀ b a).2 he.ge
    exact pos_inj (hconn g₀ a) (hconn g₀ b) (le_antisymm h1 h2)
  · intro a ha b hb
    have hf1 := (mem_cycOf _).1 ha
    have hf2 := (mem_cycOf _).1 hb
    have hmem : ∀ q, fconnect (R.double.psi (L.Γt P (i + 1))) g₀ q → q ∈ L.cornersIn P i p := by
      intro q hf
      refine Finset.mem_filter.2 ⟨h.Γt_sub i (mem_of_fconnect_psi hgt hf), ?_⟩
      have h1 : R.Same (L.Γs (P.H - i)) g₀ q := by
        rw [← e]
        exact R.double.gcomp_split_of_fconnect_psi hf
      rw [← h.nm_eq_iff.2 h1, hnm]
    exact h.data_read hU hsec i p (hmem a hf1) (hmem b hf2)
  · exact (mem_cycOf _).2 (fconnect_sym (R.double.psi _).injective _ _ hfp)

omit hsec in
/-- **The values between the hubs of a bag from a table.** -/
theorem bagVal_read {i : ℕ} (hi : i ≤ P.H) (z : D × Bool) {vx : ℕ → V}
    (hv : ∀ p, vx (L.code p) = L.t.vertM p) (a b : V) :
    bagVal L.t L.code L.Γs P.H (L.vals P g) (L.nm (P.H - i) z) a b =
      bagT vx L.W (P.dec i) (L.vT P g sec i z) a b := by
  classical
  have hT := h.vT_ok (P := P) (g := g) (sec := sec) i z
  rw [hT.bag h.hinj h.hcW (fun p _ => hv p)
    (fun p hp q hq => h.vals_eq hU i (Finset.mem_filter.1 hp).1 (Finset.mem_filter.1 hq).1)]
  have e1 : (Nat.unpair (L.nm (P.H - i) z)).1 = P.H - i := bagName_fst _ _
  have e2 : P.H - (P.H - i) = i := by omega
  have hset : bagCorners (L.Γt P i) (bagDarts R L.code L.Γs P.H (L.nm (P.H - i) z)) =
      L.cornersIn P i z := by
    ext p
    rw [mem_bagCorners]
    simp only [cornersIn, Finset.mem_filter]
    refine and_congr_right fun _ => ?_
    show (_ ∧ _) ↔ _
    rw [e1]
    exact ⟨fun h1 => h1.2, fun h1 => ⟨by omega, h1⟩⟩
  unfold bagVal hubLevel
  rw [e1, e2]
  show hubDist (bagHubs L.t (L.Γt P i) (bagDarts R L.code L.Γs P.H (L.nm (P.H - i) z)))
    (bagStep L.t (L.Γt P i) (bagDarts R L.code L.Γs P.H (L.nm (P.H - i) z)) (L.vals P g i)) a b = _
  unfold bagHubs bagStep
  rw [hset]

end OK

/-- The hypotheses for the values along the levels. -/
structure VOK (L : LevelData V R) (P : ValP) (g : D × Bool → ℕ) (C Cl cl B Wt h : ℕ) : Prop where
  hC : Congest.RealizationBox C
  hq : LabelQuery Cl cl P.U P.query
  hU : 1 ≤ P.U
  hg : ∀ z, 1 ≤ g z
  hWt : ∀ z, g z ≤ Wt
  hs : 1 ≤ P.s
  hB : 1 ≤ B
  hks : C * (2 + P.H * (2 + 4 * h) + 1) ^ 6 ≤ P.s
  hBig : 2 * (P.U * Fintype.card (D × Bool) * Wt) ≤ B
  hcn : cU P.U ^ (2 * P.H + 1) ≤ 2
  hLb : P.Lb = bagLen Cl cl P.U P.s B
  hWb : P.Wb = bagWord cl P.s B
  hdep : ∀ v, L.t.dep v ≤ h

namespace OK

variable {C Cl cl B Wt h : ℕ} (hO : L.OK) (hV : VOK L P g C Cl cl B Wt h)

include hO hV

/-- **The values along the levels have the bounds of a metric.** -/
theorem vals_metric : ∀ i, i ≤ P.H → ∃ μ, LevelMetric R.double g L.code P.U P.s (L.Γt P i)
    (cU P.U ^ (2 * i)) μ (L.vals P g i) := by
  intro i hi
  unfold vals
  rw [hV.hLb, hV.hWb]
  refine levelMetric_seq hV.hC hV.hq (R.double_planar hO.hR hO.hc) (R.double_connected hO.hc) (L.Γt P)
    (fun i _ => hO.Γt_sub i) (fun i _ => (hO.Γt_level i).nonempty) (fun i _ => (hO.Γt_level i).skel)
    hO.hinj hV.hU hV.hg hV.hWt hV.hs hV.hB (fun i _ x _ => ?_) hV.hBig hV.hcn i hi
  refine le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 6)) hV.hks
  have := hO.decomp.cycOf_length_le (code := L.code) hV.hdep (H := P.H) i x
  exact Nat.succ_le_succ this

/-- **The labels of the corners of a level are short, with small words.** -/
theorem label_bounds {i : ℕ} (hi : i ≤ P.H) {z : D × Bool} (hz : z ∈ L.Γt P (i + 1)) :
    (L.labelOf P g (i + 1) z).length ≤ P.Lb ∧ ∀ w ∈ L.labelOf P g (i + 1) z, w < P.Wb := by
  obtain ⟨μ', h'⟩ := hO.vals_metric hV i hi
  have hc1 := one_le_cU hV.hU
  have h1 : 1 ≤ cU P.U ^ (2 * i) := one_le_pow₀ hc1
  have h2 : cU P.U * cU P.U ^ (2 * i) ≤ 2 := by
    refine le_trans ?_ hV.hcn
    rw [← pow_succ']
    exact pow_le_pow_right₀ hc1 (by omega)
  obtain ⟨-, hb⟩ := levelMetric_step (Γ := L.Γt P (i + 1)) hV.hC hV.hq (query := P.query)
    (s := P.s) (B := B) (R.double_planar hO.hR hO.hc) (R.double_connected hO.hc) (hO.Γt_sub i)
    (hO.Γt_level (i + 1)).nonempty (hO.Γt_level (i + 1)).skel (hO.Γt_level i).skel hO.hinj hV.hU hV.hg
    hV.hWt hV.hs hV.hB (fun x _ => by
      refine le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 6)) hV.hks
      have := hO.decomp.cycOf_length_le (code := L.code) hV.hdep (H := P.H) (i + 1) x
      exact Nat.succ_le_succ this) hV.hBig h1 h2 h'
  have hx := self_mem_cycOf (R.double.psi (L.Γt P (i + 1))) (code := L.code) z
  have e : L.labelOf P g (i + 1) z = (bagData P.query P.U P.s P.Lb P.Wb _
      (listMat (L.wOf P g i) (cycOf (R.double.psi (L.Γt P (i + 1))) L.code z))).1
        ⟨(cycOf (R.double.psi (L.Γt P (i + 1))) L.code z).idxOf z, List.idxOf_lt_length_iff.2 hx⟩ := by
    show labOn P.bagF _ _ z = _
    unfold labOn
    rw [dite_eq_left hx]
    rfl
  rw [e, hV.hLb, hV.hWb]
  exact hb z hz _

theorem label_len {i : ℕ} (hi : i ≤ P.H) {z : D × Bool} (hz : z ∈ L.Γt P i) :
    (L.labelOf P g i z).length ≤ P.Lb + 1 := by
  cases i with
  | zero =>
    show ([g z] : List ℕ).length ≤ _
    simp
  | succ i => exact (hO.label_bounds hV (by omega) hz).1.trans (by omega)

theorem label_word {i : ℕ} (hi : i ≤ P.H) {z : D × Bool} (hz : z ∈ L.Γt P i) {w : ℕ}
    (hw : w ∈ L.labelOf P g i z) : w < P.Wb + (Wt + 1) := by
  cases i with
  | zero =>
    obtain rfl : w = g z := List.mem_singleton.1 hw
    have := hV.hWt z
    omega
  | succ i =>
    have := (hO.label_bounds hV (by omega) hz).2 w hw
    omega

/-- **The corners of a bag at the depth of a call are few.** -/
theorem card_cornersIn {Jl : ℕ}
    (hleaf : ∀ z, (Finset.univ.filter fun p => L.nm P.H p = L.nm P.H z).card ≤ Jl) {i : ℕ} (hi : i ≤ P.H)
    (z : D × Bool) : (L.cornersIn P i z).card ≤ Jl + (1 + P.H * (2 + 4 * h)) := by
  classical
  cases i with
  | zero =>
    have := hleaf z
    refine (Finset.card_le_card (t := Finset.univ.filter fun p => L.nm P.H p = L.nm P.H z) ?_).trans
      (by omega)
    intro p hp
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hp).2⟩
  | succ i =>
    have e : P.H - i = (P.H - (i + 1)) + 1 := by omega
    have h1 := hO.decomp.card_filter_succ hV.hdep (P.H - (i + 1)) z
    rw [← e] at h1
    have h2 : (P.H - i) * (2 + 4 * h) ≤ P.H * (2 + 4 * h) := Nat.mul_le_mul_right _ (by omega)
    refine (Finset.card_le_card ?_).trans (h1.trans (by omega))
    intro p hp
    obtain ⟨h3, h4⟩ := Finset.mem_filter.1 hp
    rw [Γt_succ] at h3
    exact Finset.mem_filter.2 ⟨h3, hO.nm_eq_iff.1 h4.symm⟩

omit hV in
/-- The keys of a value call in a bag are few. -/
theorem exists_val_keys {i Lm J : ℕ} {z : D × Bool}
    (hLen : ∀ z, z ∈ L.Γt P i → (L.labelOf P g i z).length ≤ Lm) (hJ : (L.cornersIn P i z).card ≤ J) :
    ∃ K : Finset ℕ, K.card ≤ J * (5 + Lm) ∧
      ∀ z', L.nm (P.H - i) z' = L.nm (P.H - i) z → ∀ p ∈ L.vItems P g sec i z', p.1 ∈ K := by
  classical
  refine ⟨(L.cornersIn P i z).biUnion fun p => (Finset.range (5 + Lm)).image (Nat.pair (L.code p)), ?_, ?_⟩
  · refine (Finset.card_biUnion_le_card_mul _ _ (5 + Lm) fun p _ => ?_).trans
      (Nat.mul_le_mul_right _ hJ)
    exact Finset.card_image_le.trans (by simp)
  · rintro z' hn ⟨κ, a⟩ hm
    obtain ⟨hz', j, hj, rfl, -⟩ := mem_vItems.1 hm
    have := hLen z' hz'
    exact Finset.mem_biUnion.2 ⟨z', Finset.mem_filter.2 ⟨hz', hn⟩,
      Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by omega), rfl⟩⟩

/-- The numbers of a value call are small. -/
theorem vItems_lt {b i : ℕ} (hi : i ≤ P.H) (hHW : P.H ≤ L.W) (hb2 : (L.W + 6 + P.Lb) ^ 2 ≤ 2 ^ b)
    (hb3 : P.Wb + Wt + 1 ≤ 2 ^ b) (hsecb : ∀ i z, sec i z < 2 ^ b) {z : D × Bool} {p : ℕ × ℕ}
    (hm : p ∈ L.vItems P g sec i z) : p.1 < 2 ^ b ∧ p.2 < 2 ^ b := by
  obtain ⟨κ, a⟩ := p
  obtain ⟨hz, j, hj, rfl, rfl⟩ := mem_vItems.1 hm
  have hlen := hO.label_len hV hi hz
  have hW : L.W + 6 + P.Lb ≤ 2 ^ b := le_trans (Nat.le_self_pow (by norm_num) _) hb2
  have hsq : ∀ x, x < L.W + 6 + P.Lb → x * 1 < 2 ^ b := fun x hx => by omega
  refine ⟨?_, ?_⟩
  · refine (Nat.pair_lt_max_add_one_sq _ _).trans_le (le_trans (Nat.pow_le_pow_left ?_ 2) hb2)
    have := hO.hcW z
    have : max (L.code z) j ≤ L.W + 5 + P.Lb := max_le (by omega) (by omega)
    omega
  · have hsq2 : (L.W + 1) ^ 2 ≤ 2 ^ b := le_trans (Nat.pow_le_pow_left (by omega) 2) hb2
    rcases j with _ | _ | _ | _ | _ | j
    · show L.cyId P i z < 2 ^ b
      unfold cyId
      split_ifs with hi0
      · refine (Nat.pair_lt_max_add_one_sq _ _).trans_le (le_trans (Nat.pow_le_pow_left ?_ 2) hsq2)
        have h1 := hO.hcW z
        have h2 : min (L.code z) (L.code (R.double.rev z)) ≤ L.code z := min_le_left _ _
        have : max 0 (min (L.code z) (L.code (R.double.rev z))) ≤ L.W := max_le (by omega) (by omega)
        omega
      · exact (hO.nm_lt hHW (by omega) z).trans_le hsq2
    · exact hsecb i z
    · have := hO.pos_le_W (L.t.tau L.w₀) L.w₀ z
      show pos (L.t.tau L.w₀) L.w₀ z < 2 ^ b
      omega
    · show L.flagOf P i z < 2 ^ b
      have h1 : L.flagOf P i z ≤ 1 := by
        unfold flagOf
        split_ifs <;> omega
      omega
    · show (L.labelOf P g i z).length < 2 ^ b
      omega
    · have hj' : j < (L.labelOf P g i z).length := by omega
      show (L.labelOf P g i z).getD j 0 < 2 ^ b
      have h1 : (L.labelOf P g i z).getD j 0 = (L.labelOf P g i z)[j] := by
        simp [List.getD_eq_getElem?_getD, hj']
      rw [h1]
      have := hO.label_word hV hi hz (List.getElem_mem hj')
      omega

end OK

end LevelData

end SsspFlow.Congest
