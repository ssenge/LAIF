import SsspFlow.LevelTab

/-!
# The level phases at the nodes

A node reads the phases of a level from its memory. The readers (`candAL`, `isAL`, `candYL`, `isYL`, `railL`,
`corL`, `portItsL`) take numbers and the memory, and they do not depend on the network. Given the entries of the
memory, they agree with the tables of `LevelTab`. A run of the phases gives these entries at all depths
(`levels_of_run`), so a node knows its corners at all levels (`corL_eq`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SsspFlow.Congest

open Cslib.Congest Cslib.Congest.Algorithm FourColor RotSystem RotSystem.RootedTree

variable {n : ℕ}

/-- The code of the reverse of a dart at a node. -/
def cR (v : Fin n) (y : Fin n × Bool) : ℕ := codeRaw n y.1 v (!y.2)

/-- The phase of the flood of the names of a depth. -/
def phFlood (d : ℕ) : ℕ := 10 + 6 * d

/-- The phase of the table of the corners of a depth. -/
def phPorts (d : ℕ) : ℕ := 11 + 6 * d

/-- The phase of the least first dart of a depth. -/
def phSelA (d : ℕ) : ℕ := 12 + 6 * d

/-- The phase of the record of the first dart of a depth. -/
def phRecA (d : ℕ) : ℕ := 13 + 6 * d

/-- The phase of the least second dart of a depth. -/
def phSelY (d : ℕ) : ℕ := 14 + 6 * d

/-- The phase of the record of the second dart of a depth. -/
def phRecY (d : ℕ) : ℕ := 15 + 6 * d

section Readers

variable (W : ℕ) (r : Fin n) (rl : List (Fin n)) (v : Fin n) (m : Mem) (d : ℕ)
  (C : Finset (Fin n × Bool)) (y : Fin n × Bool)

/-- The least code of a corner of the bag of a dart, from the memory. -/
def minC : ℕ := m (phFlood d) (cL v y)

/-- The name of the bag of a dart, from the memory. -/
def nameL : ℕ := Nat.pair d (minC v m d y)

/-- The table of the corners of the bag of a dart, from the memory. -/
def tabPL (κ : ℕ) : ℕ := m (phPorts d) (Nat.pair (nameL v m d y) κ)

/-- The numbers of a dart, from the memory. -/
noncomputable def viewL : View :=
  (cL v y, numPL r rl v m y, numFL 0 3 5 r rl v m y, numFL 1 4 6 r rl v m y)

/-- The numbers of the reverse of a dart, from the memory. -/
def viewR : View := (cR v y, revR 9 m y, revR 7 m y, revR 8 m y)

/-- The dart is a mark of the level with corners `C` at the node. -/
def mkL : Prop := (v ≠ r ∧ y = (parR rl v m, true) ∧ C = ∅) ∨ (isC0L v m y ∧ y ∉ C)

/-- The dart is the first rail of a node without a corner. -/
def smL : Prop := v ≠ r ∧ y = (parR rl v m, false) ∧ C = ∅

/-- The value of a dart as the first dart of a cut, from the memory. -/
noncomputable def candAL : Option ℕ :=
  candA W (tabPL v m d y) (minC v m d y) (viewL r rl v m y) (viewR v m y) (mkL r rl v m C y)
    (smL r rl v m C y)

/-- The pairs of a dart in the call for the first dart. -/
noncomputable def selAIts : List (ℕ × ℕ) := (candAL W r rl v m d C y).toList.map fun a => (0, a)

/-- The answer of the call for the first dart. -/
def minAL : ℕ := m (phSelA d) (Nat.pair (nameL v m d y) 0)

/-- The dart is the first dart of the cut of its bag, from the memory. -/
def isAL : Prop := ∃ a, candAL W r rl v m d C y = some a ∧ minAL v m d y = a + 1

/-- The name of the face of a dart, from the memory. -/
def fidL : ℕ :=
  if y.2 then Nat.pair 0 (m 0 y.1)
  else Nat.pair 1 (min (codeRaw n v y.1 false) (codeRaw n y.1 v false))

open Classical in
/-- The pairs of a dart in the call for the record of the first dart. -/
noncomputable def recAIts : List (ℕ × ℕ) :=
  if isAL W r rl v m d C y then
    [(0, numPL r rl v m y), (1, mFT W (tabPL v m d y) (minC v m d y) (viewL r rl v m y)),
      (2, pUT W (tabPL v m d y) (minC v m d y) (viewL r rl v m y)), (3, fidL v m y)]
  else []

/-- The record of the first dart, from the memory. -/
def recAL (κ : ℕ) : ℕ := m (phRecA d) (Nat.pair (nameL v m d y) κ)

/-- The value of a dart as the second dart of a cut, from the memory. -/
noncomputable def candYL : Option ℕ :=
  candY W (tabPL v m d y) (minC v m d y) (recAL v m d y 0 ≠ 0) (recAL v m d y 2 - 1) (recAL v m d y 1 - 1)
    (recAL v m d y 3 - 1) (fidL v m y) (viewL r rl v m y)

/-- The pairs of a dart in the call for the second dart. -/
noncomputable def selYIts : List (ℕ × ℕ) := (candYL W r rl v m d y).toList.map fun a => (0, a)

/-- The answer of the call for the second dart. -/
def minYL : ℕ := m (phSelY d) (Nat.pair (nameL v m d y) 0)

/-- The dart is the second dart of the cut of its bag, from the memory. -/
def isYL : Prop := ∃ a, candYL W r rl v m d y = some a ∧ minYL v m d y = a + 1

open Classical in
/-- The pairs of a dart in the call for the record of the second dart. -/
noncomputable def recYIts : List (ℕ × ℕ) := if isYL W r rl v m d y then [(0, numPL r rl v m y)] else []

/-- The record of the second dart, from the memory. -/
def recYL : ℕ := m (phRecY d) (Nat.pair (nameL v m d y) 0)

/-- A dart of the cut of the bag lies in an interval of positions, from the memory. -/
def inIv (lo hi : ℕ) : Prop :=
  (recAL v m d y 0 ≠ 0 ∧ lo ≤ recAL v m d y 0 - 1 ∧ recAL v m d y 0 - 1 ≤ hi) ∨
    (recYL v m d y ≠ 0 ∧ lo ≤ recYL v m d y - 1 ∧ recYL v m d y - 1 ≤ hi)

/-- The dart is a rail on a walk up from a dart of the cut, from the memory. -/
def railL : Prop :=
  (v ≠ r ∧ y = (parR rl v m, false) ∧
      inIv v m d y (numPL r rl v m (parR rl v m, true)) (numPL r rl v m y)) ∨
    (isC0L v m y ∧ inIv v m d y (revR 9 m y) (revR 9 m (y.1, true)))

open Classical in
/-- The number `phiB` of a corner, from the memory. -/
noncomputable def phibL (φ : Fin n × Bool → ℕ) (ι : ℕ) : ℕ :=
  if v ≠ r ∧ (firstReturn (rotV rl) C)⁻¹ y = (parR rl v m, false) then
    φ (rotV rl ((firstReturn (rotV rl) C)⁻¹ y)) - ι
  else φ ((firstReturn (rotV rl) C)⁻¹ y)

open Classical in
/-- The number `arcV` of a corner, from the memory. -/
noncomputable def arcL (φ : Fin n × Bool → ℕ) (ι : ℕ) : ℕ :=
  if (rotV rl)⁻¹ y ∈ C then ι else φ ((rotV rl)⁻¹ y) - phibL r rl v m C y φ ι + ι

/-- The fields of a corner, from the memory. -/
noncomputable def portFieldL (j : ℕ) : ℕ :=
  match j with
  | 0 => numPL r rl v m y
  | 1 => arcL r rl v m C y (numFL 0 3 5 r rl v m) 0
  | 2 => arcL r rl v m C y (numFL 1 4 6 r rl v m) 1
  | 3 => phibL r rl v m C y (numFL 0 3 5 r rl v m) 0
  | _ => phibL r rl v m C y (numFL 1 4 6 r rl v m) 1

open Classical in
/-- The pairs of a dart in the call for the corners. -/
noncomputable def portItsL : List (ℕ × ℕ) :=
  if y ∈ C then (List.range 5).map fun j => (Nat.pair (cL v y) j, portFieldL r rl v m C y j) else []

end Readers

open Classical in
/-- The corners of a level at a node, from the memory. -/
noncomputable def corL (W : ℕ) (r : Fin n) (rl : List (Fin n)) (v : Fin n) (m : Mem) :
    ℕ → Finset (Fin n × Bool)
  | 0 => if v = r then {(rl.headD v, true)} else ∅
  | d + 1 => corL W r rl v m d ∪ (ownL rl).toFinset.filter fun y =>
      isAL W r rl v m d (corL W r rl v m d) y ∨ isYL W r rl v m d y ∨ railL r rl v m d y

section Entries

variable (N : Net (Fin n)) (L : LevelData (Fin n) N.toRot) (m : Fin n → Mem) (d : ℕ)

/-- The entries of the flood. -/
def EF : Prop := ∀ z : N.G.Dart × Bool, m z.1.fst (phFlood d) (N.codeN z) = L.mcOf d z

/-- The entries of the table of corners. -/
def EP : Prop := ∀ (z : N.G.Dart × Bool) (κ : ℕ),
  m z.1.fst (phPorts d) (Nat.pair (L.nm d z) κ) = L.ptOf d z κ

/-- The entries of the least first dart. -/
def EA : Prop := ∀ z : N.G.Dart × Bool, m z.1.fst (phSelA d) (Nat.pair (L.nm d z) 0) = L.aOf d z

/-- The entries of the record of the first dart. -/
def ER : Prop := ∀ (z : N.G.Dart × Bool) (κ : ℕ),
  m z.1.fst (phRecA d) (Nat.pair (L.nm d z) κ) = L.raOf d z κ

/-- The entries of the least second dart. -/
def EY : Prop := ∀ z : N.G.Dart × Bool, m z.1.fst (phSelY d) (Nat.pair (L.nm d z) 0) = L.yOf d z

/-- The entries of the record of the second dart. -/
def ES : Prop := ∀ z : N.G.Dart × Bool, m z.1.fst (phRecY d) (Nat.pair (L.nm d z) 0) = L.ryOf d z

/-- All entries of a depth. -/
structure EAll : Prop where
  f : EF N L m d
  p : EP N L m d
  a : EA N L m d
  ra : ER N L m d
  y : EY N L m d
  ry : ES N L m d

end Entries

section Read

variable {N : Net (Fin n)} {L : LevelData (Fin n) N.toRot} {m : Fin n → Mem} {d : ℕ}

theorem minC_eq (hF : EF N L m d) (z : N.G.Dart × Bool) :
    minC z.1.fst (m z.1.fst) d (N.locN z) = L.mcOf d z := hF z

theorem nameL_eq (hF : EF N L m d) (z : N.G.Dart × Bool) :
    nameL z.1.fst (m z.1.fst) d (N.locN z) = L.nm d z := congrArg (Nat.pair d) (hF z)

theorem tabPL_eq (hF : EF N L m d) (hP : EP N L m d) (z : N.G.Dart × Bool) :
    tabPL z.1.fst (m z.1.fst) d (N.locN z) = L.ptOf d z := by
  funext κ
  show m z.1.fst (phPorts d) (Nat.pair (nameL z.1.fst (m z.1.fst) d (N.locN z)) κ) = _
  rw [nameL_eq hF z]
  exact hP z κ

theorem minAL_eq (hF : EF N L m d) (hA : EA N L m d) (z : N.G.Dart × Bool) :
    minAL z.1.fst (m z.1.fst) d (N.locN z) = L.aOf d z := by
  show m z.1.fst (phSelA d) (Nat.pair (nameL z.1.fst (m z.1.fst) d (N.locN z)) 0) = _
  rw [nameL_eq hF z]
  exact hA z

theorem recAL_eq (hF : EF N L m d) (hR : ER N L m d) (z : N.G.Dart × Bool) :
    recAL z.1.fst (m z.1.fst) d (N.locN z) = L.raOf d z := by
  funext κ
  show m z.1.fst (phRecA d) (Nat.pair (nameL z.1.fst (m z.1.fst) d (N.locN z)) κ) = _
  rw [nameL_eq hF z]
  exact hR z κ

theorem minYL_eq (hF : EF N L m d) (hY : EY N L m d) (z : N.G.Dart × Bool) :
    minYL z.1.fst (m z.1.fst) d (N.locN z) = L.yOf d z := by
  show m z.1.fst (phSelY d) (Nat.pair (nameL z.1.fst (m z.1.fst) d (N.locN z)) 0) = _
  rw [nameL_eq hF z]
  exact hY z

theorem recYL_eq (hF : EF N L m d) (hS : ES N L m d) (z : N.G.Dart × Bool) :
    recYL z.1.fst (m z.1.fst) d (N.locN z) = L.ryOf d z := by
  show m z.1.fst (phRecY d) (Nat.pair (nameL z.1.fst (m z.1.fst) d (N.locN z)) 0) = _
  rw [nameL_eq hF z]
  exact hS z

theorem inIv_iff (hF : EF N L m d) (hR : ER N L m d) (hS : ES N L m d) (z : N.G.Dart × Bool) (lo hi : ℕ) :
    inIv z.1.fst (m z.1.fst) d (N.locN z) lo hi ↔ L.ivOf d z lo hi := by
  unfold inIv LevelData.ivOf
  rw [recAL_eq hF hR z, recYL_eq hF hS z]

end Read

/-- The data of the levels of a network. -/
noncomputable abbrev levelD (N : Net (Fin n)) (hG : N.G.Connected) (r : Fin n) (d₀ : N.G.Dart) (W : ℕ)
    (id : N.G.Dart → ℕ) : LevelData (Fin n) N.toRot :=
  ⟨N.treeN hG r d₀, N.codeN, W, N.fidN id, (d₀, true)⟩

section Concrete

variable {N : Net (Fin n)} (hG : N.G.Connected) {r : Fin n} {d₀ : N.G.Dart} {W : ℕ} {id : N.G.Dart → ℕ}
  {m : Fin n → Mem} {d : ℕ}

local notation "𝓛" => levelD N hG r d₀ W id
local notation "𝓣" => Net.treeN N hG r d₀
local notation "𝓦" => ((d₀, true) : N.G.Dart × Bool)

variable (r d₀) in
theorem corners_empty_iff {v : Fin n} {Γ : Finset (N.G.Dart × Bool)} :
    N.cornersAt v Γ = ∅ ↔ (𝓣).NP Γ v := by
  constructor
  · intro h z hz hv
    have h1 : N.locN z ∈ N.cornersAt v Γ := (N.mem_cornersAt hv).2 hz
    rw [h] at h1
    simp at h1
  · intro h
    rw [Finset.eq_empty_iff_forall_notMem]
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hz
    exact h z h1 h2

theorem c1_not_mark {Γ : Finset (N.G.Dart × Bool)} (hL : (𝓣).IsLevel Γ) {u : Fin n} (hu : u ≠ r)
    (hnp : ¬ (𝓣).NP Γ u) : (𝓣).c1 u ∉ (𝓣).marks Γ := by
  intro hm
  obtain ⟨v, hv, h | h⟩ := (mem_marks (𝓣)).1 hm
  · have h1 := congrArg (𝓣).vertM h
    rw [(𝓣).vertM_c1 hu, (𝓣).vertM_c1 (hv.ne_root hL)] at h1
    exact hnp (h1 ▸ hv)
  · exact c1_ne_c0 _ _ h

variable (hC : ∀ v, ConstAt N hG r d₀ (m v) v)

include hC in
theorem viewR_eq (z : N.G.Dart × Bool) :
    viewR z.1.fst (m z.1.fst) (N.locN z) = (𝓛).view (N.toRot.double.rev z) :=
  Prod.ext rfl (Prod.ext ((hC _).revP z rfl) (Prod.ext ((hC _).revF z rfl) ((hC _).revU z rfl)))

include hC in
theorem mkL_iff {Γ : Finset (N.G.Dart × Bool)} (hL : (𝓣).IsLevel Γ) (z : N.G.Dart × Bool) :
    mkL r (N.rotList z.1.fst) z.1.fst (m z.1.fst) (N.cornersAt z.1.fst Γ) (N.locN z) ↔ z ∈ (𝓣).marks Γ := by
  rw [mem_marks]
  constructor
  · rintro (⟨hv, hy, hC0⟩ | ⟨hy, hC0⟩)
    · have hnp := (corners_empty_iff hG r d₀).1 hC0
      rw [constAt_par hG hC] at hy
      exact ⟨z.1.fst, hnp, Or.inl ((N.treeN_c1_iff hG d₀ hv z).2
        ⟨rfl, congrArg Prod.fst hy, congrArg Prod.snd hy⟩)⟩
    · obtain ⟨u, hu, hzu⟩ := (isC0L_iff hG m (constAt_par hG hC) (constAt_np hG hC) rfl).1 hy
      have hnot : z ∉ Γ := fun h => hC0 ((N.mem_cornersAt rfl).2 h)
      rw [hzu] at hnot
      exact ⟨u, np_of_c0_not_mem hL hu hnot, Or.inr hzu⟩
  · rintro ⟨u, hu, hz | hz⟩
    · have hne : u ≠ r := hu.ne_root hL
      obtain ⟨h1, h2, h3⟩ := (N.treeN_c1_iff hG d₀ hne z).1 hz
      refine Or.inl ⟨h1 ▸ hne, ?_, (corners_empty_iff hG r d₀).2 (h1 ▸ hu)⟩
      rw [constAt_par hG hC, h1]
      exact Prod.ext h2 h3
    · have hne : u ≠ r := hu.ne_root hL
      refine Or.inr ⟨(isC0L_iff hG m (constAt_par hG hC) (constAt_np hG hC) rfl).2 ⟨u, hne, hz⟩, fun h => ?_⟩
      have h1 := (N.mem_cornersAt rfl).1 h
      rw [hz] at h1
      exact hL.c0_not_mem hu h1

include hC in
theorem smL_iff {Γ : Finset (N.G.Dart × Bool)} (hL : (𝓣).IsLevel Γ) (z : N.G.Dart × Bool) :
    smL r (N.rotList z.1.fst) z.1.fst (m z.1.fst) (N.cornersAt z.1.fst Γ) (N.locN z) ↔
      ∃ u, (𝓣).NP Γ u ∧ z = (𝓣).r0 u := by
  constructor
  · rintro ⟨hv, hy, hC0⟩
    rw [constAt_par hG hC] at hy
    exact ⟨z.1.fst, (corners_empty_iff hG r d₀).1 hC0, (N.treeN_r0_iff hG d₀ hv z).2
      ⟨rfl, congrArg Prod.fst hy, congrArg Prod.snd hy⟩⟩
  · rintro ⟨u, hu, hz⟩
    have hne : u ≠ r := hu.ne_root hL
    obtain ⟨h1, h2, h3⟩ := (N.treeN_r0_iff hG d₀ hne z).1 hz
    refine ⟨h1 ▸ hne, ?_, (corners_empty_iff hG r d₀).2 (h1 ▸ hu)⟩
    rw [constAt_par hG hC, h1]
    exact Prod.ext h2 h3

include hC in
theorem isR0_iff {x : N.G.Dart × Bool} {v : Fin n} (hx : x.1.fst = v) :
    (𝓣).IsR0 x ↔ v ≠ r ∧ N.locN x = (parR (N.rotList v) v (m v), false) := by
  subst hx
  rw [constAt_par hG hC]
  constructor
  · rintro ⟨u, hu, hx⟩
    have hne : u ≠ r := hu
    obtain ⟨h1, h2, h3⟩ := (N.treeN_r0_iff hG d₀ hne x).1 hx
    refine ⟨h1 ▸ hne, ?_⟩
    rw [h1]
    exact Prod.ext h2 h3
  · rintro ⟨hv, hy⟩
    exact ⟨x.1.fst, hv, (N.treeN_r0_iff hG d₀ hv x).2
      ⟨rfl, congrArg Prod.fst hy, congrArg Prod.snd hy⟩⟩

section Fields

variable {Γ : Finset (N.G.Dart × Bool)} {T₀ T : Finset (N.G.Dart × Bool)} {φ : Fin n × Bool → ℕ} {ι : ℕ}
  {z : N.G.Dart × Bool}

include hC in
theorem phibL_eq (hφ : ∀ x : N.G.Dart × Bool, x.1.fst = z.1.fst → φ (N.locN x) = (𝓣).phi T₀ 𝓦 x)
    (hι : ∀ u, u ≠ r → ¬ (𝓣).NP Γ u → ind T ((𝓣).c1 u) = ι) (hz : z ∈ Γ) :
    phibL r (N.rotList z.1.fst) z.1.fst (m z.1.fst) (N.cornersAt z.1.fst Γ) (N.locN z) φ ι =
      (𝓣).phiB T₀ T 𝓦 ((N.toRot.double.nodeReturn Γ)⁻¹ z) := by
  classical
  have he := N.loc_nodeReturn_inv (v := z.1.fst) (Γ := Γ) rfl hz
  have hf := N.fst_nodeReturn_inv (Γ := Γ) z
  have hmem : (N.toRot.double.nodeReturn Γ)⁻¹ z ∈ Γ := by
    have h1 : firstReturn N.toRot.double.rot Γ ((N.toRot.double.nodeReturn Γ)⁻¹ z) = z :=
      perm_apply_inv_self (N.toRot.double.nodeReturn Γ) z
    rw [← firstReturn_mem_iff N.toRot.double.rot Γ, h1]
    exact hz
  generalize (N.toRot.double.nodeReturn Γ)⁻¹ z = e at he hf hmem ⊢
  unfold phibL RotSystem.RootedTree.phiB
  rw [← he]
  by_cases hr : (𝓣).IsR0 e
  · have hr' := (isR0_iff hG hC hf).1 hr
    rw [if_pos hr, if_pos hr']
    obtain ⟨u, hu, hue⟩ := hr
    have hv : (𝓣).vertM e = u := by
      rw [hue]
      exact (𝓣).vertM_r0 hu
    have hi := hι u hu fun h => h e hmem hv
    have h1 : N.toRot.double.rot e = (𝓣).c1 u := by
      rw [hue]
      rfl
    have h2 : N.locN (N.toRot.double.rot e) = rotV (N.rotList z.1.fst) (N.locN e) := by
      rw [N.loc_rot e, hf]
    have h3 : (N.toRot.double.rot e).1.fst = z.1.fst := by
      rw [N.fst_rot e, hf]
    rw [← h2, hφ _ h3, h1, hi]
  · rw [if_neg hr, if_neg (mt (isR0_iff hG hC hf).2 hr), hφ _ hf]

include hC in
theorem arcL_eq (hφ : ∀ x : N.G.Dart × Bool, x.1.fst = z.1.fst → φ (N.locN x) = (𝓣).phi T₀ 𝓦 x)
    (hι : ∀ u, u ≠ r → ¬ (𝓣).NP Γ u → ind T ((𝓣).c1 u) = ι) (hz : z ∈ Γ) (hzi : ind T z = ι) :
    arcL r (N.rotList z.1.fst) z.1.fst (m z.1.fst) (N.cornersAt z.1.fst Γ) (N.locN z) φ ι =
      (𝓣).arcV Γ T₀ T 𝓦 z := by
  classical
  have h1 : (rotV (N.rotList z.1.fst))⁻¹ (N.locN z) = N.locN (N.toRot.double.rot⁻¹ z) :=
    (loc_rot_inv z).symm
  have hf := fst_rot_inv z
  have h2 : N.locN (N.toRot.double.rot⁻¹ z) ∈ N.cornersAt z.1.fst Γ ↔ N.toRot.double.rot⁻¹ z ∈ Γ :=
    N.mem_cornersAt hf
  unfold arcL RotSystem.RootedTree.arcV
  rw [h1, hzi]
  by_cases h3 : N.toRot.double.rot⁻¹ z ∈ Γ
  · rw [if_pos h3, if_pos (h2.2 h3)]
  · rw [if_neg h3, if_neg (mt h2.1 h3), hφ _ hf, phibL_eq hG hC hφ hι hz]

end Fields

variable (hd₀ : d₀.fst = r) (hhd : d₀.snd = (N.rotList r).headD r) (hR : N.toRot.Planar)
  (hc : N.toRot.Connected)

include hC hd₀ hhd hR hc in
theorem viewL_eq (z : N.G.Dart × Bool) :
    viewL r (N.rotList z.1.fst) z.1.fst (m z.1.fst) (N.locN z) = (𝓛).view z :=
  Prod.ext rfl (Prod.ext (constAt_numP hG hC hd₀ hhd hR hc rfl)
    (Prod.ext (constAt_numF0 hG hC hd₀ hhd hR hc rfl) (constAt_numF1 hG hC hd₀ hhd hR hc rfl)))

include hC hd₀ hhd hR hc in
theorem portFieldL_eq {Γ : Finset (N.G.Dart × Bool)} (hL : (𝓣).IsLevel Γ) {z : N.G.Dart × Bool}
    (hz : z ∈ Γ) (j : ℕ) :
    portFieldL r (N.rotList z.1.fst) z.1.fst (m z.1.fst) (N.cornersAt z.1.fst Γ) (N.locN z) j =
      (𝓛).portField Γ j z := by
  have hF0 : ∀ x : N.G.Dart × Bool, x.1.fst = z.1.fst →
      numFL 0 3 5 r (N.rotList z.1.fst) z.1.fst (m z.1.fst) (N.locN x) =
        (𝓣).phi ((𝓣).marks {𝓦}) 𝓦 x := fun x hx => constAt_numF0 hG hC hd₀ hhd hR hc hx
  have hF1 : ∀ x : N.G.Dart × Bool, x.1.fst = z.1.fst →
      numFL 1 4 6 r (N.rotList z.1.fst) z.1.fst (m z.1.fst) (N.locN x) =
        (𝓣).phi Finset.univ 𝓦 x := fun x hx => constAt_numF1 hG hC hd₀ hhd hR hc hx
  have hι0 : ∀ u, u ≠ r → ¬ (𝓣).NP Γ u → ind ((𝓣).marks Γ) ((𝓣).c1 u) = 0 := fun u hu hnp =>
    if_neg (c1_not_mark hG hL hu hnp)
  have hι1 : ∀ u, u ≠ r → ¬ (𝓣).NP Γ u → ind (Finset.univ : Finset (N.G.Dart × Bool)) ((𝓣).c1 u) = 1 :=
    fun u _ _ => if_pos (Finset.mem_univ _)
  have hz0 : ind ((𝓣).marks Γ) z = 0 := if_neg (not_mem_marks_of_mem hL hz)
  have hz1 : ind (Finset.univ : Finset (N.G.Dart × Bool)) z = 1 := if_pos (Finset.mem_univ _)
  rcases j with _ | _ | _ | _ | j
  · exact constAt_numP hG hC hd₀ hhd hR hc rfl
  · exact arcL_eq hG hC hF0 hι0 hz hz0
  · exact arcL_eq hG hC hF1 hι1 hz hz1
  · exact phibL_eq hG hC hF0 hι0 hz
  · exact phibL_eq hG hC hF1 hι1 hz

include hC hd₀ hhd hR hc in
theorem portItsL_eq (hOK : (𝓛).OK) (z : N.G.Dart × Bool) {C : Finset (Fin n × Bool)}
    (hcor : C = N.cornersAt z.1.fst ((𝓛).Γs d)) :
    portItsL r (N.rotList z.1.fst) z.1.fst (m z.1.fst) C (N.locN z) = (𝓛).portItems d z := by
  subst hcor
  classical
  unfold portItsL LevelData.portItems
  by_cases hz : z ∈ (𝓛).Γs d
  · rw [if_pos ((N.mem_cornersAt rfl).2 hz), if_pos hz]
    refine List.map_congr_left fun j _ => ?_
    rw [portFieldL_eq hG hC hd₀ hhd hR hc (hOK.level d) hz j]
    rfl
  · rw [if_neg (mt (N.mem_cornersAt rfl).1 hz), if_neg hz]

include hC hd₀ hhd hR hc in
theorem candAL_eq (hOK : (𝓛).OK) (hF : EF N (𝓛) m d) (hP : EP N (𝓛) m d) (z : N.G.Dart × Bool)
    {C : Finset (Fin n × Bool)} (hcor : C = N.cornersAt z.1.fst ((𝓛).Γs d)) :
    candAL W r (N.rotList z.1.fst) z.1.fst (m z.1.fst) d C (N.locN z) = (𝓛).aCand d z := by
  subst hcor
  unfold candAL LevelData.aCand
  rw [tabPL_eq hF hP z, minC_eq hF z, viewL_eq hG hC hd₀ hhd hR hc z, viewR_eq hG hC z,
    propext (mkL_iff hG hC (hOK.level d) z), propext (smL_iff hG hC (hOK.level d) z)]

include hC hd₀ hhd hR hc in
theorem selAIts_eq (hOK : (𝓛).OK) (hF : EF N (𝓛) m d) (hP : EP N (𝓛) m d) (z : N.G.Dart × Bool)
    {C : Finset (Fin n × Bool)} (hcor : C = N.cornersAt z.1.fst ((𝓛).Γs d)) :
    selAIts W r (N.rotList z.1.fst) z.1.fst (m z.1.fst) d C (N.locN z) = (𝓛).aItems d z := by
  unfold selAIts LevelData.aItems
  rw [candAL_eq hG hC hd₀ hhd hR hc hOK hF hP z hcor]

include hC hd₀ hhd hR hc in
theorem isAL_iff (hOK : (𝓛).OK) (hF : EF N (𝓛) m d) (hP : EP N (𝓛) m d) (hA : EA N (𝓛) m d) (z : N.G.Dart × Bool)
    {C : Finset (Fin n × Bool)} (hcor : C = N.cornersAt z.1.fst ((𝓛).Γs d)) :
    isAL W r (N.rotList z.1.fst) z.1.fst (m z.1.fst) d C (N.locN z) ↔ (𝓛).isA d z := by
  unfold isAL LevelData.isA
  rw [candAL_eq hG hC hd₀ hhd hR hc hOK hF hP z hcor, minAL_eq hF hA z]

theorem fidL_eq (hid : ∀ x : N.G.Dart, m x.fst 0 x.snd = id x) (z : N.G.Dart × Bool) :
    fidL z.1.fst (m z.1.fst) (N.locN z) = N.fidN id z := by
  obtain ⟨x, b⟩ := z
  cases b
  · rfl
  · show Nat.pair 0 (m x.fst 0 x.snd) = Nat.pair 0 (id x)
    rw [hid]

include hC hd₀ hhd hR hc in
theorem recAIts_eq (hOK : (𝓛).OK) (hid : ∀ x : N.G.Dart, m x.fst 0 x.snd = id x) (hF : EF N (𝓛) m d)
    (hP : EP N (𝓛) m d) (hA : EA N (𝓛) m d) (z : N.G.Dart × Bool)
    {C : Finset (Fin n × Bool)} (hcor : C = N.cornersAt z.1.fst ((𝓛).Γs d)) :
    recAIts W r (N.rotList z.1.fst) z.1.fst (m z.1.fst) d C (N.locN z) = (𝓛).raItems d z := by
  classical
  have e := isAL_iff hG hC hd₀ hhd hR hc hOK hF hP hA z hcor
  unfold recAIts LevelData.raItems
  by_cases h : (𝓛).isA d z
  · rw [if_pos (e.2 h), if_pos h, tabPL_eq hF hP z, minC_eq hF z, viewL_eq hG hC hd₀ hhd hR hc z,
      fidL_eq hid z, constAt_numP hG hC hd₀ hhd hR hc rfl]
    rfl
  · rw [if_neg (mt e.1 h), if_neg h]

include hC hd₀ hhd hR hc in
theorem candYL_eq (hid : ∀ x : N.G.Dart, m x.fst 0 x.snd = id x) (hF : EF N (𝓛) m d)
    (hP : EP N (𝓛) m d) (hRA : ER N (𝓛) m d) (z : N.G.Dart × Bool) :
    candYL W r (N.rotList z.1.fst) z.1.fst (m z.1.fst) d (N.locN z) = (𝓛).yCand d z := by
  unfold candYL LevelData.yCand
  rw [tabPL_eq hF hP z, minC_eq hF z, viewL_eq hG hC hd₀ hhd hR hc z, fidL_eq hid z, recAL_eq hF hRA z]

include hC hd₀ hhd hR hc in
theorem selYIts_eq (hid : ∀ x : N.G.Dart, m x.fst 0 x.snd = id x) (hF : EF N (𝓛) m d)
    (hP : EP N (𝓛) m d) (hRA : ER N (𝓛) m d) (z : N.G.Dart × Bool) :
    selYIts W r (N.rotList z.1.fst) z.1.fst (m z.1.fst) d (N.locN z) = (𝓛).yItems d z := by
  unfold selYIts LevelData.yItems
  rw [candYL_eq hG hC hd₀ hhd hR hc hid hF hP hRA z]

include hC hd₀ hhd hR hc in
theorem isYL_iff (hid : ∀ x : N.G.Dart, m x.fst 0 x.snd = id x) (hF : EF N (𝓛) m d)
    (hP : EP N (𝓛) m d) (hRA : ER N (𝓛) m d) (hY : EY N (𝓛) m d) (z : N.G.Dart × Bool) :
    isYL W r (N.rotList z.1.fst) z.1.fst (m z.1.fst) d (N.locN z) ↔ (𝓛).isY d z := by
  unfold isYL LevelData.isY
  rw [candYL_eq hG hC hd₀ hhd hR hc hid hF hP hRA z, minYL_eq hF hY z]

include hC hd₀ hhd hR hc in
theorem recYIts_eq (hid : ∀ x : N.G.Dart, m x.fst 0 x.snd = id x) (hF : EF N (𝓛) m d)
    (hP : EP N (𝓛) m d) (hRA : ER N (𝓛) m d) (hY : EY N (𝓛) m d) (z : N.G.Dart × Bool) :
    recYIts W r (N.rotList z.1.fst) z.1.fst (m z.1.fst) d (N.locN z) = (𝓛).ryItems d z := by
  classical
  have e := isYL_iff hG hC hd₀ hhd hR hc hid hF hP hRA hY z
  unfold recYIts LevelData.ryItems
  by_cases h : (𝓛).isY d z
  · rw [if_pos (e.2 h), if_pos h, constAt_numP hG hC hd₀ hhd hR hc rfl]
  · rw [if_neg (mt e.1 h), if_neg h]

include hC hd₀ hhd hR hc in
theorem railL_iff (hF : EF N (𝓛) m d) (hRA : ER N (𝓛) m d) (hS : ES N (𝓛) m d) (z : N.G.Dart × Bool) :
    railL r (N.rotList z.1.fst) z.1.fst (m z.1.fst) d (N.locN z) ↔
      ∃ u, u ≠ (𝓣).root ∧ (z = (𝓣).r0 u ∨ z = (𝓣).c0 u) ∧
        (𝓛).ivOf d z (pos ((𝓣).tau 𝓦) 𝓦 ((𝓣).c1 u)) (pos ((𝓣).tau 𝓦) 𝓦 ((𝓣).r0 u)) := by
  have hc1 : ∀ {u : Fin n}, u ≠ r → numPL r (N.rotList u) u (m u) (N.parN r u, true) =
      pos ((𝓣).tau 𝓦) 𝓦 ((𝓣).c1 u) := fun {u} hu => by
    rw [← loc_c1 hG hu]
    exact constAt_numP hG hC hd₀ hhd hR hc (fst_c1 hG hu)
  have hrev : ∀ {u : Fin n}, u ≠ r → z = (𝓣).c0 u →
      revR 9 (m z.1.fst) (N.locN z) = pos ((𝓣).tau 𝓦) 𝓦 ((𝓣).c1 u) ∧
        revR 9 (m z.1.fst) ((N.locN z).1, true) = pos ((𝓣).tau 𝓦) 𝓦 ((𝓣).r0 u) := fun {u} hu hzu => by
    have h1 := (hC z.1.fst).revP z rfl
    have h2 : N.toRot.double.rev z = (𝓣).c1 u := by
      rw [hzu]
      exact rev_c0 _ u
    have h3 := (hC z.1.fst).revP (z.1, true) rfl
    have h4 : N.toRot.double.rev (z.1, true) = (𝓣).r0 u := by
      rw [hzu]
      exact Prod.ext (N.toRot.rev_rev _) rfl
    rw [h2] at h1
    rw [h4] at h3
    exact ⟨h1, h3⟩
  constructor
  · rintro (⟨hv, hy, hi⟩ | ⟨hy, hi⟩)
    · rw [inIv_iff hF hRA hS] at hi
      rw [constAt_par hG hC] at hy hi
      have hz : z = (𝓣).r0 z.1.fst := (N.treeN_r0_iff hG d₀ hv z).2
        ⟨rfl, congrArg Prod.fst hy, congrArg Prod.snd hy⟩
      refine ⟨z.1.fst, hv, Or.inl hz, ?_⟩
      rw [← hz, ← hc1 hv, ← constAt_numP hG hC hd₀ hhd hR hc rfl]
      exact hi
    · rw [inIv_iff hF hRA hS] at hi
      obtain ⟨u, hu, hzu⟩ := (isC0L_iff hG m (constAt_par hG hC) (constAt_np hG hC) rfl).1 hy
      refine ⟨u, hu, Or.inr hzu, ?_⟩
      obtain ⟨h1, h2⟩ := hrev hu hzu
      rw [← h1, ← h2]
      exact hi
  · rintro ⟨u, hu, hz | hz, hi⟩
    · have hne : u ≠ r := hu
      obtain ⟨h1, h2, h3⟩ := (N.treeN_r0_iff hG d₀ hne z).1 hz
      subst h1
      have h4 : N.locN z = (parR (N.rotList z.1.fst) z.1.fst (m z.1.fst), false) := by
        rw [constAt_par hG hC]
        exact Prod.ext h2 h3
      refine Or.inl ⟨hne, h4, ?_⟩
      rw [inIv_iff hF hRA hS, constAt_par hG hC, hc1 hne, constAt_numP hG hC hd₀ hhd hR hc rfl]
      rw [← hz] at hi
      exact hi
    · have hne : u ≠ r := hu
      refine Or.inr ⟨(isC0L_iff hG m (constAt_par hG hC) (constAt_np hG hC) rfl).2 ⟨u, hne, hz⟩, ?_⟩
      obtain ⟨h1, h2⟩ := hrev hu hz
      rw [inIv_iff hF hRA hS, h1, h2]
      exact hi

include hC hd₀ hhd hR hc in
/-- **A node reads its corners at a level from its memory.** -/
theorem corL_eq (hOK : (𝓛).OK) (hid : ∀ x : N.G.Dart, m x.fst 0 x.snd = id x) (d : ℕ)
    (hprev : ∀ d', d' < d → EAll N (𝓛) m d') (v : Fin n) :
    corL W r (N.rotList v) v (m v) d = N.cornersAt v ((𝓛).Γs d) := by
  classical
  induction d generalizing v with
  | zero =>
    have e : (𝓛).Γs 0 = {𝓦} := rfl
    rw [e]
    unfold corL Net.cornersAt
    rw [Finset.filter_singleton]
    by_cases hv : v = r
    · subst hv
      rw [if_pos rfl, if_pos hd₀, Finset.image_singleton]
      show _ = ({(d₀.snd, true)} : Finset (Fin n × Bool))
      rw [hhd]
    · rw [if_neg hv, if_neg (fun h => hv (h.symm.trans hd₀)), Finset.image_empty]
  | succ d ih =>
    have ih' := ih (fun d' hd' => hprev d' (by omega))
    have E := hprev d (by omega)
    ext y
    by_cases hy : y ∈ ownL (N.rotList v)
    · obtain ⟨z, hz, rfl⟩ := exists_dart_of_own hy
      subst hz
      have hcor := ih' z.1.fst
      rw [N.mem_cornersAt rfl, hOK.mem_next]
      unfold corL
      rw [Finset.mem_union, hcor, N.mem_cornersAt rfl, Finset.mem_filter, List.mem_toFinset,
        isAL_iff hG hC hd₀ hhd hR hc hOK E.f E.p E.a z rfl,
        isYL_iff hG hC hd₀ hhd hR hc hid E.f E.p E.ra E.y z,
        railL_iff hG hC hd₀ hhd hR hc E.f E.ra E.ry z]
      exact or_congr_right (and_iff_right hy)
    · have h1 : y ∉ N.cornersAt v ((𝓛).Γs (d + 1)) := by
        intro hm
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hm
        obtain ⟨-, h2⟩ := Finset.mem_filter.1 hz
        subst h2
        exact hy (locN_mem_own z)
      refine iff_of_false ?_ h1
      unfold corL
      rw [Finset.mem_union, ih' v, Finset.mem_filter, List.mem_toFinset]
      rintro (hm | ⟨hm, -⟩)
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hm
        obtain ⟨-, h2⟩ := Finset.mem_filter.1 hz
        subst h2
        exact hy (locN_mem_own z)
      · exact hy hm

end Concrete

section Run

/-- What the level phases of a run compute. -/
structure LevelRun (N : Net (Fin n)) (B Tr W s k b : ℕ) (r : Fin n) (H : ℕ) (mem : ℕ → Fin n → Mem) :
    Prop where
  stable : ∀ {j k}, j < k → ∀ v, mem k v j = mem (j + 1) v j
  hFlood : ∀ d, d ≤ H → ∀ v, mem (phFlood d + 1) v (phFlood d) = relaxSt B N.G
    (fun v => floodIn W v (N.rotList v) (corL W r (N.rotList v) v (mem (phFlood d) v) d)) Tr v
  hPorts : ∀ d, d ≤ H → AggDone N (fun v => nameL v (mem (phPorts d) v) d)
    (fun v => portItsL r (N.rotList v) v (mem (phPorts d) v)
      (corL W r (N.rotList v) v (mem (phPorts d) v) d)) s k b
    (fun v => mem (phPorts d + 1) v (phPorts d))
  hSelA : ∀ d, d ≤ H → AggDone N (fun v => nameL v (mem (phSelA d) v) d)
    (fun v => selAIts W r (N.rotList v) v (mem (phSelA d) v) d
      (corL W r (N.rotList v) v (mem (phSelA d) v) d)) s k b
    (fun v => mem (phSelA d + 1) v (phSelA d))
  hRecA : ∀ d, d ≤ H → AggDone N (fun v => nameL v (mem (phRecA d) v) d)
    (fun v => recAIts W r (N.rotList v) v (mem (phRecA d) v) d
      (corL W r (N.rotList v) v (mem (phRecA d) v) d)) s k b
    (fun v => mem (phRecA d + 1) v (phRecA d))
  hSelY : ∀ d, d ≤ H → AggDone N (fun v => nameL v (mem (phSelY d) v) d)
    (fun v => selYIts W r (N.rotList v) v (mem (phSelY d) v) d) s k b
    (fun v => mem (phSelY d + 1) v (phSelY d))
  hRecY : ∀ d, d ≤ H → AggDone N (fun v => nameL v (mem (phRecY d) v) d)
    (fun v => recYIts W r (N.rotList v) v (mem (phRecY d) v) d) s k b
    (fun v => mem (phRecY d + 1) v (phRecY d))

/-- An answer of a call with given names and pairs. -/
theorem call_tab {N : Net (Fin n)} {s k b : ℕ} {nm : Fin n → Fin n × Bool → ℕ}
    {its : Fin n → Fin n × Bool → List (ℕ × ℕ)} {nmD : N.G.Dart × Bool → ℕ}
    {itsD : N.G.Dart × Bool → List (ℕ × ℕ)} {M : Fin n → ℕ → ℕ}
    (hn : ∀ z : N.G.Dart × Bool, nm z.1.fst (N.locN z) = nmD z)
    (hi : ∀ z : N.G.Dart × Bool, its z.1.fst (N.locN z) = itsD z)
    (hdone : AggDone N nm its s k b M)
    (hsymm : ∀ z, nmD (N.toRot.double.rev z) = nmD z)
    (hspan : ∀ z z', nmD z = nmD z' →
      ReachLE (fun a c => ∃ y : N.G.Dart × Bool, nmD y = nmD z ∧ y.1.fst = a ∧ y.1.snd = c) s z.1.fst z'.1.fst)
    (hk : ∀ z, ∃ K : Finset ℕ, K.card ≤ k ∧ ∀ z', nmD z' = nmD z → ∀ p ∈ itsD z', p.1 ∈ K)
    (hname : ∀ z, nmD z < 2 ^ b) (hf : ∀ z, ∀ p ∈ itsD z, p.1 < 2 ^ b ∧ p.2 < 2 ^ b)
    (z : N.G.Dart × Bool) (κ : ℕ) :
    M z.1.fst (Nat.pair (nmD z) κ) = tabD nmD itsD (nmD z) κ := by
  obtain rfl : nmD = nameOf N nm := (funext hn).symm
  obtain rfl : itsD = itsOf N its := (funext hi).symm
  exact hdone.tab (valid_of hsymm hspan hk hname hf) z κ

variable {N : Net (Fin n)} (hG : N.G.Connected) {r : Fin n} {d₀ : N.G.Dart} {W : ℕ} {id : N.G.Dart → ℕ}
  {d : ℕ}

local notation "𝓛" => levelD N hG r d₀ W id
local notation "𝓣" => Net.treeN N hG r d₀

/-- An answer of a call on the bags of a depth. -/
theorem level_call (hOK : (𝓛).OK) {h H s k b : ℕ} (hdep : ∀ v, (𝓣).dep v ≤ h) (hd : d ≤ H)
    (hs : (2 * H + 2) * (2 * (h + (1 + H * (2 + 4 * h))) + 1) ≤ s) (hnm : ∀ z, (𝓛).nm d z < 2 ^ b)
    {nm : Fin n → Fin n × Bool → ℕ} {its : Fin n → Fin n × Bool → List (ℕ × ℕ)}
    {itsD : N.G.Dart × Bool → List (ℕ × ℕ)} {M : Fin n → ℕ → ℕ}
    (hn : ∀ z : N.G.Dart × Bool, nm z.1.fst (N.locN z) = (𝓛).nm d z)
    (hi : ∀ z : N.G.Dart × Bool, its z.1.fst (N.locN z) = itsD z)
    (hdone : AggDone N nm its s k b M)
    (hk : ∀ z, ∃ K : Finset ℕ, K.card ≤ k ∧ ∀ z', (𝓛).nm d z' = (𝓛).nm d z → ∀ p ∈ itsD z', p.1 ∈ K)
    (hf : ∀ z, ∀ p ∈ itsD z, p.1 < 2 ^ b ∧ p.2 < 2 ^ b) (z : N.G.Dart × Bool) (κ : ℕ) :
    M z.1.fst (Nat.pair ((𝓛).nm d z) κ) = tabD ((𝓛).nm d) itsD ((𝓛).nm d z) κ :=
  call_tab hn hi hdone (fun z => (LevelData.nm_congr (same_rev _ z)).symm)
    (fun z z' hzz => (hOK.span hdep hd hzz).mono hs) hk hnm hf z κ

variable {B Tr s k b H h : ℕ} {mem : ℕ → Fin n → Mem}

theorem LevelRun.entry (hrun : LevelRun N B Tr W s k b r H mem) {j j' j'' : ℕ} (h1 : j < j') (h2 : j < j'')
    (v : Fin n) : mem j' v j = mem j'' v j :=
  (hrun.stable h1 v).trans (hrun.stable h2 v).symm

theorem LevelRun.transport (hrun : LevelRun N B Tr W s k b r H mem) {L : LevelData (Fin n) N.toRot}
    {d j : ℕ} (hE : EAll N L (mem (phRecY d + 1)) d) (hj : phRecY d + 1 ≤ j) : EAll N L (mem j) d where
  f z := by
    have h1 : phFlood d < j := by unfold phFlood; unfold phRecY at hj; omega
    have h2 : phFlood d < phRecY d + 1 := by unfold phFlood phRecY; omega
    rw [hrun.entry h1 h2]
    exact hE.f z
  p z κ := by
    have h1 : phPorts d < j := by unfold phPorts; unfold phRecY at hj; omega
    have h2 : phPorts d < phRecY d + 1 := by unfold phPorts phRecY; omega
    rw [hrun.entry h1 h2]
    exact hE.p z κ
  a z := by
    have h1 : phSelA d < j := by unfold phSelA; unfold phRecY at hj; omega
    have h2 : phSelA d < phRecY d + 1 := by unfold phSelA phRecY; omega
    rw [hrun.entry h1 h2]
    exact hE.a z
  ra z κ := by
    have h1 : phRecA d < j := by unfold phRecA; unfold phRecY at hj; omega
    have h2 : phRecA d < phRecY d + 1 := by unfold phRecA phRecY; omega
    rw [hrun.entry h1 h2]
    exact hE.ra z κ
  y z := by
    have h1 : phSelY d < j := by unfold phSelY; unfold phRecY at hj; omega
    have h2 : phSelY d < phRecY d + 1 := by unfold phSelY phRecY; omega
    rw [hrun.entry h1 h2]
    exact hE.y z
  ry z := by
    have h1 : phRecY d < j := by omega
    have h2 : phRecY d < phRecY d + 1 := by omega
    rw [hrun.entry h1 h2]
    exact hE.ry z

/-- **The level phases.** A run gives all entries at all depths. -/
theorem levels_of_run (hOK : (𝓛).OK) (hrun : LevelRun N B Tr W s k b r H mem)
    (hK : ∀ j, 10 ≤ j → ∀ v, ConstAt N hG r d₀ (mem j v) v)
    (hid : ∀ j, 1 ≤ j → ∀ x : N.G.Dart, mem j x.fst 0 x.snd = id x)
    (hd₀ : d₀.fst = r) (hhd : d₀.snd = (N.rotList r).headD r) (hR : N.toRot.Planar) (hc : N.toRot.Connected)
    (hdep : ∀ v, (𝓣).dep v ≤ h) (hB : (W + 1) ^ 2 ≤ 2 ^ B)
    (hTr : (2 * H + 2) * (2 * (2 * h + 1 + 2 * (1 + H * (2 + 4 * h))) + 1) ≤ Tr)
    (hs : (2 * H + 2) * (2 * (h + (1 + H * (2 + 4 * h))) + 1) ≤ s)
    (hkk : 5 * (1 + H * (2 + 4 * h)) + 4 ≤ k) (hb : (W + 2) * (W + 2) ≤ 2 ^ b)
    (hbf : ∀ z, N.fidN id z < 2 ^ b) (hHW : H ≤ W) (h5 : 5 ≤ W) :
    ∀ d, d ≤ H → EAll N (𝓛) (mem (phRecY d + 1)) d := by
  intro d
  have hW1 : (W + 1) ^ 2 ≤ 2 ^ b := by nlinarith
  have hW2 : ∀ x, x ≤ W + 1 → x < 2 ^ b := fun x hx => by nlinarith
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    have hprev : ∀ j, phFlood d ≤ j → ∀ d', d' < d → EAll N (𝓛) (mem j) d' := by
      intro j hj d' hd'
      refine hrun.transport (ih d' hd' (by omega)) ?_
      unfold phFlood at hj
      unfold phRecY
      omega
    have hcor : ∀ j, phFlood d ≤ j → ∀ v, corL W r (N.rotList v) v (mem j v) d =
        N.cornersAt v ((𝓛).Γs d) := fun j hj v =>
      corL_eq hG (hK j (by unfold phFlood at hj; omega)) hd₀ hhd hR hc hOK
        (hid j (by unfold phFlood at hj; omega)) d (hprev j hj) v
    have hnm : ∀ z, (𝓛).nm d z < 2 ^ b := fun z => (hOK.nm_lt hHW hd z).trans_le hW1
    have hF : ∀ j, phFlood d < j → EF N (𝓛) (mem j) d := by
      intro j hj z
      rw [hrun.stable hj z.1.fst, hrun.hFlood d hd z.1.fst]
      have e : (fun v => floodIn W v (N.rotList v) (corL W r (N.rotList v) v (mem (phFlood d) v) d)) =
          floodFam N W ((𝓛).Γs d) := by
        funext v
        rw [hcor _ le_rfl v]
      rw [e]
      exact flood_spec hG r d₀ hOK.decomp hR hc hdep hd (fun z => hOK.hcW z) hB hTr z
    have hP : ∀ j, phPorts d < j → EP N (𝓛) (mem j) d := by
      intro j hj z κ
      rw [hrun.stable hj z.1.fst]
      have hj1 : phFlood d < phPorts d := by unfold phFlood phPorts; omega
      refine level_call hG hOK hdep hd hs hnm (fun z => nameL_eq (hF _ hj1) z)
        (fun z => portItsL_eq hG (hK _ (by unfold phPorts; omega)) hd₀ hhd hR hc hOK z
          (hcor _ hj1.le _)) (hrun.hPorts d hd) ?_ ?_ z κ
      · intro z
        obtain ⟨K, hK1, hK2⟩ := hOK.exists_port_keys hdep d z
        refine ⟨K, hK1.trans ?_, hK2⟩
        have : d * (2 + 4 * h) ≤ H * (2 + 4 * h) := Nat.mul_le_mul_right _ hd
        omega
      · rintro z ⟨κ', a⟩ hm
        obtain ⟨h1, h2⟩ := hOK.portItems_lt h5 hm
        exact ⟨h1.trans_le hW1, hW2 _ h2⟩
    have hA : ∀ j, phSelA d < j → EA N (𝓛) (mem j) d := by
      intro j hj z
      rw [hrun.stable hj z.1.fst]
      have hj1 : phFlood d < phSelA d := by unfold phFlood phSelA; omega
      have hj2 : phPorts d < phSelA d := by unfold phPorts phSelA; omega
      refine level_call hG hOK hdep hd hs hnm (fun z => nameL_eq (hF _ hj1) z)
        (fun z => selAIts_eq hG (hK _ (by unfold phSelA; omega)) hd₀ hhd hR hc hOK (hF _ hj1) (hP _ hj2) z
          (hcor _ hj1.le _)) (hrun.hSelA d hd) ?_ ?_ z 0
      · intro z
        refine ⟨{0}, by simp only [Finset.card_singleton]; omega, ?_⟩
        rintro z' - ⟨κ', a⟩ hm
        exact Finset.mem_singleton.2 (LevelData.mem_aItems.1 hm).1
      · rintro z ⟨κ', a⟩ hm
        obtain ⟨rfl, hc'⟩ := LevelData.mem_aItems.1 hm
        exact ⟨Nat.pos_of_ne_zero (by positivity), (hOK.aCand_lt hc').trans_le hb⟩
    have hRA : ∀ j, phRecA d < j → ER N (𝓛) (mem j) d := by
      intro j hj z κ
      rw [hrun.stable hj z.1.fst]
      have hj1 : phFlood d < phRecA d := by unfold phFlood phRecA; omega
      have hj2 : phPorts d < phRecA d := by unfold phPorts phRecA; omega
      have hj3 : phSelA d < phRecA d := by unfold phSelA phRecA; omega
      have hKj := hK (phRecA d) (by unfold phRecA; omega)
      refine level_call hG hOK hdep hd hs hnm (fun z => nameL_eq (hF _ hj1) z)
        (fun z => recAIts_eq hG hKj hd₀ hhd hR hc hOK (hid _ (by unfold phRecA; omega)) (hF _ hj1) (hP _ hj2)
          (hA _ hj3) z (hcor _ hj1.le _)) (hrun.hRecA d hd) ?_ ?_ z κ
      · intro z
        refine ⟨Finset.range 4, by simp only [Finset.card_range]; omega, ?_⟩
        rintro z' - ⟨κ', a⟩ hm
        unfold LevelData.raItems at hm
        split_ifs at hm
        · exact Finset.mem_range.2 (hOK.raFields_lt hm).1
        · simp at hm
      · rintro z ⟨κ', a⟩ hm
        unfold LevelData.raItems at hm
        split_ifs at hm
        · obtain ⟨h1, h2⟩ := hOK.raFields_lt hm
          refine ⟨?_, ?_⟩
          · exact hW2 _ (by omega)
          · rcases h2 with h2 | rfl
            · exact h2.trans_le hb
            · exact hbf z
        · simp at hm
    have hY : ∀ j, phSelY d < j → EY N (𝓛) (mem j) d := by
      intro j hj z
      rw [hrun.stable hj z.1.fst]
      have hj1 : phFlood d < phSelY d := by unfold phFlood phSelY; omega
      have hj2 : phPorts d < phSelY d := by unfold phPorts phSelY; omega
      have hj3 : phRecA d < phSelY d := by unfold phRecA phSelY; omega
      refine level_call hG hOK hdep hd hs hnm (fun z => nameL_eq (hF _ hj1) z)
        (fun z => selYIts_eq hG (hK _ (by unfold phSelY; omega)) hd₀ hhd hR hc
          (hid _ (by unfold phSelY; omega)) (hF _ hj1) (hP _ hj2) (hRA _ hj3) z) (hrun.hSelY d hd) ?_ ?_ z 0
      · intro z
        refine ⟨{0}, by simp only [Finset.card_singleton]; omega, ?_⟩
        rintro z' - ⟨κ', a⟩ hm
        exact Finset.mem_singleton.2 (LevelData.mem_yItems.1 hm).1
      · rintro z ⟨κ', a⟩ hm
        obtain ⟨rfl, hc'⟩ := LevelData.mem_yItems.1 hm
        exact ⟨Nat.pos_of_ne_zero (by positivity), (hOK.yCand_lt hc').trans_le hb⟩
    have hS : ∀ j, phRecY d < j → ES N (𝓛) (mem j) d := by
      intro j hj z
      rw [hrun.stable hj z.1.fst]
      have hj1 : phFlood d < phRecY d := by unfold phFlood phRecY; omega
      have hj2 : phPorts d < phRecY d := by unfold phPorts phRecY; omega
      have hj3 : phRecA d < phRecY d := by unfold phRecA phRecY; omega
      have hj4 : phSelY d < phRecY d := by unfold phSelY phRecY; omega
      refine level_call hG hOK hdep hd hs hnm (fun z => nameL_eq (hF _ hj1) z)
        (fun z => recYIts_eq hG (hK _ (by unfold phRecY; omega)) hd₀ hhd hR hc
          (hid _ (by unfold phRecY; omega)) (hF _ hj1) (hP _ hj2) (hRA _ hj3) (hY _ hj4) z)
        (hrun.hRecY d hd) ?_ ?_ z 0
      · intro z
        refine ⟨{0}, by simp only [Finset.card_singleton]; omega, ?_⟩
        rintro z' - ⟨κ', a⟩ hm
        unfold LevelData.ryItems at hm
        split_ifs at hm
        · simp only [List.mem_singleton, Prod.mk.injEq] at hm
          exact Finset.mem_singleton.2 hm.1
        · simp at hm
      · rintro z ⟨κ', a⟩ hm
        unfold LevelData.ryItems at hm
        split_ifs at hm
        · simp only [List.mem_singleton, Prod.mk.injEq] at hm
          obtain ⟨rfl, rfl⟩ := hm
          exact ⟨Nat.pos_of_ne_zero (by positivity), hW2 _ ((hOK.pos_le_W _ _ _).trans (Nat.le_succ _))⟩
        · simp at hm
    exact ⟨hF _ (by unfold phFlood phRecY; omega), hP _ (by unfold phPorts phRecY; omega),
      hA _ (by unfold phSelA phRecY; omega), hRA _ (by unfold phRecA phRecY; omega),
      hY _ (by unfold phSelY phRecY; omega), hS _ (by omega)⟩

end Run

end SsspFlow.Congest
