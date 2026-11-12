import SsspFlow.NetValues

/-!
# The output of a node

From the tables of the value calls a node computes its chain of bags, the hubs of these bags and the estimates to and
from the hubs (`outL`). `labelsOK_of_mem`: the entries of the memory give correct labels.

`estFix`, `estL`: the estimates by a recursion along the children of a hierarchy, and the same recursion along the chain
of one vertex. `floorE`: the floor of an extended number. The hubs of a bag lie in the bag, and the bag has short walks,
so the values stay small (`distR_le_of_reach`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal

namespace SsspFlow

open FourColor RotSystem RotSystem.RootedTree

/-! ### Floors -/

/-- The floor of an extended number. -/
noncomputable def floorE (y : ℝ≥0∞) : ℕ∞ :=
  if y = ⊤ then ⊤ else ((sInf {k : ℕ | y < ((k + 1 : ℕ) : ℝ≥0∞)} : ℕ) : ℕ∞)

theorem floorE_le (y : ℝ≥0∞) : ((floorE y : ℕ∞) : ℝ≥0∞) ≤ y := by
  unfold floorE
  by_cases hy : y = ⊤
  · rw [hy]
    exact le_top
  · rw [if_neg hy, ENat.toENNReal_coe]
    rcases hk : sInf {k : ℕ | y < ((k + 1 : ℕ) : ℝ≥0∞)} with _ | j
    · simp
    · by_contra hlt
      exact Nat.notMem_of_lt_sInf (show j < sInf {k : ℕ | y < ((k + 1 : ℕ) : ℝ≥0∞)} by omega)
        (not_le.1 hlt)

theorem le_floorE {y : ℝ≥0∞} {k : ℕ} (h : (k : ℝ≥0∞) ≤ y) :
    (k : ℝ≥0∞) ≤ ((floorE y : ℕ∞) : ℝ≥0∞) := by
  unfold floorE
  by_cases hy : y = ⊤
  · rw [if_pos hy, ENat.toENNReal_top]
    exact le_top
  · rw [if_neg hy, ENat.toENNReal_coe]
    obtain ⟨j, hj⟩ := ENNReal.exists_nat_gt hy
    have hne : {k : ℕ | y < ((k + 1 : ℕ) : ℝ≥0∞)}.Nonempty :=
      ⟨j, hj.trans_le (by exact_mod_cast Nat.le_succ j)⟩
    have hm : y < ((sInf {k : ℕ | y < ((k + 1 : ℕ) : ℝ≥0∞)} + 1 : ℕ) : ℝ≥0∞) := Nat.sInf_mem hne
    have h1 := h.trans_lt hm
    have h2 : k < sInf {k : ℕ | y < ((k + 1 : ℕ) : ℝ≥0∞)} + 1 := by exact_mod_cast h1
    exact_mod_cast Nat.lt_succ_iff.1 h2

theorem floorE_lo {U : ℕ} (hU : 1 ≤ U) {k : ℕ} {est : ℝ≥0∞} (h : (U : ℝ≥0∞) * k ≤ est) :
    (k : ℝ≥0∞) ≤ ((floorE ((U : ℝ≥0∞)⁻¹ * est) : ℕ∞) : ℝ≥0∞) :=
  le_floorE ((ENNReal.mul_le_iff_le_inv (by exact_mod_cast (by omega : U ≠ 0))
    (ENNReal.natCast_ne_top U)).1 h)

theorem floorE_hi {U : ℕ} (hU : 1 ≤ U) {c dR est : ℝ≥0∞} (h : est ≤ (c * U) * dR) :
    ((floorE ((U : ℝ≥0∞)⁻¹ * est) : ℕ∞) : ℝ≥0∞) ≤ c * dR := by
  refine (floorE_le _).trans ?_
  have h0 : (U : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : U ≠ 0)
  calc (U : ℝ≥0∞)⁻¹ * est ≤ (U : ℝ≥0∞)⁻¹ * ((c * U) * dR) := by gcongr
    _ = c * dR := by
      rw [mul_comm c, mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel h0 (ENNReal.natCast_ne_top U), one_mul]

/-! ### Walks with few arcs -/

theorem exists_walk_of_reach {V : Type*} {adj A : V → V → Prop} {w : V → V → ℝ≥0∞} {Wt : ℝ≥0∞}
    (hA : ∀ a b, A a b → adj a b) (hW : ∀ a b, A a b → w a b ≤ Wt) {a b : V} (p : Walk A a b) :
    ∃ q : Walk adj a b, q.arcsIn A ∧ q.wt w ≤ ((p.support.length - 1 : ℕ) : ℝ≥0∞) * Wt := by
  induction p with
  | nil a => exact ⟨.nil a, trivial, by simp⟩
  | @cons a m c e p ih =>
    obtain ⟨q, h1, h2⟩ := ih
    refine ⟨.cons (hA _ _ e) q, ⟨e, h1⟩, ?_⟩
    rw [Walk.wt_cons]
    have hl : 1 ≤ p.support.length := by
      cases p <;> simp [Walk.support]
    have e1 : (Walk.cons e p).support.length - 1 = (p.support.length - 1) + 1 := by
      simp only [Walk.support, List.length_cons]
      omega
    rw [e1, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]
    exact add_le_add h2 (hW _ _ e)

theorem distR_le_of_reach {V : Type*} {adj A : V → V → Prop} {w : V → V → ℝ≥0∞} {Wt : ℝ≥0∞}
    (hA : ∀ a b, A a b → adj a b) (hW : ∀ a b, A a b → w a b ≤ Wt) {m : ℕ} {a b : V}
    (h : ReachLE A m a b) : distR adj w A a b ≤ (m : ℝ≥0∞) * Wt := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, h1, h2⟩ := exists_walk_of_reach (adj := adj) (w := w) hA hW p
  refine (iInf₂_le q h1).trans (h2.trans ?_)
  gcongr
  omega

/-! ### Estimates -/

namespace RHierarchy

universe u v

variable {V : Type u} {ι : Type v} {adj : V → V → Prop} (H : RHierarchy V ι adj) (dV : ι → V → V → ℝ≥0∞)

open Classical in
/-- The estimates from the vertices of a bag to its hubs, by recursion along the children. -/
noncomputable def estFix : ι → V → V → ℝ≥0∞ :=
  H.wf.fix (C := fun _ => V → V → ℝ≥0∞) fun x F v h =>
    if v ∈ H.hub x then dV x v h
    else ⨅ (c : ι) (hk : H.kid c x) (t : V) (_ : v ∈ H.bag c ∧ t ∈ H.hub x ∧ t ∈ H.bag c),
      F c hk v t + dV x t h

open Classical in
theorem estFix_eq (x : ι) (v h : V) : H.estFix dV x v h =
    if v ∈ H.hub x then dV x v h
    else ⨅ (c : ι) (_ : H.kid c x) (t : V) (_ : v ∈ H.bag c ∧ t ∈ H.hub x ∧ t ∈ H.bag c),
      H.estFix dV c v t + dV x t h := by
  unfold estFix
  rw [WellFounded.fix_eq]

variable {H dV}

theorem estFix_hub {x : ι} {v : V} (hv : v ∈ H.hub x) (h : V) : H.estFix dV x v h = dV x v h := by
  rw [estFix_eq, if_pos hv]

theorem estFix_not_hub {x : ι} {v : V} (hv : v ∉ H.hub x) (h : V) : H.estFix dV x v h =
    ⨅ (c : ι) (t : V) (_ : H.kid c x ∧ v ∈ H.bag c ∧ t ∈ H.hub x ∧ t ∈ H.bag c),
      H.estFix dV c v t + dV x t h := by
  rw [estFix_eq, if_neg hv]
  refine le_antisymm ?_ ?_
  · refine le_iInf fun c => le_iInf fun t => le_iInf fun hA => ?_
    exact iInf_le_of_le c <| iInf_le_of_le hA.1 <| iInf_le_of_le t <| iInf_le_of_le hA.2 le_rfl
  · refine le_iInf fun c => le_iInf fun hk => le_iInf fun t => le_iInf fun hA => ?_
    exact iInf_le_of_le c <| iInf_le_of_le t <| iInf_le_of_le ⟨hk, hA⟩ le_rfl

end RHierarchy

open Classical in
/-- The estimates along the chain of one vertex, by recursion on the depth. -/
noncomputable def estL {V : Type*} (hubS : ℕ → Finset V) (val : ℕ → V → V → ℝ≥0∞) (v : V) :
    ℕ → ℕ → V → ℝ≥0∞
  | 0, d, h => val d v h
  | k + 1, d, h =>
    if v ∈ hubS d then val d v h
    else ⨅ (t : V) (_ : t ∈ hubS d ∧ t ∈ hubS (d + 1)), estL hubS val v k (d + 1) t + val d t h

/-- **A vertex computes the estimates along its chain.** -/
theorem estFix_eq_estL {V : Type*} {ι : Type*} {adj : V → V → Prop} (H : RHierarchy V ι adj)
    {dV : ι → V → V → ℝ≥0∞} {hubS : ℕ → Finset V} {val : ℕ → V → V → ℝ≥0∞} {v : V} {Hd : ℕ} (x : ℕ → ι)
    (hhub : ∀ d, d ≤ Hd → ∀ y, y ∈ hubS d ↔ y ∈ H.hub (x d))
    (hval : ∀ d, d ≤ Hd → ∀ a b, val d a b = dV (x d) a b)
    (hbag : ∀ d, d ≤ Hd → v ∈ H.bag (x d))
    (hkid : ∀ d, d < Hd → H.kid (x (d + 1)) (x d))
    (hlast : v ∈ H.hub (x Hd))
    (hhb : ∀ y t, t ∈ H.hub y → t ∈ H.bag y)
    (hubk : ∀ x c t, H.kid c x → t ∈ H.hub x → t ∈ H.bag c → t ∈ H.hub c) :
    ∀ k d, d + k = Hd → ∀ h, H.estFix dV (x d) v h = estL hubS val v k d h := by
  classical
  intro k
  induction k with
  | zero =>
    intro d hd h
    have e : d = Hd := by omega
    subst e
    rw [RHierarchy.estFix_hub hlast, ← hval d le_rfl]
    rfl
  | succ k ih =>
    intro d hd h
    have hle : d ≤ Hd := by omega
    have hle' : d + 1 ≤ Hd := by omega
    rw [estL]
    by_cases hv : v ∈ H.hub (x d)
    · rw [RHierarchy.estFix_hub hv, if_pos ((hhub d hle v).2 hv), hval d hle]
    · rw [RHierarchy.estFix_not_hub hv, if_neg (fun h' => hv ((hhub d hle v).1 h'))]
      have hk := hkid d (by omega)
      refine le_antisymm ?_ ?_
      · refine le_iInf fun t => le_iInf fun hA => ?_
        have h1' := (hhub d hle t).1 hA.1
        have h2' := (hhub (d + 1) hle' t).1 hA.2
        refine iInf_le_of_le (x (d + 1)) <| iInf_le_of_le t <|
          iInf_le_of_le ⟨hk, hbag _ hle', h1', hhb _ _ h2'⟩ ?_
        rw [ih (d + 1) (by omega) t, hval d hle]
      · refine le_iInf fun c => le_iInf fun t => le_iInf fun hA => ?_
        obtain ⟨hk', hvc, h1, h2⟩ := hA
        obtain rfl : c = x (d + 1) := H.uniq (x d) c _ v hk' hk (hbag d hle) hv hvc (hbag _ hle')
        refine iInf_le_of_le t <|
          iInf_le_of_le ⟨(hhub d hle t).2 h1, (hhub (d + 1) hle' t).2 (hubk _ _ _ hk h1 h2)⟩ ?_
        rw [ih (d + 1) (by omega) t, hval d hle]

namespace Congest

open Cslib.Congest Cslib.Congest.Algorithm

variable {n : ℕ}

/-- The dart of a node that names its bag. -/
def own0 (rl : List (Fin n)) (v : Fin n) : Fin n × Bool := (rl.headD v, false)

/-- The node of a code. -/
noncomputable def vxOf (v : Fin n) (c : ℕ) : Fin n := if h : vertC n c < n then ⟨vertC n c, h⟩ else v

section Readers

variable (P : ValP) (W : ℕ) (r : Fin n) (rl : List (Fin n)) (v : Fin n) (m : Mem)

/-- The hubs of a bag at a depth, from the memory. -/
noncomputable def hubsL (d : ℕ) : Finset (Fin n) :=
  hubsT (vxOf v) W (tabV P v m (P.H - d) (own0 rl v))

/-- The values between the hubs of a bag at a depth, from the memory. -/
noncomputable def valL (d : ℕ) : Fin n → Fin n → ℝ≥0∞ :=
  bagT (vxOf v) W (P.dec (P.H - d)) (tabV P v m (P.H - d) (own0 rl v))

/-- The value towards a hub of a bag. -/
noncomputable def toL (d : ℕ) (y : Fin n) : ℕ∞ :=
  floorE ((P.U : ℝ≥0∞)⁻¹ * estL (hubsL P W rl v m) (valL P W rl v m) v (P.H - d) d y)

/-- The value from a hub of a bag. -/
noncomputable def fromL (d : ℕ) (y : Fin n) : ℕ∞ :=
  floorE ((P.U : ℝ≥0∞)⁻¹ *
    estL (hubsL P W rl v m) (fun d a b => valL P W rl v m d b a) v (P.H - d) d y)

/-- The entry of a node for its bag at a depth. -/
noncomputable def entryL (d : ℕ) : BagEntry (Fin n) where
  bag := nameL v m d (own0 rl v)
  hubs := (hubsL P W rl v m d).toList.map fun y => ⟨y, toL P W rl v m d y, fromL P W rl v m d y⟩

open Classical in
/-- **The output of a node.** It depends on its memory and its rotation list alone. -/
noncomputable def outL : LabelOut (Fin n) where
  chain := ((List.range (P.H + 1)).filter fun d => decide (d = 0 ∨ corL W r rl v m d = ∅)).map
    (entryL P W rl v m)
  treeBags u := if u ∈ rl then
      (List.range (P.H + 1)).flatMap fun d => [nameL v m d (u, false), nameL v m d (u, true)]
    else []

theorem mem_chain_iff {E : BagEntry (Fin n)} : E ∈ (outL P W r rl v m).chain ↔
    ∃ d, d ≤ P.H ∧ (d = 0 ∨ corL W r rl v m d = ∅) ∧ entryL P W rl v m d = E := by
  classical
  unfold outL
  simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq, Nat.lt_succ_iff, and_assoc]

theorem mem_entry_hubs {d : ℕ} {F : HubEntry (Fin n)} : F ∈ (entryL P W rl v m d).hubs ↔
    ∃ y ∈ hubsL P W rl v m d, (⟨y, toL P W rl v m d y, fromL P W rl v m d y⟩ : HubEntry (Fin n)) = F := by
  unfold entryL
  simp only [List.mem_map, Finset.mem_toList]

theorem mem_treeBags {u : Fin n} (hu : u ∈ rl) {x : ℕ} : x ∈ (outL P W r rl v m).treeBags u ↔
    ∃ d, d ≤ P.H ∧ (x = nameL v m d (u, false) ∨ x = nameL v m d (u, true)) := by
  show x ∈ (if u ∈ rl then _ else _) ↔ _
  rw [if_pos hu]
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false, Nat.lt_succ_iff]

end Readers

theorem headD_mem {α : Type*} {l : List α} (h : l ≠ []) (a : α) : l.headD a ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons b l => simp

/-- The dart of a node that names its bag. -/
def Net.dart0 (N : Net (Fin n)) (hne : ∀ v, ∃ u, N.G.Adj v u) (v : Fin n) : N.G.Dart × Bool :=
  (⟨(v, (N.rotList v).headD v), by
    obtain ⟨u, hu⟩ := hne v
    have h1 : u ∈ N.rotList v := (N.mem_rotList v u).2 hu
    exact (N.mem_rotList v _).1 (headD_mem (List.ne_nil_of_mem h1) v)⟩, false)

/-- The weight of a dart. -/
def gOf (N : Net (Fin n)) (ℓ : Fin n → Fin n → ℕ) (z : N.G.Dart × Bool) : ℕ := ℓ z.1.fst z.1.snd

theorem vxOf_code {N : Net (Fin n)} (v : Fin n) (p : N.G.Dart × Bool) : vxOf v (N.codeN p) = p.1.fst := by
  have h : vertC n (N.codeN p) = p.1.fst := vertC_codeRaw p.1.snd.2 p.2
  unfold vxOf
  rw [dif_pos (by rw [h]; exact p.1.fst.2)]
  exact Fin.ext h

theorem lt_of_toENNReal_le {a : ℕ∞} {X : ℝ≥0∞} {M : ℕ} (h : ((a : ℕ∞) : ℝ≥0∞) ≤ X) (hX : X < (M : ℝ≥0∞)) :
    a < (M : ℕ∞) := by
  have h1 : ((a : ℕ∞) : ℝ≥0∞) < (((M : ℕ∞)) : ℝ≥0∞) := by
    rw [ENat.toENNReal_coe]
    exact h.trans_lt hX
  exact ENat.toENNReal_lt.1 h1

theorem dist_le_floorE {V : Type} {adj : V → V → Prop} {ℓ : V → V → ℕ} {a b : V} (p₀ : Walk adj a b) {U : ℕ}
    (hU : 1 ≤ U) {est : ℝ≥0∞} (h : (U : ℝ≥0∞) * dist adj (lenOf ℓ) Set.univ a b ≤ est) :
    dist adj (lenOf ℓ) Set.univ a b ≤ ((floorE ((U : ℝ≥0∞)⁻¹ * est) : ℕ∞) : ℝ≥0∞) := by
  obtain ⟨k, hk⟩ := dist_nat ℓ p₀
  rw [hk] at h ⊢
  exact floorE_lo hU h

section Main

variable {N : Net (Fin n)} (hG : N.G.Connected) {r : Fin n} {d₀ : N.G.Dart} {W : ℕ} {id : N.G.Dart → ℕ} {P : ValP}

local notation "𝓛" => levelD N hG r d₀ W id
local notation "𝓣" => Net.treeN N hG r d₀

theorem hadjN (r : Fin n) (d₀ : N.G.Dart) : ∀ a b, N.G.Adj a b →
    ∃ d, (N.treeN hG r d₀).vert d = a ∧ (N.treeN hG r d₀).vert (N.toRot.rev d) = b :=
  fun a b h => ⟨⟨(a, b), h⟩, rfl, rfl⟩

theorem hsurjN (r : Fin n) (d₀ : N.G.Dart) (hne : ∀ v, ∃ u, N.G.Adj v u) :
    ∀ v, ∃ d, (N.treeN hG r d₀).vert d = v :=
  fun v => by
    obtain ⟨u, hu⟩ := hne v
    exact ⟨⟨(v, u), hu⟩, rfl⟩

/-- The bags of a network. -/
noncomputable abbrev hierN (hOK : (𝓛).OK) (hne : ∀ v, ∃ u, N.G.Adj v u) {Hd : ℕ}
    (hH : ∀ v, ¬ (𝓣).NP ((𝓛).Γs Hd) v) : RHierarchy (Fin n) ℕ N.G.Adj :=
  hOK.decomp.hierarchy hOK.hc hOK.hinj (hadjN hG r d₀) (hsurjN hG r d₀ hne) hH

/-- The entries of the memory that the output reads. -/
structure MemOK (N : Net (Fin n)) (hG : N.G.Connected) (r : Fin n) (d₀ : N.G.Dart) (W : ℕ) (id : N.G.Dart → ℕ)
    (P : ValP) (g : N.G.Dart × Bool → ℕ) (m : Fin n → Mem) : Prop where
  hC : ∀ v, ConstAt N hG r d₀ (m v) v
  hid : ∀ x : N.G.Dart, m x.fst 0 x.snd = id x
  hE : ∀ d, d ≤ P.H → EAll N (levelD N hG r d₀ W id) m d
  hV : ∀ i, i ≤ P.H → EV N (levelD N hG r d₀ W id) P g (N.secN ((levelD N hG r d₀ W id).Γt P)) m i

variable {g : N.G.Dart × Bool → ℕ} {m : Fin n → Mem}

/-- The values between the hubs of the bags. -/
noncomputable abbrev dVN (hG : N.G.Connected) (r : Fin n) (d₀ : N.G.Dart) (W : ℕ) (id : N.G.Dart → ℕ) (P : ValP)
    (g : N.G.Dart × Bool → ℕ) : ℕ → Fin n → Fin n → ℝ≥0∞ :=
  bagVal (N.treeN hG r d₀) N.codeN (levelD N hG r d₀ W id).Γs P.H ((levelD N hG r d₀ W id).vals P g)

theorem nameL_own (hM : MemOK N hG r d₀ W id P g m) (hne : ∀ v, ∃ u, N.G.Adj v u) (v : Fin n) {d : ℕ}
    (hd : d ≤ P.H) : nameL v (m v) d (own0 (N.rotList v) v) = (𝓛).nm d (N.dart0 hne v) :=
  nameL_eq (hM.hE d hd).f (N.dart0 hne v)

theorem tabV_own (hM : MemOK N hG r d₀ W id P g m) (hne : ∀ v, ∃ u, N.G.Adj v u) (v : Fin n) {d : ℕ}
    (hd : d ≤ P.H) : tabV P v (m v) (P.H - d) (own0 (N.rotList v) v) =
      (𝓛).vT P g (N.secN ((𝓛).Γt P)) (P.H - d) (N.dart0 hne v) :=
  tabV_eq hG (hM.hE _ (by omega)).f (hM.hV _ (by omega)) (N.dart0 hne v)

/-- A node reads the hubs of a bag. -/
theorem mem_hubsL_iff (hOK : (𝓛).OK) (hM : MemOK N hG r d₀ W id P g m) (hne : ∀ v, ∃ u, N.G.Adj v u)
    (hH : ∀ v, ¬ (𝓣).NP ((𝓛).Γs P.H) v) (v : Fin n) {d : ℕ} (hd : d ≤ P.H) (y : Fin n) :
    y ∈ hubsL P W (N.rotList v) v (m v) d ↔ y ∈ (hierN hG hOK hne hH).hub ((𝓛).nm d (N.dart0 hne v)) := by
  classical
  have hT := hOK.vT_ok (P := P) (g := g) (sec := N.secN ((𝓛).Γt P)) (P.H - d) (N.dart0 hne v)
  have e0 : hubsL P W (N.rotList v) v (m v) d =
      ((𝓛).cornersIn P (P.H - d) (N.dart0 hne v)).image (𝓣).vertM := by
    unfold hubsL
    rw [tabV_own hG hM hne v hd]
    exact hT.hubs hOK.hcW (fun p _ => vxOf_code v p)
  rw [e0]
  have e1 := Decomp.hub_eq hOK.decomp hOK.hc hOK.hinj (hadjN hG r d₀) (hsurjN hG r d₀ hne) hH
    ((𝓛).nm d (N.dart0 hne v))
  rw [e1, Finset.mem_coe, mem_bagHubs, Finset.mem_image]
  have f1 : (Nat.unpair ((𝓛).nm d (N.dart0 hne v))).1 = d := bagName_fst _ _
  have f2 : P.H - (P.H - d) = d := by omega
  unfold hubLevel
  rw [f1]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
    rw [f2] at h2
    exact ⟨p, h1, ⟨by rw [f1]; exact hd, by rw [f1]; exact h2⟩, rfl⟩
  · rintro ⟨p, h1, h2, rfl⟩
    refine ⟨p, Finset.mem_filter.2 ⟨h1, ?_⟩, rfl⟩
    rw [f2]
    have h3 := h2.2
    rwa [f1] at h3

/-- A node reads the values of a bag. -/
theorem valL_eq (hOK : (𝓛).OK) (hM : MemOK N hG r d₀ W id P g m) (hU : 1 ≤ P.U) (hne : ∀ v, ∃ u, N.G.Adj v u)
    (v : Fin n) {d : ℕ} (hd : d ≤ P.H) (a b : Fin n) :
    valL P W (N.rotList v) v (m v) d a b = dVN hG r d₀ W id P g ((𝓛).nm d (N.dart0 hne v)) a b := by
  unfold valL
  rw [tabV_own hG hM hne v hd]
  have h := hOK.bagVal_read (P := P) (g := g) (sec := N.secN ((𝓛).Γt P)) hU (i := P.H - d) (by omega)
    (N.dart0 hne v) (vx := vxOf v) (fun p => vxOf_code v p) a b
  rw [show P.H - (P.H - d) = d by omega] at h
  exact h.symm

/-- The estimates of a node are those of the hierarchy. -/
theorem est_read (hOK : (𝓛).OK) (hM : MemOK N hG r d₀ W id P g m) (hne : ∀ v, ∃ u, N.G.Adj v u)
    (hH : ∀ v, ¬ (𝓣).NP ((𝓛).Γs P.H) v) (v : Fin n) {val : ℕ → Fin n → Fin n → ℝ≥0∞}
    {dV : ℕ → Fin n → Fin n → ℝ≥0∞}
    (hval : ∀ d, d ≤ P.H → ∀ a b, val d a b = dV ((𝓛).nm d (N.dart0 hne v)) a b)
    {d : ℕ} (hd : d ≤ P.H) (y : Fin n) :
    (hierN hG hOK hne hH).estFix dV ((𝓛).nm d (N.dart0 hne v)) v y =
      estL (hubsL P W (N.rotList v) v (m v)) val v (P.H - d) d y := by
  refine estFix_eq_estL (hierN hG hOK hne hH) (fun d => (𝓛).nm d (N.dart0 hne v))
    (fun d hd y => mem_hubsL_iff hG hOK hM hne hH v hd y) hval
    (fun d hd => ⟨N.dart0 hne v, inBag_name hd _, rfl⟩) ?_ ?_ ?_ ?_ _ d (by omega) y
  · intro d hd
    exact ⟨by rw [LevelData.nm, LevelData.nm, bagName_fst, bagName_fst], N.dart0 hne v,
      inBag_name (by omega) _, inBag_name (by omega) _⟩
  · have e1 := Decomp.hub_eq hOK.decomp hOK.hc hOK.hinj (hadjN hG r d₀) (hsurjN hG r d₀ hne) hH
      ((𝓛).nm P.H (N.dart0 hne v))
    show v ∈ (hierN hG hOK hne hH).hub _
    rw [e1, Finset.mem_coe, mem_bagHubs]
    have f1 : (Nat.unpair ((𝓛).nm P.H (N.dart0 hne v))).1 = P.H := bagName_fst _ _
    refine ⟨N.dart0 hne v, ?_, inBag_name le_rfl _, rfl⟩
    unfold hubLevel
    rw [f1, Nat.sub_self, topLevel_zero]
    exact Finset.mem_univ _
  · rintro y t ⟨g', h1, -, h3⟩
    exact ⟨g', h1, h3⟩
  · exact fun x c t hk ha hac => hOK.decomp.hub_kid hOK.hc hOK.hinj (hadjN hG r d₀) (hsurjN hG r d₀ hne) hH
      x c t hk ha hac

/-- A node with no corner at a depth reads this from its memory. -/
theorem corL_empty_iff (hOK : (𝓛).OK) (hM : MemOK N hG r d₀ W id P g m) (hd₀ : d₀.fst = r)
    (hhd : d₀.snd = (N.rotList r).headD r) (hR : N.toRot.Planar) (hc : N.toRot.Connected) {d : ℕ} (hd : d ≤ P.H)
    (v : Fin n) : corL W r (N.rotList v) v (m v) d = ∅ ↔ (𝓣).NP ((𝓛).Γs d) v := by
  rw [corL_eq hG hM.hC hd₀ hhd hR hc hOK hM.hid d (fun d' hd' => hM.hE d' (by omega)) v]
  exact corners_empty_iff hG r d₀

variable {ℓ : Fin n → Fin n → ℕ} {C Cl cl B Wt h : ℕ}

/-- The bounds of the estimates of a node. -/
theorem entry_bounds (hOK : (𝓛).OK) (hVk : LevelData.VOK (𝓛) P (gOf N ℓ) C Cl cl B Wt h)
    (hM : MemOK N hG r d₀ W id P (gOf N ℓ) m) (hne : ∀ v, ∃ u, N.G.Adj v u)
    (hH : ∀ v, ¬ (𝓣).NP ((𝓛).Γs P.H) v) (v : Fin n) {d : ℕ} (hd : d ≤ P.H) {y : Fin n}
    (hy : y ∈ hubsL P W (N.rotList v) v (m v) d) :
    let A := (hierN hG hOK hne hH).arc ((𝓛).nm d (N.dart0 hne v))
    let c := cU P.U ^ (2 * P.H + 1)
    dist N.G.Adj (lenOf ℓ) Set.univ v y ≤ ((toL P W (N.rotList v) v (m v) d y : ℕ∞) : ℝ≥0∞) ∧
    ((toL P W (N.rotList v) v (m v) d y : ℕ∞) : ℝ≥0∞) ≤ c * distR N.G.Adj (lenOf ℓ) A v y ∧
    dist N.G.Adj (lenOf ℓ) Set.univ y v ≤ ((fromL P W (N.rotList v) v (m v) d y : ℕ∞) : ℝ≥0∞) ∧
    ((fromL P W (N.rotList v) v (m v) d y : ℕ∞) : ℝ≥0∞) ≤ c * distR N.G.Adj (lenOf ℓ) A y v := by
  classical
  intro A c
  have hU := hVk.hU
  have hD := hOK.decomp
  have hUne : (P.U : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : P.U ≠ 0)
  have hc0 : c ≠ 0 := pow_ne_zero _ (cU_ne_zero hU)
  have hcT : c ≠ ⊤ := ENNReal.pow_ne_top (cU_ne_top hU)
  have hlam0 : c * (P.U : ℝ≥0∞) ≠ 0 := mul_ne_zero hc0 hUne
  have hlamT : c * (P.U : ℝ≥0∞) ≠ ⊤ := ENNReal.mul_ne_top hcT (ENNReal.natCast_ne_top _)
  have hvals := hOK.vals_metric hVk
  have hgw : ∀ z : N.G.Dart × Bool, ((gOf N ℓ z : ℕ) : ℝ≥0∞) =
      lenOf ℓ ((𝓣).vertM z) ((𝓣).vertM (N.toRot.double.rev z)) := fun _ => rfl
  have hadj' : ∀ z : N.G.Dart × Bool, N.G.Adj ((𝓣).vertM z) ((𝓣).vertM (N.toRot.double.rev z)) :=
    fun z => z.1.adj
  have hlo : ∀ x, ∀ a ∈ (hierN hG hOK hne hH).hub x, ∀ b ∈ (hierN hG hOK hne hH).hub x,
      (P.U : ℝ≥0∞) * dist N.G.Adj (lenOf ℓ) Set.univ a b ≤ dVN hG r d₀ W id P (gOf N ℓ) x a b :=
    fun x a _ b _ => hD.bagVal_lo hadj' hgw hvals x a b
  have hhi : ∀ x, ∀ a ∈ (hierN hG hOK hne hH).hub x, ∀ b ∈ (hierN hG hOK hne hH).hub x,
      dVN hG r d₀ W id P (gOf N ℓ) x a b ≤
        (c * (P.U : ℝ≥0∞)) * distR N.G.Adj (lenOf ℓ) ((hierN hG hOK hne hH).arc x) a b :=
    fun x a ha b hb => hD.bagVal_hi hOK.hc hOK.hinj (hadjN hG r d₀) (hsurjN hG r d₀ hne) hH hgw hU hvals x a b ha hb
  have hubk : ∀ x c t, (hierN hG hOK hne hH).kid c x → t ∈ (hierN hG hOK hne hH).hub x →
      t ∈ (hierN hG hOK hne hH).bag c → t ∈ (hierN hG hOK hne hH).hub c :=
    fun x c t hk ha hac => hD.hub_kid hOK.hc hOK.hinj (hadjN hG r d₀) (hsurjN hG r d₀ hne) hH x c t hk ha hac
  have hhub := (mem_hubsL_iff hG hOK hM hne hH v hd y).1 hy
  have hbag : v ∈ (hierN hG hOK hne hH).bag ((𝓛).nm d (N.dart0 hne v)) := ⟨N.dart0 hne v, inBag_name hd _, rfl⟩
  have hybag : y ∈ (hierN hG hOK hne hH).bag ((𝓛).nm d (N.dart0 hne v)) := by
    obtain ⟨g', h1, -, h3⟩ := hhub
    exact ⟨g', h1, h3⟩
  have hreach := Decomp.span (hD := hD) (hc := hOK.hc) (hinj := hOK.hinj) (hadj := hadjN hG r d₀)
    (hsurj := hsurjN hG r d₀ hne) (hH := hH) hOK.hR hVk.hdep hbag hybag
  have hreach' := Decomp.span (hD := hD) (hc := hOK.hc) (hinj := hOK.hinj) (hadj := hadjN hG r d₀)
    (hsurj := hsurjN hG r d₀ hne) (hH := hH) hOK.hR hVk.hdep hybag hbag
  have hArcAdj : ∀ a b, A a b → N.G.Adj a b := by
    rintro a b ⟨z, -, rfl, rfl⟩
    exact z.1.adj
  obtain ⟨p, -⟩ := hreach
  obtain ⟨p', -⟩ := hreach'
  obtain ⟨q, -, -⟩ := exists_walk_of_reach (adj := N.G.Adj) (w := fun _ _ => (0 : ℝ≥0∞)) (Wt := 0) hArcAdj
    (fun _ _ _ => le_rfl) p
  obtain ⟨q', -, -⟩ := exists_walk_of_reach (adj := N.G.Adj) (w := fun _ _ => (0 : ℝ≥0∞)) (Wt := 0) hArcAdj
    (fun _ _ _ => le_rfl) p'
  have hedge := fun x a b h' ha => hD.hedge_out hOK.hc hOK.hinj (hadjN hG r d₀) (hsurjN hG r d₀ hne) hH x a b h' ha
  have hedge' := fun x a b h' ha => hD.hedge_in hOK.hc hOK.hinj (hadjN hG r d₀) (hsurjN hG r d₀ hne) hH x a b h' ha
  have b1 := (hierN hG hOK hne hH).est_bounds hedge hubk (lenOf ℓ) (P.U : ℝ≥0∞) (c * (P.U : ℝ≥0∞)) hlam0 hlamT
    (dVN hG r d₀ W id P (gOf N ℓ)) hlo hhi ((hierN hG hOK hne hH).estFix (dVN hG r d₀ W id P (gOf N ℓ)))
    (fun x v h hv _ => RHierarchy.estFix_hub hv h)
    (fun x v h _ hv _ => RHierarchy.estFix_not_hub hv h) _ v hbag y hhub
  have b2 := (hierN hG hOK hne hH).est_bounds_in hedge' hubk (lenOf ℓ) (P.U : ℝ≥0∞) (c * (P.U : ℝ≥0∞)) hlam0 hlamT
    (dVN hG r d₀ W id P (gOf N ℓ)) hlo hhi
    ((hierN hG hOK hne hH).estFix (fun x a b => dVN hG r d₀ W id P (gOf N ℓ) x b a))
    (fun x v h hv _ => RHierarchy.estFix_hub hv h)
    (fun x v h _ hv _ => RHierarchy.estFix_not_hub hv h) _ v hbag y hhub
  have e1 := est_read hG hOK hM hne hH v (val := valL P W (N.rotList v) v (m v))
    (dV := dVN hG r d₀ W id P (gOf N ℓ)) (fun d hd a b => valL_eq hG hOK hM hU hne v hd a b) hd y
  have e2 := est_read hG hOK hM hne hH v (val := fun d a b => valL P W (N.rotList v) v (m v) d b a)
    (dV := fun x a b => dVN hG r d₀ W id P (gOf N ℓ) x b a)
    (fun d hd a b => valL_eq hG hOK hM hU hne v hd b a) hd y
  rw [e1] at b1
  rw [e2] at b2
  exact ⟨dist_le_floorE q hU b1.1, floorE_hi hU b1.2, dist_le_floorE q' hU b2.1, floorE_hi hU b2.2⟩

/-- **The entries of the memory give correct labels.** -/
theorem labelsOK_of_mem {e hh ss ww : ℕ} (hOK : (𝓛).OK) (hVk : LevelData.VOK (𝓛) P (gOf N ℓ) C Cl cl B Wt h)
    (hM : MemOK N hG r d₀ W id P (gOf N ℓ) m) (hne : ∀ v, ∃ u, N.G.Adj v u)
    (hH : ∀ v, ¬ (𝓣).NP ((𝓛).Γs P.H) v) (hd₀ : d₀.fst = r) (hhd : d₀.snd = (N.rotList r).headD r)
    (hR : N.toRot.Planar) (hc : N.toRot.Connected) (hce : cU P.U ^ (2 * P.H + 1) ≤ 1 + (e : ℝ≥0∞)⁻¹)
    (hhh : P.H ≤ hh) (hspan : (2 * P.H + 2) * (2 * (h + (1 + P.H * (2 + 4 * h))) + 1) ≤ ss)
    (hcard : 1 + (P.H + 1) * (2 + 4 * h) ≤ ss) (hHW : P.H ≤ W) (hname : (W + 1) ^ 2 ≤ 2 ^ ww)
    (hval : 2 * (((2 * P.H + 2) * (2 * (h + (1 + P.H * (2 + 4 * h))) + 1)) * Wt) < 2 ^ ww) :
    LabelsOK N ℓ e hh ss ww (fun v => outL P W r (N.rotList v) v (m v)) := by
  classical
  have hD := hOK.decomp
  have hreach₀ : ∀ x a b, a ∈ (hierN hG hOK hne hH).bag x → b ∈ (hierN hG hOK hne hH).bag x →
      ReachLE ((hierN hG hOK hne hH).arc x) ((2 * P.H + 2) * (2 * (h + (1 + P.H * (2 + 4 * h))) + 1)) a b :=
    fun x a b ha hb => Decomp.span (hD := hD) (hc := hOK.hc) (hinj := hOK.hinj) (hadj := hadjN hG r d₀)
      (hsurj := hsurjN hG r d₀ hne) (hH := hH) hOK.hR hVk.hdep ha hb
  have hreach : ∀ x a b, a ∈ (hierN hG hOK hne hH).bag x → b ∈ (hierN hG hOK hne hH).bag x →
      ReachLE ((hierN hG hOK hne hH).arc x) ss a b := fun x a b ha hb =>
    ReachLE.mono (hreach₀ x a b ha hb) hspan
  have hArcAdj : ∀ x a b, (hierN hG hOK hne hH).arc x a b → N.G.Adj a b := by
    rintro x a b ⟨z, -, rfl, rfl⟩
    exact z.1.adj
  have hArcW : ∀ x a b, (hierN hG hOK hne hH).arc x a b → lenOf ℓ a b ≤ (Wt : ℝ≥0∞) := by
    rintro x a b ⟨z, -, rfl, rfl⟩
    show ((gOf N ℓ z : ℕ) : ℝ≥0∞) ≤ _
    exact_mod_cast hVk.hWt z
  have hsmall : ∀ x a b, a ∈ (hierN hG hOK hne hH).bag x → b ∈ (hierN hG hOK hne hH).bag x →
      cU P.U ^ (2 * P.H + 1) * distR N.G.Adj (lenOf ℓ) ((hierN hG hOK hne hH).arc x) a b <
        ((2 ^ ww : ℕ) : ℝ≥0∞) := by
    intro x a b ha hb
    calc cU P.U ^ (2 * P.H + 1) * distR N.G.Adj (lenOf ℓ) ((hierN hG hOK hne hH).arc x) a b
        ≤ 2 * ((((2 * P.H + 2) * (2 * (h + (1 + P.H * (2 + 4 * h))) + 1) : ℕ) : ℝ≥0∞) * Wt) :=
          mul_le_mul' hVk.hcn (distR_le_of_reach (hArcAdj x) (hArcW x) (hreach₀ x a b ha hb))
      _ = ((2 * (((2 * P.H + 2) * (2 * (h + (1 + P.H * (2 + 4 * h))) + 1)) * Wt) : ℕ) : ℝ≥0∞) := by
        push_cast; rfl
      _ < _ := by exact_mod_cast hval
  have hsame : ∀ (v : Fin n) (d : ℕ) (z z' : N.G.Dart × Bool), (𝓣).vertM z = v → (𝓣).vertM z' = v →
      (d = 0 ∨ (𝓣).NP ((𝓛).Γs d) v) → N.toRot.Same ((𝓛).Γs d) z z' := by
    rintro v d z z' hz hz' (rfl | hA)
    · exact hD.same_zero hOK.hc z z'
    · exact hA.gcomp hz hz'
  have hbags : ∀ (v : Fin n) (d : ℕ), d ≤ P.H → ∀ y ∈ hubsL P W (N.rotList v) v (m v) d,
      v ∈ (hierN hG hOK hne hH).bag ((𝓛).nm d (N.dart0 hne v)) ∧
        y ∈ (hierN hG hOK hne hH).bag ((𝓛).nm d (N.dart0 hne v)) := by
    intro v d hd y hy
    refine ⟨⟨N.dart0 hne v, inBag_name hd _, rfl⟩, ?_⟩
    obtain ⟨g', h1, -, h3⟩ := (mem_hubsL_iff hG hOK hM hne hH v hd y).1 hy
    exact ⟨g', h1, h3⟩
  refine ⟨{
    H := hierN hG hOK hne hH
    tree := (hierN hG hOK hne hH).arc
    depth := Decomp.depthOf P.H
    depth_kid := fun c x hk => Decomp.depth_kid (hD := hD) (hc := hOK.hc) (hinj := hOK.hinj)
      (hadj := hadjN hG r d₀) (hsurj := hsurjN hG r d₀ hne) (hH := hH) hk
    height := fun x => (Decomp.depthOf_le (hD := hD) (hc := hOK.hc) (hinj := hOK.hinj) P.H x).trans hhh
    tree_adj := hArcAdj
    tree_symm := ?_
    tree_span := fun x a b ha hb => hreach x a b ha hb
    congestion := ?_
    hub_card := fun x => (Decomp.hub_card (hD := hD) (hc := hOK.hc) (hinj := hOK.hinj)
      (hadj := hadjN hG r d₀) (hsurj := hsurjN hG r d₀ hne) (hH := hH) hVk.hdep x).trans hcard
    chain_iff := ?_
    hubs_iff := ?_
    tree_know := ?_
    to_lo := ?_
    to_hi := ?_
    from_lo := ?_
    from_hi := ?_
    name_lt := ?_
    treeBags_lt := ?_
    value_lt := ?_ }⟩
  · rintro x a b ⟨z, hz, rfl, rfl⟩
    exact ⟨N.toRot.double.rev z, hz.same (same_rev _ z), rfl, by rw [N.toRot.double.rev_rev]⟩
  · intro d a b
    obtain ⟨F, h1, h2⟩ := Decomp.congestion (hD := hD) (hc := hOK.hc) (hinj := hOK.hinj) (H := P.H)
      (fun d d' e1 e2 => SimpleGraph.Dart.ext _ _ (Prod.ext e1 e2)) d a b
    exact ⟨F, h1, fun x hx ht => h2 x hx ht⟩
  · intro v x
    refine (Decomp.chain_iff (hD := hD) (hc := hOK.hc) (hinj := hOK.hinj)
      (hadj := hadjN hG r d₀) (hsurj := hsurjN hG r d₀ hne) (hH := hH)).trans ?_
    constructor
    · rintro ⟨d, z, hd, hz, hA, rfl⟩
      refine ⟨entryL P W (N.rotList v) v (m v) d, (mem_chain_iff _ _ _ _ _ _).2 ⟨d, hd, ?_, rfl⟩, ?_⟩
      · rcases hA with rfl | hA
        · exact Or.inl rfl
        · exact Or.inr ((corL_empty_iff hG hOK hM hd₀ hhd hR hc hd v).2 hA)
      · show nameL v (m v) d (own0 (N.rotList v) v) = _
        rw [nameL_own hG hM hne v hd]
        exact LevelData.nm_congr (hsame v d _ _ rfl hz hA)
    · rintro ⟨E, hE, rfl⟩
      obtain ⟨d, hd, hA, rfl⟩ := (mem_chain_iff _ _ _ _ _ _).1 hE
      refine ⟨d, N.dart0 hne v, hd, rfl, ?_, nameL_own hG hM hne v hd⟩
      rcases hA with rfl | hA
      · exact Or.inl rfl
      · exact Or.inr ((corL_empty_iff hG hOK hM hd₀ hhd hR hc hd v).1 hA)
  · intro v E hE y
    obtain ⟨d, hd, -, rfl⟩ := (mem_chain_iff _ _ _ _ _ _).1 hE
    show y ∈ (hierN hG hOK hne hH).hub (nameL v (m v) d (own0 (N.rotList v) v)) ↔ _
    rw [nameL_own hG hM hne v hd, ← mem_hubsL_iff hG hOK hM hne hH v hd y]
    constructor
    · intro hy
      exact ⟨⟨y, _, _⟩, (mem_entry_hubs _ _ _ _ _).2 ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨F, hF, rfl⟩
      obtain ⟨y', hy', rfl⟩ := (mem_entry_hubs _ _ _ _ _).1 hF
      exact hy'
  · intro v u huv x
    have hu : u ∈ N.rotList v := (N.mem_rotList v u).2 huv
    refine (mem_treeBags _ _ _ _ _ _ hu).trans ?_
    constructor
    · rintro ⟨d, hd, rfl | rfl⟩
      · rw [show nameL v (m v) d (u, false) = (𝓛).nm d (N.dartAt v (u, false) huv) from
          nameL_eq (hM.hE d hd).f (N.dartAt v (u, false) huv)]
        exact ⟨N.dartAt v (u, false) huv, inBag_name hd _, rfl, rfl⟩
      · rw [show nameL v (m v) d (u, true) = (𝓛).nm d (N.dartAt v (u, true) huv) from
          nameL_eq (hM.hE d hd).f (N.dartAt v (u, true) huv)]
        exact ⟨N.dartAt v (u, true) huv, inBag_name hd _, rfl, rfl⟩
    · rintro ⟨z, hz, h1, h2⟩
      have hzv : z.1.fst = v := h1
      have hzu : z.1.snd = u := h2
      refine ⟨(Nat.unpair x).1, hz.1, ?_⟩
      have e2 := nameL_eq (hM.hE _ hz.1).f z
      have e3 : x = nameL z.1.fst (m z.1.fst) (Nat.unpair x).1 (z.1.snd, z.2) := hz.eq_name.trans e2.symm
      rw [hzv, hzu] at e3
      cases hb : z.2 with
      | false => left; rw [hb] at e3; exact e3
      | true => right; rw [hb] at e3; exact e3
  · intro v E hE F hF
    obtain ⟨d, hd, -, rfl⟩ := (mem_chain_iff _ _ _ _ _ _).1 hE
    obtain ⟨y, hy, rfl⟩ := (mem_entry_hubs _ _ _ _ _).1 hF
    exact (entry_bounds hG hOK hVk hM hne hH v hd hy).1
  · intro v E hE F hF
    obtain ⟨d, hd, -, rfl⟩ := (mem_chain_iff _ _ _ _ _ _).1 hE
    obtain ⟨y, hy, rfl⟩ := (mem_entry_hubs _ _ _ _ _).1 hF
    show _ ≤ (1 + (e : ℝ≥0∞)⁻¹) * distR N.G.Adj (lenOf ℓ)
      ((hierN hG hOK hne hH).arc (nameL v (m v) d (own0 (N.rotList v) v))) v y
    rw [nameL_own hG hM hne v hd]
    exact (entry_bounds hG hOK hVk hM hne hH v hd hy).2.1.trans (mul_le_mul_left hce _)
  · intro v E hE F hF
    obtain ⟨d, hd, -, rfl⟩ := (mem_chain_iff _ _ _ _ _ _).1 hE
    obtain ⟨y, hy, rfl⟩ := (mem_entry_hubs _ _ _ _ _).1 hF
    exact (entry_bounds hG hOK hVk hM hne hH v hd hy).2.2.1
  · intro v E hE F hF
    obtain ⟨d, hd, -, rfl⟩ := (mem_chain_iff _ _ _ _ _ _).1 hE
    obtain ⟨y, hy, rfl⟩ := (mem_entry_hubs _ _ _ _ _).1 hF
    show _ ≤ (1 + (e : ℝ≥0∞)⁻¹) * distR N.G.Adj (lenOf ℓ)
      ((hierN hG hOK hne hH).arc (nameL v (m v) d (own0 (N.rotList v) v))) y v
    rw [nameL_own hG hM hne v hd]
    exact (entry_bounds hG hOK hVk hM hne hH v hd hy).2.2.2.trans (mul_le_mul_left hce _)
  · intro v E hE
    obtain ⟨d, hd, -, rfl⟩ := (mem_chain_iff _ _ _ _ _ _).1 hE
    show nameL v (m v) d (own0 (N.rotList v) v) < _
    rw [nameL_own hG hM hne v hd]
    exact (hOK.nm_lt hHW hd _).trans_le hname
  · intro v u x hx
    by_cases hu : u ∈ N.rotList v
    · obtain ⟨d, hd, hx⟩ := (mem_treeBags _ _ _ _ _ _ hu).1 hx
      have huv := (N.mem_rotList v u).1 hu
      rcases hx with rfl | rfl
      · rw [show nameL v (m v) d (u, false) = (𝓛).nm d (N.dartAt v (u, false) huv) from
          nameL_eq (hM.hE d hd).f (N.dartAt v (u, false) huv)]
        exact (hOK.nm_lt hHW hd _).trans_le hname
      · rw [show nameL v (m v) d (u, true) = (𝓛).nm d (N.dartAt v (u, true) huv) from
          nameL_eq (hM.hE d hd).f (N.dartAt v (u, true) huv)]
        exact (hOK.nm_lt hHW hd _).trans_le hname
    · have h0 : (outL P W r (N.rotList v) v (m v)).treeBags u = [] := if_neg hu
      rw [h0] at hx
      cases hx
  · intro v E hE F hF
    obtain ⟨d, hd, -, rfl⟩ := (mem_chain_iff _ _ _ _ _ _).1 hE
    obtain ⟨y, hy, rfl⟩ := (mem_entry_hubs _ _ _ _ _).1 hF
    have hb := entry_bounds hG hOK hVk hM hne hH v hd hy
    obtain ⟨hv, hy'⟩ := hbags v d hd y hy
    exact ⟨Or.inr (lt_of_toENNReal_le hb.2.1 (hsmall _ _ _ hv hy')),
      Or.inr (lt_of_toENNReal_le hb.2.2.2 (hsmall _ _ _ hy' hv))⟩

end Main

end Congest

end SsspFlow
