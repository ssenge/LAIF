import SsspFlow.LevelT
import SsspFlow.Machine
import SsspFlow.MaxFlow
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# The tree and the numbers of a network

A connected network gets the tree of shortest walks from a root, where each node takes its neighbour of least
number that is closer to the root (`treeN`). Its darts of the doubled map get codes (`codeN`) and names of faces
(`fidN`). A node sees the rotation of its own darts as a permutation that depends only on its list of neighbours
(`rotV`), and numbers along this rotation follow from numbers along the rotation of the map
(`pos_transport`, `offBy_transport`, `firstReturn_transport`, `sec_iff`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SsspFlow

open FourColor

section Transport

variable {X X' : Type*} [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X']
  {f : Equiv.Perm X} {f' : Equiv.Perm X'} {ι : X → X'} {b : X}

theorem iterate_transport (hι : ∀ x, fconnect f b x → ι (f x) = f' (ι x)) (k : ℕ) :
    ι (f^[k] b) = f'^[k] (ι b) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hι _ (fconnect_iterate _ _ _), ih]

theorem pos_transport (hι : ∀ x, fconnect f b x → ι (f x) = f' (ι x)) {z : X}
    (hinj : ∀ x, fconnect f b x → ι x = ι z → x = z) :
    pos f' (ι b) (ι z) = pos f b z := by
  unfold pos
  congr 1
  ext k
  simp only [Set.mem_setOf_eq]
  rw [← iterate_transport hι]
  exact ⟨fun h => hinj _ (fconnect_iterate _ _ _) h, fun h => by rw [h]⟩

theorem offBy_transport (hι : ∀ x, fconnect f b x → ι (f x) = f' (ι x)) {z : X}
    (hinj : ∀ x, fconnect f b x → ι x = ι z → x = z) (inc' : X' → ℕ) :
    offBy f' inc' (ι b) (ι z) = offBy f (fun y => inc' (ι y)) b z := by
  unfold offBy
  rw [pos_transport hι hinj]
  refine Finset.sum_congr rfl fun j _ => ?_
  show inc' _ = inc' (ι _)
  rw [iterate_transport hι]

variable {S : Finset X} {S' : Finset X'}

theorem trail_transport (hι : ∀ x, fconnect f b x → ι (f x) = f' (ι x))
    (hS : ∀ x, fconnect f b x → (x ∈ S ↔ ι x ∈ S')) {x c : X} (h : Trail f S x c)
    (hx : fconnect f b x) : Trail f' S' (ι x) (ι c) := by
  induction h with
  | here hm => exact .here ((hS _ hx).1 hm)
  | step hy _ ih =>
    refine .step (fun hm => hy ((hS _ hx).2 hm)) ?_
    rw [← hι _ hx]
    exact ih (fconnect_apply hx)

theorem firstReturn_transport (hι : ∀ x, fconnect f b x → ι (f x) = f' (ι x))
    (hS : ∀ x, fconnect f b x → (x ∈ S ↔ ι x ∈ S')) {x : X} (hx : fconnect f b x) (hm : x ∈ S) :
    ι (firstReturn f S x) = firstReturn f' S' (ι x) := by
  symm
  refine firstReturn_eq_of_trail f' ((hS _ hx).1 hm) ?_
  rw [← hι _ hx]
  exact trail_transport hι hS (firstReturn_trail f hm) (fconnect_apply hx)

theorem firstReturn_inv_transport (hι : ∀ x, fconnect f b x → ι (f x) = f' (ι x))
    (hS : ∀ x, fconnect f b x → (x ∈ S ↔ ι x ∈ S')) {h : X} (hh : fconnect f b h) (hm : h ∈ S) :
    ι ((firstReturn f S)⁻¹ h) = (firstReturn f' S')⁻¹ (ι h) := by
  have he : firstReturn f S ((firstReturn f S)⁻¹ h) = h := perm_apply_inv_self _ _
  have h1 := fconnect_firstReturn f S ((firstReturn f S)⁻¹ h)
  rw [he] at h1
  have hb : fconnect f b ((firstReturn f S)⁻¹ h) := connect_trans hh (fconnect_symm h1)
  have hmem : (firstReturn f S)⁻¹ h ∈ S := (firstReturn_mem_iff f S _).1 (by rw [he]; exact hm)
  have h2 := firstReturn_transport hι hS hb hmem
  rw [he] at h2
  rw [h2, perm_inv_apply_self]

open Classical in
/-- The end of the trail from `y`, if there is one. -/
noncomputable def secOf (f : Equiv.Perm X) (S : Finset X) (y : X) : Option X :=
  if h : ∃ c, Trail f S y c then some h.choose else none

theorem secOf_of_trail {y c : X} (h : Trail f S y c) : secOf f S y = some c := by
  classical
  have h' : ∃ c, Trail f S y c := ⟨c, h⟩
  unfold secOf
  rw [dif_pos h']
  exact congrArg some (h'.choose_spec.unique h)

theorem secOf_of_not {y : X} (h : ∀ c, ¬ Trail f S y c) : secOf f S y = none := by
  classical
  unfold secOf
  rw [dif_neg]
  exact fun ⟨c, hc⟩ => h c hc

end Transport

namespace Congest

variable {n : ℕ}

/-- The rotation of the darts of the doubled map at a node, from its list of neighbours. -/
def rotV (rl : List (Fin n)) : Equiv.Perm (Fin n × Bool) where
  toFun y := if y.2 then (rl.formPerm y.1, false) else (y.1, true)
  invFun y := if y.2 then (y.1, false) else (rl.formPerm.symm y.1, true)
  left_inv y := by rcases y with ⟨u, _ | _⟩ <;> simp
  right_inv y := by rcases y with ⟨u, _ | _⟩ <;> simp

/-- The code of a dart from its numbers. -/
def codeRaw (n v u : ℕ) (b : Bool) : ℕ := (v * n + u) * 2 + b.toNat

theorem codeRaw_lt {v u : ℕ} (hv : v < n) (hu : u < n) (b : Bool) : codeRaw n v u b < 2 * n * n := by
  unfold codeRaw
  have h1 : v * n + u + 1 ≤ n * n := by
    calc v * n + u + 1 ≤ v * n + n := by omega
      _ = (v + 1) * n := by rw [Nat.succ_mul]
      _ ≤ n * n := Nat.mul_le_mul_right _ hv
  have h2 : b.toNat ≤ 1 := Bool.toNat_le b
  have h3 : 2 * n * n = 2 * (n * n) := Nat.mul_assoc _ _ _
  omega

/-- The node of a dart from its code. -/
def vertC (n c : ℕ) : ℕ := c / 2 / n

/-- The neighbour of a dart from its code. -/
def nbrC (n c : ℕ) : ℕ := c / 2 % n

theorem div_two_codeRaw (n v u : ℕ) (b : Bool) : codeRaw n v u b / 2 = v * n + u := by
  unfold codeRaw
  have h2 : b.toNat ≤ 1 := Bool.toNat_le b
  omega

theorem vertC_codeRaw {v u : ℕ} (hu : u < n) (b : Bool) : vertC n (codeRaw n v u b) = v := by
  unfold vertC
  rw [div_two_codeRaw, Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hu, Nat.add_zero]

theorem nbrC_codeRaw {v u : ℕ} (hu : u < n) (b : Bool) : nbrC n (codeRaw n v u b) = u := by
  unfold nbrC
  rw [div_two_codeRaw, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hu]

theorem bit_codeRaw (n v u : ℕ) (b : Bool) : codeRaw n v u b % 2 = b.toNat := by
  unfold codeRaw
  have h2 : b.toNat ≤ 1 := Bool.toNat_le b
  omega

variable (N : Net (Fin n))

namespace Net

/-- The code of a dart of the doubled map. -/
def codeN (z : N.G.Dart × Bool) : ℕ := codeRaw n z.1.fst z.1.snd z.2

/-- A dart of the doubled map as seen at its node. -/
def locN (z : N.G.Dart × Bool) : Fin n × Bool := (z.1.snd, z.2)

theorem codeN_lt (z : N.G.Dart × Bool) : N.codeN z < 2 * n * n :=
  codeRaw_lt z.1.fst.2 z.1.snd.2 z.2

theorem dart_ext {x y : N.G.Dart × Bool} (h1 : x.1.fst = y.1.fst) (h2 : N.locN x = N.locN y) : x = y := by
  have h3 : x.1.snd = y.1.snd := congrArg (fun p : Fin n × Bool => p.1) h2
  have h4 : x.2 = y.2 := congrArg (fun p : Fin n × Bool => p.2) h2
  exact Prod.ext (SimpleGraph.Dart.ext _ _ (Prod.ext h1 h3)) h4

theorem codeN_inj : Function.Injective N.codeN := by
  intro x y h
  have hx : vertC n (N.codeN x) = x.1.fst := vertC_codeRaw x.1.snd.2 _
  have hy : vertC n (N.codeN y) = y.1.fst := vertC_codeRaw y.1.snd.2 _
  have hx' : nbrC n (N.codeN x) = x.1.snd := nbrC_codeRaw x.1.snd.2 _
  have hy' : nbrC n (N.codeN y) = y.1.snd := nbrC_codeRaw y.1.snd.2 _
  have h1 : x.1.fst = y.1.fst := Fin.ext (by rw [← hx, ← hy, h])
  have h2 : x.1.snd = y.1.snd := Fin.ext (by rw [← hx', ← hy', h])
  have h3 : x.2.toNat = y.2.toNat := by
    have e1 : N.codeN x % 2 = x.2.toNat := bit_codeRaw _ _ _ _
    have e2 : N.codeN y % 2 = y.2.toNat := bit_codeRaw _ _ _ _
    rw [← e1, ← e2, h]
  have h4 : x.2 = y.2 := by
    rcases hx2 : x.2 with _ | _ <;> rcases hy2 : y.2 with _ | _ <;> simp [hx2, hy2] at h3 ⊢
  exact N.dart_ext h1 (Prod.ext h2 h4)

theorem card_le : Fintype.card (N.G.Dart × Bool) ≤ 2 * n * n := by
  have h := Fintype.card_le_of_injective
    (fun z => (⟨N.codeN z, N.codeN_lt z⟩ : Fin (2 * n * n)))
    (fun x y e => N.codeN_inj (congrArg Fin.val e))
  rwa [Fintype.card_fin] at h

theorem loc_rot (z : N.G.Dart × Bool) :
    N.locN (N.toRot.double.rot z) = rotV (N.rotList z.1.fst) (N.locN z) := by
  obtain ⟨d, _ | _⟩ := z <;> rfl

theorem fst_rot (z : N.G.Dart × Bool) : (N.toRot.double.rot z).1.fst = z.1.fst := by
  obtain ⟨d, _ | _⟩ := z <;> rfl

theorem fst_iterate (z : N.G.Dart × Bool) (k : ℕ) : ((⇑N.toRot.double.rot)^[k] z).1.fst = z.1.fst := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', fst_rot, ih]

theorem fst_of_fconnect {x y : N.G.Dart × Bool} (h : fconnect N.toRot.double.rot x y) : y.1.fst = x.1.fst := by
  obtain ⟨k, rfl⟩ := fconnect_iff_iterate.1 h
  exact N.fst_iterate x k

/-- The least element of a set, or a default. -/
noncomputable def parLoc (v : Fin n) (S : Finset (Fin n)) : Fin n :=
  if h : S.Nonempty then S.min' h else v

/-- The neighbours of a node that are closer to the root. -/
noncomputable def parSet (r v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun u => N.G.Adj v u ∧ N.G.dist r u + 1 = N.G.dist r v

/-- The parent of a node. -/
noncomputable def parN (r v : Fin n) : Fin n := parLoc v (N.parSet r v)

theorem parSet_nonempty (hG : N.G.Connected) {r v : Fin n} (hv : v ≠ r) : (N.parSet r v).Nonempty := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist v r
  cases p with
  | nil => exact (hv rfl).elim
  | @cons _ u _ h q =>
    refine ⟨u, Finset.mem_filter.2 ⟨Finset.mem_univ _, h, ?_⟩⟩
    rw [SimpleGraph.Walk.length_cons] at hp
    have h1 : N.G.dist u r ≤ q.length := SimpleGraph.dist_le q
    have h2 : N.G.dist v r ≤ N.G.dist v u + N.G.dist u r := hG.dist_triangle
    have h3 : N.G.dist v u = 1 := SimpleGraph.dist_eq_one_iff_adj.2 h
    rw [SimpleGraph.dist_comm (u := r) (v := u), SimpleGraph.dist_comm (u := r) (v := v)]
    omega

theorem parN_mem (hG : N.G.Connected) {r v : Fin n} (hv : v ≠ r) : N.parN r v ∈ N.parSet r v := by
  unfold parN parLoc
  rw [dif_pos (N.parSet_nonempty hG hv)]
  exact Finset.min'_mem _ _

theorem parN_adj (hG : N.G.Connected) {r v : Fin n} (hv : v ≠ r) : N.G.Adj v (N.parN r v) :=
  (Finset.mem_filter.1 (N.parN_mem hG hv)).2.1

theorem parN_dist (hG : N.G.Connected) {r v : Fin n} (hv : v ≠ r) :
    N.G.dist r (N.parN r v) + 1 = N.G.dist r v :=
  (Finset.mem_filter.1 (N.parN_mem hG hv)).2.2

theorem parN_root (r : Fin n) : N.parN r r = r := by
  unfold parN parLoc
  rw [dif_neg]
  rintro ⟨u, hu⟩
  have := (Finset.mem_filter.1 hu).2.2
  rw [SimpleGraph.dist_self] at this
  omega

/-- The dart of a node to its parent. -/
noncomputable def upN (d₀ : N.G.Dart) (r v : Fin n) : N.G.Dart :=
  if h : N.G.Adj v (N.parN r v) then ⟨(v, N.parN r v), h⟩ else d₀

theorem upN_of_ne (hG : N.G.Connected) (d₀ : N.G.Dart) {r v : Fin n} (hv : v ≠ r) :
    N.upN d₀ r v = ⟨(v, N.parN r v), N.parN_adj hG hv⟩ := by
  unfold upN
  rw [dif_pos (N.parN_adj hG hv)]

/-- **The tree of shortest walks.** -/
noncomputable def treeN (hG : N.G.Connected) (r : Fin n) (d₀ : N.G.Dart) :
    N.toRot.RootedTree (Fin n) where
  vert d := d.fst
  vert_eq_iff d d' := N.tail_eq_iff.symm.trans (N.toRot.tail_eq_iff d d')
  root := r
  dep := N.G.dist r
  dep_root := SimpleGraph.dist_self
  up := N.upN d₀ r
  vert_up v hv := by rw [N.upN_of_ne hG d₀ hv]
  dep_par v hv := by
    rw [N.upN_of_ne hG d₀ hv]
    exact N.parN_dist hG hv

variable (hG : N.G.Connected) (r : Fin n) (d₀ : N.G.Dart)

theorem treeN_vertM (z : N.G.Dart × Bool) : (N.treeN hG r d₀).vertM z = z.1.fst := rfl

theorem treeN_root : (N.treeN hG r d₀).root = r := rfl

theorem treeN_dep (v : Fin n) : (N.treeN hG r d₀).dep v = N.G.dist r v := rfl

variable {r}

theorem treeN_c1_iff {u : Fin n} (hu : u ≠ r) (z : N.G.Dart × Bool) :
    z = (N.treeN hG r d₀).c1 u ↔ z.1.fst = u ∧ z.1.snd = N.parN r u ∧ z.2 = true := by
  have hc : (N.treeN hG r d₀).c1 u = (⟨(u, N.parN r u), N.parN_adj hG hu⟩, true) :=
    congrArg (fun d => (d, true)) (N.upN_of_ne hG d₀ hu)
  rw [hc]
  constructor
  · rintro rfl
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    exact Prod.ext (SimpleGraph.Dart.ext _ _ (Prod.ext h1 h2)) h3

theorem treeN_r0_iff {u : Fin n} (hu : u ≠ r) (z : N.G.Dart × Bool) :
    z = (N.treeN hG r d₀).r0 u ↔ z.1.fst = u ∧ z.1.snd = N.parN r u ∧ z.2 = false := by
  have hc : (N.treeN hG r d₀).r0 u = (⟨(u, N.parN r u), N.parN_adj hG hu⟩, false) :=
    congrArg (fun d => (d, false)) (N.upN_of_ne hG d₀ hu)
  rw [hc]
  constructor
  · rintro rfl
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    exact Prod.ext (SimpleGraph.Dart.ext _ _ (Prod.ext h1 h2)) h3

theorem treeN_c0_iff {u : Fin n} (hu : u ≠ r) (z : N.G.Dart × Bool) :
    z = (N.treeN hG r d₀).c0 u ↔ z.1.fst = N.parN r u ∧ z.1.snd = u ∧ z.2 = false := by
  have hc : (N.treeN hG r d₀).c0 u =
      ((⟨(u, N.parN r u), N.parN_adj hG hu⟩ : N.G.Dart).symm, false) :=
    congrArg (fun d => (SimpleGraph.Dart.symm d, false)) (N.upN_of_ne hG d₀ hu)
  rw [hc]
  constructor
  · rintro rfl
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    exact Prod.ext (SimpleGraph.Dart.ext _ _ (Prod.ext h1 h2)) h3

/-- A dart from a node to a child is the first rail of the child. -/
theorem isC0_iff {z : N.G.Dart × Bool} :
    (N.treeN hG r d₀).IsC0 z ↔ z.2 = false ∧ N.parN r z.1.snd = z.1.fst := by
  constructor
  · rintro ⟨u, hu, hz⟩
    obtain ⟨h1, h2, h3⟩ := (N.treeN_c0_iff hG d₀ hu z).1 hz
    exact ⟨h3, by rw [h2]; exact h1.symm⟩
  · rintro ⟨h1, h2⟩
    have hne : z.1.snd ≠ r := by
      intro e
      have h3 := z.1.adj
      rw [← h2, e, N.parN_root] at h3
      exact N.G.ne_of_adj h3 rfl
    exact ⟨z.1.snd, hne, (N.treeN_c0_iff hG d₀ hne z).2 ⟨h2.symm, rfl, h1⟩⟩

/-- A name of a face of the doubled map, from names of the faces of the map. -/
def fidN (id : N.G.Dart → ℕ) (z : N.G.Dart × Bool) : ℕ :=
  if z.2 then Nat.pair 0 (id z.1)
  else Nat.pair 1 (min (N.codeN (z.1, false)) (N.codeN (z.1.symm, false)))

/-- **Names of the faces of the doubled map.** -/
theorem fid_iff {id : N.G.Dart → ℕ} (hid : ∀ d d', id d = id d' ↔ N.toRot.faceOf d = N.toRot.faceOf d')
    (x y : N.G.Dart × Bool) : N.fidN id x = N.fidN id y ↔ fconnect N.toRot.double.facePerm x y := by
  have hface : ∀ (d d' : N.G.Dart), fconnect N.toRot.facePerm d d' ↔
      fconnect N.toRot.double.facePerm (d, true) (d', true) := fun d d' => by
    have hit : ∀ k, (⇑N.toRot.double.facePerm)^[k] (d, true) = ((⇑N.toRot.facePerm)^[k] d, true) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]; rfl
    constructor
    · intro h
      obtain ⟨k, rfl⟩ := fconnect_iff_iterate.1 h
      exact fconnect_iff_iterate.2 ⟨k, hit k⟩
    · intro h
      obtain ⟨k, hk⟩ := fconnect_iff_iterate.1 h
      rw [hit] at hk
      exact fconnect_iff_iterate.2 ⟨k, congrArg Prod.fst hk⟩
  obtain ⟨d, _ | _⟩ := x <;> obtain ⟨d', _ | _⟩ := y
  · show Nat.pair 1 _ = Nat.pair 1 _ ↔ _
    rw [Nat.pair_eq_pair]
    have hc := N.codeN_inj
    constructor
    · rintro ⟨-, h⟩
      have hx : d' = d ∨ d' = d.symm := by
        rcases min_choice (N.codeN (d, false)) (N.codeN (d.symm, false)) with h1 | h1 <;>
          rcases min_choice (N.codeN (d', false)) (N.codeN (d'.symm, false)) with h2 | h2 <;>
            rw [h1, h2] at h
        · exact Or.inl (congrArg Prod.fst (hc h)).symm
        · have := congrArg Prod.fst (hc h)
          exact Or.inr (by rw [show d = d'.symm from this, SimpleGraph.Dart.symm_symm])
        · exact Or.inr (congrArg Prod.fst (hc h)).symm
        · have : d.symm = d'.symm := congrArg Prod.fst (hc h)
          exact Or.inl (N.toRot.rev_injective this).symm
      rcases hx with rfl | rfl
      · exact connect_refl _
      · exact fconnect1 _ _
    · intro h
      refine ⟨rfl, ?_⟩
      rcases RotSystem.RootedTree.fconnect_digon h with h1 | h1
      · have : d' = d := congrArg Prod.fst h1
        rw [this]
      · have : d' = d.symm := congrArg Prod.fst h1
        rw [this, SimpleGraph.Dart.symm_symm, min_comm]
  · constructor
    · intro h
      have := (Nat.pair_eq_pair.1 h).1
      omega
    · intro h
      have := RotSystem.RootedTree.snd_of_fconnect_face h
      simp at this
  · constructor
    · intro h
      have := (Nat.pair_eq_pair.1 h).1
      omega
    · intro h
      have := RotSystem.RootedTree.snd_of_fconnect_face h
      simp at this
  · show Nat.pair 0 (id d) = Nat.pair 0 (id d') ↔ _
    rw [Nat.pair_eq_pair, ← hface]
    constructor
    · rintro ⟨-, h⟩
      exact (N.toRot.faceOf_eq_iff d d').1 ((hid d d').1 h)
    · intro h
      exact ⟨rfl, (hid d d').2 ((N.toRot.faceOf_eq_iff d d').2 h)⟩

/-- The corners of a level at a node. -/
noncomputable def cornersAt (v : Fin n) (Γ : Finset (N.G.Dart × Bool)) : Finset (Fin n × Bool) :=
  (Γ.filter fun z => z.1.fst = v).image N.locN

theorem mem_cornersAt {v : Fin n} {Γ : Finset (N.G.Dart × Bool)} {z : N.G.Dart × Bool}
    (hz : z.1.fst = v) : N.locN z ∈ N.cornersAt v Γ ↔ z ∈ Γ := by
  unfold cornersAt
  constructor
  · intro h
    obtain ⟨y, hy, e⟩ := Finset.mem_image.1 h
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hy
    rwa [← N.dart_ext (h2.trans hz.symm) e]
  · intro h
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨h, hz⟩)

variable {v : Fin n} {Γ : Finset (N.G.Dart × Bool)}

theorem loc_hyp {b : N.G.Dart × Bool}
    (hbv : b.1.fst = v) (x : N.G.Dart × Bool) (hx : fconnect N.toRot.double.rot b x) :
    N.locN (N.toRot.double.rot x) = rotV (N.rotList v) (N.locN x) := by
  rw [N.loc_rot, N.fst_of_fconnect hx, hbv]

theorem loc_inj {b z : N.G.Dart × Bool} (hbv : b.1.fst = v) (hz : z.1.fst = v) (x : N.G.Dart × Bool)
    (hx : fconnect N.toRot.double.rot b x) (e : N.locN x = N.locN z) : x = z :=
  N.dart_ext (by rw [N.fst_of_fconnect hx, hbv, hz]) e

theorem loc_mem {b : N.G.Dart × Bool} (hbv : b.1.fst = v) (x : N.G.Dart × Bool)
    (hx : fconnect N.toRot.double.rot b x) : x ∈ Γ ↔ N.locN x ∈ N.cornersAt v Γ :=
  (N.mem_cornersAt (by rw [N.fst_of_fconnect hx, hbv])).symm

/-- **The previous corner at a node.** -/
theorem loc_nodeReturn_inv {h : N.G.Dart × Bool} (hv : h.1.fst = v) (hm : h ∈ Γ) :
    N.locN ((N.toRot.double.nodeReturn Γ)⁻¹ h) =
      (firstReturn (rotV (N.rotList v)) (N.cornersAt v Γ))⁻¹ (N.locN h) :=
  firstReturn_inv_transport (b := h) (N.loc_hyp hv) (N.loc_mem hv) (connect_refl _) hm

theorem fst_nodeReturn_inv (h : N.G.Dart × Bool) :
    ((N.toRot.double.nodeReturn Γ)⁻¹ h).1.fst = h.1.fst := by
  have he : N.toRot.double.nodeReturn Γ ((N.toRot.double.nodeReturn Γ)⁻¹ h) = h :=
    perm_apply_inv_self _ _
  have h1 := fconnect_firstReturn N.toRot.double.rot Γ ((N.toRot.double.nodeReturn Γ)⁻¹ h)
  have h2 : firstReturn N.toRot.double.rot Γ ((N.toRot.double.nodeReturn Γ)⁻¹ h) = h := he
  rw [h2] at h1
  exact (N.fst_of_fconnect h1).symm

/-- **Sectors at a node.** Two darts at a node lie in one sector of a level if and only if the trails along the
rotation at the node end at the same corner. -/
theorem sec_iff (t : N.toRot.RootedTree (Fin n)) (ht : ∀ z, t.vertM z = z.1.fst)
    {x y : N.G.Dart × Bool} (hx : x.1.fst = v) (hy : y.1.fst = v) :
    (N.toRot.double.split Γ).tail x = (N.toRot.double.split Γ).tail y ↔
      secOf (rotV (N.rotList v)) (N.cornersAt v Γ) (N.locN x) =
        secOf (rotV (N.rotList v)) (N.cornersAt v Γ) (N.locN y) := by
  have hno : ∀ c', c' ∈ N.cornersAt v Γ → ¬ t.NP Γ v := fun c' hc' hn => by
    obtain ⟨z, hz, -⟩ := Finset.mem_image.1 hc'
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hz
    exact hn z h1 (by rw [ht, h2])
  by_cases hn : t.NP Γ v
  · have hxv : t.vertM x = v := (ht x).trans hx
    have hyv : t.vertM y = v := (ht y).trans hy
    have h0 : ∀ w : Fin n × Bool, secOf (rotV (N.rotList v)) (N.cornersAt v Γ) w = none := fun w =>
      secOf_of_not fun c hc => hno c hc.mem hn
    rw [h0, h0]
    exact ⟨fun _ => rfl, fun _ => hn.tail_eq hxv hyv⟩
  · have hex : ∃ g ∈ Γ, g.1.fst = v := by
      by_contra hne
      refine hn fun z hz e => hne ⟨z, hz, ?_⟩
      rw [← ht z]
      exact e
    obtain ⟨g, hg, hgv⟩ := hex
    have hcon : ∀ {w : N.G.Dart × Bool}, w.1.fst = v → fconnect N.toRot.double.rot w g := fun {w} hw =>
      (t.vertM_eq_iff _ _).1 (by rw [ht, ht, hw, hgv])
    obtain ⟨cx, hcx⟩ := exists_trail hg (hcon hx)
    obtain ⟨cy, hcy⟩ := exists_trail hg (hcon hy)
    have hsx := secOf_of_trail (trail_transport (N.loc_hyp hx) (N.loc_mem hx) hcx (connect_refl _))
    have hsy := secOf_of_trail (trail_transport (N.loc_hyp hy) (N.loc_mem hy) hcy (connect_refl _))
    have hcxv : cx.1.fst = v := by
      rw [N.fst_of_fconnect hcx.to_fconnect, hx]
    have hcyv : cy.1.fst = v := by
      rw [N.fst_of_fconnect hcy.to_fconnect, hy]
    rw [hsx, hsy, RotSystem.RootedTree.split_tail_of_trail hcx, RotSystem.RootedTree.split_tail_of_trail hcy]
    constructor
    · intro h
      have h1 : fconnect (N.toRot.double.split Γ).rot cx cy := ((N.toRot.double.split Γ).tail_eq_iff _ _).1 h
      have h2 := (fconnect_firstReturn_iff (N.toRot.double.split Γ).rot hcx.mem hcy.mem).2 h1
      have h3 : firstReturn (N.toRot.double.split Γ).rot Γ = 1 := N.toRot.double.nodeReturn_split Γ
      rw [h3] at h2
      have h4 : (1 : Equiv.Perm (N.G.Dart × Bool)) cx = cx := rfl
      rw [eq_of_fconnect_of_fixed h4 h2]
    · intro h
      have h1 : N.locN cx = N.locN cy := Option.some.inj h
      rw [N.dart_ext (hcxv.trans hcyv.symm) h1]

end Net

end Congest

end SsspFlow
