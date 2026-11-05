import SsspFlow.Disks
import SsspFlow.LemmaVChain

/-!
# The bags of a sequence of levels

The components of the split at a level `Γ` of the doubled map are the bags of this level. This file
counts their corners, shows that two corners of one face of the map that are not digon corners lie in
different bags (`not_same_of_face`), and bounds the hop diameter of a bag by its number of corners and
the depth of the tree (`bag_diam`). A sequence of levels with balanced cuts ends after logarithmically
many steps (`Decomp.final`) and gives a hierarchy of bags (`Decomp.hierarchy`) with short chains, few
hubs, small diameter and low congestion (`Decomp.chain_iff`, `Decomp.hub_card`, `Decomp.span`,
`Decomp.congestion`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal

namespace SsspFlow

open FourColor

/-! ### Walks of bounded length -/

section Reach

variable {V : Type*}

/-- There is a walk of at most `n` arcs from `a` to `b`. -/
def ReachLE (adj : V → V → Prop) (n : ℕ) (a b : V) : Prop :=
  ∃ p : Walk adj a b, p.support.length ≤ n + 1

variable {adj : V → V → Prop}

theorem Walk.support_append_length {a b c : V} (p : Walk adj a b) (q : Walk adj b c) :
    (p.append q).support.length + 1 = p.support.length + q.support.length := by
  induction p with
  | nil a =>
    simp only [Walk.append, Walk.support_nil, List.length_singleton]
    omega
  | cons e p ih =>
    simp only [Walk.append, Walk.support_cons, List.length_cons]
    have := ih q
    omega

theorem ReachLE.refl (a : V) : ReachLE adj 0 a a := ⟨Walk.nil a, by simp⟩

theorem ReachLE.mono_adj {adj' : V → V → Prop} (h : ∀ a b, adj a b → adj' a b) {n : ℕ} {a b : V}
    (H : ReachLE adj n a b) : ReachLE adj' n a b := by
  obtain ⟨p, hp⟩ := H
  have key : ∀ {a b : V} (p : Walk adj a b), ∃ q : Walk adj' a b, q.support = p.support := by
    intro a b p
    induction p with
    | nil a => exact ⟨Walk.nil a, rfl⟩
    | cons e p ih =>
      obtain ⟨q, hq⟩ := ih
      exact ⟨Walk.cons (h _ _ e) q, by simp [hq]⟩
  obtain ⟨q, hq⟩ := key p
  exact ⟨q, by rw [hq]; exact hp⟩

theorem ReachLE.mono {n m : ℕ} {a b : V} (h : ReachLE adj n a b) (hnm : n ≤ m) : ReachLE adj m a b := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, by omega⟩

theorem ReachLE.trans {n m : ℕ} {a b c : V} (h : ReachLE adj n a b) (h' : ReachLE adj m b c) :
    ReachLE adj (n + m) a c := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := h'
  have := Walk.support_append_length p q
  exact ⟨p.append q, by omega⟩

theorem ReachLE.of_adj {a b : V} (h : adj a b) : ReachLE adj 1 a b :=
  ⟨Walk.cons h (Walk.nil b), by simp⟩

theorem ReachLE.symm (hs : ∀ a b, adj a b → adj b a) {n : ℕ} {a b : V} (h : ReachLE adj n a b) :
    ReachLE adj n b a := by
  obtain ⟨p, hp⟩ := h
  induction p generalizing n with
  | nil a => exact ⟨Walk.nil a, hp⟩
  | @cons a m c e p ih =>
    simp only [Walk.support_cons, List.length_cons] at hp
    have h1 := ih (n := n - 1) (by omega)
    have h2 : n - 1 + 1 = n := by
      have := p.start_mem
      have : 0 < p.support.length := List.length_pos_of_mem this
      omega
    exact h2 ▸ h1.trans (ReachLE.of_adj (hs _ _ e))

/-- **Centers.** In a connected graph, in which every vertex is within `r` of one of finitely many
centers, the diameter is at most the number of centers times `2 r + 1`. -/
theorem centers_diam (hs : ∀ a b, adj a b → adj b a) {S : Set V}
    (hconn : ∀ a ∈ S, ∀ b ∈ S, Relation.ReflTransGen adj a b)
    (hS : ∀ a b, adj a b → a ∈ S ∧ b ∈ S) {K : Finset V} {r : ℕ}
    (hK : ∀ a ∈ S, ∃ c ∈ K, c ∈ S ∧ ReachLE adj r a c) {a b : V} (ha : a ∈ S) (hb : b ∈ S) :
    ReachLE adj (K.card * (2 * r + 1)) a b := by
  classical
  choose! cen hcenK hcenS hcen using hK
  -- the graph on the centers
  let G : SimpleGraph {c // c ∈ K} :=
    { Adj := fun x y => x ≠ y ∧ ReachLE adj (2 * r + 1) x.1 y.1
      symm := ⟨fun x y h => ⟨h.1.symm, ReachLE.symm hs h.2⟩⟩
      loopless := ⟨fun x h => h.1 rfl⟩ }
  have hstep : ∀ x y, adj x y → x ∈ S → y ∈ S →
      ReachLE adj (2 * r + 1) (cen x) (cen y) := by
    intro x y hxy hx hy
    have h1 := ReachLE.symm hs (hcen x hx)
    have h2 := hcen y hy
    exact (h1.trans (ReachLE.of_adj hxy)).trans h2 |>.mono (by omega)
  have hreach : ∀ x (hx : x ∈ S), ∀ y, Relation.ReflTransGen adj x y → ∀ (hy : y ∈ S),
      G.Reachable ⟨cen x, hcenK x hx⟩ ⟨cen y, hcenK y hy⟩ := by
    intro x hx y h
    induction h with
    | refl => exact fun _ => SimpleGraph.Reachable.refl _
    | @tail y z _ hyz ih =>
      intro hz
      have hy := (hS _ _ hyz).1
      refine (ih hy).trans ?_
      by_cases e : cen y = cen z
      · have : (⟨cen y, hcenK y hy⟩ : {c // c ∈ K}) = ⟨cen z, hcenK z hz⟩ := Subtype.ext e
        rw [this]
      · exact SimpleGraph.Adj.reachable ⟨fun h => e (congrArg Subtype.val h), hstep y z hyz hy hz⟩
  obtain ⟨wk⟩ := hreach a ha b (hconn a ha b hb) hb
  have hlen : wk.toPath.1.length < Fintype.card {c // c ∈ K} := wk.toPath.2.length_lt
  have hcard : Fintype.card {c // c ∈ K} = K.card := Fintype.card_coe K
  have hwalk : ∀ {x y : {c // c ∈ K}} (w : G.Walk x y),
      ReachLE adj (w.length * (2 * r + 1)) x.1 y.1 := by
    intro x y w
    induction w with
    | nil => simpa using ReachLE.refl _
    | @cons u v w huv _ ih =>
      have h1 := huv.2.trans ih
      rw [SimpleGraph.Walk.length_cons]
      exact h1.mono (by ring_nf; omega)
  have h3 := hwalk wk.toPath.1
  have h4 := ((hcen a ha).trans h3).trans (ReachLE.symm hs (hcen b hb))
  refine h4.mono ?_
  have h5 : wk.toPath.1.length + 1 ≤ K.card := by omega
  calc r + wk.toPath.1.length * (2 * r + 1) + r ≤ (wk.toPath.1.length + 1) * (2 * r + 1) := by
        ring_nf; omega
    _ ≤ K.card * (2 * r + 1) := Nat.mul_le_mul_right _ h5

end Reach

/-! ### Positions on an orbit -/

section Orbit

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- A first point exists on an orbit that meets `S`. -/
theorem exists_trail {f : Equiv.Perm D} {S : Finset D} {z g : D} (hg : g ∈ S) (h : fconnect f z g) :
    ∃ c, Trail f S z c := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨g, Trail.here hg⟩
  | @head a c hac _ ih =>
    obtain rfl : f a = c := hac
    obtain ⟨c', hc'⟩ := ih
    by_cases ha : a ∈ S
    · exact ⟨a, Trail.here ha⟩
    · exact ⟨c', Trail.step ha hc'⟩

/-- The position on an orbit is smaller than the size of any set that contains the orbit. -/
theorem pos_lt_card (f : Equiv.Perm D) {x y : D} (hy : fconnect f x y) {S : Finset D}
    (hS : ∀ z, fconnect f x z → z ∈ S) : pos f x y < S.card := by
  have hmap : ∀ i ∈ Finset.range (pos f x y + 1), (⇑f)^[i] x ∈ S :=
    fun i _ => hS _ (fconnect_iterate _ _ _)
  have hinj : Set.InjOn (fun i => (⇑f)^[i] x) (Finset.range (pos f x y + 1) : Set ℕ) := by
    have key : ∀ i j, i < j → j ≤ pos f x y → (⇑f)^[i] x ≠ (⇑f)^[j] x := by
      intro i j hij hj e
      have h1 : (⇑f)^[j - i] x = x := by
        apply f.injective.iterate i
        rw [← Function.iterate_add_apply, show i + (j - i) = j by omega]
        exact e.symm
      have h2 : (⇑f)^[pos f x y - (j - i)] x = y := by
        calc (⇑f)^[pos f x y - (j - i)] x = (⇑f)^[pos f x y - (j - i)] ((⇑f)^[j - i] x) := by rw [h1]
          _ = (⇑f)^[pos f x y - (j - i) + (j - i)] x := (Function.iterate_add_apply _ _ _ _).symm
          _ = (⇑f)^[pos f x y] x := by rw [show pos f x y - (j - i) + (j - i) = pos f x y by omega]
          _ = y := pos_spec hy
      have h3 := pos_le h2
      omega
    intro i hi j hj e
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with h | h | h
    · exact (key i j h (by omega) e).elim
    · exact h
    · exact (key j i h (by omega) e.symm).elim
  have := Finset.card_le_card_of_injOn _ hmap hinj
  simp only [Finset.card_range] at this
  omega

theorem firstReturn_singleton (f : Equiv.Perm D) (x : D) : firstReturn f {x} = 1 := by
  ext z
  by_cases hz : z = x
  · subst hz
    obtain ⟨k, _, h, hk, _⟩ := firstReturn_spec f (Finset.mem_singleton_self z)
    rw [h]
    simpa using hk
  · rw [firstReturn_of_not_mem f (by simpa using hz)]
    rfl

end Orbit

namespace RotSystem

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- A dart lies in one component of the split with the first point of `Γ` on its rotation. -/
theorem gcomp_split_of_trail (R : RotSystem D) {Γ : Finset D} {y z : D} (h : Trail R.rot Γ y z) :
    (R.split Γ).toHypermap.gcomp y z := by
  induction h with
  | here _ => exact connect_refl _
  | step hn _ ih =>
    exact connect_trans (connect_of_rel (Or.inr (Or.inl (R.split_rot_of_not_mem hn)))) ih

theorem cone_singleton_facePerm (R : RotSystem D) (x : D) : (R.cone {x}).facePerm = R.facePerm := by
  rw [cone_facePerm]
  show (firstReturn R.facePerm {x})⁻¹ * R.facePerm = R.facePerm
  rw [firstReturn_singleton]
  simp

variable {R : RotSystem D}

/-- Two darts lie in one bag of the level `Γ`. -/
abbrev Same (R : RotSystem D) (Γ : Finset (D × Bool)) (u u' : D × Bool) : Prop :=
  (R.double.split Γ).toHypermap.gcomp u u'

theorem Same.symm {Γ : Finset (D × Bool)} {u u' : D × Bool} (h : R.Same Γ u u') : R.Same Γ u' u :=
  (R.double.split Γ).toHypermap.glinkC _ _ h

theorem Same.trans {Γ : Finset (D × Bool)} {u u' u'' : D × Bool} (h : R.Same Γ u u')
    (h' : R.Same Γ u' u'') : R.Same Γ u u'' := connect_trans h h'

theorem same_rev (Γ : Finset (D × Bool)) (u : D × Bool) : R.Same Γ u (R.double.rev u) :=
  connect_of_rel (Or.inl rfl)

variable (R) in
open Classical in
/-- The corners of the level `Γ` in the bag of `u`. -/
noncomputable def portsOf (Γ : Finset (D × Bool)) (u : D × Bool) : Finset (D × Bool) :=
  Γ.filter (R.Same Γ u)

variable (R) in
open Classical in
/-- The corners of the level `Γ` in the bag of `u` that are not digon corners. -/
noncomputable def gapsOf (Γ : Finset (D × Bool)) (u : D × Bool) : Finset (D × Bool) :=
  Γ.filter fun z => z.2 = true ∧ R.Same Γ u z

theorem mem_portsOf {Γ : Finset (D × Bool)} {u z : D × Bool} :
    z ∈ R.portsOf Γ u ↔ z ∈ Γ ∧ R.Same Γ u z := by
  simp [portsOf]

theorem mem_gapsOf {Γ : Finset (D × Bool)} {u z : D × Bool} :
    z ∈ R.gapsOf Γ u ↔ z ∈ Γ ∧ z.2 = true ∧ R.Same Γ u z := by
  simp [gapsOf]

namespace RootedTree

variable {V : Type*} [Fintype V] [DecidableEq V] {t : R.RootedTree V}

section Bag

variable {Γ Γ' : Finset (D × Bool)}

/-- **Sectors.** A dart at a vertex with a corner lies in one bag with a corner at this vertex. -/
theorem exists_corner_of_not_NP {u : D × Bool} (h : ¬ t.NP Γ (t.vertM u)) :
    ∃ g ∈ Γ, t.vertM g = t.vertM u ∧ R.Same Γ u g := by
  have h' : ∃ g ∈ Γ, t.vertM g = t.vertM u := by
    by_contra hn
    push Not at hn
    exact h hn
  obtain ⟨g, hg, hgu⟩ := h'
  obtain ⟨c, hc⟩ := exists_trail hg ((t.vertM_eq_iff u g).1 hgu.symm)
  exact ⟨c, hc.mem, ((t.vertM_eq_iff _ _).2 hc.to_fconnect).symm, R.double.gcomp_split_of_trail hc⟩

/-- **One section.** Two corners of a level on one face of the map, which are not digon corners, lie in
different bags. -/
theorem not_same_of_face {w₀ : D × Bool} (hL₀ : t.IsLevel {w₀}) (hL : t.IsLevel Γ) (h₀ : w₀ ∈ Γ)
    (hR : R.Planar) (hc : R.Connected) {g g' : D × Bool} (hg : g ∈ Γ) (hg' : g' ∈ Γ)
    (h1 : g.2 = true) (h2 : g'.2 = true) (hne : g ≠ g') (hf : fconnect R.double.facePerm g g') :
    ¬ R.Same Γ g g' := by
  have hf' : fconnect (⇑(R.double.cone {w₀}).facePerm⁻¹) g g' := by
    rw [R.double.cone_singleton_facePerm, fconnect_inv_iff]
    exact hf
  refine not_gcomp_of_cut hL₀ hR hc hne hf' hL hg hg' (Finset.singleton_subset_iff.2 h₀) ?_ ?_
  · rintro ⟨v, _, rfl⟩
    simp [c0] at h1
  · rintro ⟨v, _, rfl⟩
    simp [c0] at h2

variable (t) in
/-- The arcs of a bag: both ends of an edge copy in the bag. -/
def arcOf (Γ : Finset (D × Bool)) (u : D × Bool) (a b : V) : Prop :=
  ∃ z, R.Same Γ u z ∧ t.vertM z = a ∧ t.vertM (R.double.rev z) = b

variable (t) in
/-- The vertices of a bag. -/
def bagOf (Γ : Finset (D × Bool)) (u : D × Bool) : Set V := {a | ∃ z, R.Same Γ u z ∧ t.vertM z = a}

theorem arcOf_symm (u : D × Bool) (a b : V) (h : t.arcOf Γ u a b) : t.arcOf Γ u b a := by
  obtain ⟨z, hz, rfl, rfl⟩ := h
  exact ⟨R.double.rev z, hz.trans (same_rev Γ z), rfl, by rw [R.double.rev_rev]⟩

theorem arcOf_bag (u : D × Bool) (a b : V) (h : t.arcOf Γ u a b) :
    a ∈ t.bagOf Γ u ∧ b ∈ t.bagOf Γ u := by
  obtain ⟨z, hz, rfl, rfl⟩ := h
  exact ⟨⟨z, hz, rfl⟩, ⟨_, hz.trans (same_rev Γ z), rfl⟩⟩

/-- A bag is connected by its arcs. -/
theorem reach_of_same {u z z' : D × Bool} (hz : R.Same Γ u z) (h : R.Same Γ z z') :
    Relation.ReflTransGen (t.arcOf Γ u) (t.vertM z) (t.vertM z') := by
  have hsym : ∀ {a b : V}, Relation.ReflTransGen (t.arcOf Γ u) a b →
      Relation.ReflTransGen (t.arcOf Γ u) b a := by
    intro a b h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact (Relation.ReflTransGen.single (arcOf_symm _ _ _ hbc)).trans ih
  have h' := (R.double.gcomp_split_iff Γ z z').1 h
  clear h
  revert hz
  induction h' with
  | rel a b hab =>
    intro ha
    rcases hab with rfl | ⟨_, rfl⟩
    · exact Relation.ReflTransGen.single ⟨a, ha, rfl, rfl⟩
    · rw [t.vertM_rot]
  | refl a => exact fun _ => Relation.ReflTransGen.refl
  | symm a b hab ih =>
    intro hb
    exact hsym (ih (hb.trans ((R.double.gcomp_split_iff Γ b a).2 (Relation.EqvGen.symm _ _ hab))))
  | trans a b c hab _ ih1 ih2 =>
    intro ha
    exact (ih1 ha).trans (ih2 (ha.trans ((R.double.gcomp_split_iff Γ a b).2 hab)))

/-- From a dart in a bag, a walk up the tree in the bag reaches a corner of the bag. -/
theorem up_walk {u : D × Bool} (hL : t.IsLevel Γ) (n : ℕ) :
    ∀ z, t.dep (t.vertM z) = n → R.Same Γ u z →
      ∃ g ∈ Γ, R.Same Γ u g ∧ ReachLE (t.arcOf Γ u) n (t.vertM z) (t.vertM g) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z hn hz
    by_cases hv : t.NP Γ (t.vertM z)
    · have hne := hv.ne_root hL
      have h1 : R.Same Γ z (t.c1 (t.vertM z)) := hv.gcomp rfl (t.vertM_c1 hne)
      have h2 : R.Same Γ z (t.c0 (t.vertM z)) := (hv.gcomp_rails hL rfl).2
      have harc : t.arcOf Γ u (t.vertM z) (t.par (t.vertM z)) :=
        ⟨t.c1 (t.vertM z), hz.trans h1, t.vertM_c1 hne, rfl⟩
      obtain ⟨g, hg, hug, hr⟩ := ih (t.dep (t.vertM (t.c0 (t.vertM z))))
        (by rw [t.vertM_c0, ← hn]; exact t.dep_par_lt hne) _ rfl (hz.trans h2)
      refine ⟨g, hg, hug, ((ReachLE.of_adj harc).trans hr).mono ?_⟩
      have := t.dep_par_lt hne
      rw [t.vertM_c0]
      omega
    · obtain ⟨g, hg, hgz, hs⟩ := exists_corner_of_not_NP hv
      refine ⟨g, hg, hz.trans hs, ?_⟩
      rw [hgz]
      exact (ReachLE.refl _).mono (Nat.zero_le _)

/-- From a digon corner, the first return of the boundary of the disk moves along the edge. -/
theorem psi_digon (hL : t.IsLevel Γ) {g : D × Bool} (hg : g ∈ Γ) (h0 : g.2 = false) :
    t.vertM (R.double.psi Γ g) = t.vertM (R.double.rev g) := by
  obtain ⟨d, b⟩ := g
  obtain rfl : b = false := h0
  have hb : R.double.faceReturn Γ (d, false) = (R.rev d, false) :=
    firstReturn_eq_of_trail _ hg (Trail.here (hL.pairs d hg))
  have ha : fconnect R.double.rot (R.rev d, false) (R.double.nodeReturn Γ (R.rev d, false)) :=
    fconnect_firstReturn _ _ _
  show t.vertM (R.double.nodeReturn Γ (R.double.faceReturn Γ (d, false))) = _
  rw [hb, ← (t.vertM_eq_iff _ _).2 ha]
  rfl

/-- **The diameter of a bag.** -/
theorem bag_diam (hL : t.IsLevel Γ) (hR : R.Planar) (hc : R.Connected) {u : D × Bool} {h J G : ℕ}
    (hdep : ∀ v, t.dep v ≤ h) (hJ : (R.portsOf Γ u).card ≤ J) (hG : (R.gapsOf Γ u).card ≤ G)
    {a b : V} (ha : a ∈ t.bagOf Γ u) (hb : b ∈ t.bagOf Γ u) :
    ReachLE (t.arcOf Γ u) ((G + 1) * (2 * (h + J) + 1)) a b := by
  classical
  have hMP := R.double_planar hR hc
  have hMc := R.double_connected hc
  have horb := (R.double.split_planar hMP hMc hL.nonempty hL.skel).2.2.2
  obtain ⟨g₀, hg₀, hug₀⟩ := R.double.split_meets hMc hL.nonempty u
  let T : Finset (D × Bool) := insert g₀ (R.gapsOf Γ u)
  have hTΓ : ∀ y ∈ T, y ∈ Γ ∧ R.Same Γ u y := by
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact ⟨hg₀, hug₀⟩
    · obtain ⟨h1, _, h3⟩ := mem_gapsOf.1 hy
      exact ⟨h1, h3⟩
  have hreach : ∀ a ∈ t.bagOf Γ u, ∃ c ∈ T.image t.vertM, c ∈ t.bagOf Γ u ∧
      ReachLE (t.arcOf Γ u) (h + J) a c := by
    rintro a ⟨z, hz, rfl⟩
    obtain ⟨g, hg, hug, hr1⟩ := up_walk (u := u) hL _ z rfl hz
    have hor : ∀ y, y ∈ Γ → R.Same Γ u y → fconnect (R.double.psi Γ) g y :=
      fun y hy huy => (horb g hg y hy).1 (hug.symm.trans huy)
    obtain ⟨y, hyT, hmin⟩ := T.exists_min_image (pos (R.double.psi Γ) g) ⟨g₀, Finset.mem_insert_self _ _⟩
    obtain ⟨hyΓ, huy⟩ := hTΓ y hyT
    have hgy := hor y hyΓ huy
    have hit : ∀ i, i ≤ pos (R.double.psi Γ) g y →
        (⇑(R.double.psi Γ))^[i] g ∈ Γ ∧ R.Same Γ u ((⇑(R.double.psi Γ))^[i] g) ∧
          ReachLE (t.arcOf Γ u) i (t.vertM g) (t.vertM ((⇑(R.double.psi Γ))^[i] g)) := by
      intro i
      induction i with
      | zero => exact fun _ => ⟨hg, hug, ReachLE.refl _⟩
      | succ i ih =>
        intro hi
        obtain ⟨h1, h2, h3⟩ := ih (by omega)
        rw [Function.iterate_succ_apply']
        have hm := ((R.double.fixesOff_psi Γ).mem_iff _).2 h1
        have hs : R.Same Γ ((⇑(R.double.psi Γ))^[i] g) (R.double.psi Γ ((⇑(R.double.psi Γ))^[i] g)) :=
          R.double.gcomp_split_of_fconnect_psi (fconnect1 _ _)
        refine ⟨hm, h2.trans hs, ?_⟩
        have hb0 : ((⇑(R.double.psi Γ))^[i] g).2 = false := by
          by_contra hne
          have htrue : ((⇑(R.double.psi Γ))^[i] g).2 = true := by simpa using hne
          have hmem : (⇑(R.double.psi Γ))^[i] g ∈ T :=
            Finset.mem_insert_of_mem (mem_gapsOf.2 ⟨h1, htrue, h2⟩)
          have h4 := hmin _ hmem
          have h5 : pos (R.double.psi Γ) g ((⇑(R.double.psi Γ))^[i] g) ≤ i := pos_le rfl
          omega
        have hd := psi_digon hL h1 hb0
        have harc : t.arcOf Γ u (t.vertM ((⇑(R.double.psi Γ))^[i] g))
            (t.vertM (R.double.psi Γ ((⇑(R.double.psi Γ))^[i] g))) :=
          ⟨_, h2, rfl, hd.symm⟩
        exact h3.trans (ReachLE.of_adj harc)
    obtain ⟨_, h2, h3⟩ := hit _ le_rfl
    rw [pos_spec hgy] at h2 h3
    have hposJ : pos (R.double.psi Γ) g y < (R.portsOf Γ u).card := by
      refine pos_lt_card _ hgy fun z hz' => mem_portsOf.2 ?_
      constructor
      · have := fconnect_iff_iterate.1 hz'
        obtain ⟨n, rfl⟩ := this
        have key : ∀ n, (⇑(R.double.psi Γ))^[n] g ∈ Γ := by
          intro n
          induction n with
          | zero => exact hg
          | succ n ih =>
            rw [Function.iterate_succ_apply']
            exact ((R.double.fixesOff_psi Γ).mem_iff _).2 ih
        exact key n
      · exact hug.trans (R.double.gcomp_split_of_fconnect_psi hz')
    refine ⟨t.vertM y, Finset.mem_image_of_mem _ hyT, ⟨y, huy, rfl⟩, (hr1.trans h3).mono ?_⟩
    have := hdep (t.vertM z)
    omega
  have hcard : (T.image t.vertM).card ≤ G + 1 := by
    calc (T.image t.vertM).card ≤ T.card := Finset.card_image_le
      _ ≤ (R.gapsOf Γ u).card + 1 := Finset.card_insert_le _ _
      _ ≤ G + 1 := by omega
  have hconn : ∀ a ∈ t.bagOf Γ u, ∀ b ∈ t.bagOf Γ u, Relation.ReflTransGen (t.arcOf Γ u) a b := by
    rintro a ⟨z, hz, rfl⟩ b ⟨z', hz', rfl⟩
    exact reach_of_same hz (hz.symm.trans hz')
  have := centers_diam (fun a b h => arcOf_symm u a b h) hconn (fun a b h => arcOf_bag u a b h)
    hreach ha hb
  exact this.mono (Nat.mul_le_mul_right _ hcard)

/-! ### Counting corners of the next level -/

open Classical in
/-- The corners of the next level in a bag of this level. -/
theorem card_filter_next (hL : t.IsLevel Γ) {C : Finset (D × Bool)} {h : ℕ} (hdep : ∀ v, t.dep v ≤ h)
    (u : D × Bool) (hC : (C.filter (fun c => R.Same Γ u c)).card ≤ 2) :
    ((t.next Γ C).filter (R.Same Γ u)).card ≤ (R.portsOf Γ u).card + (2 + 4 * h) := by
  let W := C.filter (fun c => R.Same Γ u c)
  have hsub : (t.next Γ C).filter (R.Same Γ u) ⊆
      R.portsOf Γ u ∪ W.biUnion fun c => insert c (t.railsUp Γ c) := by
    intro z hz
    obtain ⟨h1, h3⟩ := Finset.mem_filter.1 hz
    rcases mem_next.1 h1 with hzΓ | ⟨c, hc, hzc⟩
    · exact Finset.mem_union_left _ (mem_portsOf.2 ⟨hzΓ, h3⟩)
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨c, ?_, ?_⟩)
      · refine Finset.mem_filter.2 ⟨hc, ?_⟩
        rcases hzc with rfl | hzc
        · exact h3
        · exact h3.trans (Same.symm (gcomp_of_mem_railsUp hL hzc))
      · rcases hzc with rfl | hzc
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem hzc
  have hb : (W.biUnion fun c => insert c (t.railsUp Γ c)).card ≤ W.card * (1 + 2 * h) := by
    refine Finset.card_biUnion_le_card_mul _ _ _ fun c _ => ?_
    calc (insert c (t.railsUp Γ c)).card ≤ (t.railsUp Γ c).card + 1 := Finset.card_insert_le _ _
      _ ≤ 2 * t.dep (t.vertM c) + 1 := by have := card_railsUp_le hL c; omega
      _ ≤ 1 + 2 * h := by have := hdep (t.vertM c); omega
  have hW : W.card ≤ 2 := hC
  calc ((t.next Γ C).filter (R.Same Γ u)).card
      ≤ (R.portsOf Γ u ∪ W.biUnion fun c => insert c (t.railsUp Γ c)).card := Finset.card_le_card hsub
    _ ≤ (R.portsOf Γ u).card + (W.biUnion fun c => insert c (t.railsUp Γ c)).card :=
        Finset.card_union_le _ _
    _ ≤ (R.portsOf Γ u).card + W.card * (1 + 2 * h) := by omega
    _ ≤ (R.portsOf Γ u).card + 2 * (1 + 2 * h) := by
        have := Nat.mul_le_mul_right (1 + 2 * h) hW
        omega
    _ = (R.portsOf Γ u).card + (2 + 4 * h) := by ring

open Classical in
/-- The corners of a bag of the next level. -/
theorem card_portsOf_next (hL : t.IsLevel Γ) {C : Finset (D × Bool)} {h : ℕ} (hdep : ∀ v, t.dep v ≤ h)
    (u : D × Bool) (hC : (C.filter (fun c => R.Same Γ u c)).card ≤ 2) :
    (R.portsOf (t.next Γ C) u).card ≤ (R.portsOf Γ u).card + (2 + 4 * h) := by
  refine (Finset.card_le_card fun z hz => ?_).trans (card_filter_next hL hdep u hC)
  obtain ⟨h1, h2⟩ := mem_portsOf.1 hz
  exact Finset.mem_filter.2 ⟨h1, gcomp_split_mono (subset_next Γ C) h2⟩

/-- The digon corners are all that a walk up the tree adds. -/
theorem railsUp_snd {c g : D × Bool} (hg : g ∈ t.railsUp Γ c) : g.2 = false := by
  obtain ⟨w, _, _, rfl | rfl⟩ := mem_railsUp.1 hg <;> rfl

open Classical in
/-- The corners of a bag of the next level that are not digon corners. -/
theorem card_gapsOf_next {C : Finset (D × Bool)} (u : D × Bool)
    (hC : (C.filter (fun c => R.Same Γ u c)).card ≤ 2) :
    (R.gapsOf (t.next Γ C) u).card ≤ (R.gapsOf Γ u).card + 2 := by
  have hsub : R.gapsOf (t.next Γ C) u ⊆ R.gapsOf Γ u ∪ C.filter (fun c => R.Same Γ u c) := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := mem_gapsOf.1 hz
    have h4 : R.Same Γ u z := gcomp_split_mono (subset_next Γ C) h3
    rcases mem_next.1 h1 with hzΓ | ⟨c, hc, rfl | hzc⟩
    · exact Finset.mem_union_left _ (mem_gapsOf.2 ⟨hzΓ, h2, h4⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hc, h4⟩)
    · have := railsUp_snd hzc
      rw [h2] at this
      exact absurd this (by simp)
  calc (R.gapsOf (t.next Γ C) u).card
      ≤ (R.gapsOf Γ u ∪ C.filter (fun c => R.Same Γ u c)).card := Finset.card_le_card hsub
    _ ≤ (R.gapsOf Γ u).card + (C.filter (fun c => R.Same Γ u c)).card := Finset.card_union_le _ _
    _ ≤ (R.gapsOf Γ u).card + 2 := by omega

end Bag

/-! ### A sequence of levels -/

open Classical in
/-- One step of a decomposition: corners that cut each bag in a balanced way, at most two per bag. -/
structure IsCut (t : R.RootedTree V) (Γ C : Finset (D × Bool)) : Prop where
  pair : ∀ d, (d, false) ∈ C → (R.rev d, false) ∈ t.next Γ C
  two : ∀ u, (C.filter (fun c => R.Same Γ u c)).card ≤ 2
  balance : ∀ u, 0 < t.npOf Γ u → 4 * t.npOf (t.next Γ C) u + 2 ≤ 3 * t.npOf Γ u

/-- A decomposition: levels that start with one corner at the root, each one cut from the one before. -/
structure Decomp (t : R.RootedTree V) (w₀ : D × Bool) (Γ C : ℕ → Finset (D × Bool)) : Prop where
  root : t.vertM w₀ = t.root
  snd : w₀.2 = true
  zero : Γ 0 = {w₀}
  succ : ∀ d, Γ (d + 1) = t.next (Γ d) (C d)
  cut : ∀ d, t.IsCut (Γ d) (C d)

/-- The number of marked darts is at most twice the number of vertices. -/
theorem card_marks_le (Γ : Finset (D × Bool)) : (t.marks Γ).card ≤ 2 * Fintype.card V := by
  classical
  have hsub : t.marks Γ ⊆ Finset.univ.image t.c1 ∪ Finset.univ.image t.c0 := by
    intro z hz
    obtain ⟨v, _, rfl | rfl⟩ := t.mem_marks.1 hz
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ v))
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ v))
  calc (t.marks Γ).card ≤ (Finset.univ.image t.c1 ∪ Finset.univ.image t.c0).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ.image t.c1).card + (Finset.univ.image t.c0).card := Finset.card_union_le _ _
    _ ≤ Fintype.card V + Fintype.card V :=
        add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * Fintype.card V := by ring

namespace Decomp

variable {w₀ : D × Bool} {Γ C : ℕ → Finset (D × Bool)} (hD : t.Decomp w₀ Γ C)

include hD

theorem level₀ : t.IsLevel {w₀} where
  root_mem := ⟨w₀, Finset.mem_singleton_self _, hD.root⟩
  rails := fun z hz hr => by
    obtain rfl := Finset.mem_singleton.1 hz
    exact (hr hD.root).elim
  pairs := fun d hd => by
    obtain rfl := Finset.mem_singleton.1 hd
    simpa using hD.snd
  skel := fun x hx y hy => by
    obtain rfl := Finset.mem_singleton.1 hx
    obtain rfl := Finset.mem_singleton.1 hy
    exact connect_refl _

theorem level : ∀ d, t.IsLevel (Γ d)
  | 0 => by rw [hD.zero]; exact hD.level₀
  | d + 1 => by
    rw [hD.succ]
    exact (level d).next (hD.cut d).pair

theorem sub_succ (d : ℕ) : Γ d ⊆ Γ (d + 1) := by
  rw [hD.succ]
  exact subset_next _ _

theorem mono {d d' : ℕ} (h : d ≤ d') : Γ d ⊆ Γ d' := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans (hD.sub_succ _)

theorem w₀_mem (d : ℕ) : w₀ ∈ Γ d :=
  hD.mono (Nat.zero_le d) (by rw [hD.zero]; exact Finset.mem_singleton_self _)

theorem card_ports {h : ℕ} (hdep : ∀ v, t.dep v ≤ h) (d : ℕ) (u : D × Bool) :
    (R.portsOf (Γ d) u).card ≤ 1 + d * (2 + 4 * h) := by
  induction d with
  | zero =>
    have : R.portsOf (Γ 0) u ⊆ {w₀} := fun z hz => by
      have := (mem_portsOf.1 hz).1
      rwa [hD.zero] at this
    have := Finset.card_le_card this
    simpa using this
  | succ d ih =>
    rw [hD.succ]
    have := card_portsOf_next (hD.level d) hdep u ((hD.cut d).two u)
    have e : (d + 1) * (2 + 4 * h) = d * (2 + 4 * h) + (2 + 4 * h) := by ring
    omega

theorem card_gaps (d : ℕ) (u : D × Bool) : (R.gapsOf (Γ d) u).card ≤ 1 + 2 * d := by
  induction d with
  | zero =>
    have : R.gapsOf (Γ 0) u ⊆ {w₀} := fun z hz => by
      have := (mem_gapsOf.1 hz).1
      rwa [hD.zero] at this
    have := Finset.card_le_card this
    simpa using this
  | succ d ih =>
    rw [hD.succ]
    have := card_gapsOf_next (t := t) u ((hD.cut d).two u)
    omega

open Classical in
/-- The corners of the next level in a bag of this level. -/
theorem card_filter_succ {h : ℕ} (hdep : ∀ v, t.dep v ≤ h) (d : ℕ) (u : D × Bool) :
    ((Γ (d + 1)).filter (R.Same (Γ d) u)).card ≤ 1 + (d + 1) * (2 + 4 * h) := by
  rw [hD.succ]
  have h1 := card_filter_next (hD.level d) hdep u ((hD.cut d).two u)
  have h2 := hD.card_ports hdep d u
  have e : (d + 1) * (2 + 4 * h) = d * (2 + 4 * h) + (2 + 4 * h) := by ring
  refine le_trans ?_ (show (R.portsOf (Γ d) u).card + (2 + 4 * h) ≤ _ by omega)
  convert h1

theorem npOf_pow (d : ℕ) (u : D × Bool) :
    t.npOf (Γ d) u * 4 ^ d ≤ t.npOf (Γ 0) u * 3 ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hm := npOf_mono (t := t) (hD.sub_succ d) u
    rw [pow_succ, pow_succ]
    by_cases h0 : t.npOf (Γ d) u = 0
    · have : t.npOf (Γ (d + 1)) u = 0 := by omega
      rw [this]
      simp
    · have hb := (hD.cut d).balance u (Nat.pos_of_ne_zero h0)
      rw [← hD.succ] at hb
      have h1 : t.npOf (Γ (d + 1)) u * 4 ≤ t.npOf (Γ d) u * 3 := by omega
      calc t.npOf (Γ (d + 1)) u * (4 ^ d * 4) = t.npOf (Γ (d + 1)) u * 4 * 4 ^ d := by ring
        _ ≤ t.npOf (Γ d) u * 3 * 4 ^ d := Nat.mul_le_mul_right _ h1
        _ = t.npOf (Γ d) u * 4 ^ d * 3 := by ring
        _ ≤ t.npOf (Γ 0) u * 3 ^ d * 3 := Nat.mul_le_mul_right _ ih
        _ = t.npOf (Γ 0) u * (3 ^ d * 3) := by ring

/-- After logarithmically many levels, no bag has a vertex without a corner. -/
theorem npOf_final (u : D × Bool) {k : ℕ} (hk : 2 * Fintype.card V < 2 ^ k) :
    t.npOf (Γ (3 * k)) u = 0 := by
  classical
  by_contra h0
  have h1 := hD.npOf_pow (3 * k) u
  have h2 : t.npOf (Γ 0) u ≤ 2 * Fintype.card V :=
    (Finset.card_filter_le _ _).trans (card_marks_le _)
  have h3 : 4 ^ (3 * k) ≤ 2 * Fintype.card V * 3 ^ (3 * k) := by
    calc 4 ^ (3 * k) ≤ t.npOf (Γ (3 * k)) u * 4 ^ (3 * k) :=
          Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero h0)
      _ ≤ t.npOf (Γ 0) u * 3 ^ (3 * k) := h1
      _ ≤ 2 * Fintype.card V * 3 ^ (3 * k) := Nat.mul_le_mul_right _ h2
  rw [pow_mul, pow_mul] at h3
  norm_num at h3
  have h4 : 2 ^ k * 27 ^ k ≤ 64 ^ k := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by norm_num) k
  have h5 : 2 * Fintype.card V * 27 ^ k < 2 ^ k * 27 ^ k :=
    Nat.mul_lt_mul_of_pos_right hk (by positivity)
  omega

theorem final {k : ℕ} (hk : 2 * Fintype.card V < 2 ^ k) (v : V) : ¬ t.NP (Γ (3 * k)) v := by
  classical
  intro hv
  have h0 := hD.npOf_final (t.c1 v) hk
  have hm : t.c1 v ∈ (t.marks (Γ (3 * k))).filter
      ((R.double.split (Γ (3 * k))).toHypermap.gcomp (t.c1 v)) :=
    Finset.mem_filter.2 ⟨t.mem_marks.2 ⟨v, hv, Or.inl rfl⟩, connect_refl _⟩
  have := Finset.card_pos.2 ⟨_, hm⟩
  unfold npOf at h0
  omega

end Decomp

end RootedTree

/-! ### The hierarchy of a decomposition -/

section Names

theorem portsOf_congr {Γ : Finset (D × Bool)} {u u' : D × Bool} (h : R.Same Γ u u') :
    R.portsOf Γ u = R.portsOf Γ u' := by
  ext z
  rw [mem_portsOf, mem_portsOf]
  exact and_congr_right fun _ => ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩

variable (R) in
/-- The least code of a corner in the bag of `u`. -/
noncomputable def minCode (code : D × Bool → ℕ) (Γ : Finset (D × Bool)) (u : D × Bool) : ℕ :=
  sInf (code '' (R.portsOf Γ u : Set (D × Bool)))

variable (R) in
/-- The name of the bag of `u` at depth `d`. -/
noncomputable def bagName (code : D × Bool → ℕ) (Γ : ℕ → Finset (D × Bool)) (d : ℕ) (u : D × Bool) :
    ℕ :=
  Nat.pair d (R.minCode code (Γ d) u)

variable {code : D × Bool → ℕ} {Γ : ℕ → Finset (D × Bool)}

theorem bagName_fst (d : ℕ) (u : D × Bool) : (Nat.unpair (R.bagName code Γ d u)).1 = d := by
  simp [bagName]

theorem bagName_congr {d : ℕ} {u u' : D × Bool} (h : R.Same (Γ d) u u') :
    R.bagName code Γ d u = R.bagName code Γ d u' := by
  unfold bagName minCode
  rw [portsOf_congr h]

/-- Two darts have one name at one depth if and only if they lie in one bag. -/
theorem bagName_eq_iff (hne : ∀ d u, ∃ g ∈ Γ d, R.Same (Γ d) u g) (hinj : Function.Injective code)
    {d : ℕ} {u u' : D × Bool} :
    R.bagName code Γ d u = R.bagName code Γ d u' ↔ R.Same (Γ d) u u' := by
  refine ⟨fun h => ?_, bagName_congr⟩
  have hmin : R.minCode code (Γ d) u = R.minCode code (Γ d) u' := by
    have := congrArg (fun x => (Nat.unpair x).2) h
    simpa [bagName] using this
  have hmem : ∀ v, R.minCode code (Γ d) v ∈ code '' (R.portsOf (Γ d) v : Set (D × Bool)) := by
    intro v
    obtain ⟨g, hg, hvg⟩ := hne d v
    exact Nat.sInf_mem ⟨code g, g, mem_portsOf.2 ⟨hg, hvg⟩, rfl⟩
  obtain ⟨g, hg, e⟩ := hmem u
  obtain ⟨g', hg', e'⟩ := hmem u'
  have : g = g' := hinj (e.trans (hmin.trans e'.symm))
  subst this
  exact (mem_portsOf.1 hg).2.trans (mem_portsOf.1 hg').2.symm

variable (R code Γ) in
/-- `z` lies in the bag named `x`, of depth at most `H`. -/
def InBag (H x : ℕ) (z : D × Bool) : Prop :=
  (Nat.unpair x).1 ≤ H ∧ R.bagName code Γ (Nat.unpair x).1 z = x

theorem inBag_name {H d : ℕ} (hd : d ≤ H) (z : D × Bool) :
    R.InBag code Γ H (R.bagName code Γ d z) z := by
  refine ⟨by rwa [bagName_fst], ?_⟩
  rw [bagName_fst]

theorem InBag.same {H x : ℕ} {z z' : D × Bool} (h : R.InBag code Γ H x z)
    (hs : R.Same (Γ (Nat.unpair x).1) z z') : R.InBag code Γ H x z' :=
  ⟨h.1, (bagName_congr hs).symm.trans h.2⟩

theorem InBag.eq_name {H x : ℕ} {z : D × Bool} (h : R.InBag code Γ H x z) :
    x = R.bagName code Γ (Nat.unpair x).1 z := h.2.symm

end Names

namespace RootedTree

variable {V : Type*} [Fintype V] [DecidableEq V] {t : R.RootedTree V}

section Hierarchy

variable {code : D × Bool → ℕ} {Γ C : ℕ → Finset (D × Bool)} {w₀ : D × Bool}

namespace Decomp

variable (hD : t.Decomp w₀ Γ C) (hR : R.Planar) (hc : R.Connected) (hinj : Function.Injective code)

include hD hc

theorem exists_port (d : ℕ) (u : D × Bool) : ∃ g ∈ Γ d, R.Same (Γ d) u g :=
  R.double.split_meets (R.double_connected hc) (hD.level d).nonempty u

/-- All darts lie in one bag at depth zero. -/
theorem same_zero (u u' : D × Bool) : R.Same (Γ 0) u u' := by
  have hsplit : R.double.split {w₀} = R.double := by
    refine RotSystem.ext rfl ?_
    rw [split_rot]
    show R.double.rot * (firstReturn R.double.rot {w₀})⁻¹ = R.double.rot
    rw [firstReturn_singleton]
    simp
  show (R.double.split (Γ 0)).toHypermap.gcomp u u'
  rw [hD.zero, hsplit]
  exact connect_of_nComp_eq_one R.double.toHypermap.glinkC (R.double_connected hc)
    (Set.mem_univ u) (Set.mem_univ u')

include hinj

variable {adj : V → V → Prop} (hadj : ∀ a b, adj a b → ∃ d, t.vert d = a ∧ t.vert (R.rev d) = b)
  (hsurj : ∀ v, ∃ d, t.vert d = v) {H : ℕ} (hH : ∀ v, ¬ t.NP (Γ H) v)

/-- A vertex of a bag off the hubs has no corner in the next level. -/
theorem np_of_not_hub {x : ℕ} {u : D × Bool} (hu : R.InBag code Γ H x u)
    (hn : ¬ ∃ g, R.InBag code Γ H x g ∧ g ∈ Γ ((Nat.unpair x).1 + 1) ∧ t.vertM g = t.vertM u) :
    t.NP (Γ ((Nat.unpair x).1 + 1)) (t.vertM u) := by
  by_contra hnp
  obtain ⟨g, hg, hgu, hs⟩ := exists_corner_of_not_NP hnp
  exact hn ⟨g, hu.same (gcomp_split_mono (hD.sub_succ _) hs), hg, hgu⟩

include hH in
/-- A vertex of a bag off the hubs has a child: the depth of the bag is below `H`. -/
theorem depth_lt_of_np {x : ℕ} {v : V} (hx : (Nat.unpair x).1 ≤ H)
    (hnp : t.NP (Γ ((Nat.unpair x).1 + 1)) v) : (Nat.unpair x).1 + 1 ≤ H := by
  by_contra hlt
  obtain rfl : (Nat.unpair x).1 = H := by omega
  exact hH v (hnp.mono (hD.sub_succ _))

include hadj hsurj hH in
/-- **The hierarchy of a decomposition.** -/
noncomputable def hierarchy : RHierarchy V ℕ adj where
  bag x := {a | ∃ z, R.InBag code Γ H x z ∧ t.vertM z = a}
  arc x a b := ∃ z, R.InBag code Γ H x z ∧ t.vertM z = a ∧ t.vertM (R.double.rev z) = b
  hub x := {a | ∃ g, R.InBag code Γ H x g ∧ g ∈ Γ ((Nat.unpair x).1 + 1) ∧ t.vertM g = a}
  kid c x := (Nat.unpair c).1 = (Nat.unpair x).1 + 1 ∧ ∃ z, R.InBag code Γ H c z ∧ R.InBag code Γ H x z
  wf := by
    refine Subrelation.wf ?_ (measure fun x => H - (Nat.unpair x).1).wf
    rintro c x ⟨h1, z, hz, _⟩
    have := hz.1
    show H - (Nat.unpair c).1 < H - (Nat.unpair x).1
    omega
  root := R.bagName code Γ 0 w₀
  root_bag z := by
    obtain ⟨d, rfl⟩ := hsurj z
    have hb : R.InBag code Γ H (R.bagName code Γ 0 w₀) (d, false) := by
      refine (inBag_name (Nat.zero_le H) w₀).same ?_
      rw [bagName_fst]
      exact hD.same_zero hc _ _
    exact ⟨(d, false), hb, rfl⟩
  root_arc a b hab := by
    obtain ⟨d, rfl, rfl⟩ := hadj a b hab
    have hb : R.InBag code Γ H (R.bagName code Γ 0 w₀) (d, false) := by
      refine (inBag_name (Nat.zero_le H) w₀).same ?_
      rw [bagName_fst]
      exact hD.same_zero hc _ _
    exact ⟨(d, false), hb, rfl, rfl⟩
  arc_bag x a b := by
    rintro ⟨z, hz, rfl, rfl⟩
    exact ⟨⟨z, hz, rfl⟩, ⟨_, hz.same (same_rev _ z), rfl⟩⟩
  cover x a := by
    rintro ⟨z, hz, rfl⟩ hn
    have hnp := hD.np_of_not_hub hc hinj hz hn
    have hlt := hD.depth_lt_of_np hc hinj hH hz.1 hnp
    refine ⟨R.bagName code Γ ((Nat.unpair x).1 + 1) z, ⟨bagName_fst _ _, z, inBag_name hlt z, hz⟩,
      ⟨z, inBag_name hlt z, rfl⟩⟩
  uniq x c c' a := by
    rintro ⟨hc1, -⟩ ⟨hc2, -⟩ ⟨z, hz, rfl⟩ hn ⟨u, hu, hua⟩ ⟨u', hu', hua'⟩
    have hnp := hD.np_of_not_hub hc hinj hz hn
    have hs : R.Same (Γ ((Nat.unpair x).1 + 1)) u u' := hnp.gcomp hua hua'
    rw [hu.eq_name, hu'.eq_name, hc1, hc2]
    exact bagName_congr hs
  edge x a b := by
    rintro ⟨z, hz, rfl, rfl⟩ hn _
    have hnp := hD.np_of_not_hub hc hinj hz hn
    have hlt := hD.depth_lt_of_np hc hinj hH hz.1 hnp
    exact ⟨R.bagName code Γ ((Nat.unpair x).1 + 1) z, ⟨bagName_fst _ _, z, inBag_name hlt z, hz⟩,
      ⟨z, inBag_name hlt z, rfl, rfl⟩⟩

variable {hD hc hinj hadj hsurj hH}

/-- The depth of a name. -/
def depthOf (H x : ℕ) : ℕ := min (Nat.unpair x).1 H

theorem depthOf_le (H x : ℕ) : depthOf H x ≤ H := min_le_right _ _

include hD hc hinj hadj hsurj hH in
/-- The depth of a child is one more. -/
theorem depth_kid {c x : ℕ} (h : (hD.hierarchy hc hinj hadj hsurj hH).kid c x) :
    depthOf H c = depthOf H x + 1 := by
  obtain ⟨h1, z, hz, _⟩ := h
  have := hz.1
  unfold depthOf
  omega

include hD in
/-- **The chains.** The chain of a vertex holds the root, and the bags of the vertex at depths where it
has no corner. -/
theorem chain_iff {v : V} {x : ℕ} :
    (hD.hierarchy hc hinj hadj hsurj hH).Chain v x ↔
      ∃ d z, d ≤ H ∧ t.vertM z = v ∧ (d = 0 ∨ t.NP (Γ d) v) ∧ x = R.bagName code Γ d z := by
  constructor
  · intro h
    induction h with
    | root =>
      obtain ⟨d, hd⟩ := hsurj v
      refine ⟨0, (d, false), Nat.zero_le H, hd, Or.inl rfl, ?_⟩
      exact bagName_congr (hD.same_zero hc _ _)
    | @step y c _ hn hk hb ih =>
      obtain ⟨d, z, hd, hz, _, rfl⟩ := ih
      obtain ⟨h1, -⟩ := hk
      obtain ⟨u, hu, hua⟩ := hb
      rw [bagName_fst] at h1
      have hzb : R.InBag code Γ H (R.bagName code Γ d z) z := inBag_name hd z
      have hnp := hD.np_of_not_hub hc hinj hzb (by
        rw [hz]
        exact hn)
      rw [bagName_fst, hz] at hnp
      have hu2 := hu.1
      rw [h1] at hu2
      refine ⟨d + 1, u, hu2, hua, Or.inr hnp, ?_⟩
      have := hu.eq_name
      rwa [h1] at this
  · rintro ⟨d, z, hd, rfl, h0, rfl⟩
    induction d generalizing z with
    | zero =>
      have : R.bagName code Γ 0 z = R.bagName code Γ 0 w₀ := bagName_congr (hD.same_zero hc _ _)
      rw [this]
      exact RHierarchy.Chain.root
    | succ d ih =>
      have hnp : t.NP (Γ (d + 1)) (t.vertM z) := by
        rcases h0 with h0 | h0
        · omega
        · exact h0
      have hc' := ih z (by omega) (Or.inr (hnp.mono (hD.sub_succ d)))
      have hz1 : R.InBag code Γ H (R.bagName code Γ d z) z := inBag_name (by omega) z
      have hz2 : R.InBag code Γ H (R.bagName code Γ (d + 1) z) z := inBag_name hd z
      refine RHierarchy.Chain.step hc' ?_ ⟨?_, z, hz2, hz1⟩ ⟨z, hz2, rfl⟩
      · rintro ⟨g, _, hg, hgz⟩
        rw [bagName_fst] at hg
        exact hnp g hg hgz
      · rw [bagName_fst, bagName_fst]

include hD hc in
/-- The number of hubs of a bag. -/
theorem hub_card {h : ℕ} (hdep : ∀ v, t.dep v ≤ h) (x : ℕ) :
    ((hD.hierarchy hc hinj hadj hsurj hH).hub x).ncard ≤ 1 + (H + 1) * (2 + 4 * h) := by
  classical
  by_cases hx : ∃ u, R.InBag code Γ H x u
  · obtain ⟨u, hu⟩ := hx
    have hsub : (hD.hierarchy hc hinj hadj hsurj hH).hub x ⊆
        t.vertM '' (((Γ ((Nat.unpair x).1 + 1)).filter (R.Same (Γ (Nat.unpair x).1) u) :
          Finset (D × Bool)) : Set (D × Bool)) := by
      rintro a ⟨g, hg, hgm, rfl⟩
      refine Set.mem_image_of_mem _ (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hgm, ?_⟩))
      exact (bagName_eq_iff (hD.exists_port hc) hinj).1 (hu.2.trans hg.2.symm)
    have h1 := hD.card_filter_succ hdep (Nat.unpair x).1 u
    have h2 : ((hD.hierarchy hc hinj hadj hsurj hH).hub x).ncard ≤
        ((Γ ((Nat.unpair x).1 + 1)).filter (R.Same (Γ (Nat.unpair x).1) u)).card := by
      refine (Set.ncard_le_ncard hsub (Set.Finite.image _ (Finset.finite_toSet _))).trans ?_
      refine (Set.ncard_image_le (Finset.finite_toSet _)).trans ?_
      rw [Set.ncard_coe_finset]
    refine h2.trans (h1.trans ?_)
    have h3 := hu.1
    have : ((Nat.unpair x).1 + 1) * (2 + 4 * h) ≤ (H + 1) * (2 + 4 * h) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · have hemp : (hD.hierarchy hc hinj hadj hsurj hH).hub x = ∅ := by
      ext a
      constructor
      · rintro ⟨g, hg, _, _⟩
        exact (hx ⟨g, hg⟩).elim
      · intro ha
        exact ha.elim
    rw [hemp, Set.ncard_empty]
    exact Nat.zero_le _

include hD hc hR in
/-- **The diameter of the bags of the hierarchy.** -/
theorem span {h : ℕ} (hdep : ∀ v, t.dep v ≤ h) {x : ℕ} {a b : V}
    (ha : a ∈ (hD.hierarchy hc hinj hadj hsurj hH).bag x)
    (hb : b ∈ (hD.hierarchy hc hinj hadj hsurj hH).bag x) :
    ReachLE ((hD.hierarchy hc hinj hadj hsurj hH).arc x)
      ((2 * H + 2) * (2 * (h + (1 + H * (2 + 4 * h))) + 1)) a b := by
  obtain ⟨z, hz, rfl⟩ := ha
  obtain ⟨z', hz', rfl⟩ := hb
  have hle := hz.1
  have hJ : (R.portsOf (Γ (Nat.unpair x).1) z).card ≤ 1 + H * (2 + 4 * h) := by
    have h1 := hD.card_ports hdep (Nat.unpair x).1 z
    have h2 : (Nat.unpair x).1 * (2 + 4 * h) ≤ H * (2 + 4 * h) := Nat.mul_le_mul_right _ hle
    omega
  have hG : (R.gapsOf (Γ (Nat.unpair x).1) z).card ≤ 2 * H + 1 := by
    have h1 := hD.card_gaps (Nat.unpair x).1 z
    omega
  have hs : R.Same (Γ (Nat.unpair x).1) z z' :=
    (bagName_eq_iff (hD.exists_port hc) hinj).1 (hz.2.trans hz'.2.symm)
  have hdiam := bag_diam (hD.level (Nat.unpair x).1) hR hc hdep hJ hG (u := z)
    ⟨z, connect_refl z, rfl⟩ ⟨z', hs, rfl⟩
  refine ReachLE.mono_adj ?_ hdiam
  rintro a' b' ⟨w, hw, rfl, rfl⟩
  exact ⟨w, hz.same hw, rfl, rfl⟩

/-- **Congestion.** At one depth, at most two bags contain an arc. -/
theorem congestion (hsimple : ∀ d d', t.vert d = t.vert d' → t.vert (R.rev d) = t.vert (R.rev d') →
    d = d') (d' : ℕ) (a b : V) :
    ∃ F : Finset ℕ, F.card ≤ 2 ∧ ∀ x, depthOf H x = d' →
      (∃ z, R.InBag code Γ H x z ∧ t.vertM z = a ∧ t.vertM (R.double.rev z) = b) → x ∈ F := by
  classical
  by_cases hex : ∃ d, t.vert d = a ∧ t.vert (R.rev d) = b
  · obtain ⟨d, h1, h2⟩ := hex
    refine ⟨{R.bagName code Γ d' (d, false), R.bagName code Γ d' (d, true)}, Finset.card_le_two, ?_⟩
    rintro x hx ⟨⟨e, bit⟩, hz, h3, h4⟩
    have hraw : (Nat.unpair x).1 = d' := by
      have := hz.1
      unfold depthOf at hx
      omega
    have he : e = d := hsimple _ _ (h3.trans h1.symm) (h4.trans h2.symm)
    subst he
    have hname := hz.eq_name
    rw [hraw] at hname
    rw [hname]
    cases bit
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  · refine ⟨∅, by simp, ?_⟩
    rintro x _ ⟨⟨e, bit⟩, _, h3, h4⟩
    exact (hex ⟨e, h3, h4⟩).elim

end Decomp

end Hierarchy

end RootedTree

end RotSystem

end SsspFlow
