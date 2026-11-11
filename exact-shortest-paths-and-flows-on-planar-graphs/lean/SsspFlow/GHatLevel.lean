import SsspFlow.GHatNet

/-!
# The network of a level on fixed identifiers

Let `N` be a plane network on `Fin n` and `S` the data of a level of its rotation system. The nodes of
the subdivided repaired graph get fixed names `(node, neighbour, kind)` with 21 kinds: a copy is
named by its corner (`Net.nameC`), a dart of the repaired graph by a dart of `N` that starts at the
node of its first copy (`RData.nameD`). The names do not depend on the level, so an algorithm on
them is fixed before the network. All other names hang as pendant nodes at the star centre of their
node (`RData.levelPad`), in increasing order.

The lists of the network are those of Table R, with the star centre of a node in the order of its
rotation list (`RData.hatNet`). They are rotations of the lists of the subdivided repaired graph
(`RData.hatList_rot`), and rotated lists give the same rotation system (`Net.relist_planar`).

* `RData.levelNet_planar`, `RData.levelNet_diam`: for a connected plane network of diameter at most
  `D` and data without conflict with at most three cut corners, the network of the level is planar
  and has diameter at most `12 D + 16`.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest

namespace Congest

namespace Net

variable {n : ℕ} (N : Net (Fin n))

/-- The node of a vertex of the rotation system. -/
def vnode : N.toRot.Vertex → Fin n :=
  Quotient.lift (fun d : N.G.Dart => d.fst) fun _ _ h => N.tail_eq_iff.1 (Quotient.sound h)

@[simp] theorem vnode_tail (d : N.G.Dart) : N.vnode (N.toRot.tail d) = d.fst := rfl

theorem vnode_injective : Function.Injective N.vnode := by
  intro u v h
  obtain ⟨x, rfl⟩ := N.toRot.exists_tail_eq u
  obtain ⟨y, rfl⟩ := N.toRot.exists_tail_eq v
  exact N.tail_eq_iff.2 h

/-- The name of a copy: its corner and kind, or its node twice for a star centre. -/
def nameC : RotSystem.Copy N.toRot.Vertex N.G.Dart → Fin n × Fin n × Fin 21
  | .star v => (N.vnode v, N.vnode v, 0)
  | .dc c => (c.fst, c.snd, 1)
  | .lc c => (c.fst, c.snd, 2)
  | .rc c => (c.fst, c.snd, 3)
  | .xc c => (c.fst, c.snd, 4)

theorem nameC_kind (a : RotSystem.Copy N.toRot.Vertex N.G.Dart) : (N.nameC a).2.2 < 5 := by
  cases a <;> simp [nameC] <;> decide

theorem nameC_injective : Function.Injective N.nameC := by
  intro a b h
  cases a <;> cases b <;> simp only [nameC, Prod.mk.injEq] at h <;>
    first
    | exact absurd h.2.2 (by decide)
    | exact congrArg _ (N.vnode_injective h.1)
    | exact congrArg _ (SimpleGraph.Dart.ext _ _ (Prod.ext h.1 h.2.1))

/-- A walk of `N` gives a walk of its rotation system along its darts. -/
theorem isWalk_darts' {a b : Fin n} (p : N.G.Walk a b) (x y : N.G.Dart) (hx : x.fst = a)
    (hy : y.fst = b) : N.toRot.IsWalk (N.toRot.tail x) p.darts (N.toRot.tail y) := by
  induction p generalizing x with
  | nil => exact N.tail_eq_iff.2 (hx.trans hy.symm)
  | cons h q ih =>
    exact (N.toRot.isWalk_cons _ _ _ _).2 ⟨N.tail_eq_iff.2 hx.symm, ih _ rfl hy⟩

/-- The diameter of `N` bounds the walks of its rotation system. -/
theorem isWalk_of_diam {D : ℕ} (hD : N.DiamLE D) (u v : N.toRot.Vertex) :
    ∃ p, N.toRot.IsWalk u p v ∧ p.length ≤ D := by
  obtain ⟨x, rfl⟩ := N.toRot.exists_tail_eq u
  obtain ⟨y, rfl⟩ := N.toRot.exists_tail_eq v
  obtain ⟨p, hp⟩ := hD x.fst y.fst
  exact ⟨p.darts, N.isWalk_darts' p x y rfl rfl, by rw [SimpleGraph.Walk.length_darts]; exact hp⟩

end Net

section Relist

namespace Net

variable {V : Type} [Fintype V] [DecidableEq V] (N : Net V)

variable {V : Type} [Fintype V] [DecidableEq V] (N : Net V)

/-- The same network with lists that are rotations of its lists. -/
def relist (L : V → List V) (hL : ∀ v, L v ~r N.rotList v) : Net V where
  G := N.G
  rotList := L
  nodup v := (hL v).nodup_iff.2 (N.nodup v)
  mem_rotList v w := (hL v).mem_iff.trans (N.mem_rotList v w)

theorem relist_rotPerm (L : V → List V) (hL : ∀ v, L v ~r N.rotList v) :
    (N.relist L hL).rotPerm = N.rotPerm :=
  Equiv.ext fun d => SimpleGraph.Dart.ext _ _ (Prod.ext rfl (by
    show (L d.fst).formPerm d.snd = (N.rotList d.fst).formPerm d.snd
    rw [List.formPerm_eq_of_isRotated ((hL d.fst).nodup_iff.2 (N.nodup _)) (hL d.fst)]))

/-- Planarity does not depend on the instance of finiteness. -/
theorem _root_.SsspFlow.RotSystem.planar_of_inst {E : Type} [DecidableEq E] {i₁ i₂ : Fintype E}
    (R₁ : @RotSystem E i₁ _) (R₂ : @RotSystem E i₂ _)
    (hrev : @RotSystem.rev E i₁ _ R₁ = @RotSystem.rev E i₂ _ R₂)
    (hrot : @RotSystem.rot E i₁ _ R₁ = @RotSystem.rot E i₂ _ R₂)
    (h : @RotSystem.Planar E i₁ _ R₁) : @RotSystem.Planar E i₂ _ R₂ := by
  obtain rfl : i₁ = i₂ := Subsingleton.elim _ _
  cases R₁
  cases R₂
  cases hrev
  cases hrot
  exact h

/-- Connectedness does not depend on the instance of finiteness. -/
theorem _root_.SsspFlow.RotSystem.connected_of_inst {E : Type} [DecidableEq E] {i₁ i₂ : Fintype E}
    (R₁ : @RotSystem E i₁ _) (R₂ : @RotSystem E i₂ _)
    (hrev : @RotSystem.rev E i₁ _ R₁ = @RotSystem.rev E i₂ _ R₂)
    (hrot : @RotSystem.rot E i₁ _ R₁ = @RotSystem.rot E i₂ _ R₂)
    (h : @RotSystem.Connected E i₁ _ R₁) : @RotSystem.Connected E i₂ _ R₂ := by
  obtain rfl : i₁ = i₂ := Subsingleton.elim _ _
  cases R₁
  cases R₂
  cases hrev
  cases hrot
  exact h

/-- **Rotated lists keep planarity.** The rotation is the same permutation of the same darts. -/
theorem relist_planar (L : V → List V) (hL : ∀ v, L v ~r N.rotList v) (h : N.toRot.Planar) :
    (N.relist L hL).toRot.Planar :=
  RotSystem.planar_of_inst N.toRot (N.relist L hL).toRot rfl (N.relist_rotPerm L hL).symm h

theorem relist_connected (L : V → List V) (hL : ∀ v, L v ~r N.rotList v) (h : N.toRot.Connected) :
    (N.relist L hL).toRot.Connected :=
  RotSystem.connected_of_inst N.toRot (N.relist L hL).toRot rfl (N.relist_rotPerm L hL).symm h

theorem relist_diam (L : V → List V) (hL : ∀ v, L v ~r N.rotList v) {D : ℕ} (h : N.DiamLE D) :
    (N.relist L hL).DiamLE D := h

end Net

end Relist

end Congest

/-- Lists without repeats, with the same entries and the same cycle, are rotations of each other. -/
theorem _root_.List.isRotated_of_formPerm {α : Type*} [DecidableEq α] {l l' : List α} (hl : l.Nodup)
    (hl' : l'.Nodup) (hm : ∀ x, x ∈ l ↔ x ∈ l') (hf : l.formPerm = l'.formPerm) : l ~r l' := by
  have hp : l.Perm l' := (List.perm_ext_iff_of_nodup hl hl').2 hm
  rcases l with _ | ⟨x, _ | ⟨y, t⟩⟩
  · rw [← hp.nil_eq]
  · rw [List.singleton_perm.1 hp]
  · rcases l' with _ | ⟨x', _ | ⟨y', t'⟩⟩
    · exact absurd hp.length_eq (by simp)
    · exact absurd hp.length_eq (by simp)
    · exact (List.formPerm_ext_iff hl hl').1 hf

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData)

/-- The name of a dart of the repaired graph: a dart of `N` that starts at the node of its first
copy, and its kind. -/
def nameD : S.HD → Fin n × Fin n × Fin 21
  | (.sp c, b) => (c.fst, c.snd, if b then 12 else 11)
  | (.rim d, b) => (d.fst, d.snd, if b then 14 else 13)
  | (.tok ⟨(d, .zero), _⟩, false) => (d.fst, d.snd, 5)
  | (.tok ⟨(d, .one), _⟩, false) => (d.fst, d.snd, 6)
  | (.tok ⟨(d, .two), _⟩, false) => (d.fst, d.snd, 7)
  | (.tok ⟨(d, .zero), _⟩, true) => (d.snd, d.fst, 8)
  | (.tok ⟨(d, .one), _⟩, true) => (d.snd, d.fst, 9)
  | (.tok ⟨(d, .two), _⟩, true) => (d.snd, d.fst, 10)
  | (.lsp a, b) => (a.1.snd, a.1.fst, if b then 16 else 15)
  | (.rsp a, b) => (a.1.fst, a.1.snd, if b then 18 else 17)
  | (.xsp c, b) => (c.1.fst, c.1.snd, if b then 20 else 19)

theorem nameD_kind (x : S.HD) : 5 ≤ (S.nameD x).2.2 := by
  obtain ⟨e, b⟩ := x
  rcases e with c | c | ⟨⟨c, l⟩, hc⟩ | c | c | c <;> (try cases l) <;> cases b <;> simp [nameD] <;> decide

theorem nameD_injective : Function.Injective S.nameD := by
  have dext : ∀ {c c' : N.G.Dart}, c.fst = c'.fst → c.snd = c'.snd → c = c' :=
    fun h1 h2 => SimpleGraph.Dart.ext _ _ (Prod.ext h1 h2)
  rintro ⟨e, b⟩ ⟨e', b'⟩ h
  rcases e with c | c | ⟨⟨c, l⟩, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩ <;>
  rcases e' with c' | c' | ⟨⟨c', l'⟩, hc'⟩ | ⟨c', hc'⟩ | ⟨c', hc'⟩ | ⟨c', hc'⟩ <;>
  (try cases l) <;> (try cases l') <;> cases b <;> cases b' <;>
  simp only [nameD, Prod.mk.injEq, ite_true, ite_false, Bool.false_eq_true] at h <;>
  (try simp only [Fin.reduceEq, and_false, false_and] at h) <;>
  first
  | exact absurd h.2.2 (by decide)
  | (obtain ⟨h1, h2, -⟩ := h; (first | obtain rfl := dext h1 h2 | obtain rfl := dext h2 h1); rfl)

/-- The copy of a vertex of the repaired graph. -/
noncomputable def vcopy : S.hRot.Vertex → Copy N.toRot.Vertex N.G.Dart :=
  Quotient.lift S.tl fun a b h => (S.hRot_tail_eq_iff a b).1 (Quotient.sound h)

theorem vcopy_injective : Function.Injective S.vcopy := by
  intro u v h
  obtain ⟨x, rfl⟩ := S.hRot.exists_tail_eq u
  obtain ⟨y, rfl⟩ := S.hRot.exists_tail_eq v
  exact (S.hRot_tail_eq_iff x y).2 h

/-- The fixed identifiers. -/
def idEquiv : Fin n × Fin n × Fin 21 ≃ Fin (n * (n * 21)) :=
  (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv

/-- The name of a node of the subdivided repaired graph. -/
noncomputable def name : S.hRot.Vertex ⊕ S.HD → Fin n × Fin n × Fin 21
  | .inl v => N.nameC (S.vcopy v)
  | .inr x => S.nameD x

theorem name_injective : Function.Injective S.name := by
  rintro (u | x) (v | y) h <;> simp only [name] at h
  · rw [S.vcopy_injective (N.nameC_injective h)]
  · exact absurd (congrArg (fun p => p.2.2) h) (by
      have := N.nameC_kind (S.vcopy u); have := S.nameD_kind y; omega)
  · exact absurd (congrArg (fun p => p.2.2) h) (by
      have := N.nameC_kind (S.vcopy v); have := S.nameD_kind x; omega)
  · rw [S.nameD_injective h]

/-- **The darts at a vertex of the repaired graph** in rotation order are a rotation of the list of
Table R at its copy. -/
theorem vList_rot (v : S.hRot.Vertex) : S.hRot.vList v ~r S.lst (S.vcopy v) := by
  obtain ⟨x0, rfl⟩ := S.hRot.exists_tail_eq v
  show S.hRot.vList (S.hRot.tail x0) ~r S.lst (S.tl x0)
  have hm : ∀ d, d ∈ S.hRot.vList (S.hRot.tail x0) ↔ d ∈ S.lst (S.tl x0) := fun d => by
    rw [S.hRot.mem_vList, S.hRot_tail_eq_iff]
    exact ⟨fun h => h ▸ S.mem_lst_tl d, S.tl_of_mem _ d⟩
  refine List.isRotated_of_formPerm (S.hRot.nodup_vList _) (S.lst_nodup _) hm (Equiv.ext fun d => ?_)
  by_cases hd : d ∈ S.hRot.vList (S.hRot.tail x0)
  · rw [S.hRot.formPerm_vList hd]
    have h : S.tl d = S.tl x0 := S.tl_of_mem _ d ((hm d).1 hd)
    show (S.lst (S.tl d)).formPerm d = _
    rw [h]
  · rw [List.formPerm_apply_of_notMem hd, List.formPerm_apply_of_notMem (fun h => hd ((hm d).2 h))]

/-- **The list at a star centre from local data**, up to rotation: the darts at the node in rotation
order. -/
theorem starList_raw (d : N.G.Dart) :
    (N.toRot.starList (N.toRot.tail d)).map (fun c : N.G.Dart => c.toProd) ~r
      (N.rotList d.fst).map (Prod.mk d.fst) := by
  have hinj : Function.Injective (fun c : N.G.Dart => c.toProd) := fun a b h => SimpleGraph.Dart.ext _ _ h
  have hmem : ∀ c : N.G.Dart, c ∈ N.toRot.starList (N.toRot.tail d) ↔ c.fst = d.fst := fun c =>
    mem_starList.trans N.tail_eq_iff
  have hmem' : ∀ p : Fin n × Fin n, p ∈ (N.toRot.starList (N.toRot.tail d)).map (fun c => c.toProd) ↔
      p ∈ (N.rotList d.fst).map (Prod.mk d.fst) := by
    intro p
    constructor
    · intro h
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h
      have hcf := (hmem c).1 hc
      exact List.mem_map.2 ⟨c.snd, by rw [← hcf]; exact (N.mem_rotList _ _).2 c.adj, Prod.ext hcf.symm rfl⟩
    · intro h
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 h
      exact List.mem_map.2 ⟨⟨(d.fst, u), (N.mem_rotList _ _).1 hu⟩, (hmem _).2 rfl, rfl⟩
  refine List.isRotated_of_formPerm ((starList_nodup _).map hinj)
    ((N.nodup _).map (Prod.mk_right_injective d.fst)) hmem' (Equiv.ext fun p => ?_)
  by_cases hp : p ∈ (N.toRot.starList (N.toRot.tail d)).map (fun c => c.toProd)
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp
    have hcf : c.fst = d.fst := (hmem c).1 hc
    rw [formPerm_map_apply hinj (starList_nodup _) hc, formPerm_starList hc]
    have hcs : c.snd ∈ N.rotList d.fst := hcf ▸ (N.mem_rotList _ _).2 c.adj
    have e : c.toProd = (d.fst, c.snd) := Prod.ext hcf rfl
    rw [e, formPerm_map_apply (Prod.mk_right_injective d.fst) (N.nodup _) hcs]
    exact Prod.ext hcf (by rw [← hcf]; rfl)
  · rw [List.formPerm_apply_of_notMem hp, List.formPerm_apply_of_notMem (fun h => hp ((hmem' p).2 h))]

theorem _root_.List.isRotated_of_map {α β : Type*} {f : α → β} (hf : Function.Injective f)
    {l l' : List α} (h : l.map f ~r l'.map f) : l ~r l' := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, List.map_injective_iff.2 hf (by rw [List.map_rotate, hk])⟩

/-- The darts at a node in the order of its rotation list. -/
def starDarts (w : Fin n) : List N.G.Dart :=
  (N.rotList w).attach.map fun x => ⟨(w, x.1), (N.mem_rotList _ _).1 x.2⟩

theorem starDarts_rot (d : N.G.Dart) : starDarts d.fst ~r N.toRot.starList (N.toRot.tail d) := by
  have hinj : Function.Injective (fun c : N.G.Dart => c.toProd) := fun a b h => SimpleGraph.Dart.ext _ _ h
  refine List.isRotated_of_map hinj ?_
  have e : (starDarts d.fst).map (fun c : N.G.Dart => c.toProd) = (N.rotList d.fst).map (Prod.mk d.fst) := by
    simp only [starDarts, List.map_map]
    conv_rhs => rw [← List.attach_map_subtype_val (N.rotList d.fst), List.map_map]
    rfl
  rw [e]
  exact (starList_raw d).symm

/-- The lists of Table R, with the star centre of a node in the order of its rotation list. -/
noncomputable def lstR : Copy N.toRot.Vertex N.G.Dart → List S.HD
  | .star v => (starDarts (N.vnode v)).map fun c => fw (HE.sp c)
  | c => S.lst c

theorem lstR_rot (c : Copy N.toRot.Vertex N.G.Dart) : S.lstR c ~r S.lst c := by
  cases c
  case star v =>
    obtain ⟨d, rfl⟩ := N.toRot.exists_tail_eq v
    exact (starDarts_rot d).map _
  all_goals exact List.IsRotated.refl _

/-- The lists of the subdivided repaired graph with Table R at the copies. -/
noncomputable def hatList : S.hRot.Vertex ⊕ S.HD → List (S.hRot.Vertex ⊕ S.HD)
  | .inl v => (S.lstR (S.vcopy v)).map .inr
  | .inr x => S.hRot.subNet.rotList (.inr x)

theorem hatList_rot (z : S.hRot.Vertex ⊕ S.HD) : S.hatList z ~r S.hRot.subNet.rotList z := by
  cases z with
  | inl v => exact (((S.lstR_rot _).trans (S.vList_rot v).symm).map _)
  | inr x => exact List.IsRotated.refl _

/-- The subdivided repaired graph with the lists of Table R. -/
noncomputable def hatNet : Net (S.hRot.Vertex ⊕ S.HD) := S.hRot.subNet.relist S.hatList S.hatList_rot

variable (hN : ∀ u, ∃ w, N.G.Adj u w)

/-- The star centre of a node, as a vertex of the repaired graph. -/
noncomputable def starV (u : Fin n) : S.hRot.Vertex :=
  S.hRot.tail (HE.sp ⟨(u, (hN u).choose), (hN u).choose_spec⟩, false)

open Classical in
/-- The identifiers: the names of the nodes, and all other names hang at the star centre of their
node. -/
noncomputable def levelPad : PadMap (S.hRot.Vertex ⊕ S.HD) (Fin (n * (n * 21))) where
  ι x := idEquiv (S.name x)
  back a := if h : ∃ x, idEquiv (S.name x) = a then h.choose else .inl (S.starV hN (idEquiv.symm a).1)
  back_ι x := by
    have h : ∃ y, idEquiv (S.name y) = idEquiv (S.name x) := ⟨x, rfl⟩
    rw [dite_cond_eq_true (eq_true h)]
    exact S.name_injective (idEquiv.injective h.choose_spec)
  order s := s.sort (· ≤ ·)
  order_nodup s := s.sort_nodup _
  mem_order s _ := s.mem_sort _

/-- The network of a level. -/
noncomputable def levelNet : Net (Fin (n * (n * 21))) := padNet (S.levelPad hN) S.hatNet

/-- **The network of a level is planar.** -/
theorem levelNet_planar (hP : N.toRot.Planar) (hc : N.toRot.Connected) (hS : S.NoConflict)
    (hcut : S.cut.card ≤ 3) {D : ℕ} (hD : N.DiamLE D) : (S.levelNet hN).toRot.Planar :=
  padNet_planar (S.levelPad hN) S.hRot.subNet_noIso
    (S.hRot.subNet.relist_planar _ _ (S.hatNet_planar hP hc hS))
    (S.hRot.subNet.relist_connected _ _ (S.hRot.subNet_connected (S.hRot_connected hc)))
    (S.hatNet_diam hcut (N.isWalk_of_diam hD))

/-- **The network of a level has diameter at most `12 D + 16`.** -/
theorem levelNet_diam (hcut : S.cut.card ≤ 3) {D : ℕ} (hD : N.DiamLE D) :
    (S.levelNet hN).DiamLE (12 * D + 16) :=
  padNet_diam (S.hatNet_diam hcut (N.isWalk_of_diam hD))

end RData

end RotSystem

end SsspFlow
