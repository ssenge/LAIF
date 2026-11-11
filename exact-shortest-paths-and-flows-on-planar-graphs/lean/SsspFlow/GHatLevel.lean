import SsspFlow.GHatNet

/-!
# The network of a level on fixed identifiers

Let `N` be a plane network on `Fin n` and `S` the data of a level of its rotation system. The nodes of
the subdivided repaired graph get fixed names `(node, neighbour, kind)` with 21 kinds: a copy is
named by its corner (`Net.nameC`), a dart of the repaired graph by a dart of `N` that starts at the
node of its first copy (`RData.nameD`). The names do not depend on the level, so an algorithm on
them is fixed before the network. All other names hang as pendant nodes at the star centre of their
node (`RData.levelPad`).

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

end Congest

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

/-- The network of a level. -/
noncomputable def levelNet : Net (Fin (n * (n * 21))) := padNet (S.levelPad hN) S.hRot.subNet

/-- **The network of a level is planar.** -/
theorem levelNet_planar (hP : N.toRot.Planar) (hc : N.toRot.Connected) (hS : S.NoConflict)
    (hcut : S.cut.card ≤ 3) {D : ℕ} (hD : N.DiamLE D) : (S.levelNet hN).toRot.Planar :=
  padNet_planar (S.levelPad hN) S.hRot.subNet_noIso (S.hatNet_planar hP hc hS)
    (S.hRot.subNet_connected (S.hRot_connected hc)) (S.hatNet_diam hcut (N.isWalk_of_diam hD))

/-- **The network of a level has diameter at most `12 D + 16`.** -/
theorem levelNet_diam (hcut : S.cut.card ≤ 3) {D : ℕ} (hD : N.DiamLE D) :
    (S.levelNet hN).DiamLE (12 * D + 16) :=
  padNet_diam (S.hatNet_diam hcut (N.isWalk_of_diam hD))

end RData

end RotSystem

end SsspFlow
