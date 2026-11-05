import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import SsspFlow.Congest
import SsspFlow.PlanarDual

/-!
# Counting on plane networks, and pendant nodes

* `RotSystem.card_le_numFaces`: a function on the darts that is invariant along faces and onto a type
  `L` shows that there are at least as many faces as elements of `L`.
* `RotSystem.planar_of_count`: a connected rotation system with enough vertices and faces is planar,
  because the genus is not negative.
* `Net.numVertices_eq`, `Net.dart_card`: the counts of a network without isolated nodes.
* `padNet`: a network on a larger set of identifiers, in which all identifiers outside the image of an
  injection hang as pendant nodes at chosen nodes. It stays planar (`padNet_planar`) and its diameter
  grows by at most two (`padNet_diam`).
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor

namespace RotSystem

variable {D : Type*} [Fintype D] [DecidableEq D] (R : RotSystem D)

/-- A function that is invariant along faces, onto `L`, gives at least `Nat.card L` faces. -/
theorem card_le_numFaces {L : Type*} (lab : D → L) (h : ∀ z, lab (R.rev (R.rot z)) = lab z)
    (hs : Function.Surjective lab) : Nat.card L ≤ R.numFaces := by
  have hf : ∀ w, lab (R.facePerm w) = lab w := fun w => by
    have h1 := h (R.facePerm w)
    have h2 : R.rev (R.rot (R.facePerm w)) = w := by
      show R.rev (R.rot (R.rot.symm (R.rev w))) = w
      rw [Equiv.apply_symm_apply, R.rev_rev]
    rw [h2] at h1
    exact h1.symm
  have hit : ∀ (n : ℕ) (w : D), lab ((R.facePerm ^ n) w) = lab w := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [pow_succ', Equiv.Perm.mul_apply, hf, ih]
  let F : R.Face → L := Quotient.lift lab fun a b hab => by
    obtain ⟨n, hn⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq hab
    rw [← hn, hit]
  have hF : Function.Surjective F := fun l => by
    obtain ⟨x, rfl⟩ := hs l
    exact ⟨R.faceOf x, rfl⟩
  rw [← R.natCard_face]
  exact Nat.card_le_card_of_surjective F hF

/-- A connected rotation system with `E + 2 ≤ V + F` is planar. -/
theorem planar_of_count (hc : R.Connected) (h : R.numEdges + 2 ≤ R.numVertices + R.numFaces) :
    R.Planar := by
  have hg := R.genus_formula
  rw [show R.numComponents = 1 from hc] at hg
  show R.toHypermap.genus = 0
  omega

end RotSystem

namespace Congest

/-! ### The cycle of a list, on a concatenation -/

section FormPerm

variable {α : Type*} [DecidableEq α]

/-- The step of `A ++ B` from an element of `A` stays in `A` as the step of `A`. -/
theorem formPerm_append_left {A B : List α} (h : (A ++ B).Nodup) {x : α} (hx : x ∈ A)
    (hy : (A ++ B).formPerm x ∈ A) : (A ++ B).formPerm x = A.formPerm x := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hl : i < (A ++ B).length := by simp; omega
  have h1 := List.formPerm_apply_getElem (A ++ B) h i hl
  have h2 := List.formPerm_apply_getElem A (List.Nodup.of_append_left h) i hi
  rw [List.getElem_append_left hi] at h1
  rw [h1] at hy ⊢
  rw [h2]
  by_cases hs : i + 1 < A.length
  · have e1 : (i + 1) % (A ++ B).length = i + 1 := Nat.mod_eq_of_lt (by simp; omega)
    have e2 : (i + 1) % A.length = i + 1 := Nat.mod_eq_of_lt hs
    simp only [e1, e2, List.getElem_append_left hs]
  · have hAlen : i + 1 = A.length := by omega
    cases B with
    | nil => simp
    | cons b B =>
      exfalso
      have e1 : (i + 1) % (A ++ b :: B).length = A.length := by
        rw [hAlen]
        exact Nat.mod_eq_of_lt (by simp)
      simp only [e1] at hy
      rw [List.getElem_append_right (by omega)] at hy
      simp only [Nat.sub_self, List.getElem_cons_zero] at hy
      exact (List.nodup_append.1 h).2.2 _ hy b (by simp) rfl

/-- The step of `A ++ B` from an element of `A` into `B` starts at the last element of `A`. -/
theorem formPerm_append_last {A B : List α} (h : (A ++ B).Nodup) {x : α} (hx : x ∈ A)
    (hy : (A ++ B).formPerm x ∈ B) : A.formPerm x ∈ A ∧ ∃ a l, A = a :: l ∧ A.formPerm x = a := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hl : i < (A ++ B).length := by simp; omega
  have h1 := List.formPerm_apply_getElem (A ++ B) h i hl
  have h2 := List.formPerm_apply_getElem A (List.Nodup.of_append_left h) i hi
  rw [List.getElem_append_left hi] at h1
  rw [h1] at hy
  refine ⟨List.formPerm_apply_mem_of_mem (List.getElem_mem hi), ?_⟩
  by_cases hs : i + 1 < A.length
  · exfalso
    have e1 : (i + 1) % (A ++ B).length = i + 1 := Nat.mod_eq_of_lt (by simp; omega)
    simp only [e1] at hy
    rw [List.getElem_append_left hs] at hy
    exact (List.nodup_append.1 h).2.2 _ (List.getElem_mem hs) _ hy rfl
  · have hAlen : i + 1 = A.length := by omega
    cases A with
    | nil => simp at hi
    | cons a l =>
      refine ⟨a, l, rfl, ?_⟩
      rw [h2]
      simp [hAlen]

/-- The step of `A ++ B` from an element of `B` into `A` ends at the first element of `A`. -/
theorem formPerm_append_right {A B : List α} (h : (A ++ B).Nodup) {x : α} (hx : x ∈ B)
    (hy : (A ++ B).formPerm x ∈ A) : ∃ a l, A = a :: l ∧ (A ++ B).formPerm x = a := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hl : A.length + i < (A ++ B).length := by simp; omega
  have h1 := List.formPerm_apply_getElem (A ++ B) h (A.length + i) hl
  rw [List.getElem_append_right (by omega)] at h1
  simp only [Nat.add_sub_cancel_left] at h1
  rw [h1] at hy ⊢
  by_cases hs : A.length + i + 1 < (A ++ B).length
  · exfalso
    have e1 : (A.length + i + 1) % (A ++ B).length = A.length + i + 1 := Nat.mod_eq_of_lt hs
    simp only [e1] at hy
    rw [List.getElem_append_right (by omega)] at hy
    exact (List.nodup_append.1 h).2.2 _ hy _ (List.getElem_mem _) rfl
  · have e1 : A.length + i + 1 = (A ++ B).length := by omega
    have hpos : 0 < (A ++ B).length := by omega
    have e2 : (A.length + i + 1) % (A ++ B).length = 0 := by
      rw [e1]
      exact Nat.mod_self _
    simp only [e2]
    cases A with
    | nil =>
      exfalso
      simp at hy
    | cons a l => exact ⟨a, l, rfl, by simp⟩

/-- The cycle of an injective image. -/
theorem formPerm_map_apply {β : Type*} [DecidableEq β] {f : α → β} (hf : Function.Injective f)
    {l : List α} (hl : l.Nodup) {y : α} (hy : y ∈ l) :
    (l.map f).formPerm (f y) = f (l.formPerm y) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  have h1 := List.formPerm_apply_getElem l hl i hi
  have h2 := List.formPerm_apply_getElem (l.map f) (hl.map hf) i (by simpa using hi)
  simp only [List.getElem_map, List.length_map] at h2
  rw [h2, h1]

end FormPerm

namespace Net

variable {V : Type} [Fintype V] [DecidableEq V] (N : Net V)

/-- The neighbours of a node are its list. -/
theorem neighborFinset_eq (v : V) : N.G.neighborFinset v = (N.rotList v).toFinset := by
  ext u
  simp [N.mem_rotList]

theorem degree_eq (v : V) : N.G.degree v = (N.rotList v).length := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_eq,
    List.toFinset_card_of_nodup (N.nodup v)]

/-- The number of darts is the sum of the lengths of the lists. -/
theorem dart_card : Fintype.card N.G.Dart = ∑ v, (N.rotList v).length := by
  rw [SimpleGraph.dart_card_eq_sum_degrees]
  exact Finset.sum_congr rfl fun v _ => N.degree_eq v

theorem cnode_iff (x y : N.G.Dart) : N.toRot.toHypermap.cnode x y ↔ x.fst = y.fst :=
  (N.toRot.tail_eq_iff x y).symm.trans N.tail_eq_iff

/-- Without isolated nodes, the vertices of the rotation system are the nodes. -/
theorem numVertices_eq (h : ∀ v, ∃ u, N.G.Adj v u) : N.toRot.numVertices = Fintype.card V := by
  have h1 := RotSystem.fcard_eq_card_image N.toRot.toHypermap.cnode_sym (fun d : N.G.Dart => d.fst)
    N.cnode_iff
  have h2 : (Finset.univ.image fun d : N.G.Dart => d.fst) = Finset.univ := by
    ext v
    obtain ⟨u, hu⟩ := h v
    simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    exact ⟨⟨(v, u), hu⟩, rfl⟩
  unfold RotSystem.numVertices
  rw [h1, h2, Finset.card_univ]

theorem numEdges_eq : N.toRot.numEdges = (∑ v, (N.rotList v).length) / 2 := by
  rw [RotSystem.numEdges_eq, dart_card]

end Net

/-- A walk with at most `k` steps. -/
def Reach {V : Type*} (G : SimpleGraph V) (k : ℕ) (a b : V) : Prop := ∃ p : G.Walk a b, p.length ≤ k

namespace Reach

variable {V : Type*} {G : SimpleGraph V} {j k : ℕ} {a b c : V}

theorem refl (a : V) : Reach G 0 a a := ⟨.nil, le_rfl⟩

theorem of_adj (h : G.Adj a b) : Reach G 1 a b := ⟨.cons h .nil, le_rfl⟩

theorem trans (h₁ : Reach G j a b) (h₂ : Reach G k b c) : Reach G (j + k) a c := by
  obtain ⟨p, hp⟩ := h₁
  obtain ⟨q, hq⟩ := h₂
  exact ⟨p.append q, by rw [SimpleGraph.Walk.length_append]; omega⟩

theorem mono (h : Reach G j a b) (hjk : j ≤ k) : Reach G k a b := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, hp.trans hjk⟩

end Reach

/-! ### Pendant nodes -/

/-- An injection of the nodes `V₀` into the identifiers `W`, with a left inverse that also names the
node at which an identifier outside the image hangs. -/
structure PadMap (V₀ W : Type) where
  /-- The identifier of a node. -/
  ι : V₀ → W
  /-- The node of an identifier: the one it names, or the one at which it hangs. -/
  back : W → V₀
  back_ι : ∀ x, back (ι x) = x

section Pad

variable {V₀ W : Type}

namespace PadMap

variable (P : PadMap V₀ W)

theorem ι_injective : Function.Injective P.ι := fun a b h => by
  rw [← P.back_ι a, ← P.back_ι b, h]

/-- The identifier names a node. -/
def IsReal (a : W) : Prop := a = P.ι (P.back a)

theorem isReal_ι (x : V₀) : P.IsReal (P.ι x) := by
  show P.ι x = P.ι (P.back (P.ι x))
  rw [P.back_ι]

instance [DecidableEq W] : DecidablePred P.IsReal :=
  fun a => inferInstanceAs (Decidable (a = P.ι (P.back a)))

/-- The identifiers that hang at a node. -/
def extras [Fintype W] [DecidableEq W] [DecidableEq V₀] (x : V₀) : Finset W :=
  Finset.univ.filter fun e => ¬ P.IsReal e ∧ P.back e = x

theorem mem_extras [Fintype W] [DecidableEq W] [DecidableEq V₀] {x : V₀} {e : W} :
    e ∈ P.extras x ↔ ¬ P.IsReal e ∧ P.back e = x := by
  simp [extras]

end PadMap

variable [Fintype V₀] [DecidableEq V₀] [Fintype W] [DecidableEq W]
variable (P : PadMap V₀ W)

/-- The list of an identifier: for a node its old list and the identifiers that hang at it, and
otherwise the node at which it hangs. -/
noncomputable def padList (N₀ : Net V₀) (a : W) : List W :=
  if P.IsReal a then (N₀.rotList (P.back a)).map P.ι ++ (P.extras (P.back a)).toList
  else [P.ι (P.back a)]

variable {P} {N₀ : Net V₀}

theorem padList_ι (x : V₀) :
    padList P N₀ (P.ι x) = (N₀.rotList x).map P.ι ++ (P.extras x).toList := by
  rw [padList, ite_eq_left (P.isReal_ι x), P.back_ι]

theorem padList_of_not {a : W} (h : ¬ P.IsReal a) : padList P N₀ a = [P.ι (P.back a)] := by
  rw [padList, ite_eq_right h]

theorem padList_nodup_ι (x : V₀) : ((N₀.rotList x).map P.ι ++ (P.extras x).toList).Nodup := by
  rw [List.nodup_append]
  refine ⟨(N₀.nodup x).map P.ι_injective, Finset.nodup_toList _, ?_⟩
  intro a ha b hb hab
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 ha
  rw [Finset.mem_toList, P.mem_extras] at hb
  exact hb.1 (hab ▸ P.isReal_ι y)

theorem padList_nodup (a : W) : (padList P N₀ a).Nodup := by
  by_cases h : P.IsReal a
  · rw [padList, ite_eq_left h]
    exact padList_nodup_ι _
  · rw [padList_of_not h]
    exact List.nodup_singleton _

theorem padList_symm {a b : W} (h : b ∈ padList P N₀ a) : a ∈ padList P N₀ b := by
  by_cases ha : P.IsReal a
  · rw [padList, ite_eq_left ha, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h
      have hsymm := (N₀.mem_rotList _ _).2 ((N₀.mem_rotList _ _).1 hy).symm
      rw [padList_ι, List.mem_append]
      exact Or.inl (List.mem_map.2 ⟨_, hsymm, ha.symm⟩)
    · rw [Finset.mem_toList, P.mem_extras] at h
      rw [padList_of_not h.1, h.2, List.mem_singleton]
      exact ha
  · rw [padList_of_not ha, List.mem_singleton] at h
    subst h
    rw [padList_ι, List.mem_append]
    exact Or.inr (Finset.mem_toList.2 (P.mem_extras.2 ⟨ha, rfl⟩))

theorem padList_irrefl (a : W) : a ∉ padList P N₀ a := by
  intro h
  by_cases ha : P.IsReal a
  · rw [padList, ite_eq_left ha, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨y, hy, hya⟩ := List.mem_map.1 h
      have hb : P.back a = y := by rw [← hya, P.back_ι]
      rw [hb] at hy
      exact (N₀.G.loopless.irrefl y) ((N₀.mem_rotList _ _).1 hy)
    · rw [Finset.mem_toList, P.mem_extras] at h
      exact h.1 ha
  · rw [padList_of_not ha, List.mem_singleton] at h
    exact ha h

variable (P N₀) in
/-- The network with pendant nodes. -/
noncomputable def padNet : Net W where
  G := { Adj := fun a b => b ∈ padList P N₀ a
         symm := ⟨fun _ _ h => padList_symm h⟩
         loopless := ⟨padList_irrefl⟩ }
  rotList := padList P N₀
  nodup := padList_nodup
  mem_rotList _ _ := Iff.rfl

theorem padNet_adj_ι {x y : V₀} (h : N₀.G.Adj x y) : (padNet P N₀).G.Adj (P.ι x) (P.ι y) := by
  show P.ι y ∈ padList P N₀ (P.ι x)
  rw [padList_ι, List.mem_append]
  exact Or.inl (List.mem_map.2 ⟨y, (N₀.mem_rotList _ _).2 h, rfl⟩)

theorem padNet_reach_ι {x y : V₀} {k : ℕ} (h : Reach N₀.G k x y) :
    Reach (padNet P N₀).G k (P.ι x) (P.ι y) := by
  obtain ⟨p, hp⟩ := h
  refine Reach.mono ?_ hp
  clear hp
  induction p with
  | nil => exact Reach.refl _
  | cons h _ ih =>
    rw [SimpleGraph.Walk.length_cons, add_comm]
    exact (Reach.of_adj (padNet_adj_ι h)).trans ih

theorem padNet_reach_back (a : W) : Reach (padNet P N₀).G 1 a (P.ι (P.back a)) := by
  by_cases h : P.IsReal a
  · have e : P.ι (P.back a) = a := h.symm
    rw [e]
    exact (Reach.refl a).mono (Nat.zero_le _)
  · apply Reach.of_adj
    show _ ∈ padList P N₀ a
    rw [padList_of_not h, List.mem_singleton]

/-- The diameter grows by at most two. -/
theorem padNet_diam {D : ℕ} (h : N₀.DiamLE D) : (padNet P N₀).DiamLE (D + 2) := by
  intro a b
  obtain ⟨p, hp⟩ := h (P.back a) (P.back b)
  have h1 := padNet_reach_back (P := P) (N₀ := N₀) a
  have h2 := padNet_reach_back (P := P) (N₀ := N₀) b
  obtain ⟨q₂, hq₂⟩ := h2
  have h3 : Reach (padNet P N₀).G 1 (P.ι (P.back b)) b := ⟨q₂.reverse, by simpa using hq₂⟩
  exact ((h1.trans (padNet_reach_ι ⟨p, hp⟩)).trans h3).mono (by omega)

/-- The number of darts of the network with pendant nodes. -/
theorem padNet_sum :
    ∑ a, (padList P N₀ a).length + 2 * Fintype.card V₀ =
      ∑ x, (N₀.rotList x).length + 2 * Fintype.card W := by
  classical
  have hsplit : ∀ f : W → ℕ, ∑ a, f a =
      ∑ x, f (P.ι x) + ∑ e ∈ Finset.univ.filter (fun e => ¬ P.IsReal e), f e := by
    intro f
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ P.IsReal f]
    congr 1
    have : Finset.univ.filter P.IsReal = Finset.univ.map ⟨P.ι, P.ι_injective⟩ := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Function.Embedding.coeFn_mk]
      constructor
      · intro h
        exact ⟨_, Eq.symm h⟩
      · rintro ⟨x, rfl⟩
        exact P.isReal_ι x
    rw [this, Finset.sum_map]
    rfl
  have hcard : Fintype.card W = Fintype.card V₀ +
      (Finset.univ.filter fun e => ¬ P.IsReal e).card := by
    have := hsplit (fun _ => 1)
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ] at this
    exact this
  have hex : ∑ x, (P.extras x).card = (Finset.univ.filter fun e => ¬ P.IsReal e).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := P.back) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    ext e
    simp [PadMap.mem_extras]
  rw [hsplit]
  have h1 : ∀ x, (padList P N₀ (P.ι x)).length = (N₀.rotList x).length + (P.extras x).card := by
    intro x
    rw [padList_ι, List.length_append, List.length_map, Finset.length_toList]
  have h2 : ∑ e ∈ Finset.univ.filter (fun e => ¬ P.IsReal e), (padList P N₀ e).length =
      (Finset.univ.filter fun e => ¬ P.IsReal e).card := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [padList_of_not (Finset.mem_filter.1 he).2]
    rfl
  simp only [h1, Finset.sum_add_distrib, hex, h2]
  omega

/-- All identifiers have a neighbour. -/
theorem padNet_noIso (h : ∀ x, ∃ y, N₀.G.Adj x y) (a : W) : ∃ b, (padNet P N₀).G.Adj a b := by
  by_cases ha : P.IsReal a
  · obtain ⟨y, hy⟩ := h (P.back a)
    exact ⟨P.ι y, by rw [ha]; exact padNet_adj_ι hy⟩
  · exact ⟨P.ι (P.back a), by
      show _ ∈ padList P N₀ a
      rw [padList_of_not ha, List.mem_singleton]⟩

section Faces

variable (hN : ∀ x, ∃ y, N₀.G.Adj x y)

omit [Fintype V₀] [DecidableEq V₀] in
private theorem rotList_ne_nil [Fintype V₀] [DecidableEq V₀] {N₀ : Net V₀}
    (hN : ∀ x, ∃ y, N₀.G.Adj x y) (x : V₀) : N₀.rotList x ≠ [] := fun h0 => by
  obtain ⟨y, hy⟩ := hN x
  rw [← N₀.mem_rotList, h0] at hy
  simp at hy

/-- The face at the place where the pendant nodes hang: that of the dart from the first neighbour. -/
private noncomputable def cFace (x : V₀) : N₀.toRot.Face :=
  N₀.toRot.faceOf ⟨((N₀.rotList x).head (rotList_ne_nil hN x), x),
    ((N₀.mem_rotList _ _).1 (List.head_mem _)).symm⟩

private theorem cFace_eq {x y : V₀} {l : List V₀} (h : N₀.rotList x = y :: l) (hadj : N₀.G.Adj y x) :
    cFace hN x = N₀.toRot.faceOf ⟨(y, x), hadj⟩ := by
  refine congrArg N₀.toRot.faceOf (SimpleGraph.Dart.ext _ _ (Prod.ext ?_ rfl))
  simp [h]

open Classical in
variable (P) in
/-- The face of the old network for a pair of identifiers. -/
private noncomputable def padLab (a b : W) : N₀.toRot.Face :=
  if P.IsReal a ∧ P.IsReal b then
    (if h : N₀.G.Adj (P.back a) (P.back b) then N₀.toRot.faceOf ⟨(P.back a, P.back b), h⟩
      else cFace hN (P.back a))
  else cFace hN (P.back a)

omit [Fintype W] in
private theorem padLab_real {x y : V₀} (h : N₀.G.Adj x y) :
    padLab P hN (P.ι x) (P.ι y) = N₀.toRot.faceOf ⟨(x, y), h⟩ := by
  unfold padLab
  rw [ite_eq_left ⟨P.isReal_ι x, P.isReal_ι y⟩]
  simp only [P.back_ι]
  rw [dite_eq_left h]

omit [Fintype W] in
private theorem padLab_right {x : V₀} {e : W} (he : ¬ P.IsReal e) :
    padLab P hN (P.ι x) e = cFace hN x := by
  unfold padLab
  rw [ite_eq_right (fun h => he h.2), P.back_ι]

omit [Fintype W] in
private theorem padLab_left {x : V₀} {e : W} (he : ¬ P.IsReal e) (hx : P.back e = x) :
    padLab P hN e (P.ι x) = cFace hN x := by
  unfold padLab
  rw [ite_eq_right (fun h => he h.1), hx]

/-- The face of the dart to `x` from the neighbour after `y` is that of the dart from `x` to `y`. -/
private theorem face_step {x y y' : V₀} (h : N₀.G.Adj x y) (hy : y' = (N₀.rotList x).formPerm y)
    (h' : N₀.G.Adj y' x) :
    N₀.toRot.faceOf ⟨(y', x), h'⟩ = N₀.toRot.faceOf ⟨(x, y), h⟩ := by
  subst hy
  exact N₀.toRot.faceOf_rev_rot ⟨(x, y), h⟩

/-- The new label is invariant along the faces. -/
private theorem padLab_step (a b : W) (hab : b ∈ padList P N₀ a) :
    padLab P hN ((padList P N₀ a).formPerm b) a = padLab P hN a b := by
  by_cases ha : P.IsReal a
  · obtain ⟨x, rfl⟩ : ∃ x, a = P.ι x := ⟨_, ha⟩
    have hnd : ((N₀.rotList x).map P.ι ++ (P.extras x).toList).Nodup := padList_nodup_ι x
    have hL : padList P N₀ (P.ι x) = (N₀.rotList x).map P.ι ++ (P.extras x).toList := padList_ι x
    rw [hL] at hab ⊢
    have hmem := List.formPerm_apply_mem_of_mem hab
    rcases List.mem_append.1 hab with hb | hb
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
      have hxy : N₀.G.Adj x y := (N₀.mem_rotList _ _).1 hy
      rw [padLab_real hN hxy]
      rcases List.mem_append.1 hmem with hb' | hb'
      · rw [formPerm_append_left hnd hb hb', formPerm_map_apply P.ι_injective (N₀.nodup x) hy]
        have hy' := List.formPerm_apply_mem_of_mem hy
        have hadj : N₀.G.Adj ((N₀.rotList x).formPerm y) x := ((N₀.mem_rotList _ _).1 hy').symm
        rw [padLab_real hN hadj]
        exact face_step hxy rfl hadj
      · have he := Finset.mem_toList.1 hb'
        rw [P.mem_extras] at he
        rw [padLab_left hN he.1 he.2]
        obtain ⟨-, a₀, l, hA, hstep⟩ := formPerm_append_last hnd hb hb'
        obtain ⟨y₀, l', hr, rfl, -⟩ := List.map_eq_cons_iff.1 hA
        rw [formPerm_map_apply P.ι_injective (N₀.nodup x) hy] at hstep
        have hy₀ : (N₀.rotList x).formPerm y = y₀ := P.ι_injective hstep
        have hadj : N₀.G.Adj y₀ x := ((N₀.mem_rotList _ _).1 (by rw [hr]; simp)).symm
        rw [cFace_eq hN hr hadj]
        exact face_step hxy hy₀.symm hadj
    · have he := Finset.mem_toList.1 hb
      rw [P.mem_extras] at he
      rw [padLab_right hN he.1]
      rcases List.mem_append.1 hmem with hb' | hb'
      · obtain ⟨a₀, l, hA, hstep⟩ := formPerm_append_right hnd hb hb'
        obtain ⟨y₀, l', hr, rfl, -⟩ := List.map_eq_cons_iff.1 hA
        have hadj : N₀.G.Adj y₀ x := ((N₀.mem_rotList _ _).1 (by rw [hr]; simp)).symm
        rw [hstep, padLab_real hN hadj, cFace_eq hN hr hadj]
      · have he' := Finset.mem_toList.1 hb'
        rw [P.mem_extras] at he'
        exact padLab_left hN he'.1 he'.2
  · rw [padList_of_not ha] at hab ⊢
    rw [List.mem_singleton] at hab
    subst hab
    rw [List.formPerm_singleton, Equiv.Perm.one_apply]
    rw [padLab_right hN ha, padLab_left hN ha rfl]

include hN in
variable (P) in
/-- **The network with pendant nodes is planar.** -/
theorem padNet_planar (hP : N₀.toRot.Planar) (hc : N₀.toRot.Connected) {D : ℕ} (hD : N₀.DiamLE D) :
    (padNet P N₀).toRot.Planar := by
  classical
  obtain ⟨⟨d₀⟩, -⟩ := N₀.toRot.connected_iff.1 hc
  have hdiam := padNet_diam (P := P) hD
  have hne : Nonempty W := ⟨P.ι d₀.fst⟩
  have hG : (padNet P N₀).G.Connected :=
    { preconnected := fun u v => by
        obtain ⟨p, -⟩ := hdiam u v
        exact ⟨p⟩ }
  have hd' : (padNet P N₀).G.Adj (P.ι d₀.fst) (P.ι d₀.snd) := padNet_adj_ι d₀.adj
  have hc' : (padNet P N₀).toRot.Connected := (padNet P N₀).toRot_connected hG ⟨(_, _), hd'⟩
  refine RotSystem.planar_of_count _ hc' ?_
  have hfaces : N₀.toRot.numFaces ≤ (padNet P N₀).toRot.numFaces := by
    rw [← N₀.toRot.natCard_face]
    refine RotSystem.card_le_numFaces _ (fun z => padLab P hN z.fst z.snd) (fun z => ?_) (fun f => ?_)
    · exact padLab_step hN z.fst z.snd z.adj
    · obtain ⟨d, rfl⟩ := Quotient.exists_rep f
      exact ⟨⟨(P.ι d.fst, P.ι d.snd), padNet_adj_ι d.adj⟩, padLab_real hN d.adj⟩
  have h1 := (padNet P N₀).numVertices_eq (padNet_noIso hN)
  have h2 := N₀.numVertices_eq hN
  have h3 := (padNet P N₀).numEdges_eq
  have h4 := N₀.toRot.card_eq
  have h5 := N₀.toRot.euler hP hc
  have h6 := padNet_sum (P := P) (N₀ := N₀)
  have h7 := N₀.dart_card
  have h8 : ∑ a, ((padNet P N₀).rotList a).length = ∑ a, (padList P N₀ a).length := rfl
  omega

end Faces

end Pad

end Congest

end SsspFlow
