import SsspFlow.NetPad

/-!
# Rotation systems from lists

A rotation system given by a list of darts at each vertex: each dart lies in the list of its tail,
each list has no repetitions, and the rotation sends a dart to the next one in its list, cyclically.
Parallel edges and loops are allowed.

* `ListData.toRot`: the rotation system.
* `ListData.tail_eq_iff`: two darts have the same vertex exactly when they have the same tail, so
  `ListData.numVertices_eq`: the vertices are the tails that occur.
* `rel_formPerm_of_isChain`: a relation that holds between neighbours of a list, read cyclically,
  holds between each element and its image under the cycle of the list.
* `ListData.lab_rev_rot`, `ListData.lab_rev_rot_of_mem`: a label of the darts that agrees on every dart and the reverse of the next
  dart in its list is invariant along faces.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor

namespace RotSystem

/-- A rotation system given by the list of darts at each vertex. -/
structure ListData (D V : Type*) [Fintype D] [DecidableEq D] where
  rev : D → D
  rev_rev : ∀ x, rev (rev x) = x
  rev_ne : ∀ x, rev x ≠ x
  /-- The vertex at which a dart starts. -/
  tl : D → V
  /-- The darts at a vertex, in rotation order. -/
  lst : V → List D
  nodup : ∀ v, (lst v).Nodup
  mem_iff : ∀ v x, x ∈ lst v ↔ tl x = v

/-- A relation between each element of a list and the next one, cyclically, holds between each
element and its image under the cycle of the list. -/
theorem rel_formPerm_of_isChain {α : Type*} [DecidableEq α] {R : α → α → Prop} {l : List α}
    (hn : l.Nodup) (h : List.IsChain R (l ++ l.take 1)) {x : α} (hx : x ∈ l) :
    R x (l.formPerm x) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [List.formPerm_apply_getElem _ hn]
  have hl : (l ++ l.take 1).length = l.length + 1 := by
    simp only [List.length_append, List.length_take]; omega
  have h1 := h.getElem i (by omega)
  rw [List.getElem_append_left hi] at h1
  by_cases hs : i + 1 < l.length
  · rw [List.getElem_append_left hs] at h1
    convert h1 using 2
    exact Nat.mod_eq_of_lt hs
  · have he : i + 1 = l.length := by omega
    have h0 : (i + 1) % l.length = 0 := by rw [he, Nat.mod_self]
    convert h1 using 1
    rw [List.getElem_append_right (by omega)]
    simp [h0, he]

/-- The cycle of a list commutes with an injective map. -/
theorem formPerm_map_apply {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) {l : List α} (hn : l.Nodup) {c : α} (hc : c ∈ l) :
    (l.map f).formPerm (f c) = f (l.formPerm c) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have hi' : i < (l.map f).length := by simpa using hi
  have h := List.formPerm_apply_getElem (l.map f) (hn.map hf) i hi'
  simp only [List.getElem_map, List.length_map] at h
  rw [h, List.formPerm_apply_getElem _ hn]

namespace ListData

variable {D V : Type*} [Fintype D] [DecidableEq D] (L : ListData D V)

theorem mem_self (x : D) : x ∈ L.lst (L.tl x) := (L.mem_iff _ _).2 rfl

theorem tl_formPerm (x : D) : L.tl ((L.lst (L.tl x)).formPerm x) = L.tl x :=
  (L.mem_iff _ _).1 (List.formPerm_apply_mem_of_mem (L.mem_self x))

theorem tl_formPerm_symm (x : D) : L.tl ((L.lst (L.tl x)).formPerm.symm x) = L.tl x := by
  apply (L.mem_iff _ _).1
  apply List.formPerm_mem_iff_mem.1
  rw [Equiv.apply_symm_apply]
  exact L.mem_self x

/-- The rotation: the next dart in the list of the tail. -/
def rotPerm : Equiv.Perm D where
  toFun x := (L.lst (L.tl x)).formPerm x
  invFun x := (L.lst (L.tl x)).formPerm.symm x
  left_inv x := by
    show (L.lst (L.tl ((L.lst (L.tl x)).formPerm x))).formPerm.symm ((L.lst (L.tl x)).formPerm x) = x
    rw [L.tl_formPerm, Equiv.symm_apply_apply]
  right_inv x := by
    show (L.lst (L.tl ((L.lst (L.tl x)).formPerm.symm x))).formPerm ((L.lst (L.tl x)).formPerm.symm x) = x
    rw [L.tl_formPerm_symm, Equiv.apply_symm_apply]

/-- The rotation system of the lists. -/
def toRot : RotSystem D := ⟨L.rev, L.rev_rev, L.rev_ne, L.rotPerm⟩

theorem rot_apply (x : D) : L.toRot.rot x = (L.lst (L.tl x)).formPerm x := rfl

@[simp] theorem rev_apply (x : D) : L.toRot.rev x = L.rev x := rfl

theorem tl_rot (x : D) : L.tl (L.toRot.rot x) = L.tl x := L.tl_formPerm x

theorem tl_rot_pow (n : ℕ) (x : D) : L.tl ((L.toRot.rot ^ n) x) = L.tl x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, L.tl_rot, ih]

theorem rot_pow_eq {v : V} (n : ℕ) {x : D} (hx : L.tl x = v) :
    (L.toRot.rot ^ n) x = ((L.lst v).formPerm ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ', Equiv.Perm.mul_apply, L.rot_apply]
    congr 2
    rw [← ih, L.tl_rot_pow, hx]

/-- Two darts have the same vertex exactly when they have the same tail. -/
theorem tail_eq_iff (x y : D) : L.toRot.tail x = L.toRot.tail y ↔ L.tl x = L.tl y := by
  show Quotient.mk _ x = Quotient.mk _ y ↔ _
  rw [Quotient.eq]
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq h
    exact (L.tl_rot_pow n x).symm
  · intro h
    obtain ⟨v, hv⟩ : ∃ v, L.tl x = v := ⟨_, rfl⟩
    have hx : x ∈ L.lst v := (L.mem_iff _ _).2 hv
    have hy : y ∈ L.lst v := (L.mem_iff _ _).2 (h.symm.trans hv)
    obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
    obtain ⟨j, hj, hyj⟩ := List.getElem_of_mem hy
    refine ⟨((j + (L.lst v).length - i : ℕ) : ℤ), ?_⟩
    rw [zpow_natCast, L.rot_pow_eq _ hv, ← hxi, List.formPerm_pow_apply_getElem _ (L.nodup _)]
    convert hyj using 2
    rw [show i + (j + (L.lst v).length - i) = j + (L.lst v).length by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hj]

/-- The vertices of the rotation system are the tails that occur. -/
theorem numVertices_eq [DecidableEq V] : L.toRot.numVertices = (Finset.univ.image L.tl).card := by
  have h := fcard_eq_card_image L.toRot.toHypermap.cnode_sym L.tl
    fun x y => (L.toRot.tail_eq_iff x y).symm.trans (L.tail_eq_iff x y)
  unfold RotSystem.numVertices
  exact h

/-- A label that agrees on each dart of a list and the reverse of the next dart is invariant along
faces. -/
theorem lab_rev_rot {β : Type*} (lab : D → β)
    (h : ∀ v (i : ℕ) (hi : i < (L.lst v).length),
      lab (L.rev ((L.lst v)[(i + 1) % (L.lst v).length]'(Nat.mod_lt _ (by omega)))) =
        lab ((L.lst v)[i])) (z : D) : lab (L.toRot.rev (L.toRot.rot z)) = lab z := by
  obtain ⟨v, hv⟩ : ∃ v, L.tl z = v := ⟨_, rfl⟩
  obtain ⟨i, hi, hz⟩ := List.getElem_of_mem ((L.mem_iff _ _).2 hv)
  have key := List.formPerm_apply_getElem _ (L.nodup v) i hi
  rw [hz] at key
  rw [rev_apply, L.rot_apply, hv, key]
  conv_rhs => rw [← hz]
  exact h v i hi

/-- A label that agrees on each dart and the reverse of its image under the cycle of its list is
invariant along faces. -/
theorem lab_rev_rot_of_mem {β : Type*} (lab : D → β)
    (h : ∀ v, ∀ x ∈ L.lst v, lab (L.rev ((L.lst v).formPerm x)) = lab x) (z : D) :
    lab (L.toRot.rev (L.toRot.rot z)) = lab z :=
  h _ _ (L.mem_self z)

end ListData

end RotSystem

end SsspFlow
