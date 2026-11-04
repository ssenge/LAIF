import Dominators.DFS
import Dominators.Semidom

/-!
# The executable search produces a depth-first tree

`dfs_isDfsTree`: the preorder numbers, parents and order computed by `dfs` satisfy `IsDfsTree`. So the theorems
of `Semidom.lean` apply to the output of the algorithm, and the tree properties are not assumed.
-/

namespace Dominators

universe u

variable {V : Type u} [DecidableEq V] {E : V → V → Prop}

/-- The tree computed by a search. -/
def St.tree (s : St V) : DfsTree V := ⟨s.pre, s.parent, s.order⟩

/-- Changing the parent of a vertex outside a set closed under parents does not change ancestors inside it. -/
theorem Anc.update_of_closed {p : V → Option V} {vis : V → Prop} {w : V} {q : Option V} (hw : ¬ vis w)
    (hcl : ∀ x y, vis x → p x = some y → vis y) {a x : V} (hx : vis x) (h : Anc p a x) :
    Anc (Function.update p w q) a x := by
  induction h with
  | refl => exact .refl _
  | @step x y hp _ ih =>
    have hxw : x ≠ w := fun e => hw (e ▸ hx)
    exact .step (by rw [Function.update_of_ne hxw]; exact hp) (ih (hcl x y hx hp))

theorem Anc.of_update_of_closed {p : V → Option V} {vis : V → Prop} {w : V} {q : Option V} (hw : ¬ vis w)
    (hcl : ∀ x y, vis x → p x = some y → vis y) {a x : V} (hx : vis x)
    (h : Anc (Function.update p w q) a x) : Anc p a x := by
  induction h with
  | refl => exact .refl _
  | @step x y hp _ ih =>
    have hxw : x ≠ w := fun e => hw (e ▸ hx)
    rw [Function.update_of_ne hxw] at hp
    exact .step hp (ih (hcl x y hx hp))

omit [DecidableEq V] in
/-- Ancestors of a visited vertex are visited. -/
theorem Anc.mem_of_closed {p : V → Option V} {vis : V → Prop}
    (hcl : ∀ x y, vis x → p x = some y → vis y) {a x : V} (hx : vis x) (h : Anc p a x) : vis a := by
  induction h with
  | refl => exact hx
  | @step x y hp _ ih => exact ih (hcl x y hx hp)

/-- The tree invariant of a search from `r`. -/
structure TInv (E : V → V → Prop) (r : V) (s : St V) : Prop where
  root_mem : r ∈ s.visited
  parent_root : s.parent r = none
  parent_new : ∀ x, x ∉ s.visited → s.parent x = none
  parent_spec : ∀ x, x ∈ s.visited → x ≠ r → ∃ p, s.parent x = some p ∧ E p x ∧ p ∈ s.visited ∧ s.pre p < s.pre x
  pre_lt : ∀ x ∈ s.visited, s.pre x < s.visited.card
  pre_inj : ∀ x ∈ s.visited, ∀ y ∈ s.visited, s.pre x = s.pre y → x = y
  mem_order : ∀ x, x ∈ s.order ↔ x ∈ s.visited
  sorted : s.order.Pairwise (fun a b => s.pre b < s.pre a)
  anc_stack : s.stack.Pairwise (fun x a => Anc s.parent a x)
  stack_closed : ∀ a, ∀ x ∈ s.stack, Anc s.parent a x → a ∈ s.stack
  stack_desc : ∀ a ∈ s.stack, ∀ y ∈ s.visited, s.pre a ≤ s.pre y → Anc s.parent a y
  forward : ∀ v ∈ s.visited, ∀ w ∈ s.visited, E v w → s.pre v < s.pre w → Anc s.parent v w
  interval : ∀ a, ∀ x ∈ s.visited, ∀ y ∈ s.visited, Anc s.parent a x → s.pre a ≤ s.pre y → s.pre y ≤ s.pre x →
    Anc s.parent a y

namespace TInv

variable {r : V} {s : St V}

theorem parent_closed (h : TInv E r s) (x y : V) (hx : x ∈ s.visited) (hp : s.parent x = some y) :
    y ∈ s.visited := by
  by_cases hxr : x = r
  · rw [hxr, h.parent_root] at hp
    cases hp
  · obtain ⟨p, h1, _, h3, _⟩ := h.parent_spec x hx hxr
    rw [hp] at h1
    cases h1
    exact h3

omit [DecidableEq V] in
theorem anc_le (h : TInv E r s) {a x : V} (hx : x ∈ s.visited) (hA : Anc s.parent a x) :
    s.pre a ≤ s.pre x ∧ (a ≠ x → s.pre a < s.pre x) := by
  induction hA with
  | refl => exact ⟨le_rfl, fun h => absurd rfl h⟩
  | @step x y hp _ ih =>
    have hxr : x ≠ r := by
      rintro rfl
      rw [h.parent_root] at hp
      cases hp
    obtain ⟨p, h1, _, h3, h4⟩ := h.parent_spec x hx hxr
    rw [hp] at h1
    cases h1
    have := (ih h3).1
    exact ⟨by omega, fun _ => by omega⟩

/-- Pushing the new vertex `w` under `v`, keeping the invariant. The fields other than `searches` are as in
`St.push`. -/
theorem push_found (h : TInv E r s) (hI : Inv E s) {v w : V} {rest : List V} (hst : s.stack = v :: rest)
    (he : E v w) (hw : w ∉ s.visited) (c : ℕ) :
    TInv E r { s.push w (some v) with searches := c } := by
  have hv : v ∈ s.visited := (hI.mem_visited v).mpr (Or.inl (by simp [hst]))
  have hwr : w ≠ r := fun e => hw (e ▸ h.root_mem)
  have hcl : ∀ x y, x ∈ s.visited → s.parent x = some y → y ∈ s.visited := h.parent_closed
  have hupd : ∀ {a x : V}, x ∈ s.visited → Anc s.parent a x →
      Anc (Function.update s.parent w (some v)) a x :=
    fun hx hA => Anc.update_of_closed (vis := fun t => t ∈ s.visited) hw hcl hx hA
  have hback : ∀ {a x : V}, x ∈ s.visited → Anc (Function.update s.parent w (some v)) a x →
      Anc s.parent a x :=
    fun hx hA => Anc.of_update_of_closed (vis := fun t => t ∈ s.visited) hw hcl hx hA
  have hpw : Function.update s.parent w (some v) w = some v := Function.update_self ..
  have hpre : ∀ x, x ≠ w → Function.update s.pre w s.visited.card x = s.pre x :=
    fun x hx => Function.update_of_ne hx _ _
  have hprew : Function.update s.pre w s.visited.card w = s.visited.card := Function.update_self ..
  have hchk := h.anc_stack
  rw [hst] at hchk
  have htop : ∀ a ∈ s.stack, Anc s.parent a v := by
    intro a ha
    rw [hst] at ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact .refl _
    · exact (List.pairwise_cons.mp hchk).1 a ha
  have hancw : ∀ a ∈ s.stack, Anc (Function.update s.parent w (some v)) a w := fun a ha =>
    .step hpw (hupd hv (htop a ha))
  refine
    { root_mem := by simp [St.push, h.root_mem]
      parent_root := ?_
      parent_new := ?_
      parent_spec := ?_
      pre_lt := ?_
      pre_inj := ?_
      mem_order := ?_
      sorted := ?_
      anc_stack := ?_
      stack_closed := ?_
      stack_desc := ?_
      forward := ?_
      interval := ?_ }
  · simp only [St.push]
    rw [Function.update_of_ne (Ne.symm hwr)]
    exact h.parent_root
  · intro x hx
    simp only [St.push, Finset.mem_insert, not_or] at hx ⊢
    rw [Function.update_of_ne hx.1]
    exact h.parent_new x hx.2
  · intro x hx hxr
    simp only [St.push, Finset.mem_insert] at hx ⊢
    rcases hx with rfl | hx
    · refine ⟨v, hpw, he, Or.inr hv, ?_⟩
      have hvw : v ≠ x := fun e => hw (e ▸ hv)
      rw [hpre v hvw, hprew]
      exact h.pre_lt v hv
    · have hxw : x ≠ w := fun e => hw (e ▸ hx)
      obtain ⟨p, h1, h2, h3, h4⟩ := h.parent_spec x hx hxr
      have hpw' : p ≠ w := fun e => hw (e ▸ h3)
      refine ⟨p, ?_, h2, Or.inr h3, ?_⟩
      · rw [Function.update_of_ne hxw]
        exact h1
      · rw [hpre p hpw', hpre x hxw]
        exact h4
  · intro x hx
    simp only [St.push, Finset.mem_insert, Finset.card_insert_of_notMem hw] at hx ⊢
    rcases hx with rfl | hx
    · rw [hprew]
      omega
    · have hxw : x ≠ w := fun e => hw (e ▸ hx)
      rw [hpre x hxw]
      have := h.pre_lt x hx
      omega
  · intro x hx y hy hxy
    simp only [St.push, Finset.mem_insert] at hx hy hxy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · rfl
    · have hyw : y ≠ x := fun e => hw (e ▸ hy)
      rw [hprew, hpre y hyw] at hxy
      have := h.pre_lt y hy
      omega
    · have hxw : x ≠ y := fun e => hw (e ▸ hx)
      rw [hprew, hpre x hxw] at hxy
      have := h.pre_lt x hx
      omega
    · have hxw : x ≠ w := fun e => hw (e ▸ hx)
      have hyw : y ≠ w := fun e => hw (e ▸ hy)
      rw [hpre x hxw, hpre y hyw] at hxy
      exact h.pre_inj x hx y hy hxy
  · intro x
    simp only [St.push, List.mem_cons, Finset.mem_insert, h.mem_order]
  · simp only [St.push]
    refine List.pairwise_cons.mpr ⟨?_, ?_⟩
    · intro b hb
      have hbv : b ∈ s.visited := (h.mem_order b).mp hb
      have hbw : b ≠ w := fun e => hw (e ▸ hbv)
      rw [hpre b hbw, hprew]
      exact h.pre_lt b hbv
    · refine h.sorted.imp_of_mem ?_
      intro a b ha hb hab
      have hav : a ∈ s.visited := (h.mem_order a).mp ha
      have hbv : b ∈ s.visited := (h.mem_order b).mp hb
      have haw : a ≠ w := fun e => hw (e ▸ hav)
      have hbw : b ≠ w := fun e => hw (e ▸ hbv)
      rw [hpre a haw, hpre b hbw]
      exact hab
  · simp only [St.push]
    refine List.pairwise_cons.mpr ⟨?_, ?_⟩
    · intro a ha
      exact hancw a ha
    · refine h.anc_stack.imp_of_mem ?_
      intro x a hx _ hA
      exact hupd ((hI.mem_visited x).mpr (Or.inl hx)) hA
  · intro a x hx hA
    change Anc (Function.update s.parent w (some v)) a x at hA
    simp only [St.push, List.mem_cons] at hx ⊢
    rcases hx with rfl | hx
    · cases hA with
      | refl => exact Or.inl rfl
      | step hp ha =>
        rw [hpw] at hp
        cases hp
        exact Or.inr (h.stack_closed a v (by simp [hst]) (hback hv ha))
    · have hxv : x ∈ s.visited := (hI.mem_visited x).mpr (Or.inl hx)
      exact Or.inr (h.stack_closed a x hx (hback hxv hA))
  · intro a ha y hy hle
    simp only [St.push, List.mem_cons, Finset.mem_insert] at ha hy hle ⊢
    rcases ha with rfl | ha
    · rcases hy with rfl | hy
      · exact .refl _
      · have hyw : y ≠ a := fun e => hw (e ▸ hy)
        rw [hprew, hpre y hyw] at hle
        have := h.pre_lt y hy
        omega
    · have hav : a ∈ s.visited := (hI.mem_visited a).mpr (Or.inl ha)
      have haw : a ≠ w := fun e => hw (e ▸ hav)
      rcases hy with rfl | hy
      · exact hancw a ha
      · have hyw : y ≠ w := fun e => hw (e ▸ hy)
        rw [hpre a haw, hpre y hyw] at hle
        exact hupd hy (h.stack_desc a ha y hy hle)
  · intro v' hv' w' hw' hee hlt
    simp only [St.push, Finset.mem_insert] at hv' hw' hlt ⊢
    rcases hw' with rfl | hw'
    · rcases hv' with rfl | hv'
      · omega
      · have hv'w : v' ≠ w' := fun e => hw (e ▸ hv')
        rcases (hI.mem_visited v').mp hv' with hs | hf
        · exact hancw v' hs
        · exact absurd (hI.closed v' hf w' hee) hw
    · have hww : w' ≠ w := fun e => hw (e ▸ hw')
      rcases hv' with rfl | hv'
      · rw [hprew, hpre w' hww] at hlt
        have := h.pre_lt w' hw'
        omega
      · have hvw : v' ≠ w := fun e => hw (e ▸ hv')
        rw [hpre v' hvw, hpre w' hww] at hlt
        exact hupd hw' (h.forward v' hv' w' hw' hee hlt)
  · intro a x hx y hy hA h1 h2
    change Anc (Function.update s.parent w (some v)) a x at hA
    simp only [St.push, Finset.mem_insert] at hx hy h1 h2 ⊢
    rcases hx with rfl | hx
    · -- `x` is the new vertex
      cases hA with
      | refl =>
        rcases hy with rfl | hy
        · exact .refl _
        · have hyw : y ≠ a := fun e => hw (e ▸ hy)
          rw [hprew, hpre y hyw] at h1
          have := h.pre_lt y hy
          omega
      | step hp ha =>
        rw [hpw] at hp
        cases hp
        have hat : a ∈ s.stack := h.stack_closed a v (by simp [hst]) (hback hv ha)
        rcases hy with rfl | hy
        · exact .step hpw ha
        · have hav : a ∈ s.visited := (hI.mem_visited a).mpr (Or.inl hat)
          have haw : a ≠ x := fun e => hw (e ▸ hav)
          have hyw : y ≠ x := fun e => hw (e ▸ hy)
          rw [hpre a haw, hpre y hyw] at h1
          exact hupd hy (h.stack_desc a hat y hy h1)
    · have hxw : x ≠ w := fun e => hw (e ▸ hx)
      have hA' := hback hx hA
      have hav : a ∈ s.visited := Anc.mem_of_closed (vis := fun t => t ∈ s.visited) hcl hx hA'
      have haw : a ≠ w := fun e => hw (e ▸ hav)
      rcases hy with rfl | hy
      · rw [hprew, hpre x hxw] at h2
        have := h.pre_lt x hx
        omega
      · have hyw : y ≠ w := fun e => hw (e ▸ hy)
        rw [hpre a haw, hpre y hyw] at h1
        rw [hpre y hyw, hpre x hxw] at h2
        exact hupd hy (h.interval a x hx y hy hA' h1 h2)

omit [DecidableEq V] in
/-- Popping keeps the invariant. -/
theorem pop (h : TInv E r s) (hI : Inv E s) {v : V} {rest : List V} (hst : s.stack = v :: rest) :
    TInv E r { s with stack := rest, finished := v :: s.finished, searches := s.searches + 1 } := by
  have hchk := h.anc_stack
  rw [hst] at hchk
  have hnd := hI.nodup
  rw [hst] at hnd
  have hv : v ∈ s.visited := (hI.mem_visited v).mpr (Or.inl (by simp [hst]))
  refine
    { root_mem := h.root_mem
      parent_root := h.parent_root
      parent_new := h.parent_new
      parent_spec := h.parent_spec
      pre_lt := h.pre_lt
      pre_inj := h.pre_inj
      mem_order := h.mem_order
      sorted := h.sorted
      anc_stack := (List.pairwise_cons.mp hchk).2
      stack_closed := ?_
      stack_desc := ?_
      forward := h.forward
      interval := h.interval }
  · intro a x hx hA
    have hxs : x ∈ s.stack := by simp [hst, hx]
    have ha := h.stack_closed a x hxs hA
    rw [hst] at ha
    rcases List.mem_cons.mp ha with rfl | ha
    · -- the top of the stack cannot be an ancestor of a vertex below it
      exfalso
      have hxv : x ∈ s.visited := (hI.mem_visited x).mpr (Or.inl hxs)
      have h1 := (h.anc_le hxv hA).1
      have hne : x ≠ a := by
        rintro rfl
        simp only [List.cons_append, List.nodup_cons, List.mem_append, not_or] at hnd
        exact hnd.1.1 hx
      have h2 := (h.anc_le hv ((List.pairwise_cons.mp hchk).1 x hx)).2 hne
      omega
    · exact ha
  · intro a ha y hy hle
    exact h.stack_desc a (by simp [hst, ha]) y hy hle

theorem step {search : V → Finset V → Option V} (hS : IsSearch E search) (h : TInv E r s) (hI : Inv E s) :
    TInv E r (Dominators.step search s) := by
  cases hst : s.stack with
  | nil => rwa [step_nil hst]
  | cons v rest =>
    cases hq : search v s.visited with
    | none =>
      rw [step_none hst hq]
      exact h.pop hI hst
    | some w =>
      rw [step_found hst hq]
      obtain ⟨he, hw⟩ := hS.found hq
      exact h.push_found hI hst he hw _

end TInv

/-- The invariant right after the root is pushed. -/
theorem TInv.start (r : V) : TInv E r ((St.init : St V).push r none) := by
  have hprew : Function.update (fun _ : V => 0) r 0 = fun _ => 0 := by
    funext x
    by_cases h : x = r
    · subst h
      simp
    · simp [Function.update_of_ne h]
  have hpar : Function.update (fun _ : V => (none : Option V)) r none = fun _ => none := by
    funext x
    by_cases h : x = r
    · subst h
      simp
    · simp [Function.update_of_ne h]
  refine
    { root_mem := by simp [St.init, St.push]
      parent_root := by simp [St.init, St.push]
      parent_new := by simp [St.init, St.push]
      parent_spec := ?_
      pre_lt := by simp [St.init, St.push]
      pre_inj := by simp [St.init, St.push]
      mem_order := by simp [St.init, St.push]
      sorted := by simp [St.init, St.push]
      anc_stack := by simp [St.init, St.push]
      stack_closed := ?_
      stack_desc := ?_
      forward := ?_
      interval := ?_ }
  · intro x hx hxr
    simp [St.init, St.push] at hx
    exact absurd hx hxr
  · intro a x hx hA
    simp only [St.init, St.push, List.mem_cons, List.not_mem_nil, or_false, hpar] at hx hA ⊢
    subst hx
    cases hA with
    | refl => rfl
    | step hp _ => simp at hp
  · intro a ha y hy _
    simp only [St.init, St.push, List.mem_cons, List.not_mem_nil, or_false] at ha
    simp [St.init, St.push] at hy
    rw [ha, hy]
    exact .refl _
  · intro v hv w hw _ _
    simp [St.init, St.push] at hv hw
    rw [hv, hw]
    exact .refl _
  · intro a x hx y hy hA _ _
    simp only [St.init, St.push, Finset.mem_insert, Finset.notMem_empty, or_false] at hx hy hA
    subst hx
    rw [hy]
    exact hA

/-- **The search produces a depth-first tree.** -/
theorem dfs_isDfsTree [Fintype V] {search : V → Finset V → Option V} (hS : IsSearch E search) {fuel : ℕ}
    (hf : 2 * Fintype.card V ≤ fuel) (r : V) : IsDfsTree E r (dfs search fuel r).tree := by
  have hdfs : dfs search fuel r = run search fuel ((St.init : St V).push r none) := by
    simp [dfs, visit, St.init]
  have hboth : TInv E r (dfs search fuel r) ∧ Inv E (dfs search fuel r) := by
    rw [hdfs]
    exact run_induct (fun t => TInv E r t ∧ Inv E t) (fun _ h => ⟨h.1.step hS h.2, h.2.step hS⟩) fuel _
      ⟨TInv.start r, Inv.init.push_root rfl (by simp [St.init])⟩
  obtain ⟨hT, _⟩ := hboth
  have hreach : ∀ x, x ∈ (dfs search fuel r).visited ↔ Reach E r x := dfs_visited_iff hS hf r
  refine
    { parent_root := hT.parent_root
      parent_spec := ?_
      pre_inj := ?_
      forward := ?_
      interval := ?_
      mem_order := ?_
      sorted := hT.sorted }
  · intro w hw hwr
    obtain ⟨p, h1, h2, h3, h4⟩ := hT.parent_spec w ((hreach w).mpr hw) hwr
    exact ⟨p, h1, h2, (hreach p).mp h3, h4⟩
  · intro x y hx hy hxy
    exact hT.pre_inj x ((hreach x).mpr hx) y ((hreach y).mpr hy) hxy
  · intro v w hv he hlt
    exact hT.forward v ((hreach v).mpr hv) w ((hreach w).mpr (hv.tail he)) he hlt
  · intro a x y hx hy hA h1 h2
    exact hT.interval a x ((hreach x).mpr hx) y ((hreach y).mpr hy) hA h1 h2
  · intro x
    exact (hT.mem_order x).trans (hreach x)

end Dominators
