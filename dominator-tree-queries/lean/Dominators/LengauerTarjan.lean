import Dominators.DfsTree

/-!
# The dominator algorithm

An executable form of Section 2 of `README.md`. Vertices are processed in decreasing preorder, and `sd w` is
found by a minimum search over the predecessors of `w`. The minimum search is a parameter with a specification,
`IsMinFind`, as the search of `DFS.lean` is. Then `idom` is computed in increasing preorder as a nearest common
ancestor. Main result: `dominators_correct`. It assumes no classical theorem on dominators: the two facts it
needs are `IsDfsTree.sdom_formula` and `IsDfsTree.idom_iff_nca`.
-/

namespace Dominators

universe u

variable {V : Type u} [DecidableEq V] {E : V → V → Prop} {r : V} {T : DfsTree V}

/-- The specification of minimum finding over the predecessors of `w`: the value is the least of `f` on the
predecessors, and `⊤` if there are none. -/
structure IsMinFind (E : V → V → Prop) (minFind : V → (V → WithTop ℕ) → WithTop ℕ) : Prop where
  lower : ∀ w f v, E v w → minFind w f ≤ f v
  attained : ∀ w f, minFind w f = ⊤ ∨ ∃ v, E v w ∧ minFind w f = f v

/-- The smallest `sd u` over `u` on the forest path from `u` upward, while `u` is above `w`. -/
def climb (T : DfsTree V) (sd : V → WithTop ℕ) (w : V) : ℕ → V → WithTop ℕ
  | 0, _ => ⊤
  | k + 1, u =>
    if T.pre w < T.pre u then
      min (sd u) (match T.parent u with
        | some p => climb T sd w k p
        | none => ⊤)
    else ⊤

/-- `f_w(v)` of `README.md`. -/
def fval (T : DfsTree V) (sd : V → WithTop ℕ) (w v : V) : WithTop ℕ :=
  if v ∈ T.order then
    if T.pre v < T.pre w then (T.pre v : ℕ) else climb T sd w (T.pre v + 1) v
  else ⊤

/-- The semidominator pass, over vertices in decreasing preorder. -/
def sdomPass (minFind : V → (V → WithTop ℕ) → WithTop ℕ) (T : DfsTree V) :
    List V → (V → WithTop ℕ) → (V → WithTop ℕ)
  | [], sd => sd
  | w :: ws, sd => sdomPass minFind T ws (Function.update sd w (minFind w (fval T sd w)))

/-- The semidominator numbers of all tree vertices but the root. -/
def sdomTable (minFind : V → (V → WithTop ℕ) → WithTop ℕ) (T : DfsTree V) (r : V) : V → WithTop ℕ :=
  sdomPass minFind T (T.order.filter (· ≠ r)) (fun _ => ⊤)

/-! ## The climb -/

section Climb

theorem climb_spec (hT : IsDfsTree E r T) {sd : V → WithTop ℕ} {w : V} (k : ℕ) (u : V) (hu : Reach E r u)
    (hk : T.pre u < k) :
    (∀ a, Anc T.parent a u → T.pre w < T.pre a → climb T sd w k u ≤ sd a) ∧
      (climb T sd w k u = ⊤ ∨ ∃ a, Anc T.parent a u ∧ T.pre w < T.pre a ∧ climb T sd w k u = sd a) := by
  induction k generalizing u with
  | zero => omega
  | succ k ih =>
    rw [climb]
    split_ifs with hlt
    · cases hp : T.parent u with
      | none =>
        constructor
        · intro a hA _
          cases hA with
          | refl => simp
          | step h _ =>
            rw [hp] at h
            cases h
        · right
          exact ⟨u, .refl _, hlt, by simp⟩
      | some p =>
        obtain ⟨_, hrp, hplt⟩ := hT.parent_eq hu hp
        obtain ⟨h1, h2⟩ := ih p hrp (by omega)
        constructor
        · intro a hA ha
          simp only
          by_cases hau : a = u
          · rw [hau]
            exact min_le_left _ _
          · exact (min_le_right _ _).trans (h1 a (hA.of_ne hau hp) ha)
        · simp only
          rcases le_total (sd u) (climb T sd w k p) with hle | hle
          · right
            exact ⟨u, .refl _, hlt, min_eq_left hle⟩
          · rw [min_eq_right hle]
            rcases h2 with h2 | ⟨a, h3, h4, h5⟩
            · exact Or.inl h2
            · exact Or.inr ⟨a, .step hp h3, h4, h5⟩
    · constructor
      · intro a hA ha
        have := (hT.anc_le hu hA).1
        omega
      · exact Or.inl rfl

end Climb

/-! ## One semidominator step -/

/-- If `sd` is right for all vertices above `w`, then the minimum over the predecessors gives `sdom(w)`. -/
theorem sdom_step (hT : IsDfsTree E r T) {minFind : V → (V → WithTop ℕ) → WithTop ℕ}
    (hM : IsMinFind E minFind) {sd : V → WithTop ℕ} {w : V} (hw : Reach E r w) (hwr : w ≠ r)
    (hsd : ∀ x, Reach E r x → T.pre w < T.pre x → ∃ s, IsSdom E r T.pre s x ∧ sd x = (T.pre s : ℕ)) :
    ∃ s, IsSdom E r T.pre s w ∧ minFind w (fval T sd w) = (T.pre s : ℕ) := by
  obtain ⟨s, hs⟩ := hT.exists_sdom hw hwr
  refine ⟨s, hs, ?_⟩
  obtain ⟨hmem, hlow⟩ := hT.sdom_formula hw hwr hs
  have hle : ∀ k ∈ FormulaSet E r T w, minFind w (fval T sd w) ≤ (k : ℕ) := by
    rintro k (⟨v, hv, he, hlt, rfl⟩ | ⟨u, v, s', hv, he, hu, hA, hs', rfl⟩)
    · refine (hM.lower w _ v he).trans ?_
      simp [fval, (hT.mem_order v).mpr hv, hlt]
    · refine (hM.lower w _ v he).trans ?_
      have hnlt : ¬ T.pre v < T.pre w := by
        have := (hT.anc_le hv hA).1
        omega
      simp only [fval, (hT.mem_order v).mpr hv, ite_true, hnlt, ite_false]
      have hru : Reach E r u := (hT.anc_le hv hA).2.2
      obtain ⟨s'', h1, h2⟩ := hsd u hru hu
      have h3 := ((climb_spec hT (sd := sd) (w := w) (T.pre v + 1) v hv (by omega)).1 u hA hu)
      rw [h2, h1.pre_eq hs'] at h3
      exact h3
  have hge : (T.pre s : WithTop ℕ) ≤ minFind w (fval T sd w) := by
    rcases hM.attained w (fval T sd w) with h | ⟨v, he, h⟩
    · rw [h]
      exact le_top
    · rw [h]
      by_cases hv : v ∈ T.order
      · have hrv := (hT.mem_order v).mp hv
        simp only [fval, hv, ite_true]
        split_ifs with hlt
        · exact_mod_cast hlow (Or.inl ⟨v, hrv, he, hlt, rfl⟩)
        · rcases (climb_spec hT (sd := sd) (w := w) (T.pre v + 1) v hrv (by omega)).2 with h1 | ⟨a, h2, h3, h4⟩
          · rw [h1]
            exact le_top
          · rw [h4]
            have hra : Reach E r a := (hT.anc_le hrv h2).2.2
            obtain ⟨s'', h5, h6⟩ := hsd a hra h3
            rw [h6]
            exact_mod_cast hlow (Or.inr ⟨a, v, s'', hrv, he, h3, h2, h5, rfl⟩)
      · simp [fval, hv]
  exact le_antisymm (hle _ hmem) hge

/-- The semidominator pass is correct. -/
theorem sdomPass_spec (hT : IsDfsTree E r T) {minFind : V → (V → WithTop ℕ) → WithTop ℕ}
    (hM : IsMinFind E minFind) (ws : List V) (sd : V → WithTop ℕ)
    (hws : ws.Pairwise (fun a b => T.pre b < T.pre a))
    (hwr : ∀ x ∈ ws, Reach E r x ∧ x ≠ r)
    (hdone : ∀ x, Reach E r x → x ≠ r → x ∉ ws →
      (∃ s, IsSdom E r T.pre s x ∧ sd x = (T.pre s : ℕ)) ∧ ∀ y ∈ ws, T.pre y < T.pre x) :
    ∀ x, Reach E r x → x ≠ r → ∃ s, IsSdom E r T.pre s x ∧ sdomPass minFind T ws sd x = (T.pre s : ℕ) := by
  induction ws generalizing sd with
  | nil =>
    intro x hx hxr
    exact (hdone x hx hxr (by simp)).1
  | cons w ws ih =>
    rw [sdomPass]
    obtain ⟨hrw, hne⟩ := hwr w (by simp)
    obtain ⟨h1, h2⟩ := List.pairwise_cons.mp hws
    have hab : ∀ x, Reach E r x → T.pre w < T.pre x → ∃ s, IsSdom E r T.pre s x ∧ sd x = (T.pre s : ℕ) := by
      intro x hx hlt
      have hxr : x ≠ r := by
        rintro rfl
        have := hT.root_le hrw
        omega
      have hxn : x ∉ w :: ws := by
        intro hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · omega
        · have := h1 x hmem
          omega
      exact (hdone x hx hxr hxn).1
    apply ih _ h2 (fun x hx => hwr x (by simp [hx]))
    intro x hx hxr hxn
    by_cases hxw : x = w
    · subst hxw
      obtain ⟨s, hs, hv⟩ := sdom_step hT hM hx hxr hab
      refine ⟨⟨s, hs, ?_⟩, fun y hy => h1 y hy⟩
      rw [Function.update_self]
      exact hv
    · have hxn' : x ∉ w :: ws := by
        simp [hxw, hxn]
      obtain ⟨⟨s, hs, hv⟩, h3⟩ := hdone x hx hxr hxn'
      refine ⟨⟨s, hs, ?_⟩, fun y hy => h3 y (by simp [hy])⟩
      rw [Function.update_of_ne hxw]
      exact hv

/-- The table of semidominator numbers is right. -/
theorem sdomTable_spec (hT : IsDfsTree E r T) {minFind : V → (V → WithTop ℕ) → WithTop ℕ}
    (hM : IsMinFind E minFind) {x : V} (hx : Reach E r x) (hxr : x ≠ r) :
    ∃ s, IsSdom E r T.pre s x ∧ sdomTable minFind T r x = (T.pre s : ℕ) := by
  refine sdomPass_spec hT hM _ _ (hT.sorted.filter _) ?_ ?_ x hx hxr
  · intro y hy
    obtain ⟨h1, h2⟩ := List.mem_filter.mp hy
    exact ⟨(hT.mem_order y).mp h1, by simpa using h2⟩
  · intro y hy hyr hyn
    exfalso
    apply hyn
    exact List.mem_filter.mpr ⟨(hT.mem_order y).mpr hy, by simpa using hyr⟩

/-! ## The dominator tree from the semidominators -/

/-- The nearest common ancestor in the dominator tree so far: climb from the larger of the two numbers. -/
def nca (T : DfsTree V) (d : V → V) : ℕ → V → V → V
  | 0, a, _ => a
  | k + 1, a, b =>
    if a = b then a
    else if T.pre a < T.pre b then nca T d k a (d b)
    else nca T d k (d a) b

/-- The vertex with a given number. -/
def vertexAt (T : DfsTree V) (k : WithTop ℕ) : Option V :=
  T.order.find? (fun x => decide ((T.pre x : WithTop ℕ) = k))

/-- The immediate dominator of `w` from the table so far. -/
def idomStep (T : DfsTree V) (sd : V → WithTop ℕ) (d : V → V) (w : V) : V :=
  match T.parent w, vertexAt T (sd w) with
  | some p, some s => nca T d (T.pre p + T.pre s + 1) p s
  | _, _ => w

/-- The immediate dominator pass, over vertices in increasing preorder. -/
def idomPass (T : DfsTree V) (sd : V → WithTop ℕ) : List V → (V → V) → (V → V)
  | [], d => d
  | w :: ws, d => idomPass T sd ws (Function.update d w (idomStep T sd d w))

/-- The nearest common ancestor is right, given a right table below the bound `B`. -/
theorem nca_spec (hT : IsDfsTree E r T) {d : V → V} {B : ℕ}
    (hd : ∀ x, Reach E r x → x ≠ r → T.pre x < B → IsIdom E r (d x) x) (k : ℕ) (a b : V)
    (ha : Reach E r a) (hb : Reach E r b) (haB : T.pre a < B) (hbB : T.pre b < B)
    (hk : T.pre a + T.pre b < k) : IsNCA E r a b (nca T d k a b) := by
  induction k generalizing a b with
  | zero => omega
  | succ k ih =>
    rw [nca]
    split_ifs with hab hlt
    · subst hab
      exact IsNCA.self a
    · have hbr : b ≠ r := by
        rintro rfl
        have := hT.root_le ha
        omega
      have hi := hd b hb hbr hbB
      have hA := hT.anc_of_dominates hb hi.2.2.1
      obtain ⟨_, h2, h3⟩ := hT.anc_le hb hA
      have hlt' := h2 hi.2.1
      have := ih a (d b) ha h3 haB (by omega) (by omega)
      exact this.of_idom hT ha hlt hi
    · have hne : T.pre a ≠ T.pre b := fun e => hab (hT.pre_inj a b ha hb e)
      have hlt2 : T.pre b < T.pre a := by omega
      have har : a ≠ r := by
        rintro rfl
        have := hT.root_le hb
        omega
      have hi := hd a ha har haB
      have hA := hT.anc_of_dominates ha hi.2.2.1
      obtain ⟨_, h2, h3⟩ := hT.anc_le ha hA
      have hlt' := h2 hi.2.1
      have := ih (d a) b h3 hb (by omega) hbB (by omega)
      exact (this.symm.of_idom hT hb hlt2 hi).symm

omit [DecidableEq V] in
theorem vertexAt_pre (hT : IsDfsTree E r T) {s : V} (hs : Reach E r s) : vertexAt T (T.pre s : ℕ) = some s := by
  have hmem : s ∈ T.order := (hT.mem_order s).mpr hs
  have hfind : (T.order.find? (fun x => decide ((T.pre x : WithTop ℕ) = (T.pre s : ℕ)))).isSome := by
    rw [List.find?_isSome]
    exact ⟨s, hmem, by simp⟩
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hfind
  have hy1 := List.mem_of_find?_eq_some hy
  have hy2 := List.find?_some hy
  simp only [decide_eq_true_eq, Nat.cast_inj] at hy2
  have : y = s := hT.pre_inj y s ((hT.mem_order y).mp hy1) hs (by exact_mod_cast hy2)
  rw [vertexAt, hy, this]

/-- One step of the immediate dominator pass is right. -/
theorem idomStep_spec (hT : IsDfsTree E r T) {sd : V → WithTop ℕ}
    (hsd : ∀ x, Reach E r x → x ≠ r → ∃ s, IsSdom E r T.pre s x ∧ sd x = (T.pre s : ℕ)) {d : V → V} {w : V}
    (hw : Reach E r w) (hwr : w ≠ r) (hd : ∀ x, Reach E r x → x ≠ r → T.pre x < T.pre w → IsIdom E r (d x) x) :
    IsIdom E r (idomStep T sd d w) w := by
  obtain ⟨p, hp, he, hrp, hplt⟩ := hT.parent_spec w hw hwr
  obtain ⟨s, hs, hsv⟩ := hsd w hw hwr
  have hslt := hT.sdom_lt hw hwr hs
  have hv : vertexAt T (sd w) = some s := by
    rw [hsv]
    exact vertexAt_pre hT hs.reach
  have hstep : idomStep T sd d w = nca T d (T.pre p + T.pre s + 1) p s := by
    simp [idomStep, hp, hv]
  rw [hstep, hT.idom_iff_nca hw hwr hp hs]
  exact nca_spec hT hd _ p s hrp hs.reach hplt hslt (by omega)

/-- The immediate dominator pass is correct. -/
theorem idomPass_spec (hT : IsDfsTree E r T) {sd : V → WithTop ℕ}
    (hsd : ∀ x, Reach E r x → x ≠ r → ∃ s, IsSdom E r T.pre s x ∧ sd x = (T.pre s : ℕ)) (ws : List V)
    (d : V → V) (hws : ws.Pairwise (fun a b => T.pre a < T.pre b)) (hwr : ∀ x ∈ ws, Reach E r x ∧ x ≠ r)
    (hdone : ∀ x, Reach E r x → x ≠ r → x ∉ ws → IsIdom E r (d x) x ∧ ∀ y ∈ ws, T.pre x < T.pre y) :
    ∀ x, Reach E r x → x ≠ r → IsIdom E r (idomPass T sd ws d x) x := by
  induction ws generalizing d with
  | nil =>
    intro x hx hxr
    exact (hdone x hx hxr (by simp)).1
  | cons w ws ih =>
    rw [idomPass]
    obtain ⟨hrw, hne⟩ := hwr w (by simp)
    obtain ⟨h1, h2⟩ := List.pairwise_cons.mp hws
    have hbelow : ∀ x, Reach E r x → x ≠ r → T.pre x < T.pre w → IsIdom E r (d x) x := by
      intro x hx hxr hlt
      have hxn : x ∉ w :: ws := by
        intro hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · omega
        · have := h1 x hmem
          omega
      exact (hdone x hx hxr hxn).1
    apply ih _ h2 (fun x hx => hwr x (by simp [hx]))
    intro x hx hxr hxn
    by_cases hxw : x = w
    · subst hxw
      refine ⟨?_, fun y hy => h1 y hy⟩
      rw [Function.update_self]
      exact idomStep_spec hT hsd hx hxr hbelow
    · have hxn' : x ∉ w :: ws := by
        simp [hxw, hxn]
      obtain ⟨h3, h4⟩ := hdone x hx hxr hxn'
      refine ⟨?_, fun y hy => h4 y (by simp [hy])⟩
      rw [Function.update_of_ne hxw]
      exact h3

/-! ## The whole algorithm -/

/-- The dominator tree from a search tree: `some u` means `idom(w) = u`, and `none` means that `w` is the root
or unreachable. -/
def idomOfTree (minFind : V → (V → WithTop ℕ) → WithTop ℕ) (T : DfsTree V) (r : V) : V → Option V :=
  let order := T.order.filter (· ≠ r)
  let d := idomPass T (sdomTable minFind T r) order.reverse id
  fun w => if w ∈ order then some (d w) else none

theorem idomOfTree_spec (hT : IsDfsTree E r T) {minFind : V → (V → WithTop ℕ) → WithTop ℕ}
    (hM : IsMinFind E minFind) (u w : V) : idomOfTree minFind T r w = some u ↔ IsIdom E r u w := by
  have hsd : ∀ x, Reach E r x → x ≠ r →
      ∃ s, IsSdom E r T.pre s x ∧ sdomTable minFind T r x = (T.pre s : ℕ) :=
    fun _ hx hxr => sdomTable_spec hT hM hx hxr
  have hmem : ∀ x, x ∈ T.order.filter (· ≠ r) ↔ Reach E r x ∧ x ≠ r := by
    intro x
    rw [List.mem_filter, hT.mem_order]
    simp
  have hd : ∀ x, Reach E r x → x ≠ r →
      IsIdom E r (idomPass T (sdomTable minFind T r) (T.order.filter (· ≠ r)).reverse id x) x := by
    refine idomPass_spec hT hsd _ _ ?_ ?_ ?_
    · rw [List.pairwise_reverse]
      exact hT.sorted.filter _
    · intro x hx
      exact (hmem x).mp (List.mem_reverse.mp hx)
    · intro x hx hxr hxn
      exact absurd (List.mem_reverse.mpr ((hmem x).mpr ⟨hx, hxr⟩)) hxn
  simp only [idomOfTree]
  constructor
  · intro h
    split_ifs at h with hw
    obtain ⟨hrw, hwr⟩ := (hmem w).mp hw
    cases h
    exact hd w hrw hwr
  · intro h
    have hwr : w ≠ r := by
      rintro rfl
      exact not_isIdom_root u h
    rw [ite_eq_left ((hmem w).mpr ⟨h.1, hwr⟩)]
    congr 1
    exact (hd w h.1 hwr).unique h

variable [Fintype V]

/-- **The dominator algorithm**: a search, the semidominator pass, the immediate dominator pass. -/
def dominators (search : V → Finset V → Option V) (minFind : V → (V → WithTop ℕ) → WithTop ℕ) (fuel : ℕ)
    (r : V) : V → Option V :=
  idomOfTree minFind (dfs search fuel r).tree r

/-- **Correctness of the dominator algorithm.** With a search and a minimum finding that meet their
specifications and `2n` fuel, the output is exactly the immediate dominator of each reachable non-root vertex,
and `none` for the others. No classical result on dominators is assumed. -/
theorem dominators_correct {search : V → Finset V → Option V}
    {minFind : V → (V → WithTop ℕ) → WithTop ℕ} (hS : IsSearch E search) (hM : IsMinFind E minFind)
    {fuel : ℕ} (hf : 2 * Fintype.card V ≤ fuel) (r u w : V) :
    dominators search minFind fuel r w = some u ↔ IsIdom E r u w :=
  idomOfTree_spec (dfs_isDfsTree hS hf r) hM u w

/-- The output is `none` exactly at the root and at unreachable vertices. So it shows the reachable set. -/
theorem dominators_none_iff {search : V → Finset V → Option V}
    {minFind : V → (V → WithTop ℕ) → WithTop ℕ} (hS : IsSearch E search) (hM : IsMinFind E minFind)
    {fuel : ℕ} (hf : 2 * Fintype.card V ≤ fuel) (r w : V) :
    dominators search minFind fuel r w = none ↔ w = r ∨ ¬ Reach E r w := by
  constructor
  · intro h
    by_contra hno
    push Not at hno
    obtain ⟨u, hu⟩ := exists_idom hno.2 hno.1
    have := (dominators_correct hS hM hf r u w).mpr hu
    rw [h] at this
    cases this
  · intro h
    by_contra hne
    obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hne
    have hi := (dominators_correct hS hM hf r u w).mp hu
    rcases h with rfl | h
    · exact not_isIdom_root u hi
    · exact h hi.1

end Dominators
