import Arborescence.AlgoStruct

/-!
# Correctness of the algorithm

For a correct oracle, `solve` returns a minimum-cost arborescence, and `none` only if there is no arborescence.

The proof is an invariant `CInv` on the states. It follows Lemma 2 of the README, with one simplification: instead of
tightness and "exactly one entering edge", which give `cost = Σ y` in the README, the invariant `NodeC.costEq`
tracks the cost of the expansion of each node directly: `cost of the expansion of T entered at v + y v = total of T`,
where the total of `T` is the sum of the dual values below `T`. At the end `cost = Σ y`, and `weak_duality_list` of
`WeakDuality.lean` finishes the proof. Lemma 3 of `Lists.lean` gives the correctness of `Cheapest`.
-/

set_option linter.unusedSectionVars false

open Finset

namespace Arborescence

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Reachability along a function. -/
abbrev RT (P : V → V) : V → V → Prop := Relation.ReflTransGen fun a b => P a = b

theorem RT.step {P : V → V} {x y : V} (h : P x = y) : RT P x y := Relation.ReflTransGen.single h

theorem iterate_of_rt {P : V → V} {x y : V} (h : RT P x y) : ∃ k : ℕ, P^[k] x = y := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hb ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, by rw [Function.iterate_succ_apply', hk, hb]⟩

/-- The sum of dual values of sets that contain `x` and not `u`, the left side of inequality (1). -/
def Dsum (D : List (Finset V × ℤ)) (u x : V) : ℤ := dsum D fun Z => x ∈ Z ∧ u ∉ Z

/-- Inequality (1) for all edges with head `x`. -/
def Feas (g : Graph V) (D : List (Finset V × ℤ)) (x : V) : Prop :=
  ∀ u, u ≠ x → g.adj u x = true → Dsum D u x ≤ g.w u x

theorem dsum_cons (Z : Finset V) (c : ℤ) (D : List (Finset V × ℤ)) (P : Finset V → Prop) [DecidablePred P] :
    dsum ((Z, c) :: D) P = (if P Z then c else 0) + dsum D P := by
  by_cases h : P Z <;> simp [dsum, List.filter_cons, h]

theorem dsum_congr {D : List (Finset V × ℤ)} {P Q : Finset V → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ d ∈ D, P d.1 ↔ Q d.1) : dsum D P = dsum D Q := by
  unfold dsum
  congr 2
  exact List.filter_congr fun d hd => by simpa using h d hd

/-- The correctness facts about a group. -/
structure GroupC (g : Graph V) (y : V → ℤ) (G : Group V) : Prop where
  topK : ∃ I, ListShape g G.verts G.builtIn G.y0 G.K I G.entries G.complete ∧
    IsTopK (inEdges g G.verts) (buildF g G.builtIn G.y0) Prod.fst G.K I
  shift : ∃ t : ℤ, ∀ v ∈ G.verts, y v = G.y0 v + t

/-- The correctness facts about a current container. -/
structure NodeC (g : Graph V) (y : V → ℤ) (D : List (Finset V × ℤ)) (T : Node V) : Prop where
  tree : ∀ v ∈ T.verts, ∀ P : V → V, (∀ a ∈ T.verts, a ≠ v → P a = T.exp v a) → ∀ x ∈ T.verts, RT P x v
  edge : ∀ v ∈ T.verts, ∀ a ∈ T.verts, a ≠ v → g.adj (T.exp v a) a = true
  costEq : ∀ v ∈ T.verts, ∑ a ∈ T.verts.erase v, g.w (T.exp v a) a + y v = T.total
  groups : ∀ G ∈ T.groups, GroupC g y G
  lamin : ∀ d ∈ D, ∀ x ∈ T.verts, x ∈ d.1 → d.1 ⊆ T.verts
  feas : 2 ≤ T.verts.card → ∀ x ∈ T.verts, Feas g D x

/-- The correctness facts about a node that has selected. -/
structure SelC (g : Graph V) (y : V → ℤ) (D : List (Finset V × ℤ)) (T : Node V) : Prop where
  head : T.inE.2 ∈ T.verts
  src : T.inE.1 ∉ T.verts
  adj : g.adj T.inE.1 T.inE.2 = true
  tight : y T.inE.2 = g.w T.inE.1 T.inE.2
  feas : ∀ x ∈ T.verts, Feas g D x

/-- The correctness facts about what is attached. -/
structure AttC (g : Graph V) (D : List (Finset V × ℤ)) (A : Att V) : Prop where
  par_root : A.par g.root = g.root
  tree : ∀ P : V → V, (∀ a ∈ A.verts, a ≠ g.root → P a = A.par a) → ∀ x ∈ A.verts, RT P x g.root
  edge : ∀ a ∈ A.verts, a ≠ g.root → g.adj (A.par a) a = true
  cost : ∑ a ∈ A.verts.erase g.root, g.w (A.par a) a = A.total
  feas : ∀ x ∈ A.verts, x ≠ g.root → Feas g D x

/-- In a chain, the source of the selected edge of each node lies in the node before it. -/
def Chained : List (Node V) → Prop
  | [] => True
  | [_] => True
  | a :: b :: l => b.inE.1 ∈ a.verts ∧ Chained (b :: l)

theorem Chained.tail {a : Node V} {l : List (Node V)} (h : Chained (a :: l)) : Chained l := by
  cases l with
  | nil => trivial
  | cons b l => exact h.2

theorem Chained.of_append {l₁ l₂ : List (Node V)} (h : Chained (l₁ ++ l₂)) : Chained l₂ := by
  induction l₁ with
  | nil => exact h
  | cons a l ih => exact ih (Chained.tail h)

theorem Chained.prefix {l₁ l₂ : List (Node V)} (h : Chained (l₁ ++ l₂)) : Chained l₁ := by
  induction l₁ with
  | nil => trivial
  | cons a l ih =>
    cases l with
    | nil => trivial
    | cons b l => exact ⟨h.1, ih h.2⟩

/-- The invariant for correctness. -/
structure CInv (g : Graph V) (st : St V) : Prop where
  y_eq : ∀ x, st.y x = dsum st.duals fun Z => x ∈ Z
  dne : ∀ d ∈ st.duals, d.1.Nonempty
  droot : ∀ d ∈ st.duals, g.root ∉ d.1
  dsign : ∀ d ∈ st.duals, 2 ≤ d.1.card → 0 ≤ d.2
  att : AttC g st.duals st.A
  node : ∀ T ∈ tops st, NodeC g st.y st.duals T
  sel : ∀ T ∈ st.path, SelC g st.y st.duals T
  chain : Chained (st.cur.toList ++ st.path)
  total : st.A.total + ((tops st).map Node.total).sum = (st.duals.map Prod.snd).sum

/-! ## Build -/

theorem build_groupC {o : Oracle V} (ho : o.Correct) (g : Graph V) (C : Finset V) (y : V → ℤ)
    (verts : Finset V) (K : ℕ) : GroupC g y (build o g C y verts K) :=
  ⟨⟨_, build_shape ho.structural g C y verts K, ho _ _ _⟩, 0, fun _ _ => by simp [build]⟩

/-! ## The initial state -/

theorem init_cinv {o : Oracle V} (ho : o.Correct) (g : Graph V) {us : List V} (hroot : g.root ∉ us) :
    CInv g (initSt o g us) := by
  have htops : tops (initSt o g us) = us.map (Node.singleton o g) := by simp [tops, initSt]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp [initSt, dsum]
  · simp [initSt]
  · simp [initSt]
  · simp [initSt]
  · refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · intro P _ x hx
      have : x = g.root := by simpa [initSt] using hx
      rw [this]
    · intro a ha hne
      exact absurd (by simpa [initSt] using ha) hne
    · simp [initSt]
    · intro x hx hne
      exact absurd (by simpa [initSt] using hx) hne
  · intro T hT
    rw [htops] at hT
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hT
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro w hw P _ x hx
      have h1 : w = v := by simpa [Node.singleton] using hw
      have h2 : x = v := by simpa [Node.singleton] using hx
      rw [h1, h2]
    · intro w hw a ha hne
      have h1 : w = v := by simpa [Node.singleton] using hw
      have h2 : a = v := by simpa [Node.singleton] using ha
      exact absurd (h2.trans h1.symm) hne
    · intro w hw
      have h1 : w = v := by simpa [Node.singleton] using hw
      subst h1
      simp [Node.singleton, initSt]
    · intro G hG
      have : G = build o g {v} (fun _ => 0) {v} 1 := by simpa [Node.singleton] using hG
      rw [this]
      exact build_groupC ho g _ _ _ _
    · simp [initSt]
    · simp [Node.singleton]
  · simp [initSt]
  · simp [initSt, Chained]
  · rw [htops]
    simp only [initSt, List.map_map, List.map_nil, List.sum_nil, zero_add]
    have : ∀ l : List V, (l.map (Node.total ∘ Node.singleton o g)).sum = 0 := by
      intro l
      induction l with
      | nil => rfl
      | cons a l ih => simpa [Node.singleton] using ih
    exact this us

/-! ## Rebuilds -/

theorem refresh_groupC {o : Oracle V} (ho : o.Correct) {g : Graph V} {C : Finset V} {y : V → ℤ}
    {G : Group V} (hG : GroupC g y G) : GroupC g y (refresh o g C y G).1 := by
  unfold refresh
  cases headOut C G.entries with
  | some _ => exact hG
  | none =>
    simp only
    split_ifs with hc
    · exact hG
    · exact build_groupC ho g C y G.verts _

theorem refreshAll_groupC {o : Oracle V} (ho : o.Correct) {g : Graph V} {C : Finset V} {y : V → ℤ}
    {gs : List (Group V)} (h : ∀ G ∈ gs, GroupC g y G) :
    ∀ G ∈ (refreshAll o g C y gs).1, GroupC g y G := by
  induction gs with
  | nil => simp [refreshAll]
  | cons G gs ih =>
    intro G' hG'
    simp only [refreshAll, List.mem_cons] at hG'
    rcases hG' with rfl | hG'
    · exact refresh_groupC ho (h G (List.mem_cons_self ..))
    · exact ih (fun G'' hG'' => h G'' (List.mem_cons_of_mem _ hG'')) G' hG'

theorem refreshed_cinv {o : Oracle V} (ho : o.Correct) {g : Graph V} {st : St V} (h : CInv g st)
    {a : Node V} (hc : st.cur = some a) : CInv g (refreshed o g st a) := by
  set gs := (refreshAll o g a.verts st.y a.groups).1 with hgs
  have htops : tops (refreshed o g st a) = { a with groups := gs } :: (st.path ++ st.free) := by
    simp [tops, refreshed, hgs]
  have htops0 : tops st = a :: (st.path ++ st.free) := by simp [tops, hc]
  have hna := h.node a (by rw [htops0]; exact List.mem_cons_self ..)
  have hch0 : Chained (a :: st.path) := by simpa [hc] using h.chain
  refine ⟨h.y_eq, h.dne, h.droot, h.dsign, h.att, ?_, h.sel, ?_, ?_⟩
  · intro T hT
    rw [htops] at hT
    rcases List.mem_cons.mp hT with rfl | hT
    · exact ⟨hna.tree, hna.edge, hna.costEq, refreshAll_groupC ho hna.groups, hna.lamin, hna.feas⟩
    · exact h.node T (by rw [htops0]; exact List.mem_cons_of_mem _ hT)
  · show Chained ({ a with groups := gs } :: st.path)
    cases hp : st.path with
    | nil => trivial
    | cons b l =>
      rw [hp] at hch0
      exact hch0
  · have := h.total
    rw [htops0] at this
    rw [htops]
    simpa [refreshed] using this

/-! ## Cheapest -/

theorem cheapest_none {o : Oracle V} {g : Graph V} {C : Finset V} {y : V → ℤ}
    {gs : List (Group V)} (hS : ∀ G ∈ gs, GroupS g C G) (hC : ∀ G ∈ gs, GroupC g y G)
    (hcompl : ∀ G ∈ gs, headOut C G.entries = none → G.complete = true)
    (hcov : ∀ x, x ∈ C ↔ ∃ G ∈ gs, x ∈ G.verts)
    (h : minBy (redCost g y) (heads C gs) = none) :
    ∀ u v, g.adj u v = true → v ∈ C → u ∈ C := by
  intro u v huv hv
  obtain ⟨G, hG, hvG⟩ := (hcov v).mp hv
  have hempty := minBy_none h
  have hhead : headOut C G.entries = none := by
    cases hh : headOut C G.entries with
    | none => rfl
    | some e =>
      have : e ∈ heads C gs := List.mem_filterMap.mpr ⟨G, hG, hh⟩
      rw [hempty] at this
      simp at this
  obtain ⟨I, hI, htk⟩ := (hC G hG).topK
  exact lemma3b hI htk (hS G hG).built (hcompl G hG hhead) hhead u v huv hvG

theorem cheapest_some {g : Graph V} {C : Finset V} {y : V → ℤ}
    {gs : List (Group V)} (hS : ∀ G ∈ gs, GroupS g C G) (hC : ∀ G ∈ gs, GroupC g y G)
    (hcompl : ∀ G ∈ gs, headOut C G.entries = none → G.complete = true)
    (hcov : ∀ x, x ∈ C ↔ ∃ G ∈ gs, x ∈ G.verts) {e : V × V}
    (h : minBy (redCost g y) (heads C gs) = some e) :
    g.adj e.1 e.2 = true ∧ e.2 ∈ C ∧ e.1 ∉ C ∧
      ∀ u v, g.adj u v = true → v ∈ C → u ∉ C → redCost g y e ≤ g.w u v - y v := by
  obtain ⟨he, hmin⟩ := minBy_some h
  obtain ⟨G, hG, hh⟩ := List.mem_filterMap.mp he
  obtain ⟨I, hI, htk⟩ := (hC G hG).topK
  obtain ⟨t, ht⟩ := (hC G hG).shift
  obtain ⟨h1, h2, h3, _⟩ := lemma3a hI htk (hS G hG).built ht hh
  refine ⟨h1, (hcov _).mpr ⟨G, hG, h2⟩, h3, ?_⟩
  intro u v huv hv hu
  obtain ⟨G', hG', hvG'⟩ := (hcov v).mp hv
  obtain ⟨I', hI', htk'⟩ := (hC G' hG').topK
  obtain ⟨t', ht'⟩ := (hC G' hG').shift
  cases hh' : headOut C G'.entries with
  | none =>
    exact absurd (lemma3b hI' htk' (hS G' hG').built (hcompl G' hG' hh') hh' u v huv hvG') hu
  | some e' =>
    obtain ⟨_, _, _, h4⟩ := lemma3a hI' htk' (hS G' hG').built ht' hh'
    have h5 := hmin e' (List.mem_filterMap.mpr ⟨G', hG', hh'⟩)
    exact h5.trans (h4 u v huv hvG' hu)

/-! ## Selection -/

theorem Feas.cons_of_notMem {g : Graph V} {D : List (Finset V × ℤ)} {x : V} (h : Feas g D x) {Z : Finset V}
    (c : ℤ) (hx : x ∉ Z) : Feas g ((Z, c) :: D) x := by
  intro u hu ha
  have := h u hu ha
  simpa [Dsum, dsum_cons, hx] using this

theorem addOn_of_notMem {y : V → ℤ} {X : Finset V} {c : ℤ} {x : V} (h : x ∉ X) : addOn y X c x = y x := by
  simp [addOn, h]

theorem addOn_of_mem {y : V → ℤ} {X : Finset V} {c : ℤ} {x : V} (h : x ∈ X) : addOn y X c x = y x + c := by
  simp [addOn, h]

/-- A node other than the selected one keeps its facts. -/
theorem NodeC.of_select {g : Graph V} {y : V → ℤ} {D : List (Finset V × ℤ)} {T : Node V} (h : NodeC g y D T)
    (hS : NodeS g T) {Z : Finset V} {c : ℤ} (hd : Disjoint T.verts Z) :
    NodeC g (addOn y Z c) ((Z, c) :: D) T := by
  have hnot : ∀ x ∈ T.verts, x ∉ Z := fun x hx => Finset.disjoint_left.mp hd hx
  refine ⟨h.tree, h.edge, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [addOn_of_notMem (hnot v hv)]
    exact h.costEq v hv
  · intro G hG
    obtain ⟨t, ht⟩ := (h.groups G hG).shift
    refine ⟨(h.groups G hG).topK, t, fun v hv => ?_⟩
    rw [addOn_of_notMem (hnot v ((hS.cover v).mpr ⟨G, hG, hv⟩))]
    exact ht v hv
  · intro d hd' x hx hxd
    rcases List.mem_cons.mp hd' with rfl | hd'
    · exact absurd hxd (hnot x hx)
    · exact h.lamin d hd' x hx hxd
  · intro h2 x hx
    exact (h.feas h2 x hx).cons_of_notMem c (hnot x hx)

/-- For a vertex of a container and a source outside, the sum in (1) is the offset. -/
theorem dsum_eq_y {g : Graph V} {y : V → ℤ} {D : List (Finset V × ℤ)} {T : Node V} (h : NodeC g y D T)
    (hy : ∀ x, y x = dsum D fun Z => x ∈ Z) {u x : V} (hx : x ∈ T.verts) (hu : u ∉ T.verts) :
    Dsum D u x = y x := by
  rw [hy x, Dsum]
  refine dsum_congr fun d hd => ?_
  constructor
  · exact fun h1 => h1.1
  · exact fun h1 => ⟨h1, fun h2 => hu (h.lamin d hd x hx h1 h2)⟩

theorem select_feas {g : Graph V} {y : V → ℤ} {D : List (Finset V × ℤ)} {T : Node V} (h : NodeC g y D T)
    (hy : ∀ x, y x = dsum D fun Z => x ∈ Z) {c : ℤ}
    (hmin : ∀ u v, g.adj u v = true → v ∈ T.verts → u ∉ T.verts → c ≤ g.w u v - y v) :
    ∀ x ∈ T.verts, Feas g ((T.verts, c) :: D) x := by
  intro x hx u hux ha
  by_cases hu : u ∈ T.verts
  · have h2 : 2 ≤ T.verts.card := by
      have : ({u, x} : Finset V) ⊆ T.verts := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hu
        · rw [Finset.mem_singleton.mp hz]
          exact hx
      have h3 := Finset.card_le_card this
      rwa [Finset.card_pair hux] at h3
    have := h.feas h2 x hx u hux ha
    simpa [Dsum, dsum_cons, hu] using this
  · have h1 := hmin u x ha hx hu
    have h2 := dsum_eq_y h hy hx hu
    have h3 : Dsum ((T.verts, c) :: D) u x = c + Dsum D u x := by
      simp [Dsum, dsum_cons, hx, hu]
    rw [h3, h2]
    omega

theorem selected_cinv {g : Graph V} {st : St V} (h : CInv g st) (hS : ∀ T ∈ tops st, NodeS g T)
    (hdis : ((tops st).map Node.verts).Pairwise Disjoint) (hdA : ∀ T ∈ tops st, Disjoint T.verts st.A.verts)
    (hroot : g.root ∈ st.A.verts)
    {a : Node V} (hc : st.cur = some a) {e : V × V}
    (he : g.adj e.1 e.2 = true ∧ e.2 ∈ a.verts ∧ e.1 ∉ a.verts ∧
      ∀ u v, g.adj u v = true → v ∈ a.verts → u ∉ a.verts → redCost g st.y e ≤ g.w u v - st.y v) :
    CInv g { (selected st a e (redCost g st.y e)).1 with
      path := (selected st a e (redCost g st.y e)).2 :: (selected st a e (redCost g st.y e)).1.path } := by
  obtain ⟨he1, he2, he3, hmin⟩ := he
  set c := redCost g st.y e with hcdef
  set a₁ := (selected st a e c).2 with ha₁
  have htops0 : tops st = a :: (st.path ++ st.free) := by simp [tops, hc]
  have hna := h.node a (by rw [htops0]; exact List.mem_cons_self ..)
  have hSa := hS a (by rw [htops0]; exact List.mem_cons_self ..)
  have hdis' := hdis
  rw [htops0, List.map_cons, List.pairwise_cons] at hdis'
  have hother : ∀ T ∈ st.path ++ st.free, Disjoint T.verts a.verts := fun T hT =>
    (hdis'.1 _ (List.mem_map_of_mem hT)).symm
  have hmemO : ∀ T ∈ st.path ++ st.free, T ∈ tops st := fun T hT => by
    rw [htops0]
    exact List.mem_cons_of_mem _ hT
  have hch0 : Chained (a :: st.path) := by simpa [hc] using h.chain
  have hfeas := select_feas hna h.y_eq hmin
  have hr : g.root ∉ a.verts := fun hr' =>
    Finset.disjoint_left.mp (hdA a (by rw [htops0]; exact List.mem_cons_self ..)) hr' hroot
  have hy1 : addOn st.y a.verts c e.2 = g.w e.1 e.2 := by
    rw [addOn_of_mem he2, hcdef, redCost]
    omega
  have ha₁C : NodeC g (addOn st.y a.verts c) ((a.verts, c) :: st.duals) a₁ := by
    refine ⟨hna.tree, hna.edge, ?_, ?_, ?_, fun _ => hfeas⟩
    · intro v hv
      have hv' : v ∈ a.verts := hv
      have := hna.costEq v hv'
      rw [addOn_of_mem hv']
      show ∑ x ∈ a.verts.erase v, g.w (a.exp v x) x + (st.y v + c) = a.total + c
      omega
    · intro G hG
      obtain ⟨t, ht⟩ := (hna.groups G hG).shift
      refine ⟨(hna.groups G hG).topK, t + c, fun v hv => ?_⟩
      rw [addOn_of_mem ((hSa.cover v).mpr ⟨G, hG, hv⟩), ht v hv]
      omega
    · intro d hd x hx hxd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact Finset.Subset.refl _
      · exact hna.lamin d hd x hx hxd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    show addOn st.y a.verts c x = dsum ((a.verts, c) :: st.duals) fun Z => x ∈ Z
    rw [dsum_cons, ← h.y_eq x]
    by_cases hx : x ∈ a.verts
    · rw [addOn_of_mem hx]
      simp [hx]
      omega
    · rw [addOn_of_notMem hx]
      simp [hx]
  · intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hSa.nonempty
    · exact h.dne d hd
  · intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hr
    · exact h.droot d hd
  · intro d hd h2
    rcases List.mem_cons.mp hd with rfl | hd
    · have h3 := hna.feas h2 e.2 he2 e.1 (fun h4 => he3 (h4 ▸ he2)) he1
      rw [dsum_eq_y hna h.y_eq he2 he3] at h3
      show 0 ≤ redCost g st.y e
      rw [redCost]
      omega
    · exact h.dsign d hd h2
  · have hA := h.att
    have hnA : ∀ x ∈ st.A.verts, x ∉ a.verts := fun x hx hxa =>
      Finset.disjoint_left.mp (hdA a (by rw [htops0]; exact List.mem_cons_self ..)) hxa hx
    exact ⟨hA.par_root, hA.tree, hA.edge, hA.cost, fun x hx hxr =>
      (hA.feas x hx hxr).cons_of_notMem c (hnA x hx)⟩
  · intro T hT
    have hT' : T = a₁ ∨ T ∈ st.path ++ st.free := by
      simpa [tops, selected, ha₁, List.mem_append] using hT
    rcases hT' with rfl | hT'
    · exact ha₁C
    · exact (h.node T (hmemO T hT')).of_select (hS T (hmemO T hT')) (hother T hT')
  · intro T hT
    rcases List.mem_cons.mp hT with rfl | hT
    · refine ⟨he2, he3, he1, hy1, hfeas⟩
    · have hT0 : T ∈ st.path ++ st.free := List.mem_append_left _ hT
      have hsel := h.sel T hT
      have hnot : ∀ x ∈ T.verts, x ∉ a.verts := fun x hx => Finset.disjoint_left.mp (hother T hT0) hx
      refine ⟨hsel.head, hsel.src, hsel.adj, ?_, fun x hx => (hsel.feas x hx).cons_of_notMem c (hnot x hx)⟩
      show addOn st.y a.verts c T.inE.2 = _
      rw [addOn_of_notMem (hnot _ hsel.head)]
      exact hsel.tight
  · show Chained (a₁ :: st.path)
    cases hp : st.path with
    | nil => trivial
    | cons b l =>
      rw [hp] at hch0
      exact hch0
  · have h1 := h.total
    rw [htops0] at h1
    have h2 : tops { (selected st a e c).1 with path := a₁ :: (selected st a e c).1.path } =
        a₁ :: (st.path ++ st.free) := by
      simp [tops, selected, ha₁]
    rw [h2]
    show st.A.total + _ = c + (st.duals.map Prod.snd).sum
    simp only [List.map_cons, List.sum_cons] at h1 ⊢
    show st.A.total + (a.total + c + _) = _
    omega

/-! ## Attaching -/

theorem sum_assign {g : Graph V} {y : V → ℤ} {D : List (Finset V × ℤ)} {T : Node V} (hn : NodeC g y D T)
    (hs : SelC g y D T) : ∑ a ∈ T.verts, g.w (T.assign a) a = T.total := by
  rw [← Finset.add_sum_erase _ _ hs.head]
  have h1 : T.assign T.inE.2 = T.inE.1 := by simp [Node.assign]
  have h2 : ∀ a ∈ T.verts.erase T.inE.2, g.w (T.assign a) a = g.w (T.exp T.inE.2 a) a := fun a ha => by
    simp [Node.assign, (Finset.mem_erase.mp ha).1]
  rw [h1, Finset.sum_congr rfl h2, ← hs.tight, add_comm]
  exact hn.costEq _ hs.head

theorem AttC.add {g : Graph V} {D : List (Finset V × ℤ)} {y : V → ℤ} {A : Att V} {T : Node V} (hA : AttC g D A)
    (hroot : g.root ∈ A.verts) (hn : NodeC g y D T) (hs : SelC g y D T) (hd : Disjoint T.verts A.verts)
    (hsrc : T.inE.1 ∈ A.verts) : AttC g D (A.add T) := by
  have hnot : ∀ x ∈ A.verts, x ∉ T.verts := fun x hx hxT => Finset.disjoint_left.mp hd hxT hx
  have hpar1 : ∀ x ∈ A.verts, (A.add T).par x = A.par x := fun x hx => by
    simp [Att.add, hnot x hx]
  have hpar2 : ∀ x ∈ T.verts, (A.add T).par x = T.assign x := fun x hx => by
    simp [Att.add, hx]
  have hrT : g.root ∉ T.verts := hnot _ hroot
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hpar1 _ hroot]
    exact hA.par_root
  · intro P hP x hx
    have hP1 : ∀ a ∈ A.verts, a ≠ g.root → P a = A.par a := fun a ha hne => by
      rw [hP a (Finset.mem_union_left _ ha) hne, hpar1 a ha]
    have hAR := hA.tree P hP1
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hAR x hx
    · have hP2 : ∀ a ∈ T.verts, a ≠ T.inE.2 → P a = T.exp T.inE.2 a := fun a ha hne => by
        have har : a ≠ g.root := fun h => hrT (h ▸ ha)
        rw [hP a (Finset.mem_union_right _ ha) har, hpar2 a ha]
        simp [Node.assign, hne]
      have h1 := hn.tree _ hs.head P hP2 x hx
      have har : T.inE.2 ≠ g.root := fun h => hrT (h ▸ hs.head)
      have h2 : P T.inE.2 = T.inE.1 := by
        rw [hP _ (Finset.mem_union_right _ hs.head) har, hpar2 _ hs.head]
        simp [Node.assign]
      exact h1.trans ((RT.step h2).trans (hAR _ hsrc))
  · intro a ha hne
    rcases Finset.mem_union.mp ha with ha | ha
    · rw [hpar1 a ha]
      exact hA.edge a ha hne
    · rw [hpar2 a ha]
      by_cases hh : a = T.inE.2
      · subst hh
        simpa [Node.assign] using hs.adj
      · simpa [Node.assign, hh] using hn.edge _ hs.head a ha hh
  · have herase : (A.add T).verts.erase g.root = A.verts.erase g.root ∪ T.verts := by
      show (A.verts ∪ T.verts).erase g.root = _
      rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hrT]
    have hdisj : Disjoint (A.verts.erase g.root) T.verts :=
      Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hd.symm
    rw [herase, Finset.sum_union hdisj]
    have h1 : ∑ a ∈ A.verts.erase g.root, g.w ((A.add T).par a) a = A.total := by
      rw [← hA.cost]
      exact Finset.sum_congr rfl fun a ha => by rw [hpar1 a (Finset.mem_of_mem_erase ha)]
    have h2 : ∑ a ∈ T.verts, g.w ((A.add T).par a) a = T.total := by
      rw [← sum_assign hn hs]
      exact Finset.sum_congr rfl fun a ha => by rw [hpar2 a ha]
    rw [h1, h2]
    rfl
  · intro x hx hne
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hA.feas x hx hne
    · exact hs.feas x hx

theorem fold_attC {g : Graph V} {D : List (Finset V × ℤ)} {y : V → ℤ} :
    ∀ (l : List (Node V)) (A : Att V), AttC g D A → g.root ∈ A.verts →
      (∀ T ∈ l, NodeC g y D T) → (∀ T ∈ l, SelC g y D T) → Chained l → (l.map Node.verts).Pairwise Disjoint →
      (∀ T ∈ l, Disjoint T.verts A.verts) → (∀ T, l.head? = some T → T.inE.1 ∈ A.verts) →
      AttC g D (l.foldl Att.add A) ∧ (l.foldl Att.add A).total = A.total + (l.map Node.total).sum
  | [], A, hA, _, _, _, _, _, _, _ => ⟨hA, by simp⟩
  | T :: l, A, hA, hroot, hn, hs, hch, hpw, hd, hh => by
    rw [List.map_cons, List.pairwise_cons] at hpw
    have hT := hA.add hroot (hn T (List.mem_cons_self ..)) (hs T (List.mem_cons_self ..))
      (hd T (List.mem_cons_self ..)) (hh T rfl)
    have hrec := fold_attC l (A.add T) hT (Finset.mem_union_left _ hroot)
      (fun T' hT' => hn T' (List.mem_cons_of_mem _ hT')) (fun T' hT' => hs T' (List.mem_cons_of_mem _ hT'))
      (Chained.tail hch) hpw.2
      (fun T' hT' => Finset.disjoint_union_right.mpr
        ⟨hd T' (List.mem_cons_of_mem _ hT'), (hpw.1 _ (List.mem_map_of_mem hT')).symm⟩)
      (fun T' hT' => by
        cases l with
        | nil => simp at hT'
        | cons b l =>
          have : T' = b := by simpa using hT'.symm
          subst this
          exact Finset.mem_union_right _ hch.1)
    refine ⟨hrec.1, ?_⟩
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [hrec.2]
    show A.total + T.total + _ = _
    omega

theorem attach_cinv {g : Graph V} {us : List V} {st : St V} {a : Node V} (hc : st.cur = none)
    (hS : SInv1 g us { st with path := a :: st.path }) (h : CInv g { st with path := a :: st.path })
    (hu : a.inE.1 ∈ st.A.verts) :
    CInv g { st with A := (a :: st.path).foldl Att.add st.A, path := [], cur := none } := by
  set st₂ : St V := { st with path := a :: st.path } with hst₂
  set l := a :: st.path with hl
  have htops2 : tops st₂ = l ++ st.free := by simp [tops, hst₂, hc, hl]
  have htops : tops { st with A := l.foldl Att.add st.A, path := [], cur := none } = st.free := by
    simp [tops]
  have hdis := hS.disj
  rw [htops2, List.map_append, List.pairwise_append] at hdis
  have hch : Chained l := by simpa [hst₂, hc] using h.chain
  have hfold := fold_attC (y := st₂.y) l st.A h.att hS.root
    (fun T hT => h.node T (by rw [htops2]; exact List.mem_append_left _ hT)) h.sel hch hdis.1
    (fun T hT => hS.dAtt T (by rw [htops2]; exact List.mem_append_left _ hT))
    (fun T hT => by
      have : T = a := by simpa [hl] using hT.symm
      subst this
      exact hu)
  refine ⟨h.y_eq, h.dne, h.droot, h.dsign, hfold.1, ?_, by simp, by simp [Chained], ?_⟩
  · intro T hT
    rw [htops] at hT
    exact h.node T (by rw [htops2]; exact List.mem_append_right _ hT)
  · rw [htops]
    have h1 := h.total
    rw [htops2, List.map_append, List.sum_append] at h1
    show (l.foldl Att.add st.A).total + _ = _
    rw [hfold.2]
    have : st₂.A.total = st.A.total := rfl
    rw [this] at h1
    show _ = (st₂.duals.map Prod.snd).sum
    omega

/-! ## Pushing -/

theorem push_cinv {g : Graph V} {st : St V} {a b : Node V} {f1 f2 : List (Node V)}
    (hc : st.cur = none) (hf : st.free = f1 ++ b :: f2) (hsrc : a.inE.1 ∈ b.verts)
    (h : CInv g { st with path := a :: st.path }) :
    CInv g { st with free := f1 ++ f2, path := a :: st.path, cur := some b } := by
  set st₂ : St V := { st with path := a :: st.path } with hst₂
  set st₃ : St V := { st with free := f1 ++ f2, path := a :: st.path, cur := some b } with hst₃
  have hperm : List.Perm (tops st₃) (tops st₂) := by
    simp only [tops, hst₃, hst₂, hc, hf, Option.toList_some, Option.toList_none, List.nil_append]
    have h2 := (List.perm_middle (a := b) (l₁ := (a :: st.path) ++ f1) (l₂ := f2)).symm
    simpa [List.append_assoc] using h2
  refine ⟨h.y_eq, h.dne, h.droot, h.dsign, h.att, fun T hT => h.node T (hperm.mem_iff.mp hT), h.sel, ?_, ?_⟩
  · have hch : Chained (a :: st.path) := by simpa [hst₂, hc] using h.chain
    exact ⟨hsrc, hch⟩
  · have h1 := h.total
    rw [← (hperm.map Node.total).sum_eq] at h1
    exact h1

/-! ## Contracting -/

theorem find?_parts {l : List (Node V)} (hpw : (l.map Node.verts).Pairwise Disjoint) {T : Node V} (hT : T ∈ l)
    {x : V} (hx : x ∈ T.verts) : l.find? (fun T => decide (x ∈ T.verts)) = some T := by
  induction l with
  | nil => simp at hT
  | cons b l ih =>
    rw [List.map_cons, List.pairwise_cons] at hpw
    rcases List.mem_cons.mp hT with rfl | hT'
    · simp [hx]
    · have hxb : x ∉ b.verts := fun h =>
        Finset.disjoint_left.mp (hpw.1 _ (List.mem_map_of_mem hT')) h hx
      simp only [List.find?_cons, hxb, decide_false]
      exact ih hpw.2 hT'

theorem contractExp_of_mem {l : List (Node V)} (hpw : (l.map Node.verts).Pairwise Disjoint) {T : Node V}
    (hT : T ∈ l) {x : V} (hx : x ∈ T.verts) (v : V) :
    contractExp l v x = if v ∈ T.verts then T.exp v x else T.assign x := by
  unfold contractExp
  rw [find?_parts hpw hT hx]

theorem sum_erase_unionV (F : V → ℤ) (v : V) {l : List (Node V)} (hpw : (l.map Node.verts).Pairwise Disjoint) :
    ∑ a ∈ (unionV l).erase v, F a = (l.map fun T => ∑ a ∈ T.verts.erase v, F a).sum := by
  induction l with
  | nil => simp [unionV]
  | cons T l ih =>
    rw [List.map_cons, List.pairwise_cons] at hpw
    have hd : Disjoint T.verts (unionV l) := disjoint_unionV.mpr fun T' hT' => hpw.1 _ (List.mem_map_of_mem hT')
    simp only [unionV, List.map_cons, List.sum_cons]
    rw [Finset.erase_union_distrib, Finset.sum_union
      (Finset.disjoint_of_subset_left (Finset.erase_subset _ _)
        (Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hd)), ih hpw.2]

theorem sum_total_parts (F : V → ℤ) (y : V → ℤ) (v : V) {l : List (Node V)}
    (hpw : (l.map Node.verts).Pairwise Disjoint)
    (hF : ∀ T ∈ l, ∑ a ∈ T.verts.erase v, F a = T.total - if v ∈ T.verts then y v else 0) :
    ∑ a ∈ (unionV l).erase v, F a + (if v ∈ unionV l then y v else 0) = (l.map Node.total).sum := by
  rw [sum_erase_unionV F v hpw]
  induction l with
  | nil => simp [unionV]
  | cons T l ih =>
    rw [List.map_cons, List.pairwise_cons] at hpw
    have hd : Disjoint T.verts (unionV l) := disjoint_unionV.mpr fun T' hT' => hpw.1 _ (List.mem_map_of_mem hT')
    have h1 := ih hpw.2 fun T' hT' => hF T' (List.mem_cons_of_mem _ hT')
    have h2 := hF T (List.mem_cons_self ..)
    simp only [List.map_cons, List.sum_cons, unionV, Finset.mem_union]
    by_cases hv : v ∈ T.verts
    · have hv' : v ∉ unionV l := fun h => Finset.disjoint_left.mp hd hv h
      simp only [hv, if_true, true_or] at h2 ⊢
      simp only [hv', if_false] at h1
      omega
    · simp only [hv, if_false, false_or] at h2 ⊢
      omega

theorem unionV_perm {l₁ l₂ : List (Node V)} (h : List.Perm l₁ l₂) : unionV l₁ = unionV l₂ := by
  ext x
  simp only [mem_unionV]
  constructor
  · rintro ⟨T, hT, hx⟩
    exact ⟨T, h.mem_iff.mp hT, hx⟩
  · rintro ⟨T, hT, hx⟩
    exact ⟨T, h.mem_iff.mpr hT, hx⟩

theorem absorbF_members : ∀ (k : ℕ) (H : Finset V) (gs : List (Group V)), ∀ G ∈ (absorbF k H gs).2, G ∈ gs
  | 0, _, _ => fun _ hG => hG
  | k + 1, H, gs => by
    intro G hG
    cases hs : split (fun G => decide (lg G.verts.card = lg H.card)) gs with
    | none =>
      have hab : absorbF (k + 1) H gs = (H, gs) := by simp [absorbF, hs]
      rw [hab] at hG
      exact hG
    | some r =>
      obtain ⟨g1, G0, g2⟩ := r
      have hab : absorbF (k + 1) H gs = absorbF k (H ∪ G0.verts) (g1 ++ g2) := by simp [absorbF, hs]
      rw [hab] at hG
      have h1 := absorbF_members k _ _ G hG
      rw [(split_some hs).1]
      simp only [List.mem_append, List.mem_cons] at h1 ⊢
      tauto

/-- Good propagates along a chain. -/
theorem chain_good {Good : Node V → Prop} {P : List (Node V)}
    (hstep : ∀ A ∈ P, ∀ B ∈ P, B.inE.1 ∈ A.verts → Good A → Good B) :
    ∀ (l : List (Node V)) (A : Node V), (∀ T ∈ A :: l, T ∈ P) → Chained (A :: l) → Good A →
      ∀ T ∈ A :: l, Good T
  | [], A, _, _, hg, T, hT => by
    rw [List.mem_singleton.mp hT]
    exact hg
  | B :: l, A, hsub, hch, hg, T, hT => by
    rcases List.mem_cons.mp hT with rfl | hT
    · exact hg
    · have hgB := hstep A (hsub A (List.mem_cons_self ..)) B (hsub B (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        hch.1 hg
      exact chain_good hstep l B (fun T' hT' => hsub T' (List.mem_cons_of_mem _ hT')) hch.2 hgB T hT

theorem last_mem_of_append {α : Type*} {l₁ l₂ x : List α} {h b : α} (he : l₁ ++ h :: l₂ = x ++ [b]) :
    b ∈ h :: l₂ := by
  have h1 := congrArg List.getLast? he
  rw [List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_concat] at h1
  exact List.mem_of_getLast? h1

/-- Good propagates around the cycle from any node of the cycle. -/
theorem cycle_good {Good : Node V → Prop} {a b : Node V} {seg : List (Node V)}
    (hstep : ∀ A ∈ a :: seg ++ [b], ∀ B ∈ a :: seg ++ [b], B.inE.1 ∈ A.verts → Good A → Good B)
    (hch : Chained (a :: seg ++ [b])) (hclose : a.inE.1 ∈ b.verts) {h : Node V} (hh : h ∈ a :: seg ++ [b])
    (hg : Good h) : ∀ T ∈ a :: seg ++ [b], Good T := by
  obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem hh
  have hch2 : Chained (h :: l₂) := by
    rw [hsplit] at hch
    exact Chained.of_append hch
  have hsub : ∀ T ∈ h :: l₂, T ∈ a :: seg ++ [b] := fun T hT => by
    rw [hsplit]
    exact List.mem_append_right _ hT
  have hall := chain_good hstep l₂ h hsub hch2 hg
  have hb : b ∈ h :: l₂ := by
    refine last_mem_of_append (l₁ := l₁) (x := a :: seg) ?_
    rw [← hsplit]
  have hga : Good a := hstep b (hsub b hb) a (List.mem_cons_self ..) hclose (hall b hb)
  exact chain_good hstep (seg ++ [b]) a (fun T hT => hT) hch hga

theorem contract_cinv {o : Oracle V} (ho : o.Correct) {g : Graph V} {us : List V} {st : St V}
    {a b : Node V} {seg pre : List (Node V)} (hc : st.cur = none) (hpath : st.path = seg ++ b :: pre)
    (hclose : a.inE.1 ∈ b.verts)
    (hS : SInv1 g us { st with path := a :: st.path }) (h : CInv g { st with path := a :: st.path }) :
    CInv g { st with
      path := pre
      cur := some (contractNode o g st.y a (seg ++ [b]))
      builds := (contractH a (seg ++ [b]), (contractH a (seg ++ [b])).card) :: st.builds } := by
  set rest := seg ++ [b] with hrest
  set parts := a :: rest with hparts
  set st₂ : St V := { st with path := a :: st.path } with hst₂
  have hy : st₂.y = st.y := rfl
  have hD : st₂.duals = st.duals := rfl
  have htops2 : tops st₂ = parts ++ (pre ++ st.free) := by
    simp [tops, hst₂, hc, hpath, hparts, hrest]
  have hdis := hS.disj
  rw [htops2, List.map_append, List.pairwise_append] at hdis
  obtain ⟨hdp, hdr, hdpr⟩ := hdis
  have hpath2 : st₂.path = parts ++ pre := by simp [hst₂, hpath, hparts, hrest]
  have hnp : ∀ T ∈ parts, NodeC g st.y st.duals T := fun T hT =>
    h.node T (by rw [htops2]; exact List.mem_append_left _ hT)
  have hsp : ∀ T ∈ parts, SelC g st.y st.duals T := fun T hT =>
    h.sel T (by rw [hpath2]; exact List.mem_append_left _ hT)
  have hnr : ∀ T ∈ pre ++ st.free, NodeC g st.y st.duals T := fun T hT =>
    h.node T (by rw [htops2]; exact List.mem_append_right _ hT)
  have hchain : Chained (parts ++ pre) := by
    have := h.chain
    rw [hpath2] at this
    simpa [hst₂, hc] using this
  have hperm : List.Perm ((pick a rest).1 :: (pick a rest).2) parts := pick_perm a rest
  set S := (pick a rest).1 with hSdef
  set others := (pick a rest).2 with hothers
  set H := (absorb (unionV others) S.groups).1 with hH
  set gs' := (absorb (unionV others) S.groups).2 with hgs'
  set X := contractNode o g st.y a rest with hX
  have hXv : X.verts = unionV parts := unionV_perm hperm
  have hXg : X.groups = build o g X.verts st.y H H.card :: gs' := rfl
  have hXexp : X.exp = contractExp parts := rfl
  have hXtot : X.total = (parts.map Node.total).sum := rfl
  have hXmem : ∀ x, x ∈ X.verts ↔ ∃ T ∈ parts, x ∈ T.verts := fun x => by rw [hXv, mem_unionV]
  have hexp : ∀ T ∈ parts, ∀ x ∈ T.verts, ∀ v, X.exp v x = if v ∈ T.verts then T.exp v x else T.assign x :=
    fun T hT x hx v => by
      rw [hXexp]
      exact contractExp_of_mem hdp hT hx v
  have hNX : NodeC g st.y st.duals X := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro v hv P hP
      obtain ⟨Tv, hTv, hvT⟩ := (hXmem v).mp hv
      have hmemX : ∀ T ∈ parts, ∀ x ∈ T.verts, x ∈ X.verts := fun T hT x hx => (hXmem x).mpr ⟨T, hT, hx⟩
      have hgoodv : ∀ T ∈ parts, v ∈ T.verts → ∀ x ∈ T.verts, RT P x v := by
        intro T hT hvT x hx
        refine (hnp T hT).tree v hvT P (fun a' ha' hne => ?_) x hx
        rw [hP a' (hmemX T hT a' ha') hne, hexp T hT a' ha' v, if_pos hvT]
      have hstep : ∀ A ∈ parts, ∀ B ∈ parts, B.inE.1 ∈ A.verts →
          (∀ x ∈ A.verts, RT P x v) → (∀ x ∈ B.verts, RT P x v) := by
        intro A _ B hB hsrc hgA
        by_cases hvB : v ∈ B.verts
        · exact hgoodv B hB hvB
        · intro x hx
          have hsel := hsp B hB
          have hagree : ∀ a' ∈ B.verts, a' ≠ B.inE.2 → P a' = B.exp B.inE.2 a' := fun a' ha' hne => by
            have hav : a' ≠ v := fun h => hvB (h ▸ ha')
            rw [hP a' (hmemX B hB a' ha') hav, hexp B hB a' ha' v, if_neg hvB]
            simp [Node.assign, hne]
          have h1 := (hnp B hB).tree _ hsel.head P hagree x hx
          have hhv : B.inE.2 ≠ v := fun h => hvB (h ▸ hsel.head)
          have h2 : P B.inE.2 = B.inE.1 := by
            rw [hP _ (hmemX B hB _ hsel.head) hhv, hexp B hB _ hsel.head v, if_neg hvB]
            simp [Node.assign]
          exact h1.trans ((RT.step h2).trans (hgA _ hsrc))
      have hchp : Chained parts := Chained.prefix hchain
      have hall := cycle_good (Good := fun T => ∀ x ∈ T.verts, RT P x v) (a := a) (b := b) (seg := seg)
        hstep hchp hclose hTv (hgoodv Tv hTv hvT)
      intro x hx
      obtain ⟨T, hT, hxT⟩ := (hXmem x).mp hx
      exact hall T hT x hxT
    · intro v _ a' ha' hne
      obtain ⟨T, hT, ha'T⟩ := (hXmem a').mp ha'
      rw [hexp T hT a' ha'T v]
      split_ifs with hvT
      · exact (hnp T hT).edge v hvT a' ha'T hne
      · by_cases hh : a' = T.inE.2
        · subst hh
          simpa [Node.assign] using (hsp T hT).adj
        · simpa [Node.assign, hh] using (hnp T hT).edge _ (hsp T hT).head a' ha'T hh
    · intro v hv
      have hsum := sum_total_parts (fun x => g.w (X.exp v x) x) st.y v hdp (fun T hT => by
        by_cases hvT : v ∈ T.verts
        · have h1 := (hnp T hT).costEq v hvT
          have h2 : ∑ x ∈ T.verts.erase v, g.w (X.exp v x) x = ∑ x ∈ T.verts.erase v, g.w (T.exp v x) x :=
            Finset.sum_congr rfl fun x hx => by
              rw [hexp T hT x (Finset.mem_of_mem_erase hx) v, if_pos hvT]
          simp only [hvT, if_true, h2]
          omega
        · have h1 := sum_assign (hnp T hT) (hsp T hT)
          have h2 : ∑ x ∈ T.verts.erase v, g.w (X.exp v x) x = ∑ x ∈ T.verts, g.w (T.assign x) x := by
            rw [Finset.erase_eq_of_notMem hvT]
            exact Finset.sum_congr rfl fun x hx => by rw [hexp T hT x hx v, if_neg hvT]
          simp only [hvT, if_false, h2, h1, sub_zero])
      rw [← hXv] at hsum
      simpa [hv, hXtot] using hsum
    · intro G hG
      rw [hXg] at hG
      rcases List.mem_cons.mp hG with rfl | hG'
      · exact build_groupC ho g _ _ _ _
      · exact (hnp S (hperm.mem_iff.mp (List.mem_cons_self ..))).groups G (absorbF_members _ _ _ G hG')
    · intro d hd x hx hxd
      obtain ⟨T, hT, hxT⟩ := (hXmem x).mp hx
      intro z hz
      exact (hXmem z).mpr ⟨T, hT, (hnp T hT).lamin d hd x hxT hxd hz⟩
    · intro _ x hx
      obtain ⟨T, hT, hxT⟩ := (hXmem x).mp hx
      exact (hsp T hT).feas x hxT
  have htops4 : tops { st with path := pre, cur := some X, builds := (contractH a rest, (contractH a rest).card) :: st.builds } = X :: (pre ++ st.free) := by
    simp [tops]
  refine ⟨h.y_eq, h.dne, h.droot, h.dsign, h.att, ?_, ?_, ?_, ?_⟩
  · intro T hT
    rw [htops4] at hT
    rcases List.mem_cons.mp hT with rfl | hT
    · exact hNX
    · exact hnr T hT
  · intro T hT
    exact h.sel T (by rw [hpath2]; exact List.mem_append_right _ hT)
  · show Chained (X :: pre)
    have hb : Chained (b :: pre) := by
      have : parts ++ pre = (a :: seg) ++ b :: pre := by simp [hparts, hrest]
      rw [this] at hchain
      exact Chained.of_append hchain
    cases hp : pre with
    | nil => trivial
    | cons p l =>
      rw [hp] at hb
      refine ⟨(hXmem _).mpr ⟨b, ?_, hb.1⟩, hb.2⟩
      simp [hparts, hrest]
  · rw [htops4]
    have h1 := h.total
    rw [htops2, List.map_append, List.sum_append] at h1
    simp only [List.map_cons, List.sum_cons]
    rw [hXtot]
    exact h1

theorem route_cinv {o : Oracle V} (ho : o.Correct) {g : Graph V} {us : List V} {st : St V} {a : Node V}
    (hc : st.cur = none) (hS : SInv1 g us { st with path := a :: st.path })
    (h : CInv g { st with path := a :: st.path }) (hu : a.inE.1 ∉ a.verts) :
    CInv g (route o g st a) := by
  unfold route
  simp only
  split_ifs with hA
  · exact attach_cinv hc hS h hA
  · cases hs : split (fun T => decide (a.inE.1 ∈ T.verts)) st.path with
    | some r =>
      obtain ⟨seg, b, pre⟩ := r
      have hp := split_some hs
      exact contract_cinv ho hc hp.1 (by simpa using hp.2.1) hS h
    | none =>
      simp only
      cases hf : split (fun T => decide (a.inE.1 ∈ T.verts)) st.free with
      | some r =>
        obtain ⟨f1, b, f2⟩ := r
        have hp := split_some hf
        exact push_cinv hc hp.1 (by simpa using hp.2.1) h
      | none =>
        exfalso
        rcases hS.cover a.inE.1 with hx | ⟨T, hT, hx⟩
        · exact hA hx
        · simp only [tops, hc, Option.toList_none, List.nil_append, List.mem_cons, List.mem_append] at hT
          rcases hT with (rfl | hT) | hT
          · exact hu hx
          · have := split_none hs T hT
            simp [hx] at this
          · have := split_none hf T hT
            simp [hx] at this

/-! ## One step -/

theorem pop_cinv {g : Graph V} {us : List V} {st : St V} (hS : SInv g us st) (h : CInv g st) (hc : st.cur = none)
    {a : Node V} {rest : List (Node V)} (hf : st.free = a :: rest) :
    CInv g { st with free := rest, cur := some a } := by
  have hp := hS.curNone hc
  have htops : tops { st with free := rest, cur := some a } = tops st := by
    simp [tops, hc, hp, hf]
  refine ⟨h.y_eq, h.dne, h.droot, h.dsign, h.att, fun T hT => h.node T (htops ▸ hT), h.sel, ?_, ?_⟩
  · simp [hp, Chained]
  · rw [htops]
    exact h.total

theorem step_cinv {o : Oracle V} (ho : o.Correct) {g : Graph V} {us : List V} {st st' : St V}
    (hS : SInv g us st) (h : CInv g st) (hs : step o g st = .running st') : CInv g st' := by
  rcases step_running hs with ⟨hc, a, rest, hf, rfl⟩ | ⟨a, e, hc, hm, rfl⟩
  · exact pop_cinv hS h hc hf
  · have hS0 := refreshed_sinv ho.structural hS hc
    have h0 := refreshed_cinv ho h hc
    set gs := (refreshAll o g a.verts st.y a.groups).1 with hgs
    have hc0 : (refreshed o g st a).cur = some { a with groups := gs } := rfl
    have hmem0 : ({ a with groups := gs } : Node V) ∈ tops (refreshed o g st a) := by simp [tops, hc0]
    have hN := hS0.node _ hmem0
    have hC := h0.node _ hmem0
    have hmem : a ∈ tops st := by simp [tops, hc]
    have hcompl := refreshAll_complete (o := o) ho.structural st.y (hS.node a hmem).groups
    have he := cheapest_some (g := g) (C := a.verts) (y := st.y) (gs := gs) hN.groups hC.groups hcompl
      hN.cover hm
    have h1 := selected_cinv h0 hS0.node hS0.disj hS0.dAtt hS0.root hc0 he
    have h2 := selected_sinv hS0 hc0 e (redCost g st.y e)
    exact route_cinv ho rfl h2 h1 he.2.2.1

theorem reach_inv {o : Oracle V} (ho : o.Correct) {g : Graph V} {us : List V} {st s : St V}
    (hS : SInv g us st) (h : CInv g st) (hr : Reach o g st s) : SInv g us s ∧ CInv g s := by
  induction hr with
  | refl => exact ⟨hS, h⟩
  | step _ hb ih => exact ⟨step_sinv ho.structural ih.1 hb, step_cinv ho ih.1 ih.2 hb⟩

/-! ## The theorems about `solve` -/

/-- **The final state of a run gives a minimum arborescence.** -/
theorem done_isMinArb {g : Graph V} {us : List V} {st : St V} (hS : SInv g us st) (h : CInv g st)
    (hc : st.cur = none) (hf : st.free = []) : IsMinArb g st.A.par := by
  have hp := hS.curNone hc
  have htops : tops st = [] := by simp [tops, hc, hp, hf]
  have huniv : st.A.verts = univ := by
    ext x
    simp only [Finset.mem_univ, iff_true]
    rcases hS.cover x with hx | ⟨T, hT, _⟩
    · exact hx
    · rw [htops] at hT
      simp at hT
  have hA := h.att
  have hIs : IsArb g st.A.par := by
    refine ⟨hA.par_root, fun v hv => hA.edge v (huniv ▸ Finset.mem_univ v) hv, fun v => ?_⟩
    exact iterate_of_rt (hA.tree _ (fun _ _ _ => rfl) v (huniv ▸ Finset.mem_univ v))
  have hcost : cost g st.A.par = (st.duals.map Prod.snd).sum := by
    have h1 := h.total
    rw [htops] at h1
    simp only [List.map_nil, List.sum_nil, add_zero] at h1
    rw [← h1, ← hA.cost, huniv]
    rfl
  refine ⟨hIs, fun q hq => ?_⟩
  rw [hcost]
  refine weak_duality_list h.dne h.droot h.dsign ?_ hq
  intro u v huv hv ha
  exact hA.feas v (huniv ▸ Finset.mem_univ v) hv u huv ha

/-- **A report of none is correct.** -/
theorem noArb_correct {o : Oracle V} (ho : o.Correct) {g : Graph V} {us : List V} {st : St V}
    (hS : SInv g us st) (h : CInv g st) {a : Node V} (hc : st.cur = some a)
    (hm : minBy (redCost g st.y) (heads a.verts (refreshAll o g a.verts st.y a.groups).1) = none) :
    ¬ ∃ p, IsArb g p := by
  have hS0 := refreshed_sinv ho.structural hS hc
  have h0 := refreshed_cinv ho h hc
  set gs := (refreshAll o g a.verts st.y a.groups).1 with hgs
  have hmem0 : ({ a with groups := gs } : Node V) ∈ tops (refreshed o g st a) := by simp [tops, refreshed, hgs]
  have hN := hS0.node _ hmem0
  have hC := h0.node _ hmem0
  have hmem : a ∈ tops st := by simp [tops, hc]
  have hcompl := refreshAll_complete (o := o) ho.structural st.y (hS.node a hmem).groups
  have hno := cheapest_none (o := o) (g := g) (C := a.verts) (y := st.y) (gs := gs) hN.groups hC.groups hcompl
    hN.cover hm
  refine no_arb_of_no_entering hN.nonempty ?_ ?_
  · exact fun hr => Finset.disjoint_left.mp (hS.dAtt a hmem) hr hS.root
  · intro u v hv hu
    cases hadj : g.adj u v with
    | false => rfl
    | true => exact absurd (hno u v hadj hv) hu

/-- **Goal 6, correctness.** With a correct TopK oracle, an output `some p` is a minimum-cost arborescence. -/
theorem solve_some {o : Oracle V} (ho : o.Correct) (g : Graph V) {vs : List V} (hvs : vs.Nodup)
    (hall : ∀ v, v ∈ vs) {p : V → V} (hp : (solve o g vs).1 = some p) : IsMinArb g p := by
  set us := vs.filter fun v => decide (v ≠ g.root) with hus
  have hroot : g.root ∉ us := by simp [hus]
  have h0 := init_sinv (o := o) ho.structural g (hvs.filter _) hroot (fun v hv => by simp [hus, hv, hall])
  have h1 := init_cinv (o := o) ho g hroot
  obtain ⟨s, hr, hd⟩ := solve_reach o g vs
  obtain ⟨hS, hC⟩ := reach_inv ho h0 h1 hr
  rcases hd with ⟨s', h2, h3⟩ | ⟨s', h2, h3⟩
  · obtain ⟨rfl, hc, hf⟩ := step_done h2
    rw [h3] at hp
    simp only [Option.some.injEq] at hp
    rw [← hp]
    exact done_isMinArb hS hC hc hf
  · rw [h3] at hp
    simp at hp

/-- **Goal 6, correctness.** With a correct TopK oracle, the output `none` means that there is no arborescence. -/
theorem solve_none {o : Oracle V} (ho : o.Correct) (g : Graph V) {vs : List V} (hvs : vs.Nodup)
    (hall : ∀ v, v ∈ vs) (hp : (solve o g vs).1 = none) : ¬ ∃ p, IsArb g p := by
  set us := vs.filter fun v => decide (v ≠ g.root) with hus
  have hroot : g.root ∉ us := by simp [hus]
  have h0 := init_sinv (o := o) ho.structural g (hvs.filter _) hroot (fun v hv => by simp [hus, hv, hall])
  have h1 := init_cinv (o := o) ho g hroot
  obtain ⟨s, hr, hd⟩ := solve_reach o g vs
  obtain ⟨hS, hC⟩ := reach_inv ho h0 h1 hr
  rcases hd with ⟨s', h2, h3⟩ | ⟨s', h2, h3⟩
  · rw [h3] at hp
    simp at hp
  · obtain ⟨a, hc, _, hm⟩ := step_noArb h2
    exact noArb_correct ho hS hC hc hm

/-- **Goal 6.** For a correct oracle: `some p` is a minimum-cost arborescence, `none` means that there is no
arborescence, and the charges of the builds of the run obey the bound of Lemma 5. -/
theorem solve_correct {o : Oracle V} (ho : o.Correct) (g : Graph V) {vs : List V} (hvs : vs.Nodup)
    (hall : ∀ v, v ∈ vs) :
    (∀ p, (solve o g vs).1 = some p → IsMinArb g p) ∧
    ((solve o g vs).1 = none → ¬ ∃ p, IsArb g p) ∧
    ((solve o g vs).2.map fun b => topKCost b.2 (inEdges g b.1).card).sum ≤
      6 * Real.sqrt ((Fintype.card V : ℝ) * (numEdges g : ℝ)) * (logL (Fintype.card V) : ℝ) ^ 2 :=
  ⟨fun _ h => solve_some ho g hvs hall h, solve_none ho g hvs hall, solve_cost ho.structural g hvs hall⟩

/-- **Queries**, under the hypothesis `DHHMTheorem6` on the query count `q` of a call. It needs only the structure of
the outputs of the oracle. With `L = O(log n)` this is `O(√(nm) log² n)` queries at constant error per call. The extra
`log n` of Theorem 1 comes from the error reduction per call, and is not modelled. -/
theorem solve_queries {o : Oracle V} (ho : o.Structural) (g : Graph V) {vs : List V} (hvs : vs.Nodup)
    (hall : ∀ v, v ∈ vs) {q : ℕ → ℕ → ℝ} (hq : DHHMTheorem6 q) :
    ∃ C : ℝ, 0 < C ∧ ((solve o g vs).2.map fun b => q b.2 (inEdges g b.1).card).sum ≤
      C * (6 * Real.sqrt ((Fintype.card V : ℝ) * (numEdges g : ℝ)) * (logL (Fintype.card V) : ℝ) ^ 2) := by
  obtain ⟨C, hC, hle⟩ := hq
  refine ⟨C, hC, le_trans ?_ (mul_le_mul_of_nonneg_left (solve_cost ho g hvs hall) hC.le)⟩
  induction (solve o g vs).2 with
  | nil => simp
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons, mul_add]
    exact add_le_add (hle _ _) ih

end Arborescence
