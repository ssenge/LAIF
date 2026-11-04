import Arborescence.Algorithm

/-!
# The trace of the algorithm is a run of the abstract machine

For any oracle that returns items with distinct types (`Oracle.Structural`), correct or not, every reachable state
of the algorithm has a partition into containers and groups, and its builds are `allBuilds us evs` for a run `evs` of
the abstract machine of `Counting.lean`. So the cost bound for the algorithm holds with no assumption that TopK
answers correctly, as the README claim in the proof of Theorem 1. `SInv` is that invariant.
-/

set_option linter.unusedSectionVars false

open Finset

namespace Arborescence

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The abstraction -/

/-- A group without its list. -/
def absG (G : Group V) : Grp V := ⟨G.verts, G.K, G.builtIn.card⟩

/-- A node as a container of the abstract machine. -/
def absN (T : Node V) : Cont V := ⟨T.verts, ((T.groups.map absG : List (Grp V)) : Multiset (Grp V))⟩

/-- A list of nodes. -/
def absL (l : List (Node V)) : Multiset (Cont V) := ((l.map absN : List (Cont V)) : Multiset (Cont V))

theorem absL_nil : absL ([] : List (Node V)) = 0 := rfl

theorem absL_cons (a : Node V) (l : List (Node V)) : absL (a :: l) = absN a ::ₘ absL l := rfl

theorem absL_append (l₁ l₂ : List (Node V)) : absL (l₁ ++ l₂) = absL l₁ + absL l₂ := by
  simp [absL]

theorem absL_perm {l₁ l₂ : List (Node V)} (h : List.Perm l₁ l₂) : absL l₁ = absL l₂ :=
  Multiset.coe_eq_coe.mpr (h.map _)

/-- The containers of a state. -/
def absSt (st : St V) : Multiset (Cont V) :=
  absL st.A.nodes + absL st.cur.toList + absL st.path + absL st.free

/-- The current containers that are not attached. -/
def tops (st : St V) : List (Node V) := st.cur.toList ++ st.path ++ st.free

/-! ## The invariant -/

/-- The structural facts about a group of a container `C`. -/
structure GroupS (g : Graph V) (C : Finset V) (G : Group V) : Prop where
  K_pos : 1 ≤ G.K
  built : G.builtIn ⊆ C
  shape : ∃ I, ListShape g G.verts G.builtIn G.y0 G.K I G.entries G.complete

/-- The structural facts about a node: its groups partition it. -/
structure NodeS (g : Graph V) (T : Node V) : Prop where
  nonempty : T.verts.Nonempty
  pw : (T.groups.map Group.verts).Pairwise Disjoint
  cover : ∀ x, x ∈ T.verts ↔ ∃ G ∈ T.groups, x ∈ G.verts
  groups : ∀ G ∈ T.groups, GroupS g T.verts G

/-- The structural invariant, without the statement that a state with no current node has an empty path. -/
structure SInv1 (g : Graph V) (us : List V) (st : St V) : Prop where
  root : g.root ∈ st.A.verts
  disj : ((tops st).map Node.verts).Pairwise Disjoint
  dAtt : ∀ T ∈ tops st, Disjoint T.verts st.A.verts
  cover : ∀ x, x ∈ st.A.verts ∨ ∃ T ∈ tops st, x ∈ T.verts
  node : ∀ T ∈ tops st, NodeS g T
  run : ∃ evs, Run us evs (absSt st) ∧ allBuilds us evs = st.builds

/-- The structural invariant. -/
structure SInv (g : Graph V) (us : List V) (st : St V) : Prop extends SInv1 g us st where
  curNone : st.cur = none → st.path = []

/-! ## Build -/

theorem build_shape {o : Oracle V} (ho : o.Structural) (g : Graph V) (C : Finset V) (y : V → ℤ)
    (verts : Finset V) (K : ℕ) :
    ListShape g verts C y K (o (inEdges g verts) (buildF g C y) K).toFinset
      (build o g C y verts K).entries (build o g C y verts K).complete := by
  set I := o (inEdges g verts) (buildF g C y) K with hI
  have hfin : ∀ e, finiteAt g C e = true ↔ buildF g C y e ≠ ⊤ := by
    intro e
    rw [buildF_ne_top]
    simp [finiteAt]
  refine ⟨(ho _ _ _).1, (ho _ _ _).2, ?_, ?_, ?_⟩
  · simp only [build]
    haveI : Std.Total fun a b : V × V => redCost g y a ≤ redCost g y b := ⟨fun a b => le_total _ _⟩
    haveI : IsTrans (V × V) fun a b => redCost g y a ≤ redCost g y b := ⟨fun a b c => le_trans⟩
    have h1 := List.pairwise_insertionSort (fun a b : V × V => redCost g y a ≤ redCost g y b)
      (I.filter (finiteAt g C))
    refine h1.imp_of_mem fun {a b} ha hb hab => ?_
    have ha' := (List.mem_filter.mp ((List.perm_insertionSort _ _).mem_iff.mp ha)).2
    have hb' := (List.mem_filter.mp ((List.perm_insertionSort _ _).mem_iff.mp hb)).2
    rw [buildF_of_ne_top (by simpa [finiteAt] using ha'), buildF_of_ne_top (by simpa [finiteAt] using hb')]
    exact WithTop.coe_le_coe.mpr hab
  · intro e
    simp only [build]
    rw [(List.perm_insertionSort _ _).mem_iff, List.mem_filter, hfin, List.mem_toFinset]
  · simp only [build, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.not_eq_true']
    refine or_congr Iff.rfl ?_
    constructor
    · rintro ⟨e, he, hf⟩
      refine ⟨e, List.mem_toFinset.mpr he, ?_⟩
      by_contra hne
      have := (hfin e).mpr hne
      rw [hf] at this
      exact Bool.false_ne_true this
    · rintro ⟨e, he, hf⟩
      refine ⟨e, List.mem_toFinset.mp he, ?_⟩
      cases h : finiteAt g C e with
      | false => rfl
      | true => exact absurd hf ((hfin e).mp h)

theorem build_groupS {o : Oracle V} (ho : o.Structural) (g : Graph V) {C X : Finset V} (y : V → ℤ)
    (verts : Finset V) {K : ℕ} (hK : 1 ≤ K) (hC : C ⊆ X) : GroupS g X (build o g C y verts K) :=
  ⟨hK, hC, ⟨_, build_shape ho g C y verts K⟩⟩

theorem absG_build (o : Oracle V) (g : Graph V) (C : Finset V) (y : V → ℤ) (verts : Finset V) (K : ℕ) :
    absG (build o g C y verts K) = ⟨verts, K, C.card⟩ := rfl

/-! ## The initial state -/

theorem init_sinv {o : Oracle V} (ho : o.Structural) (g : Graph V) {us : List V} (hus : us.Nodup)
    (hroot : g.root ∉ us) (hall : ∀ v, v ≠ g.root → v ∈ us) : SInv g us (initSt o g us) := by
  have htops : tops (initSt o g us) = us.map (Node.singleton o g) := by simp [tops, initSt]
  refine { root := by simp [initSt], disj := ?_, dAtt := ?_, cover := ?_, node := ?_, run := ?_, curNone := ?_ }
  · rw [htops, List.map_map]
    refine List.Pairwise.map _ (fun a b hab => ?_) (List.Pairwise.imp (fun h => h) hus)
    simpa [Node.singleton] using hab
  · intro T hT
    rw [htops] at hT
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hT
    have : v ≠ g.root := fun h => hroot (h ▸ hv)
    simpa [Node.singleton, initSt] using this
  · intro x
    by_cases hx : x = g.root
    · exact Or.inl (by simp [initSt, hx])
    · refine Or.inr ⟨Node.singleton o g x, ?_, by simp [Node.singleton]⟩
      rw [htops]
      exact List.mem_map_of_mem (hall x hx)
  · intro T hT
    rw [htops] at hT
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hT
    refine ⟨by simp [Node.singleton], by simp [Node.singleton], ?_, ?_⟩
    · intro x
      simp [Node.singleton, build]
    · intro G hG
      have : G = build o g {v} (fun _ => 0) {v} 1 := by simpa [Node.singleton] using hG
      rw [this]
      exact build_groupS ho g _ _ le_rfl (Finset.Subset.refl _)
  · refine ⟨[], ?_, ?_⟩
    · have : absSt (initSt o g us) = initConts us := by
        have h1 : absL (us.map (Node.singleton o g)) = initConts us := by
          simp [absL, initConts, Function.comp_def, absN, Node.singleton, absG_build]
        simp [absSt, initSt, absL_nil, h1]
      rw [this]
      exact Run.init
    · simp [allBuilds, initSt]
  · intro _
    rfl

/-! ## Transfer of the invariant -/

theorem SInv1.mk' {g : Graph V} {us : List V} {st st' : St V} (h : SInv1 g us st)
    (hA : st'.A.verts = st.A.verts)
    (hverts : List.Perm ((tops st').map Node.verts) ((tops st).map Node.verts))
    (hnode : ∀ T ∈ tops st', NodeS g T)
    (hrun : ∃ evs, Run us evs (absSt st') ∧ allBuilds us evs = st'.builds) : SInv1 g us st' := by
  refine ⟨hA ▸ h.root, ?_, ?_, ?_, hnode, hrun⟩
  · exact (hverts.pairwise_iff (fun {a b} hab => hab.symm)).mpr h.disj
  · intro T hT
    have h1 : T.verts ∈ (tops st).map Node.verts := hverts.mem_iff.mp (List.mem_map_of_mem hT)
    obtain ⟨T0, hT0, h2⟩ := List.mem_map.mp h1
    rw [hA, ← h2]
    exact h.dAtt T0 hT0
  · intro x
    rcases h.cover x with hx | ⟨T, hT, hx⟩
    · exact Or.inl (hA ▸ hx)
    · have h1 : T.verts ∈ (tops st').map Node.verts := hverts.mem_iff.mpr (List.mem_map_of_mem hT)
      obtain ⟨T0, hT0, h2⟩ := List.mem_map.mp h1
      exact Or.inr ⟨T0, hT0, h2 ▸ hx⟩

/-! ## The first step of a loop -/

theorem pop_sinv {g : Graph V} {us : List V} {st : St V} (h : SInv g us st) (hc : st.cur = none)
    {a : Node V} {rest : List (Node V)} (hf : st.free = a :: rest) :
    SInv g us { st with free := rest, cur := some a } := by
  have hp := h.curNone hc
  have htops : tops { st with free := rest, cur := some a } = tops st := by
    simp [tops, hc, hp, hf]
  have habs : absSt { st with free := rest, cur := some a } = absSt st := by
    have : absL (a :: rest) = absL [a] + absL rest := absL_append [a] rest
    simp [absSt, hc, hp, hf, absL_nil, this]
    exact add_assoc _ _ _
  obtain ⟨evs, h1, h2⟩ := h.run
  have hi := SInv1.mk' (st' := { st with free := rest, cur := some a }) h.toSInv1 rfl (by rw [htops])
    (fun T hT => h.node T (htops ▸ hT)) ⟨evs, by rw [habs]; exact h1, h2⟩
  exact { hi with curNone := fun hn => by simp at hn }

/-! ## The rebuilds of Cheapest -/

theorem refresh_verts (o : Oracle V) (g : Graph V) (C : Finset V) (y : V → ℤ) (G : Group V) :
    (refresh o g C y G).1.verts = G.verts := by
  unfold refresh
  cases headOut C G.entries with
  | some _ => rfl
  | none =>
    simp only
    split_ifs <;> rfl

theorem refreshAll_verts (o : Oracle V) (g : Graph V) (C : Finset V) (y : V → ℤ) (gs : List (Group V)) :
    (refreshAll o g C y gs).1.map Group.verts = gs.map Group.verts := by
  induction gs with
  | nil => rfl
  | cons G gs ih => simp [refreshAll, refresh_verts, ih]

theorem exists_verts_of_map_eq {l l' : List (Group V)} (h : l.map Group.verts = l'.map Group.verts) (x : V) :
    (∃ G ∈ l, x ∈ G.verts) ↔ ∃ G ∈ l', x ∈ G.verts := by
  have key : ∀ m : List (Group V), (∃ G ∈ m, x ∈ G.verts) ↔ ∃ A ∈ m.map Group.verts, x ∈ A := by
    intro m
    simp
  rw [key, key, h]

theorem refresh_groupS {o : Oracle V} (ho : o.Structural) {g : Graph V} {C : Finset V} (y : V → ℤ)
    {G : Group V} (hG : GroupS g C G) : GroupS g C (refresh o g C y G).1 := by
  unfold refresh
  cases headOut C G.entries with
  | some _ => exact hG
  | none =>
    simp only
    split_ifs with hc
    · exact hG
    · exact build_groupS ho g y G.verts (by have := hG.K_pos; omega) (Finset.Subset.refl C)

theorem refreshAll_groupS {o : Oracle V} (ho : o.Structural) {g : Graph V} {C : Finset V} (y : V → ℤ)
    {gs : List (Group V)} (h : ∀ G ∈ gs, GroupS g C G) :
    ∀ G ∈ (refreshAll o g C y gs).1, GroupS g C G := by
  induction gs with
  | nil => simp [refreshAll]
  | cons G gs ih =>
    intro G' hG'
    simp only [refreshAll, List.mem_cons] at hG'
    rcases hG' with rfl | hG'
    · exact refresh_groupS ho y (h G (List.mem_cons_self ..))
    · exact ih (fun G'' hG'' => h G'' (List.mem_cons_of_mem _ hG'')) G' hG'

/-- After the rebuilds, a list without a head is complete. -/
theorem refreshAll_complete {o : Oracle V} (ho : o.Structural) {g : Graph V} {C : Finset V} (y : V → ℤ)
    {gs : List (Group V)} (h : ∀ G ∈ gs, GroupS g C G) :
    ∀ G ∈ (refreshAll o g C y gs).1, headOut C G.entries = none → G.complete = true := by
  induction gs with
  | nil => simp [refreshAll]
  | cons G gs ih =>
    intro G' hG' hhead
    simp only [refreshAll, List.mem_cons] at hG'
    rcases hG' with rfl | hG'
    · have hGS := h G (List.mem_cons_self ..)
      cases hh : headOut C G.entries with
      | some e =>
        have h1 : refresh o g C y G = (G, []) := by simp [refresh, hh]
        rw [h1] at hhead ⊢
        simp only at hhead
        rw [hh] at hhead
        simp at hhead
      | none =>
        cases hcc : G.complete with
        | true =>
          have h1 : refresh o g C y G = (G, []) := by simp [refresh, hh, hcc]
          rw [h1]
          exact hcc
        | false =>
          have h1 : refresh o g C y G = (build o g C y G.verts (2 * G.K), [(G.verts, 2 * G.K)]) := by
            simp [refresh, hh, hcc]
          rw [h1] at hhead ⊢
          exact (build_shape ho g C y G.verts (2 * G.K)).complete_of_fresh
            (by have := hGS.K_pos; omega) hhead
    · exact ih (fun G'' hG'' => h G'' (List.mem_cons_of_mem _ hG'')) G' hG' hhead

/-- The rebuilds are events of the abstract machine. -/
theorem run_refresh {o : Oracle V} (ho : o.Structural) {g : Graph V} {us : List V} {C : Finset V} (y : V → ℤ)
    (rest : Multiset (Cont V)) :
    ∀ (todo done : List (Group V)) (evs : List (Ev V)),
      Run us evs (⟨C, (((done ++ todo).map absG : List (Grp V)) : Multiset (Grp V))⟩ ::ₘ rest) →
      (∀ G ∈ todo, GroupS g C G) →
      ∃ evs', Run us evs'
          (⟨C, (((done ++ (refreshAll o g C y todo).1).map absG : List (Grp V)) : Multiset (Grp V))⟩ ::ₘ rest) ∧
        allBuilds us evs' = (refreshAll o g C y todo).2 ++ allBuilds us evs := by
  intro todo
  induction todo with
  | nil =>
    intro done evs hr _
    exact ⟨evs, by simpa [refreshAll] using hr, by simp [refreshAll]⟩
  | cons G todo ih =>
    intro done evs hr hG
    have hGS := hG G (List.mem_cons_self ..)
    have hrest : ∀ G' ∈ todo, GroupS g C G' := fun G' hG' => hG G' (List.mem_cons_of_mem _ hG')
    by_cases hneed : headOut C G.entries = none ∧ G.complete = false
    · obtain ⟨hh, hcomp⟩ := hneed
      have hr1 : refresh o g C y G = (build o g C y G.verts (2 * G.K), [(G.verts, 2 * G.K)]) := by
        simp [refresh, hh, hcomp]
      obtain ⟨I, hI⟩ := hGS.shape
      have hgrow := lemma3c hI hGS.built hcomp hh
      have hperm : (((done ++ G :: todo).map absG : List (Grp V)) : Multiset (Grp V)) =
          absG G ::ₘ (((done ++ todo).map absG : List (Grp V)) : Multiset (Grp V)) := by
        rw [Multiset.cons_coe, Multiset.coe_eq_coe]
        simpa using List.perm_middle.map absG
      have hstep : AStep (⟨C, (((done ++ G :: todo).map absG : List (Grp V)) : Multiset (Grp V))⟩ ::ₘ rest)
          (.exhaust G.verts (2 * G.K))
          (⟨C, ⟨G.verts, 2 * G.K, C.card⟩ ::ₘ (((done ++ todo).map absG : List (Grp V)) : Multiset (Grp V))⟩ ::ₘ rest) :=
        AStep.exhaust rest _ (absG G) _ hperm hgrow
      have hr2 : Run us (.exhaust G.verts (2 * G.K) :: evs)
          (⟨C, (((done ++ [build o g C y G.verts (2 * G.K)] ++ todo).map absG : List (Grp V)) : Multiset (Grp V))⟩ ::ₘ rest) := by
        have heq : (((done ++ [build o g C y G.verts (2 * G.K)] ++ todo).map absG : List (Grp V)) : Multiset (Grp V)) =
            ⟨G.verts, 2 * G.K, C.card⟩ ::ₘ (((done ++ todo).map absG : List (Grp V)) : Multiset (Grp V)) := by
          rw [Multiset.cons_coe, Multiset.coe_eq_coe]
          have := (List.perm_middle (a := build o g C y G.verts (2 * G.K)) (l₁ := done) (l₂ := todo)).map absG
          simpa [absG_build] using this
        rw [heq]
        exact Run.step hr hstep
      obtain ⟨evs', h1, h2⟩ := ih (done ++ [build o g C y G.verts (2 * G.K)]) _ hr2 hrest
      refine ⟨evs', ?_, ?_⟩
      · simp only [refreshAll, hr1]
        simpa using h1
      · simp only [refreshAll, hr1, h2]
        simp [allBuilds, Ev.build]
    · have hr1 : (refresh o g C y G) = (G, []) := by
        unfold refresh
        cases hh : headOut C G.entries with
        | some _ => rfl
        | none =>
          simp only
          cases hcc : G.complete with
          | true => rfl
          | false => exact absurd ⟨hh, hcc⟩ hneed
      have hr2 : Run us evs (⟨C, (((done ++ [G] ++ todo).map absG : List (Grp V)) : Multiset (Grp V))⟩ ::ₘ rest) := by
        simpa using hr
      obtain ⟨evs', h1, h2⟩ := ih (done ++ [G]) evs hr2 hrest
      refine ⟨evs', ?_, ?_⟩
      · simp only [refreshAll, hr1]
        simpa using h1
      · simp only [refreshAll, hr1, h2]
        simp

theorem refreshed_sinv {o : Oracle V} (ho : o.Structural) {g : Graph V} {us : List V} {st : St V}
    (h : SInv g us st) {a : Node V} (hc : st.cur = some a) : SInv g us (refreshed o g st a) := by
  have hmem : a ∈ tops st := by simp [tops, hc]
  have hna := h.node a hmem
  set r := refreshAll o g a.verts st.y a.groups with hr
  have htops : tops (refreshed o g st a) = { a with groups := r.1 } :: (st.path ++ st.free) := by
    simp [tops, refreshed, hr]
  have htops0 : tops st = a :: (st.path ++ st.free) := by simp [tops, hc]
  have hnew : NodeS g { a with groups := r.1 } := by
    refine ⟨hna.nonempty, ?_, ?_, refreshAll_groupS ho st.y hna.groups⟩
    · simp only [hr]
      rw [refreshAll_verts]
      exact hna.pw
    · intro x
      rw [hna.cover x]
      exact (exists_verts_of_map_eq (refreshAll_verts o g a.verts st.y a.groups) x).symm
  have hrun : ∃ evs, Run us evs (absSt (refreshed o g st a)) ∧ allBuilds us evs = (refreshed o g st a).builds := by
    obtain ⟨evs, h1, h2⟩ := h.run
    set rest := absL st.A.nodes + absL st.path + absL st.free with hrest
    have habs : absSt st = absN a ::ₘ rest := by
      simp only [absSt, hc, hrest, Option.toList_some, absL_cons, absL_nil]
      simp only [← Multiset.singleton_add]
      abel
    have habs' : absSt (refreshed o g st a) = absN { a with groups := r.1 } ::ₘ rest := by
      simp only [absSt, refreshed, hrest, Option.toList_some, absL_cons, absL_nil, hr]
      simp only [← Multiset.singleton_add]
      abel
    rw [habs] at h1
    obtain ⟨evs', h3, h4⟩ := run_refresh ho st.y rest a.groups [] evs (by simpa [absN] using h1) hna.groups
    refine ⟨evs', ?_, ?_⟩
    · rw [habs']
      simpa [absN, hr] using h3
    · rw [h4, h2]
      rfl
  have hi := SInv1.mk' (st' := refreshed o g st a) h.toSInv1 rfl (by rw [htops, htops0]; rfl)
    (fun T hT => by
      rw [htops] at hT
      rcases List.mem_cons.mp hT with rfl | hT
      · exact hnew
      · exact h.node T (by rw [htops0]; exact List.mem_cons_of_mem _ hT)) hrun
  exact { hi with curNone := fun hn => by simp [refreshed] at hn }

/-! ## Unions of nodes and the absorption loop -/

theorem disjoint_unionV {A : Finset V} {l : List (Node V)} :
    Disjoint A (unionV l) ↔ ∀ T ∈ l, Disjoint A T.verts := by
  induction l with
  | nil => simp [unionV]
  | cons a l ih => simp [unionV, Finset.disjoint_union_right, ih]

theorem wt_unionV (d : V → ℕ) {l : List (Node V)} (h : (l.map Node.verts).Pairwise Disjoint) :
    wt d (unionV l) = (l.map fun T => wt d T.verts).sum := by
  induction l with
  | nil => simp [unionV, wt]
  | cons a l ih =>
    rw [List.map_cons, List.pairwise_cons] at h
    have hd : Disjoint a.verts (unionV l) :=
      disjoint_unionV.mpr fun T hT => h.1 _ (List.mem_map_of_mem hT)
    simp only [unionV, List.map_cons, List.sum_cons]
    rw [wt_union d hd, ih h.2]

theorem absorbF_spec : ∀ (k : ℕ) (H : Finset V) (gs : List (Group V)), gs.length ≤ k →
    (gs.map Group.verts).Pairwise Disjoint → (∀ G ∈ gs, Disjoint H G.verts) →
    (∃ A, Absorb ((gs.map absG : List (Grp V)) : Multiset (Grp V)) H A
        (((absorbF k H gs).2.map absG : List (Grp V)) : Multiset (Grp V)) (absorbF k H gs).1) ∧
    H ⊆ (absorbF k H gs).1 ∧ (∀ G ∈ (absorbF k H gs).2, G ∈ gs) ∧
    ((absorbF k H gs).2.map Group.verts).Pairwise Disjoint ∧
    (∀ G ∈ (absorbF k H gs).2, Disjoint (absorbF k H gs).1 G.verts) ∧
    (∀ x, (x ∈ (absorbF k H gs).1 ∨ ∃ G ∈ (absorbF k H gs).2, x ∈ G.verts) ↔ (x ∈ H ∨ ∃ G ∈ gs, x ∈ G.verts)) := by
  intro k
  induction k with
  | zero =>
    intro H gs hl hp hd
    obtain rfl : gs = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)
    refine ⟨⟨0, Absorb.stop _ _ (by simp)⟩, Finset.Subset.refl _, by simp [absorbF], by simp [absorbF], ?_, ?_⟩
    · simp [absorbF]
    · simp [absorbF]
  | succ k ih =>
    intro H gs hl hp hd
    cases hs : split (fun G => decide (lg G.verts.card = lg H.card)) gs with
    | none =>
      have hab : absorbF (k + 1) H gs = (H, gs) := by simp [absorbF, hs]
      rw [hab]
      refine ⟨⟨0, Absorb.stop _ _ ?_⟩, Finset.Subset.refl _, fun G hG => hG, hp, hd, fun x => Iff.rfl⟩
      intro G' hG'
      obtain ⟨G, hG, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp hG')
      have := split_none hs G hG
      simpa [Grp.cls, absG] using this
    | some r =>
      obtain ⟨g1, G, g2⟩ := r
      have hab : absorbF (k + 1) H gs = absorbF k (H ∪ G.verts) (g1 ++ g2) := by simp [absorbF, hs]
      rw [hab]
      obtain ⟨h1, h2, _⟩ := split_some hs
      simp only at h1 h2
      have hperm : List.Perm gs (G :: (g1 ++ g2)) := h1 ▸ List.perm_middle
      have hp' := ((hperm.map Group.verts).pairwise_iff (fun {a b} hab => hab.symm)).mp hp
      rw [List.map_cons, List.pairwise_cons] at hp'
      have hlen : (g1 ++ g2).length ≤ k := by
        have := hperm.length_eq
        simp only [List.length_cons] at this
        omega
      have hmemG : G ∈ gs := hperm.mem_iff.mpr (List.mem_cons_self ..)
      have hmemO : ∀ G' ∈ g1 ++ g2, G' ∈ gs := fun G' hG' => hperm.mem_iff.mpr (List.mem_cons_of_mem _ hG')
      have hdH : ∀ G' ∈ g1 ++ g2, Disjoint (H ∪ G.verts) G'.verts := fun G' hG' =>
        Finset.disjoint_union_left.mpr ⟨hd G' (hmemO G' hG'), hp'.1 _ (List.mem_map_of_mem hG')⟩
      obtain ⟨⟨A, hA⟩, a2, a3, a4, a5, a6⟩ := ih (H ∪ G.verts) (g1 ++ g2) hlen hp'.2 hdH
      refine ⟨⟨G.verts ::ₘ A, ?_⟩, Finset.subset_union_left.trans a2, fun G' hG' => hmemO G' (a3 G' hG'), a4, a5, ?_⟩
      · have hco : ((gs.map absG : List (Grp V)) : Multiset (Grp V)) =
            absG G ::ₘ (((g1 ++ g2).map absG : List (Grp V)) : Multiset (Grp V)) :=
          Multiset.coe_eq_coe.mpr (hperm.map absG)
        rw [hco]
        exact Absorb.absorb (absG G) _ H A _ _ (by simpa [Grp.cls, absG] using h2) (hd G hmemG) hA
      · intro x
        rw [a6 x, Finset.mem_union]
        constructor
        · rintro ((hx | hx) | ⟨G', hG', hx⟩)
          · exact Or.inl hx
          · exact Or.inr ⟨G, hmemG, hx⟩
          · exact Or.inr ⟨G', hmemO G' hG', hx⟩
        · rintro (hx | ⟨G', hG', hx⟩)
          · exact Or.inl (Or.inl hx)
          · rcases List.mem_cons.mp (hperm.mem_iff.mp hG') with rfl | hG''
            · exact Or.inl (Or.inr hx)
            · exact Or.inr ⟨G', hG'', hx⟩

/-! ## Selection -/

theorem selected_sinv {g : Graph V} {us : List V} {st : St V} (h : SInv g us st) {a : Node V}
    (hc : st.cur = some a) (e : V × V) (c : ℤ) :
    SInv1 g us { (selected st a e c).1 with path := (selected st a e c).2 :: (selected st a e c).1.path } := by
  have hmem : a ∈ tops st := by simp [tops, hc]
  have hna := h.node a hmem
  set a₁ := (selected st a e c).2 with ha₁
  set st₂ := { (selected st a e c).1 with path := a₁ :: (selected st a e c).1.path } with hst₂
  have htops : tops st₂ = a₁ :: (st.path ++ st.free) := by simp [tops, hst₂, selected]
  have htops0 : tops st = a :: (st.path ++ st.free) := by simp [tops, hc]
  have habs : absSt st₂ = absSt st := by
    have h1 : absL [a] = absL [a₁] := rfl
    have h2 : absL (a₁ :: st.path) = absL [a₁] + absL st.path := absL_append [a₁] st.path
    simp only [absSt, hst₂, selected, hc, Option.toList_some, Option.toList_none, absL_nil, add_zero]
    rw [h2, ← h1]
    abel
  refine SInv1.mk' h.toSInv1 rfl (by rw [htops, htops0]; rfl) ?_ ?_
  · intro T hT
    rw [htops] at hT
    rcases List.mem_cons.mp hT with rfl | hT
    · exact ⟨hna.nonempty, hna.pw, hna.cover, hna.groups⟩
    · exact h.node T (by rw [htops0]; exact List.mem_cons_of_mem _ hT)
  · obtain ⟨evs, h1, h2⟩ := h.run
    exact ⟨evs, by rw [habs]; exact h1, h2⟩

/-! ## The three branches of `route` -/

theorem foldl_add_nodes (l : List (Node V)) (A : Att V) :
    absL (l.foldl Att.add A).nodes = absL l + absL A.nodes := by
  induction l generalizing A with
  | nil => simp [absL_nil]
  | cons a l ih =>
    simp only [List.foldl_cons, ih, Att.add, absL_cons, Multiset.add_cons, Multiset.cons_add]

theorem attach_sinv {g : Graph V} {us : List V} {st : St V} {a : Node V} (hc : st.cur = none)
    (h : SInv1 g us { st with path := a :: st.path }) :
    SInv g us { st with A := (a :: st.path).foldl Att.add st.A, path := [], cur := none } := by
  set st₂ : St V := { st with path := a :: st.path } with hst₂
  set l := a :: st.path with hl
  have htops2 : tops st₂ = l ++ st.free := by simp [tops, hst₂, hc, hl]
  have htops : tops { st with A := l.foldl Att.add st.A, path := [], cur := none } = st.free := by
    simp [tops]
  have hdis := h.disj
  rw [htops2, List.map_append, List.pairwise_append] at hdis
  obtain ⟨_, hd2, hd3⟩ := hdis
  have hverts : (l.foldl Att.add st.A).verts = st.A.verts ∪ unionV l := foldl_add_path l st.A
  refine { root := ?_, disj := ?_, dAtt := ?_, cover := ?_, node := ?_, run := ?_, curNone := fun _ => rfl }
  · show g.root ∈ (l.foldl Att.add st.A).verts
    rw [hverts]
    exact Finset.mem_union_left _ h.root
  · rw [htops]
    exact hd2
  · intro T hT
    rw [htops] at hT
    show Disjoint T.verts (l.foldl Att.add st.A).verts
    rw [hverts, Finset.disjoint_union_right]
    refine ⟨h.dAtt T (by rw [htops2]; exact List.mem_append_right _ hT), ?_⟩
    exact disjoint_unionV.mpr fun T' hT' => (hd3 _ (List.mem_map_of_mem hT') _ (List.mem_map_of_mem hT)).symm
  · intro x
    rcases h.cover x with hx | ⟨T, hT, hx⟩
    · refine Or.inl ?_
      show x ∈ (l.foldl Att.add st.A).verts
      rw [hverts]
      exact Finset.mem_union_left _ hx
    · rw [htops2] at hT
      rcases List.mem_append.mp hT with hT | hT
      · refine Or.inl ?_
        show x ∈ (l.foldl Att.add st.A).verts
        rw [hverts]
        exact Finset.mem_union_right _ (mem_unionV.mpr ⟨T, hT, hx⟩)
      · exact Or.inr ⟨T, by rw [htops]; exact hT, hx⟩
  · intro T hT
    rw [htops] at hT
    exact h.node T (by rw [htops2]; exact List.mem_append_right _ hT)
  · obtain ⟨evs, h1, h2⟩ := h.run
    refine ⟨evs, ?_, h2⟩
    have : absSt { st with A := l.foldl Att.add st.A, path := [], cur := none } = absSt st₂ := by
      simp only [absSt, hst₂, hc, Option.toList_none, absL_nil, add_zero, foldl_add_nodes]
      rw [add_comm (absL l)]
    rw [this]
    exact h1

theorem push_sinv {g : Graph V} {us : List V} {st : St V} {a b : Node V} {f1 f2 : List (Node V)}
    (hc : st.cur = none) (hf : st.free = f1 ++ b :: f2) (h : SInv1 g us { st with path := a :: st.path }) :
    SInv g us { st with free := f1 ++ f2, path := a :: st.path, cur := some b } := by
  set st₂ : St V := { st with path := a :: st.path } with hst₂
  set st₃ : St V := { st with free := f1 ++ f2, path := a :: st.path, cur := some b } with hst₃
  have hperm : List.Perm (tops st₃) (tops st₂) := by
    simp only [tops, hst₃, hst₂, hc, hf, Option.toList_some, Option.toList_none, List.nil_append]
    have : (a :: st.path) ++ f1 ++ b :: f2 = ((a :: st.path) ++ f1) ++ b :: f2 := rfl
    have h2 := (List.perm_middle (a := b) (l₁ := (a :: st.path) ++ f1) (l₂ := f2)).symm
    simpa [List.append_assoc] using h2
  have habs : absSt st₃ = absSt st₂ := by
    have h1 : absL (f1 ++ b :: f2) = absL [b] + absL (f1 ++ f2) := by
      rw [absL_perm (List.perm_middle (a := b) (l₁ := f1) (l₂ := f2))]
      exact absL_append [b] _
    simp only [absSt, hst₃, hst₂, hc, hf, Option.toList_some, Option.toList_none, absL_nil, add_zero, h1]
    abel
  obtain ⟨evs, h1, h2⟩ := h.run
  have hi := SInv1.mk' (st' := st₃) h rfl (hperm.map _)
    (fun T hT => h.node T (hperm.mem_iff.mp hT)) ⟨evs, by rw [habs]; exact h1, h2⟩
  exact { hi with curNone := fun hn => by simp [hst₃] at hn }

/-- The structural facts about a contraction, and the abstract event. -/
theorem contract_sinv {o : Oracle V} (ho : o.Structural) {g : Graph V} {us : List V} {st : St V}
    {a b : Node V} {seg pre : List (Node V)} (hc : st.cur = none) (hpath : st.path = seg ++ b :: pre)
    (h : SInv1 g us { st with path := a :: st.path }) :
    SInv g us { st with
      path := pre
      cur := some (contractNode o g st.y a (seg ++ [b]))
      builds := (contractH a (seg ++ [b]), (contractH a (seg ++ [b])).card) :: st.builds } := by
  set rest := seg ++ [b] with hrest
  set parts := a :: rest with hparts
  set st₂ : St V := { st with path := a :: st.path } with hst₂
  have htops2 : tops st₂ = parts ++ (pre ++ st.free) := by
    simp [tops, hst₂, hc, hpath, hparts, hrest]
  have hdis := h.disj
  rw [htops2, List.map_append, List.pairwise_append] at hdis
  obtain ⟨hdp, hdr, hdpr⟩ := hdis
  have hnp : ∀ T ∈ parts, NodeS g T := fun T hT => h.node T (by rw [htops2]; exact List.mem_append_left _ hT)
  have hnr : ∀ T ∈ pre ++ st.free, NodeS g T := fun T hT =>
    h.node T (by rw [htops2]; exact List.mem_append_right _ hT)
  have hperm : List.Perm ((pick a rest).1 :: (pick a rest).2) parts := pick_perm a rest
  set S := (pick a rest).1 with hS
  set others := (pick a rest).2 with hothers
  have hmemS : S ∈ parts := hperm.mem_iff.mp (List.mem_cons_self ..)
  have hmemO : ∀ T ∈ others, T ∈ parts := fun T hT => hperm.mem_iff.mp (List.mem_cons_of_mem _ hT)
  have hdso := ((hperm.map Node.verts).pairwise_iff (fun {a b} hab => hab.symm)).mpr hdp
  rw [List.map_cons, List.pairwise_cons] at hdso
  obtain ⟨hSO, hOO⟩ := hdso
  set M := unionV others with hM
  have hSM : Disjoint S.verts M := disjoint_unionV.mpr fun T hT => hSO _ (List.mem_map_of_mem hT)
  have hOne : others ≠ [] := by
    intro hnil
    have := hperm.length_eq
    simp [hnil, hparts, hrest] at this
  have hMne : M.Nonempty := by
    obtain ⟨T, hT⟩ := List.exists_mem_of_ne_nil _ hOne
    obtain ⟨x, hx⟩ := (hnp T (hmemO T hT)).nonempty
    exact ⟨x, mem_unionV.mpr ⟨T, hT, hx⟩⟩
  have hnS := hnp S hmemS
  have hMG : ∀ G ∈ S.groups, Disjoint M G.verts := fun G hG =>
    (Finset.disjoint_of_subset_right
      (fun x hx => (hnS.cover x).mpr ⟨G, hG, hx⟩) hSM.symm)
  obtain ⟨⟨A', hAbs⟩, hMH, hmemG, hpw', hdH, hcov⟩ :=
    absorbF_spec S.groups.length M S.groups le_rfl hnS.pw hMG
  set H := (absorbF S.groups.length M S.groups).1 with hH
  set gs' := (absorbF S.groups.length M S.groups).2 with hgs'
  have hHeq : contractH a rest = H := rfl
  set X := contractNode o g st.y a rest with hX
  have hXv : X.verts = S.verts ∪ M := rfl
  have hXg : X.groups = build o g (S.verts ∪ M) st.y H H.card :: gs' := rfl
  have hXmem : ∀ x, x ∈ X.verts ↔ ∃ T ∈ parts, x ∈ T.verts := by
    intro x
    rw [hXv, Finset.mem_union, mem_unionV]
    constructor
    · rintro (hx | ⟨T, hT, hx⟩)
      · exact ⟨S, hmemS, hx⟩
      · exact ⟨T, hmemO T hT, hx⟩
    · rintro ⟨T, hT, hx⟩
      rcases List.mem_cons.mp (hperm.mem_iff.mpr hT) with rfl | hT'
      · exact Or.inl hx
      · exact Or.inr ⟨T, hT', hx⟩
  have hXdis : ∀ T ∈ pre ++ st.free, Disjoint X.verts T.verts := by
    intro T hT
    rw [Finset.disjoint_left]
    intro x hx hxT
    obtain ⟨P, hP, hxP⟩ := (hXmem x).mp hx
    exact Finset.disjoint_left.mp (hdpr _ (List.mem_map_of_mem hP) _ (List.mem_map_of_mem hT)) hxP hxT
  have hNX : NodeS g X := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hXv]
      exact hMne.mono Finset.subset_union_right
    · rw [hXg, List.map_cons, List.pairwise_cons]
      refine ⟨fun B hB => ?_, hpw'⟩
      obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hB
      exact hdH G hG
    · intro x
      rw [hXv, hXg, Finset.mem_union]
      constructor
      · rintro (hx | hx)
        · obtain ⟨G, hG, hxG⟩ := (hnS.cover x).mp hx
          rcases (hcov x).mpr (Or.inr ⟨G, hG, hxG⟩) with hh | ⟨G', hG', hx'⟩
          · exact ⟨build o g (S.verts ∪ M) st.y H H.card, List.mem_cons_self .., hh⟩
          · exact ⟨G', List.mem_cons_of_mem _ hG', hx'⟩
        · exact ⟨build o g (S.verts ∪ M) st.y H H.card, List.mem_cons_self .., hMH hx⟩
      · rintro ⟨G, hG, hx⟩
        rcases List.mem_cons.mp hG with rfl | hG'
        · rcases (hcov x).mp (Or.inl hx) with hx' | ⟨G', hG'', hx'⟩
          · exact Or.inr hx'
          · exact Or.inl ((hnS.cover x).mpr ⟨G', hG'', hx'⟩)
        · rcases (hcov x).mp (Or.inr ⟨G, hG', hx⟩) with hx' | ⟨G', hG'', hx'⟩
          · exact Or.inr hx'
          · exact Or.inl ((hnS.cover x).mpr ⟨G', hG'', hx'⟩)
    · intro G hG
      rw [hXg] at hG
      rcases List.mem_cons.mp hG with rfl | hG'
      · refine build_groupS ho g st.y H ?_ (Finset.Subset.refl _)
        exact Finset.card_pos.mpr (hMne.mono hMH)
      · have h1 := hnS.groups G (hmemG G hG')
        exact ⟨h1.K_pos, h1.built.trans (by rw [hXv]; exact Finset.subset_union_left), h1.shape⟩
  have htops4 : tops { st with path := pre, cur := some X, builds := (contractH a rest, (contractH a rest).card) :: st.builds } = X :: (pre ++ st.free) := by
    simp [tops]
  refine { root := h.root, disj := ?_, dAtt := ?_, cover := ?_, node := ?_, run := ?_,
           curNone := fun hn => by simp at hn }
  · rw [htops4, List.map_cons, List.pairwise_cons]
    refine ⟨fun B hB => ?_, hdr⟩
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hB
    exact hXdis T hT
  · intro T hT
    rw [htops4] at hT
    show Disjoint T.verts st.A.verts
    rcases List.mem_cons.mp hT with rfl | hT
    · rw [Finset.disjoint_left]
      intro x hx hxA
      obtain ⟨P, hP, hxP⟩ := (hXmem x).mp hx
      exact Finset.disjoint_left.mp (h.dAtt P (by rw [htops2]; exact List.mem_append_left _ hP)) hxP hxA
    · exact h.dAtt T (by rw [htops2]; exact List.mem_append_right _ hT)
  · intro x
    rcases h.cover x with hx | ⟨T, hT, hx⟩
    · exact Or.inl hx
    · rw [htops2] at hT
      rw [htops4]
      rcases List.mem_append.mp hT with hT | hT
      · exact Or.inr ⟨X, List.mem_cons_self .., (hXmem x).mpr ⟨T, hT, hx⟩⟩
      · exact Or.inr ⟨T, List.mem_cons_of_mem _ hT, hx⟩
  · intro T hT
    rw [htops4] at hT
    rcases List.mem_cons.mp hT with rfl | hT
    · exact hNX
    · exact hnr T hT
  · obtain ⟨evs, h1, h2⟩ := h.run
    set R := absL st.A.nodes + absL pre + absL st.free with hR
    have habs : absSt st₂ = absN S ::ₘ (absL others + R) := by
      have e1 : absL (a :: st.path) = absL parts + absL pre := by
        rw [← absL_append]
        apply absL_perm
        simp only [hparts, hrest, hpath, List.cons_append, List.append_assoc, List.singleton_append]
        exact List.Perm.refl _
      have e2 : absL parts = absN S ::ₘ absL others := (absL_perm hperm).symm
      simp only [absSt, hst₂, hc, Option.toList_none, absL_nil, add_zero, e1, e2, hR]
      simp only [← Multiset.singleton_add]
      abel
    have hstep : AStep (absN S ::ₘ (absL others + R)) (.contract M A' H)
        (⟨S.verts ∪ M, ⟨H, H.card, (S.verts ∪ M).card⟩ ::ₘ ((gs'.map absG : List (Grp V)) : Multiset (Grp V))⟩ ::ₘ R) := by
      refine AStep.contract R (absL others) (absN S) M H A' _ ?_ hMne ?_ hSM hAbs
      · intro C hC
        obtain ⟨T, hT, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp hC)
        exact pick_le a rest T hT
      · intro d
        rw [hM, wt_unionV d hOO]
        simp [absL, absN, Function.comp_def]
    refine ⟨.contract M A' H :: evs, ?_, ?_⟩
    · have habs' : absSt { st with path := pre, cur := some X, builds := (contractH a rest, (contractH a rest).card) :: st.builds } =
          (⟨S.verts ∪ M, ⟨H, H.card, (S.verts ∪ M).card⟩ ::ₘ ((gs'.map absG : List (Grp V)) : Multiset (Grp V))⟩ ::ₘ R) := by
        have e3 : absL [X] = {⟨S.verts ∪ M, ⟨H, H.card, (S.verts ∪ M).card⟩ ::ₘ ((gs'.map absG : List (Grp V)) : Multiset (Grp V))⟩} := rfl
        simp only [absSt, Option.toList_some, e3, hR]
        simp only [← Multiset.singleton_add]
        abel
      rw [habs']
      exact Run.step (habs ▸ h1) hstep
    · simp only [allBuilds, List.map_cons, Ev.build, List.cons_append] at h2 ⊢
      rw [h2]
      rfl

theorem route_sinv {o : Oracle V} (ho : o.Structural) {g : Graph V} {us : List V} {st : St V} {a : Node V}
    (hc : st.cur = none) (h : SInv1 g us { st with path := a :: st.path }) (hu : a.inE.1 ∉ a.verts) :
    SInv g us (route o g st a) := by
  unfold route
  simp only
  split_ifs with hA
  · exact attach_sinv hc h
  · cases hs : split (fun T => decide (a.inE.1 ∈ T.verts)) st.path with
    | some r =>
      obtain ⟨seg, b, pre⟩ := r
      exact contract_sinv ho hc (split_some hs).1 h
    | none =>
      simp only
      cases hf : split (fun T => decide (a.inE.1 ∈ T.verts)) st.free with
      | some r =>
        obtain ⟨f1, b, f2⟩ := r
        exact push_sinv hc (split_some hf).1 h
      | none =>
        exfalso
        rcases h.cover a.inE.1 with hx | ⟨T, hT, hx⟩
        · exact hA hx
        · simp only [tops, hc, Option.toList_none, List.nil_append, List.mem_cons, List.mem_append] at hT
          rcases hT with (rfl | hT) | hT
          · exact hu hx
          · have := split_none hs T hT
            simp [hx] at this
          · have := split_none hf T hT
            simp [hx] at this

/-- The source of the edge chosen by `Cheapest` is outside the container. -/
theorem minBy_heads_source {F : V × V → ℤ} {C : Finset V} {gs : List (Group V)} {e : V × V}
    (h : minBy F (heads C gs) = some e) : e.1 ∉ C ∧ ∃ G ∈ gs, headOut C G.entries = some e := by
  have h1 := (minBy_some h).1
  obtain ⟨G, hG, hh⟩ := List.mem_filterMap.mp h1
  exact ⟨(headOut_mem hh).2, G, hG, hh⟩

/-- **The structural invariant is preserved by a step.** -/
theorem step_sinv {o : Oracle V} (ho : o.Structural) {g : Graph V} {us : List V} {st st' : St V}
    (h : SInv g us st) (hs : step o g st = .running st') : SInv g us st' := by
  rcases step_running hs with ⟨hc, a, rest, hf, rfl⟩ | ⟨a, e, hc, hm, rfl⟩
  · exact pop_sinv h hc hf
  · have h0 := refreshed_sinv ho h hc
    have hc0 : (refreshed o g st a).cur = some { a with groups := (refreshAll o g a.verts st.y a.groups).1 } := rfl
    have h1 := selected_sinv h0 hc0 e (redCost g st.y e)
    exact route_sinv ho rfl h1 (minBy_heads_source hm).1

theorem reach_sinv {o : Oracle V} (ho : o.Structural) {g : Graph V} {us : List V} {st s : St V}
    (h : SInv g us st) (hr : Reach o g st s) : SInv g us s := by
  induction hr with
  | refl => exact h
  | step _ hb ih => exact step_sinv ho ih hb

/-! ## The bound for `solve` -/

theorem card_inEdges (g : Graph V) (G : Finset V) : (inEdges g G).card = wt (indeg g) G := by
  have h : inEdges g G = G.biUnion fun v => (univ.filter fun u => g.adj u v = true).image fun u => (u, v) := by
    ext e
    obtain ⟨u, v⟩ := e
    simp only [mem_inEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨v, h2, u, h1, rfl, rfl⟩
    · rintro ⟨v', h2, u', h1, rfl, rfl⟩
      exact ⟨h1, h2⟩
  rw [h, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.card_image_of_injective _ (fun a b hab => (Prod.mk.inj hab).1)]
    rfl
  · intro v _ w _ hvw
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨_, _, h3⟩ := Finset.mem_image.mp he'
    exact hvw (Prod.mk.inj h3).2.symm

theorem wt_indeg_univ (g : Graph V) : wt (indeg g) univ = numEdges g := rfl

/-- The builds of `solve` are the builds of a run of the abstract machine, for any oracle with outputs of items of
distinct types. -/
theorem solve_run {o : Oracle V} (ho : o.Structural) (g : Graph V) {vs : List V} (hvs : vs.Nodup)
    (hall : ∀ v, v ∈ vs) :
    ∃ σ evs, Run (vs.filter fun v => decide (v ≠ g.root)) evs σ ∧
      allBuilds (vs.filter fun v => decide (v ≠ g.root)) evs = (solve o g vs).2 := by
  set us := vs.filter fun v => decide (v ≠ g.root) with hus
  have hnd : us.Nodup := hvs.filter _
  have hroot : g.root ∉ us := by simp [hus]
  have hmem : ∀ v, v ≠ g.root → v ∈ us := fun v hv => by simp [hus, hv, hall]
  have h0 := init_sinv (o := o) ho g hnd hroot hmem
  obtain ⟨s, hr, hd⟩ := solve_reach o g vs
  have hs := reach_sinv ho h0 hr
  rcases hd with ⟨s', h1, h2⟩ | ⟨s', h1, h2⟩
  · obtain ⟨rfl, _, _⟩ := step_done h1
    obtain ⟨evs, h3, h4⟩ := hs.run
    exact ⟨_, evs, h3, by rw [h4, h2]⟩
  · obtain ⟨a, hc, rfl, _⟩ := step_noArb h1
    obtain ⟨evs, h3, h4⟩ := (refreshed_sinv ho hs hc).run
    exact ⟨_, evs, h3, by rw [h4, h2]⟩

/-- **The builds of `solve`:** `Σ K ≤ n + 2 n L + 2 n L²`. -/
theorem solve_sum_K {o : Oracle V} (ho : o.Structural) (g : Graph V) {vs : List V} (hvs : vs.Nodup)
    (hall : ∀ v, v ∈ vs) :
    ((solve o g vs).2.map Prod.snd).sum ≤
      Fintype.card V + 2 * Fintype.card V * logL (Fintype.card V) +
        2 * Fintype.card V * logL (Fintype.card V) ^ 2 := by
  obtain ⟨σ, evs, h1, h2⟩ := solve_run ho g hvs hall
  rw [← h2]
  exact lemma4e (hvs.filter _) h1

/-- **The builds of `solve`:** `Σ N(G) ≤ m (2 L + 1) (L + 1)`. -/
theorem solve_sum_N {o : Oracle V} (ho : o.Structural) (g : Graph V) {vs : List V} (hvs : vs.Nodup)
    (hall : ∀ v, v ∈ vs) :
    ((solve o g vs).2.map fun b => (inEdges g b.1).card).sum ≤
      numEdges g * ((2 * logL (Fintype.card V) + 1) * (logL (Fintype.card V) + 1)) := by
  obtain ⟨σ, evs, h1, h2⟩ := solve_run ho g hvs hall
  rw [← h2]
  simp only [card_inEdges]
  exact sum_wt_le (hvs.filter _) h1 (indeg g)

/-- **The cost bound of `solve`.** The charges of all TopK calls sum to at most `6 √(n m) L²`, with `L = ⌊log₂ n⌋ + 1`.
This needs only that outputs of the oracle are items of distinct types. -/
theorem solve_cost {o : Oracle V} (ho : o.Structural) (g : Graph V) {vs : List V} (hvs : vs.Nodup)
    (hall : ∀ v, v ∈ vs) :
    ((solve o g vs).2.map fun b => topKCost b.2 (inEdges g b.1).card).sum ≤
      6 * Real.sqrt ((Fintype.card V : ℝ) * (numEdges g : ℝ)) * (logL (Fintype.card V) : ℝ) ^ 2 := by
  obtain ⟨σ, evs, h1, h2⟩ := solve_run ho g hvs hall
  rw [← h2]
  simp only [card_inEdges]
  exact lemma5 (hvs.filter _) h1 (indeg g)

end Arborescence
