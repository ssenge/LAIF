import RiskRouting.MinProd

/-!
# From edge-disjoint to vertex-disjoint min-min

The line graph of `G` with two new terminals: a vertex for every link of `G`, joined when the links
share an end, a source joined to the links at `s`, and a sink joined to the links at `t`. A path
of `G` with `k` links becomes a path from the source to the sink with `k + 1` links, and two paths
without a common link become internally vertex-disjoint. Conversely, a path from the source to the
sink lists links of `G` in which consecutive links share an end; these contain a path of `G` from
`s` to `t` with at most as many links, found by shortcutting the walk they trace.

- `eMinMin_iff_minMin`: edge-disjoint min-min with bound `ℓ` holds in `G` iff vertex-disjoint
  min-min with bound `ℓ + 1` holds in the line graph with terminals.
- `card_lineV_le`: the new instance has at most `n² + 2` vertices.
- `reduction_line`: the map of instances, with the same answer and at most `n² + 2` vertices.
- `reduction_minProd_e`, `reduction_minProd₂_e`, `reduction_route_e`: the composed maps from
  edge-disjoint min-min, with the same answer and at most `⌈1 + (C + 2)²⌉ (n² + 3)³` vertices.
-/

namespace RiskRouting

open List SimpleGraph

variable {V : Type*}

/-- The links of a path, as unordered pairs. -/
def edgesL (p : List V) : List (Sym2 V) := (linkList p).map fun x => s(x.1, x.2)

theorem edgesL_cons_cons (a b : V) (l : List V) :
    edgesL (a :: b :: l) = s(a, b) :: edgesL (b :: l) := by
  simp [edgesL, linkList]

theorem edgesL_nil : edgesL ([] : List V) = [] := by simp [edgesL, linkList]

theorem edgesL_single (a : V) : edgesL [a] = [] := by simp [edgesL, linkList]

theorem length_edgesL (p : List V) : (edgesL p).length = links p := by
  simp [edgesL, length_linkList]

theorem mem_of_mem_edgesL : ∀ {p : List V} {e : Sym2 V}, e ∈ edgesL p → ∀ v ∈ e, v ∈ p
  | [], e, h, _, _ => by simp [edgesL_nil] at h
  | [a], e, h, _, _ => by simp [edgesL_single] at h
  | a :: b :: l, e, h, v, hv => by
      rw [edgesL_cons_cons] at h
      rcases List.mem_cons.mp h with rfl | h
      · rcases Sym2.mem_iff.mp hv with rfl | rfl <;> simp
      · exact List.mem_cons_of_mem _ (mem_of_mem_edgesL h v hv)

theorem edgesL_nodup : ∀ {p : List V}, p.Nodup → (edgesL p).Nodup
  | [], _ => by simp [edgesL_nil]
  | [a], _ => by simp [edgesL_single]
  | a :: b :: l, h => by
      rw [edgesL_cons_cons]
      refine List.nodup_cons.mpr ⟨fun hm => ?_, edgesL_nodup h.of_cons⟩
      exact (List.nodup_cons.mp h).1 (mem_of_mem_edgesL hm a (Sym2.mem_mk_left a b))

theorem edgesL_mem_edgeSet (G : SimpleGraph V) :
    ∀ {p : List V}, p.IsChain G.Adj → ∀ e ∈ edgesL p, e ∈ G.edgeSet
  | [], _, e, h => by simp [edgesL_nil] at h
  | [a], _, e, h => by simp [edgesL_single] at h
  | a :: b :: l, hc, e, h => by
      rw [edgesL_cons_cons] at h
      rw [isChain_cons_cons] at hc
      rcases List.mem_cons.mp h with rfl | h
      · exact hc.1
      · exact edgesL_mem_edgeSet G hc.2 e h

/-! ## The line graph with terminals -/

/-- Vertices: a source, a sink, and one vertex for every unordered pair of vertices of `G`; pairs
that are not links of `G` are isolated. -/
inductive LV (V : Type*) where
  | src : LV V
  | dst : LV V
  | ed : Sym2 V → LV V
  deriving DecidableEq

namespace LV

def equivOpt : LV V ≃ Option (Option (Sym2 V)) where
  toFun
    | src => none
    | dst => some none
    | ed e => some (some e)
  invFun
    | none => src
    | some none => dst
    | some (some e) => ed e
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with _ | _ | e <;> rfl

instance [Fintype V] [DecidableEq V] : Fintype (LV V) := Fintype.ofEquiv _ equivOpt.symm

theorem card [Fintype V] [DecidableEq V] : Fintype.card (LV V) = Fintype.card (Sym2 V) + 2 := by
  rw [Fintype.card_congr (equivOpt (V := V))]; simp

theorem ed_injective : Function.Injective (ed : Sym2 V → LV V) := fun _ _ h => by cases h; rfl

end LV

open LV

/-- Adjacency of the line graph with terminals. -/
def ladj (G : SimpleGraph V) (s t : V) : LV V → LV V → Prop
  | src, ed e => e ∈ G.edgeSet ∧ s ∈ e
  | ed e, src => e ∈ G.edgeSet ∧ s ∈ e
  | dst, ed e => e ∈ G.edgeSet ∧ t ∈ e
  | ed e, dst => e ∈ G.edgeSet ∧ t ∈ e
  | ed e, ed f => e ∈ G.edgeSet ∧ f ∈ G.edgeSet ∧ e ≠ f ∧ ∃ v, v ∈ e ∧ v ∈ f
  | src, src => False
  | src, dst => False
  | dst, src => False
  | dst, dst => False

/-- The line graph with terminals. -/
def lineG (G : SimpleGraph V) (s t : V) : SimpleGraph (LV V) where
  Adj := ladj G s t
  symm := ⟨by
    intro x y h
    cases x <;> cases y <;> first
      | exact h
      | exact ⟨h.2.1, h.1, h.2.2.1.symm, let ⟨v, h1, h2⟩ := h.2.2.2; ⟨v, h2, h1⟩⟩⟩
  loopless := ⟨by
    intro x h
    cases x with
    | src => exact h
    | dst => exact h
    | ed e => exact h.2.2.1 rfl⟩

variable (G : SimpleGraph V) (s t : V)

/-- Edge-disjoint min-min, decision version: two paths from `s` to `t` without a common link,
one of them with at most `ℓ` links. -/
def EMinMinYes (ℓ : ℕ) : Prop :=
  ∃ p₁ p₂, IsPathL G.Adj p₁ s t ∧ IsPathL G.Adj p₂ s t ∧ (∀ e ∈ edgesL p₁, e ∉ edgesL p₂) ∧
    links p₁ ≤ ℓ

theorem chain_edges : ∀ {p : List V}, p.IsChain G.Adj → p.Nodup →
    ((edgesL p).map ed).IsChain (ladj G s t)
  | [], _, _ => by simp [edgesL_nil]
  | [a], _, _ => by simp [edgesL_single]
  | [a, b], _, _ => by simp [edgesL_cons_cons, edgesL_single]
  | a :: b :: c :: l, hc, hn => by
      rw [edgesL_cons_cons, edgesL_cons_cons, List.map_cons, List.map_cons, isChain_cons_cons]
      have hc' := hc
      rw [isChain_cons_cons, isChain_cons_cons] at hc'
      refine ⟨⟨hc'.1, hc'.2.1, ?_, b, Sym2.mem_mk_right a b, Sym2.mem_mk_left b c⟩, ?_⟩
      · intro h
        rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
        · subst h1; simp at hn
        · subst h1; simp at hn
      · have := chain_edges (p := b :: c :: l) hc.tail hn.of_cons
        rw [edgesL_cons_cons, List.map_cons] at this
        exact this

/-- A path of `G` becomes a path of the line graph from the source to the sink. -/
theorem line_path {p : List V} (hst : s ≠ t) (hp : IsPathL G.Adj p s t) :
    IsPathL (ladj G s t) (src :: ((edgesL p).map ed ++ [dst])) src dst ∧
      links (src :: ((edgesL p).map ed ++ [dst])) = links p + 1 ∧ edgesL p ≠ [] := by
  obtain ⟨hh, hl, hc, hn⟩ := hp
  have h2 := two_le_length ⟨hh, hl, hc, hn⟩ hst
  obtain ⟨a, b, l, rfl⟩ : ∃ a b l, p = a :: b :: l := by
    match p, h2 with
    | a :: b :: l, _ => exact ⟨a, b, l, rfl⟩
  have ha : a = s := by simpa using hh
  have hE := edgesL_mem_edgeSet G hc
  have hne : edgesL (a :: b :: l) ≠ [] := by simp [edgesL_cons_cons]
  -- the last link contains t
  have hlast : ∀ e ∈ (edgesL (a :: b :: l)).getLast?, t ∈ e := by
    obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hl
    intro e he
    obtain ⟨zs, hzs⟩ := List.getLast?_eq_some_iff.mp he
    have hy : ∃ u, ys = ys.dropLast ++ [u] := by
      rcases List.eq_nil_or_concat ys with h | ⟨L, u, h⟩
      · subst h; simp at hys
      · exact ⟨u, by simp [h]⟩
    obtain ⟨u, hu⟩ := hy
    have key : edgesL (ys.dropLast ++ [u, t]) = edgesL (ys.dropLast ++ [u]) ++ [s(u, t)] := by
      generalize ys.dropLast = L
      induction L with
      | nil => simp [edgesL_cons_cons, edgesL_single]
      | cons x L ih =>
        cases L with
        | nil => simp [edgesL_cons_cons, edgesL_single]
        | cons y L =>
          simp only [List.cons_append] at ih ⊢
          rw [edgesL_cons_cons, ih, edgesL_cons_cons]; simp
    have : a :: b :: l = ys.dropLast ++ [u, t] := by rw [hys, hu]; simp
    rw [this, key] at hzs
    simp at hzs
    rw [← hzs.2]; exact Sym2.mem_mk_right u t
  refine ⟨⟨rfl, List.getLast?_eq_some_iff.mpr ⟨src :: map ed (edgesL (a :: b :: l)), rfl⟩, ?_, ?_⟩, ?_, hne⟩
  · rw [isChain_cons, isChain_append]
    refine ⟨?_, chain_edges G s t hc hn, isChain_singleton _, ?_⟩
    · intro y hy
      rw [edgesL_cons_cons] at hy
      simp at hy
      subst hy
      exact ⟨hE _ (by rw [edgesL_cons_cons]; simp), ha ▸ Sym2.mem_mk_left a b⟩
    · intro x hx y hy
      simp at hy
      subst hy
      rw [getLast?_map] at hx
      simp only [Option.mem_def, Option.map_eq_some_iff] at hx
      obtain ⟨e, he, rfl⟩ := hx
      exact ⟨hE e (mem_of_last he), hlast e he⟩
  · refine List.nodup_cons.mpr ⟨by simp, ?_⟩
    rw [List.nodup_append]
    refine ⟨(edgesL_nodup hn).map ed_injective, by simp, ?_⟩
    intro x hx y hy hxy
    simp at hx hy
    obtain ⟨e, -, rfl⟩ := hx
    subst hy; cases hxy
  · simp [links, length_edgesL]

/-- Consecutive links that share an end trace a walk from any end of the first link to `t`. -/
theorem walk_of_links : ∀ (es : List (Sym2 V)) (e : Sym2 V) (v : V), v ∈ e →
    (e :: es).IsChain (fun a b => ladj G s t (ed a) (ed b)) →
    (∀ x ∈ (e :: es).getLast?, x ∈ G.edgeSet ∧ t ∈ x) →
    ∃ w : G.Walk v t, w.length ≤ (e :: es).length ∧ ∀ x ∈ w.edges, x ∈ e :: es
  | [], e, v, hv, _, hl => by
      obtain ⟨heE, ht⟩ := hl e (by simp)
      by_cases hvt : v = t
      · subst hvt; exact ⟨Walk.nil, by simp, by simp⟩
      · have he : e = s(v, t) := (Sym2.mem_and_mem_iff hvt).mp ⟨hv, ht⟩
        subst he
        refine ⟨Walk.cons (G.mem_edgeSet.mp heE) Walk.nil, by simp [Walk.length_cons], ?_⟩
        intro x hx
        simpa [Walk.edges_cons] using hx
  | f :: es, e, v, hv, hc, hl => by
      rw [isChain_cons_cons] at hc
      obtain ⟨⟨heE, -, -, w, hwe, hwf⟩, hc'⟩ := hc
      obtain ⟨W, hW, hWe⟩ := walk_of_links es f w hwf hc'
        (fun x hx => hl x (by rw [getLast?_cons_cons]; exact hx))
      by_cases hvw : v = w
      · subst hvw
        exact ⟨W, by simp at hW ⊢; omega, fun x hx => List.mem_cons_of_mem _ (hWe x hx)⟩
      · have he : e = s(v, w) := (Sym2.mem_and_mem_iff hvw).mp ⟨hv, hwe⟩
        subst he
        refine ⟨Walk.cons (G.mem_edgeSet.mp heE) W, ?_, ?_⟩
        · rw [Walk.length_cons]; simp at hW ⊢; omega
        intro x hx
        rw [Walk.edges_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp
        · exact List.mem_cons_of_mem _ (hWe x hx)

theorem edgesL_support : ∀ {u v : V} (w : G.Walk u v), edgesL w.support = w.edges
  | _, _, .nil => by simp [edgesL_single]
  | _, _, .cons h p => by
      cases p with
      | nil => simp [edgesL_cons_cons, edgesL_single]
      | cons h' q =>
        rw [Walk.support_cons, Walk.support_cons, edgesL_cons_cons, ← Walk.support_cons h' q,
          edgesL_support (Walk.cons h' q)]
        simp

theorem isPathL_of_path {u v : V} (w : G.Walk u v) (hw : w.IsPath) :
    IsPathL G.Adj w.support u v ∧ links w.support = w.length := by
  refine ⟨⟨?_, ?_, w.isChain_adj_support, hw.support_nodup⟩, by simp [links, Walk.length_support]⟩
  · cases w <;> simp
  · rw [List.getLast?_eq_some_getLast (by simp)]; simp

/-- A path of the line graph from the source to the sink lists links of `G`. -/
theorem split_line {A : List (LV V)} (hA : IsPathL (ladj G s t) A src dst) :
    ∃ es : List (Sym2 V), A = src :: (es.map ed ++ [dst]) ∧ es ≠ [] := by
  obtain ⟨hh, hl, hc, hn⟩ := hA
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hl
  cases ys with
  | nil => simp at hh
  | cons x m =>
    simp at hh
    subst hh
    have hm : ∀ y ∈ m, y ≠ src ∧ y ≠ dst := by
      intro y hy
      simp only [List.cons_append, List.nodup_cons, List.mem_append, List.mem_singleton,
        List.nodup_append] at hn
      refine ⟨fun h => hn.1 (Or.inl (h ▸ hy)), fun h => ?_⟩
      exact hn.2.2.2 y hy dst (by simp) h
    have : ∃ es : List (Sym2 V), m = es.map ed := by
      clear hc hn hl
      induction m with
      | nil => exact ⟨[], rfl⟩
      | cons y m ih =>
        obtain ⟨es, hes⟩ := ih (fun z hz => hm z (List.mem_cons_of_mem _ hz))
        cases y with
        | src => exact absurd rfl (hm _ (by simp)).1
        | dst => exact absurd rfl (hm _ (by simp)).2
        | ed e => exact ⟨e :: es, by simp [hes]⟩
    obtain ⟨es, rfl⟩ := this
    refine ⟨es, by simp, ?_⟩
    rintro rfl
    simp at hc
    exact hc

/-- From a path of the line graph to a path of `G` from `s` to `t` on its links. -/
theorem path_of_line [DecidableEq V] {es : List (Sym2 V)} (hne : es ≠ [])
    (hc : (src :: (es.map ed ++ [dst])).IsChain (ladj G s t)) :
    ∃ q : List V, IsPathL G.Adj q s t ∧ links q ≤ es.length ∧ ∀ e ∈ edgesL q, e ∈ es := by
  obtain ⟨e, es', rfl⟩ : ∃ e es', es = e :: es' := by
    cases es with
    | nil => exact absurd rfl hne
    | cons e es' => exact ⟨e, es', rfl⟩
  rw [List.map_cons, List.cons_append, isChain_cons_cons] at hc
  obtain ⟨⟨-, hse⟩, hc⟩ := hc
  rw [← List.cons_append, isChain_append] at hc
  obtain ⟨hmid, -, hlast⟩ := hc
  have hmid' : (e :: es').IsChain (fun a b => ladj G s t (ed a) (ed b)) := by
    rw [← List.map_cons, isChain_map] at hmid; exact hmid
  have hl : ∀ x ∈ (e :: es').getLast?, x ∈ G.edgeSet ∧ t ∈ x := by
    intro x hx
    have := hlast (ed x) (by rw [← List.map_cons, getLast?_map, Option.mem_def.mp hx]; rfl)
      dst (by simp)
    exact this
  obtain ⟨W, hW, hWe⟩ := walk_of_links G s t es' e s hse hmid' hl
  obtain ⟨hP, hlen⟩ := isPathL_of_path G W.bypass W.bypass_isPath
  refine ⟨W.bypass.support, hP, ?_, ?_⟩
  · rw [hlen]; exact le_trans W.length_bypass_le_length hW
  · intro x hx
    rw [edgesL_support] at hx
    exact hWe x (W.edges_bypass_subset_edges hx)

/-- **Theorem.** Edge-disjoint min-min with bound `ℓ` in `G` is vertex-disjoint min-min with bound
`ℓ + 1` in the line graph with terminals. -/
theorem eMinMin_iff_minMin [DecidableEq V] (hst : s ≠ t) (ℓ : ℕ) :
    EMinMinYes G s t ℓ ↔ MinMinYes (lineG G s t) src dst (ℓ + 1) := by
  constructor
  · rintro ⟨p₁, p₂, h₁, h₂, hD, hl⟩
    obtain ⟨hA, lA, ne₁⟩ := line_path G s t hst h₁
    obtain ⟨hB, -, -⟩ := line_path G s t hst h₂
    refine ⟨_, _, hA, hB, ?_, ?_, by rw [lA]; omega⟩
    · intro h
      obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ ne₁
      have : ed e ∈ src :: ((edgesL p₂).map ed ++ [dst]) := h ▸ (by simp [he])
      simp at this
      exact hD e he this
    · intro x hxA hxB
      cases x with
      | src => exact Or.inl rfl
      | dst => exact Or.inr rfl
      | ed e =>
        simp at hxA hxB
        exact absurd hxB (hD e hxA)
  · rintro ⟨A, B, hA, hB, -, hD, hl⟩
    obtain ⟨esA, rfl, neA⟩ := split_line G s t hA
    obtain ⟨esB, rfl, neB⟩ := split_line G s t hB
    obtain ⟨q₁, hq₁, lq₁, sq₁⟩ := path_of_line G s t neA hA.2.2.1
    obtain ⟨q₂, hq₂, -, sq₂⟩ := path_of_line G s t neB hB.2.2.1
    refine ⟨q₁, q₂, hq₁, hq₂, ?_, ?_⟩
    · intro e h1 h2
      rcases hD (ed e) (by simp [sq₁ e h1]) (by simp [sq₂ e h2]) with h | h <;> cases h
    · have : links (src :: (esA.map ed ++ [dst])) = esA.length + 1 := by simp [links]
      rw [this] at hl
      omega

theorem card_lineV_le [Fintype V] [DecidableEq V] :
    Fintype.card (LV V) ≤ Fintype.card V ^ 2 + 2 := by
  rw [LV.card]
  have : Fintype.card (Sym2 V) ≤ Fintype.card (V × V) :=
    Fintype.card_le_of_surjective _ Sym2.mk_surjective
  simp [Fintype.card_prod] at this
  nlinarith

/-! ## Transfer of hardness -/

/-- Edge-disjoint min-min on `MMInst`: given `s ≠ t` and `ℓ`, are there two paths from `s` to `t`
without a common link, the shorter one with at most `ℓ` links? This problem on undirected graphs
is proved NP-complete in L. Guo, H. Shen, On finding min-min disjoint paths, Algorithmica 66(3),
2013. -/
def MMInst.eyes (I : MMInst) : Prop := EMinMinYes I.G I.s I.t I.ℓ

open Classical in
/-- The line graph reduction as a map of instances. -/
noncomputable def toLine (I : MMInst) : MMInst where
  V := LV I.V
  G := lineG I.G I.s I.t
  s := src
  t := dst
  hst := by intro h; cases h
  ℓ := I.ℓ + 1

/-- **The line graph as a map of instances.** -/
theorem reduction_line :
    (∀ I, MMInst.eyes I ↔ MMInst.yes (toLine I)) ∧
    ∀ I, MMInst.size (toLine I) ≤ MMInst.size I ^ 2 + 2 := by
  classical
  refine ⟨fun I => eMinMin_iff_minMin I.G I.s I.t I.hst I.ℓ, fun I => ?_⟩
  show Fintype.card (LV I.V) ≤ Fintype.card I.V ^ 2 + 2
  convert card_lineV_le (V := I.V)

theorem size_compose {C : ℚ} (I : MMInst) (m : ℕ) (h : m ≤ ⌈1 + (C + 2) ^ 2⌉₊ * (MMInst.size (toLine I) + 1) ^ 3) :
    m ≤ ⌈1 + (C + 2) ^ 2⌉₊ * (MMInst.size I ^ 2 + 3) ^ 3 :=
  h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := reduction_line.2 I; omega) 3))

/-- **Theorem 1 (reduction from edge-disjoint min-min, one terminal).** -/
theorem reduction_minProd_e {C : ℚ} (hC : 0 ≤ C) :
    (∀ I, MMInst.eyes I ↔ MPInst.yes C (toMP C (toLine I))) ∧
    ∀ I, MPInst.size (toMP C (toLine I)) ≤ ⌈1 + (C + 2) ^ 2⌉₊ * (MMInst.size I ^ 2 + 3) ^ 3 :=
  ⟨fun I => (reduction_line.1 I).trans ((reduction_minProd hC).1 _),
    fun I => size_compose I _ ((reduction_minProd hC).2 _)⟩

/-- **Theorem 1 (reduction from edge-disjoint min-min, two terminals).** -/
theorem reduction_minProd₂_e {C : ℚ} (hC : 0 ≤ C) :
    (∀ I, MMInst.eyes I ↔ MP2Inst.yes C (toMP2 C (toLine I))) ∧
    ∀ I, MP2Inst.size (toMP2 C (toLine I)) ≤ ⌈1 + (C + 2) ^ 2⌉₊ * (MMInst.size I ^ 2 + 3) ^ 3 :=
  ⟨fun I => (reduction_line.1 I).trans ((reduction_minProd₂ hC).1 _),
    fun I => size_compose I _ ((reduction_minProd₂ hC).2 _)⟩

/-- **Corollary 2 (reduction from edge-disjoint min-min).** -/
theorem reduction_route_e {q B : ℚ} (hq : 0 < q) (hB : 0 < B) :
    (∀ I, MMInst.eyes I ↔ MP2Inst.routeYes q B (toRoute q B (toLine I))) ∧
    ∀ I, MP2Inst.size (toRoute q B (toLine I)) ≤
      ⌈1 + (1 / (B * q) + 2) ^ 2⌉₊ * (MMInst.size I ^ 2 + 3) ^ 3 :=
  ⟨fun I => (reduction_line.1 I).trans ((reduction_route hq hB).1 _),
    fun I => size_compose I _ ((reduction_route hq hB).2 _)⟩

end RiskRouting
