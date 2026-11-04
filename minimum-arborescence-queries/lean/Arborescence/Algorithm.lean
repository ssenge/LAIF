import Arborescence.Counting

/-!
# The algorithm of sections 2 and 3, as a Lean function

`solve o g vs` runs the path-growing form of the classical contraction algorithm with the lists of section 3, for an arbitrary
oracle `o` for TopK, and returns a parent function or `none`, together with the list of all builds `(G, K)`.

Deviations from the wording of the README, none of which changes what is computed:

* "Discard the leading entries with source in `C`" is `headOut C L`, the first entry with source outside `C`.
  The entries before it have their source in `C` forever, so keeping them changes nothing. A list is not empty in
  the sense of `Cheapest` when `headOut` finds an entry.
* The loop `for v0 in V` is a list `free` of the containers not yet touched, all singletons, in the order of `vs`,
  and a state `cur`, the current `a`.
* The forest of contractions and its expansion are stored as closures: `Node.exp T v x` is the parent of `x ∈ T`
  in the expansion of `T` when `T` is entered at `v`. This is the recursion of "Expansion, no queries" of the README,
  evaluated lazily.
* `Group.builtIn` and `Group.y0` (the container and the offsets at the last build) are stored so that the invariants
  can name them. `Group.y0` is the same information as the values of `f` returned by TopK. The weights of list entries
  are read as `g.w`, which is not charged. An entry is in the output of TopK, so its weight is known.
* The `Node.total` is the sum of the dual values below a node. It is not needed by the algorithm.

Termination is by fuel: `measure` drops at every step, so `measure + 1` is enough, see `solve_reach`.
-/

set_option linter.unusedSectionVars false

open Finset

namespace Arborescence

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A TopK oracle, with the source as the type: items, `f`, budget, and the output as a list. -/
abbrev Oracle (V : Type*) := Finset (V × V) → (V × V → WithTop ℤ) → ℕ → List (V × V)

/-- The oracle satisfies the specification of TopK. -/
def Oracle.Correct (o : Oracle V) : Prop :=
  ∀ items f K, IsTopK items f Prod.fst K (o items f K).toFinset

/-- The minimum that the accounting needs of an oracle: outputs consist of items of distinct types. -/
def Oracle.Structural (o : Oracle V) : Prop :=
  ∀ items f K, (o items f K).toFinset ⊆ items ∧
    Set.InjOn Prod.fst (↑(o items f K).toFinset : Set (V × V))

theorem Oracle.Correct.structural {o : Oracle V} (h : o.Correct) : o.Structural :=
  fun items f K => ⟨(h items f K).subset, (h items f K).inj⟩

/-- The reduced cost of an edge. -/
def redCost (g : Graph V) (y : V → ℤ) (e : V × V) : ℤ := g.w e.1 e.2 - y e.2

/-- A group of a container, with its list. -/
structure Group (V : Type*) where
  verts : Finset V
  K : ℕ
  entries : List (V × V)
  complete : Bool
  builtIn : Finset V
  y0 : V → ℤ

/-- Is `f` finite on `e`, in a call for the container `C`? -/
def finiteAt (g : Graph V) (C : Finset V) (e : V × V) : Bool := g.adj e.1 e.2 && decide (e.1 ∉ C)

/-- **Build(G, K)** in the container `C` with offsets `y`. -/
def build (o : Oracle V) (g : Graph V) (C : Finset V) (y : V → ℤ) (verts : Finset V) (K : ℕ) : Group V :=
  let I := o (inEdges g verts) (buildF g C y) K
  { verts := verts
    K := K
    entries := (I.filter (finiteAt g C)).insertionSort fun a b => redCost g y a ≤ redCost g y b
    complete := decide (I.toFinset.card < K) || I.any fun e => !finiteAt g C e
    builtIn := C
    y0 := y }

/-- A node of the forest that is a current container. -/
structure Node (V : Type*) where
  verts : Finset V
  groups : List (Group V)
  exp : V → V → V
  total : ℤ
  inE : V × V

/-- The parent of `x ∈ T` when `T` is entered by its selected edge `in(T)`. -/
def Node.assign (T : Node V) (x : V) : V := if x = T.inE.2 then T.inE.1 else T.exp T.inE.2 x

/-- The initial node of a vertex, with `Build({v}, 1)`. The value of `inE` is a placeholder until selection. -/
def Node.singleton (o : Oracle V) (g : Graph V) (v : V) : Node V :=
  { verts := {v}
    groups := [build o g {v} (fun _ => 0) {v} 1]
    exp := fun _ x => x
    total := 0
    inE := (v, v) }

/-- The expansion of a contracted node: the parts of the cycle give parents to their vertices. -/
def contractExp (parts : List (Node V)) (v x : V) : V :=
  match parts.find? fun T => decide (x ∈ T.verts) with
  | none => x
  | some T => if v ∈ T.verts then T.exp v x else T.assign x

/-- The first element satisfying `p`, with what comes before and after it. -/
def split {α : Type*} (p : α → Bool) : List α → Option (List α × α × List α)
  | [] => none
  | a :: l => if p a then some ([], a, l) else (split p l).map fun r => (a :: r.1, r.2)

/-- The union of the vertex sets of nodes. -/
def unionV : List (Node V) → Finset V
  | [] => ∅
  | T :: l => T.verts ∪ unionV l

/-- A largest part and the others. -/
def pick (a : Node V) : List (Node V) → Node V × List (Node V)
  | [] => (a, [])
  | b :: l =>
    let r := pick b l
    if r.1.verts.card ≤ a.verts.card then (a, r.1 :: r.2) else (r.1, a :: r.2)

/-- The absorption loop of `Contract`, with fuel for the number of groups. -/
def absorbF : ℕ → Finset V → List (Group V) → Finset V × List (Group V)
  | 0, H, gs => (H, gs)
  | k + 1, H, gs =>
    match split (fun G => decide (lg G.verts.card = lg H.card)) gs with
    | none => (H, gs)
    | some (g1, G, g2) => absorbF k (H ∪ G.verts) (g1 ++ g2)

/-- The absorption loop. -/
def absorb (H : Finset V) (gs : List (Group V)) : Finset V × List (Group V) := absorbF gs.length H gs

/-- The new group `H` of a contraction of `a :: rest`. -/
def contractH (a : Node V) (rest : List (Node V)) : Finset V :=
  (absorb (unionV (pick a rest).2) (pick a rest).1.groups).1

/-- **Contract**, with the build of `H`. The value of `inE` is a placeholder until selection. -/
def contractNode (o : Oracle V) (g : Graph V) (y : V → ℤ) (a : Node V) (rest : List (Node V)) : Node V :=
  let r := pick a rest
  let M := unionV r.2
  let A := absorb M r.1.groups
  let X := r.1.verts ∪ M
  { verts := X
    groups := build o g X y A.1 A.1.card :: A.2
    exp := contractExp (a :: rest)
    total := ((a :: rest).map Node.total).sum
    inE := a.inE }

/-- What is attached so far: the vertices, the parent function on them, the sum of the dual values, the nodes. -/
structure Att (V : Type*) where
  verts : Finset V
  par : V → V
  total : ℤ
  nodes : List (Node V)

/-- Attach a selected node. -/
def Att.add (A : Att V) (T : Node V) : Att V :=
  { verts := A.verts ∪ T.verts
    par := fun x => if x ∈ T.verts then T.assign x else A.par x
    total := A.total + T.total
    nodes := T :: A.nodes }

/-- The state of the algorithm. `path` has the newest node first. -/
structure St (V : Type*) where
  y : V → ℤ
  duals : List (Finset V × ℤ)
  A : Att V
  free : List (Node V)
  path : List (Node V)
  cur : Option (Node V)
  builds : List (Finset V × ℕ)

/-- The initial state, for a list of the non-root vertices. -/
def initSt (o : Oracle V) (g : Graph V) (us : List V) : St V :=
  { y := fun _ => 0
    duals := []
    A := ⟨{g.root}, id, 0, []⟩
    free := us.map (Node.singleton o g)
    path := []
    cur := none
    builds := us.map fun v => (({v} : Finset V), 1) }

/-- The rebuild of `Cheapest`: if the list has no entry with source outside `C`, and is not complete, rebuild
with double the budget. -/
def refresh (o : Oracle V) (g : Graph V) (C : Finset V) (y : V → ℤ) (G : Group V) :
    Group V × List (Finset V × ℕ) :=
  match headOut C G.entries with
  | some _ => (G, [])
  | none => if G.complete = true then (G, []) else (build o g C y G.verts (2 * G.K), [(G.verts, 2 * G.K)])

/-- The rebuilds of `Cheapest`, over all groups, with the builds newest first. -/
def refreshAll (o : Oracle V) (g : Graph V) (C : Finset V) (y : V → ℤ) :
    List (Group V) → List (Group V) × List (Finset V × ℕ)
  | [] => ([], [])
  | G :: gs =>
    let r := refresh o g C y G
    let rs := refreshAll o g C y gs
    (r.1 :: rs.1, rs.2 ++ r.2)

/-- An element of smallest value. -/
def minBy {α : Type*} (F : α → ℤ) : List α → Option α
  | [] => none
  | a :: l =>
    match minBy F l with
    | none => some a
    | some b => if F b < F a then some b else some a

/-- What to do with the selected node `a`, by the container of the source of `in(a)`: attach, contract, or push.
The last branch is unreachable by `SInv`. -/
def route (o : Oracle V) (g : Graph V) (st : St V) (a : Node V) : St V :=
  let u := a.inE.1
  if u ∈ st.A.verts then
    { st with A := (a :: st.path).foldl Att.add st.A, path := [], cur := none }
  else
    match split (fun T => decide (u ∈ T.verts)) st.path with
    | some (seg, b, pre) =>
      { st with
        path := pre
        cur := some (contractNode o g st.y a (seg ++ [b]))
        builds := (contractH a (seg ++ [b]), (contractH a (seg ++ [b])).card) :: st.builds }
    | none =>
      match split (fun T => decide (u ∈ T.verts)) st.free with
      | some (f1, b, f2) => { st with free := f1 ++ f2, path := a :: st.path, cur := some b }
      | none => { st with path := [], cur := none }

/-- The outcome of a step. -/
inductive Out (V : Type*)
  | running (st : St V)
  | done (st : St V)
  | noArb (st : St V)
  | outOfFuel (st : St V)

/-- The candidates of `Cheapest` over refreshed groups: the heads. -/
def heads (C : Finset V) (gs : List (Group V)) : List (V × V) :=
  gs.filterMap fun G => headOut C G.entries

/-- The state after the rebuilds of `Cheapest`, on the node `a`. -/
def refreshed (o : Oracle V) (g : Graph V) (st : St V) (a : Node V) : St V :=
  let r := refreshAll o g a.verts st.y a.groups
  { st with builds := r.2 ++ st.builds, cur := some { a with groups := r.1 } }

/-- The offsets after selecting `a` with value `c`. -/
def addOn (y : V → ℤ) (X : Finset V) (c : ℤ) : V → ℤ := fun x => if x ∈ X then y x + c else y x

/-- The selection on `a`, whose groups are already refreshed: the edge `e` with value `c`. Then the state is ready
for `route`, with no current node. -/
def selected (st : St V) (a : Node V) (e : V × V) (c : ℤ) : St V × Node V :=
  ({ st with y := addOn st.y a.verts c, duals := (a.verts, c) :: st.duals, cur := none },
    { a with total := a.total + c, inE := e })

/-- One step of the outer and inner loop. -/
def step (o : Oracle V) (g : Graph V) (st : St V) : Out V :=
  match st.cur with
  | none =>
    match st.free with
    | [] => .done st
    | a :: rest => .running { st with free := rest, cur := some a }
  | some a =>
    let st0 := refreshed o g st a
    let gs := (refreshAll o g a.verts st.y a.groups).1
    match minBy (redCost g st.y) (heads a.verts gs) with
    | none => .noArb st0
    | some e =>
      let r := selected st0 { a with groups := gs } e (redCost g st.y e)
      .running (route o g r.1 r.2)

/-- The loop, with fuel. -/
def runFuel (o : Oracle V) (g : Graph V) : ℕ → St V → Out V
  | 0, st => .outOfFuel st
  | k + 1, st =>
    match step o g st with
    | .running st' => runFuel o g k st'
    | r => r

/-- The measure that drops at every step. -/
def measure (st : St V) : ℕ := 2 * st.free.length + st.path.length + st.cur.toList.length

/-- **The algorithm.** `vs` lists all vertices. The result is a parent function or `none`, and the builds. -/
def solve (o : Oracle V) (g : Graph V) (vs : List V) : Option (V → V) × List (Finset V × ℕ) :=
  let us := vs.filter fun v => decide (v ≠ g.root)
  match runFuel o g (2 * us.length + 1) (initSt o g us) with
  | .done st => (some st.A.par, st.builds)
  | .noArb st => (none, st.builds)
  | .running st => (none, st.builds)
  | .outOfFuel st => (none, st.builds)

/-! ## Pure lemmas -/

theorem split_some {α : Type*} {p : α → Bool} :
    ∀ {l : List α} {r : List α × α × List α}, split p l = some r →
      l = r.1 ++ r.2.1 :: r.2.2 ∧ p r.2.1 = true ∧ ∀ x ∈ r.1, p x = false
  | [], r, h => by simp [split] at h
  | a :: l, r, h => by
    simp only [split] at h
    split_ifs at h with hp
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨rfl, hp, by simp⟩
    · obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨h1, h2, h3⟩ := split_some hr'
      refine ⟨by simp only [List.cons_append]; exact congrArg _ h1, h2, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simpa using hp
      · exact h3 x hx

theorem split_none {α : Type*} {p : α → Bool} :
    ∀ {l : List α}, split p l = none → ∀ x ∈ l, p x = false
  | [], _, x, hx => by simp at hx
  | a :: l, h, x, hx => by
    simp only [split] at h
    split_ifs at h with hp
    rcases List.mem_cons.mp hx with rfl | hx
    · simpa using hp
    · exact split_none (Option.map_eq_none_iff.mp h) x hx

theorem mem_unionV {l : List (Node V)} {x : V} : x ∈ unionV l ↔ ∃ T ∈ l, x ∈ T.verts := by
  induction l with
  | nil => simp [unionV]
  | cons a l ih => simp [unionV, ih]

theorem unionV_append {l₁ l₂ : List (Node V)} : unionV (l₁ ++ l₂) = unionV l₁ ∪ unionV l₂ := by
  ext x
  simp [mem_unionV]
  aesop

theorem pick_perm (a : Node V) (l : List (Node V)) :
    List.Perm ((pick a l).1 :: (pick a l).2) (a :: l) := by
  induction l generalizing a with
  | nil => simp [pick]
  | cons b l ih =>
    simp only [pick]
    have := ih b
    split_ifs with h
    · exact this.cons _
    · exact (List.Perm.swap _ _ _).trans (this.cons _)

theorem pick_le (a : Node V) (l : List (Node V)) :
    ∀ T ∈ (pick a l).2, T.verts.card ≤ (pick a l).1.verts.card := by
  induction l generalizing a with
  | nil => simp [pick]
  | cons b l ih =>
    simp only [pick]
    have := ih b
    split_ifs with h
    · intro T hT
      rcases List.mem_cons.mp hT with rfl | hT
      · exact h
      · exact (this T hT).trans h
    · intro T hT
      rcases List.mem_cons.mp hT with rfl | hT
      · show T.verts.card ≤ (pick b l).1.verts.card
        omega
      · exact this T hT

theorem minBy_none {α : Type*} {F : α → ℤ} : ∀ {l : List α}, minBy F l = none → l = []
  | [], _ => rfl
  | a :: l, h => by
    simp only [minBy] at h
    cases hm : minBy F l with
    | none => simp [hm] at h
    | some b =>
      simp only [hm] at h
      split_ifs at h

theorem minBy_some {α : Type*} {F : α → ℤ} :
    ∀ {l : List α} {m : α}, minBy F l = some m → m ∈ l ∧ ∀ x ∈ l, F m ≤ F x
  | [], _, h => by simp [minBy] at h
  | a :: l, m, h => by
    simp only [minBy] at h
    cases hm : minBy F l with
    | none =>
      simp only [hm, Option.some.injEq] at h
      subst h
      rw [minBy_none hm]
      simp
    | some b =>
      simp only [hm] at h
      obtain ⟨hb, hb'⟩ := minBy_some hm
      split_ifs at h with hlt
      · simp only [Option.some.injEq] at h
        subst h
        refine ⟨List.mem_cons_of_mem _ hb, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · exact hb' x hx
      · simp only [Option.some.injEq] at h
        subst h
        refine ⟨List.mem_cons_self .., fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact le_rfl
        · have := hb' x hx
          omega

/-- The two ways for a step to keep running. -/
theorem step_running {o : Oracle V} {g : Graph V} {st st' : St V} (h : step o g st = .running st') :
    (st.cur = none ∧ ∃ a rest, st.free = a :: rest ∧ st' = { st with free := rest, cur := some a }) ∨
    ∃ a e, st.cur = some a ∧
      minBy (redCost g st.y) (heads a.verts (refreshAll o g a.verts st.y a.groups).1) = some e ∧
      st' = route o g (selected (refreshed o g st a) { a with groups := (refreshAll o g a.verts st.y a.groups).1 } e
          (redCost g st.y e)).1
        (selected (refreshed o g st a) { a with groups := (refreshAll o g a.verts st.y a.groups).1 } e
          (redCost g st.y e)).2 := by
  simp only [step] at h
  cases hc : st.cur with
  | none =>
    rw [hc] at h
    cases hf : st.free with
    | nil =>
      rw [hf] at h
      simp at h
    | cons a rest =>
      rw [hf] at h
      simp only [Out.running.injEq] at h
      exact Or.inl ⟨rfl, a, rest, rfl, h.symm⟩
  | some a =>
    rw [hc] at h
    simp only at h
    cases hm : minBy (redCost g st.y) (heads a.verts (refreshAll o g a.verts st.y a.groups).1) with
    | none =>
      rw [hm] at h
      simp at h
    | some e =>
      rw [hm] at h
      simp only [Out.running.injEq] at h
      exact Or.inr ⟨a, e, rfl, hm, h.symm⟩

theorem step_done {o : Oracle V} {g : Graph V} {st st' : St V} (h : step o g st = .done st') :
    st' = st ∧ st.cur = none ∧ st.free = [] := by
  simp only [step] at h
  cases hc : st.cur with
  | none =>
    rw [hc] at h
    cases hf : st.free with
    | nil =>
      rw [hf] at h
      simp only [Out.done.injEq] at h
      exact ⟨h.symm, rfl, rfl⟩
    | cons a rest =>
      rw [hf] at h
      simp at h
  | some a =>
    rw [hc] at h
    simp only at h
    cases hm : minBy (redCost g st.y) (heads a.verts (refreshAll o g a.verts st.y a.groups).1) with
    | none =>
      rw [hm] at h
      simp at h
    | some e =>
      rw [hm] at h
      simp at h

theorem step_noArb {o : Oracle V} {g : Graph V} {st st' : St V} (h : step o g st = .noArb st') :
    ∃ a, st.cur = some a ∧ st' = refreshed o g st a ∧
      minBy (redCost g st.y) (heads a.verts (refreshAll o g a.verts st.y a.groups).1) = none := by
  simp only [step] at h
  cases hc : st.cur with
  | none =>
    rw [hc] at h
    cases hf : st.free with
    | nil =>
      rw [hf] at h
      simp at h
    | cons a rest =>
      rw [hf] at h
      simp at h
  | some a =>
    rw [hc] at h
    simp only at h
    cases hm : minBy (redCost g st.y) (heads a.verts (refreshAll o g a.verts st.y a.groups).1) with
    | none =>
      rw [hm] at h
      simp only [Out.noArb.injEq] at h
      exact ⟨a, rfl, h.symm, hm⟩
    | some e =>
      rw [hm] at h
      simp at h

theorem foldl_add_path (l : List (Node V)) (A : Att V) :
    (l.foldl Att.add A).verts = A.verts ∪ unionV l := by
  induction l generalizing A with
  | nil => simp [unionV]
  | cons a l ih =>
    simp only [List.foldl_cons, ih, unionV, Att.add]
    rw [Finset.union_assoc]

theorem route_measure (o : Oracle V) (g : Graph V) (st : St V) (a : Node V) :
    measure (route o g st a) ≤ 2 * st.free.length + st.path.length := by
  unfold route
  simp only
  split_ifs with hu
  · simp [measure]
  · cases hs : split (fun T => decide (a.inE.1 ∈ T.verts)) st.path with
    | some r =>
      obtain ⟨r1, b, r2⟩ := r
      have h1 := (split_some hs).1
      simp only at h1 ⊢
      have h2 : st.path.length = r1.length + 1 + r2.length := by
        rw [h1]
        simp
        omega
      simp [measure]
      omega
    | none =>
      simp only
      cases hf : split (fun T => decide (a.inE.1 ∈ T.verts)) st.free with
      | some r =>
        obtain ⟨r1, b, r2⟩ := r
        have h1 := (split_some hf).1
        simp only at h1 ⊢
        have h2 : st.free.length = r1.length + 1 + r2.length := by
          rw [h1]
          simp
          omega
        simp [measure]
        omega
      | none => simp [measure]

theorem step_measure {o : Oracle V} {g : Graph V} {st st' : St V} (h : step o g st = .running st') :
    measure st' < measure st := by
  rcases step_running h with ⟨hc, a, rest, hf, rfl⟩ | ⟨a, e, hc, _, rfl⟩
  · simp [measure, hc, hf]
    omega
  · have := route_measure o g (selected (refreshed o g st a)
      { a with groups := (refreshAll o g a.verts st.y a.groups).1 } e (redCost g st.y e)).1
      (selected (refreshed o g st a)
      { a with groups := (refreshAll o g a.verts st.y a.groups).1 } e (redCost g st.y e)).2
    refine lt_of_le_of_lt this ?_
    simp [measure, hc, selected, refreshed]

/-- The states reachable from `st` by running steps. -/
inductive Reach (o : Oracle V) (g : Graph V) (st : St V) : St V → Prop
  | refl : Reach o g st st
  | step {s s' : St V} : Reach o g st s → Arborescence.step o g s = .running s' → Reach o g st s'

theorem runFuel_reach {o : Oracle V} {g : Graph V} :
    ∀ (k : ℕ) (st : St V), measure st < k → ∃ s, Reach o g st s ∧
      ((∃ s', step o g s = .done s' ∧ runFuel o g k st = .done s') ∨
       (∃ s', step o g s = .noArb s' ∧ runFuel o g k st = .noArb s'))
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, st, h => by
    cases hs : step o g st with
    | running st' =>
      have hm := step_measure hs
      obtain ⟨s, hr, hd⟩ := runFuel_reach k st' (by omega)
      have hrun : runFuel o g (k + 1) st = runFuel o g k st' := by
        simp [runFuel, hs]
      refine ⟨s, ?_, ?_⟩
      · clear hd
        induction hr with
        | refl => exact Reach.step Reach.refl hs
        | step _ hb ih => exact Reach.step ih hb
      · rw [hrun]
        exact hd
    | done s' =>
      exact ⟨st, Reach.refl, Or.inl ⟨s', hs, by simp [runFuel, hs]⟩⟩
    | noArb s' =>
      exact ⟨st, Reach.refl, Or.inr ⟨s', hs, by simp [runFuel, hs]⟩⟩
    | outOfFuel s' =>
      simp [step] at hs
      cases hc : st.cur with
      | none =>
        rw [hc] at hs
        cases hf : st.free with
        | nil =>
          rw [hf] at hs
          simp at hs
        | cons a rest =>
          rw [hf] at hs
          simp at hs
      | some a =>
        rw [hc] at hs
        simp only at hs
        cases hm : minBy (redCost g st.y) (heads a.verts (refreshAll o g a.verts st.y a.groups).1) with
        | none =>
          rw [hm] at hs
          simp at hs
        | some e =>
          rw [hm] at hs
          simp at hs

theorem measure_init (o : Oracle V) (g : Graph V) (us : List V) :
    measure (initSt o g us) < 2 * us.length + 1 := by
  simp [measure, initSt]

/-- `solve` ends in a `done` or `noArb` state that a step reaches: fuel is not an issue. -/
theorem solve_reach (o : Oracle V) (g : Graph V) (vs : List V) :
    let us := vs.filter fun v => decide (v ≠ g.root)
    ∃ s, Reach o g (initSt o g us) s ∧
      ((∃ s', step o g s = .done s' ∧ solve o g vs = (some s'.A.par, s'.builds)) ∨
       (∃ s', step o g s = .noArb s' ∧ solve o g vs = (none, s'.builds))) := by
  intro us
  obtain ⟨s, hr, hd⟩ := runFuel_reach (o := o) (g := g) _ _ (measure_init o g us)
  refine ⟨s, hr, ?_⟩
  rcases hd with ⟨s', h1, h2⟩ | ⟨s', h1, h2⟩
  · exact Or.inl ⟨s', h1, by simp only [solve, us] at h2 ⊢; rw [h2]⟩
  · exact Or.inr ⟨s', h1, by simp only [solve, us] at h2 ⊢; rw [h2]⟩

end Arborescence
