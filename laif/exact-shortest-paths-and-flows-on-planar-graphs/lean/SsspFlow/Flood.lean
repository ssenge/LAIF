import SsspFlow.DualFlow

/-!
# A unit of flow from two floods

* `floodAlg`: a flood along allowed edges from a set of seeds. A node remembers the neighbour that
  reached it first (`run_flood`).
* `floodPar`, `floodTok`: a flood from `s` gives every node a parent, and a second flood from `t` along
  the parents marks the path from `t` to `s`.
* `unitFlow_of_floods`: after `D` rounds each, the nodes hold a unit of flow from `s` to `t` on the edges
  at them, along this path.
-/

set_option autoImplicit false

open Cslib.Congest

namespace SsspFlow.Congest

open Classical in
/-- A flood. The input is whether the node is a seed and to which neighbours it passes the flood on. The
state holds these neighbours, and it is `some none` for a seed and `some (some p)` for a node reached
from `p`. -/
noncomputable def floodAlg (V : Type) :
    Algorithm V (Bool × (V → Bool)) ((V → Bool) × Option (Option V)) 1 where
  init _ i := (i.2, if i.1 then some none else none)
  send _ s w := fun _ => s.2.isSome && s.1 w
  step _ s m :=
    if s.2.isSome then s
    else if h : ∃ u, m u = some (fun _ => true) then (s.1, some (some h.choose)) else s
  out _ _ := true

section Lev

variable {V : Type} (A : V → V → Prop) (seed : V → Prop)

/-- The nodes reached after `t` rounds. -/
def Lev : ℕ → V → Prop
  | 0, v => seed v
  | t + 1, v => Lev t v ∨ ∃ u, Lev t u ∧ A u v

variable {A seed}

theorem Lev.mono {i j : ℕ} (hij : i ≤ j) {v : V} (h : Lev A seed i v) : Lev A seed j v := by
  induction hij with
  | refl => exact h
  | step _ ih => exact Or.inl ih

end Lev

section Run

variable {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj] (inp : V → Bool × (V → Bool))

/-- The edges along which the flood passes. -/
def floodA (u v : V) : Prop := G.Adj u v ∧ (inp u).2 v = true

/-- **The flood.** -/
theorem run_flood (t : ℕ) (v : V) :
    ((floodAlg V).run G inp t v).1 = (inp v).2 ∧
    (((floodAlg V).run G inp t v).2.isSome = true ↔ Lev (floodA G inp) (fun v => (inp v).1 = true) t v) ∧
    (((floodAlg V).run G inp t v).2 = some none ↔ (inp v).1 = true) ∧
    ∀ p, ((floodAlg V).run G inp t v).2 = some (some p) → floodA G inp p v ∧
      ∃ t' < t, Lev (floodA G inp) (fun v => (inp v).1 = true) t' p ∧
        ¬ Lev (floodA G inp) (fun v => (inp v).1 = true) t' v := by
  induction t generalizing v with
  | zero =>
    show ((inp v).2, if (inp v).1 then some none else none).1 = _ ∧
      (((inp v).2, if (inp v).1 then some none else none).2.isSome = true ↔ _) ∧
      (((inp v).2, if (inp v).1 then some none else none).2 = some none ↔ _) ∧ ∀ p,
      ((inp v).2, if (inp v).1 then some none else none).2 = some (some p) → _
    refine ⟨rfl, ?_, ?_, ?_⟩
    · by_cases h : (inp v).1 = true <;> simp [h, Lev]
    · by_cases h : (inp v).1 = true <;> simp [h]
    · by_cases h : (inp v).1 = true <;> simp [h]
  | succ t ih =>
    have hm : ∀ u, (if G.Adj u v then some ((floodAlg V).send u ((floodAlg V).run G inp t u) v)
        else none) = some (fun _ => true) ↔
        Lev (floodA G inp) (fun v => (inp v).1 = true) t u ∧ floodA G inp u v := by
      intro u
      have h1 := ih u
      by_cases hadj : G.Adj u v
      · rw [ite_eq_left hadj, Option.some_inj]
        constructor
        · intro h
          have h2 : (((floodAlg V).run G inp t u).2.isSome && ((floodAlg V).run G inp t u).1 v) = true :=
            congrFun h 0
          rw [Bool.and_eq_true, h1.1] at h2
          exact ⟨h1.2.1.1 h2.1, hadj, h2.2⟩
        · rintro ⟨h2, -, h3⟩
          funext _
          show (((floodAlg V).run G inp t u).2.isSome && ((floodAlg V).run G inp t u).1 v) = true
          rw [Bool.and_eq_true, h1.1]
          exact ⟨h1.2.1.2 h2, h3⟩
      · rw [ite_eq_right hadj]
        simp [floodA, hadj]
    have hrun : (floodAlg V).run G inp (t + 1) v = (floodAlg V).step v ((floodAlg V).run G inp t v)
        (fun u => if G.Adj u v then some ((floodAlg V).send u ((floodAlg V).run G inp t u) v)
          else none) := rfl
    obtain ⟨i1, i2, i3, i4⟩ := ih v
    have hold : ∀ p, ((floodAlg V).run G inp t v).2 = some (some p) → floodA G inp p v ∧
        ∃ t' < t + 1, Lev (floodA G inp) (fun v => (inp v).1 = true) t' p ∧
          ¬ Lev (floodA G inp) (fun v => (inp v).1 = true) t' v := fun p hp => by
      obtain ⟨h1, t', h2, h3⟩ := i4 p hp
      exact ⟨h1, t', by omega, h3⟩
    rw [hrun]
    by_cases hs : ((floodAlg V).run G inp t v).2.isSome = true
    · have : (floodAlg V).step v ((floodAlg V).run G inp t v) (fun u => if G.Adj u v then
          some ((floodAlg V).send u ((floodAlg V).run G inp t u) v) else none) =
          (floodAlg V).run G inp t v := by
        show (if _ then _ else _) = _
        rw [ite_eq_left hs]
      rw [this]
      exact ⟨i1, ⟨fun _ => Or.inl (i2.1 hs), fun _ => hs⟩, i3, hold⟩
    · have hnot : ¬ Lev (floodA G inp) (fun v => (inp v).1 = true) t v := fun h => hs (i2.2 h)
      have hseed : (inp v).1 ≠ true := fun h => by
        have := i3.2 h
        simp [this] at hs
      by_cases hex : ∃ u, (if G.Adj u v then
          some ((floodAlg V).send u ((floodAlg V).run G inp t u) v) else none) = some (fun _ => true)
      · have : (floodAlg V).step v ((floodAlg V).run G inp t v) (fun u => if G.Adj u v then
            some ((floodAlg V).send u ((floodAlg V).run G inp t u) v) else none) =
            (((floodAlg V).run G inp t v).1, some (some hex.choose)) := by
          show (if _ then _ else _) = _
          rw [ite_eq_right hs]
          exact dite_eq_left hex
        rw [this]
        obtain ⟨h1, h2⟩ := (hm _).1 hex.choose_spec
        refine ⟨i1, ⟨fun _ => Or.inr ⟨_, h1, h2⟩, fun _ => rfl⟩, ?_, ?_⟩
        · simp [hseed]
        · intro p hp
          obtain rfl : hex.choose = p := by simpa using hp
          exact ⟨h2, t, by omega, h1, hnot⟩
      · have : (floodAlg V).step v ((floodAlg V).run G inp t v) (fun u => if G.Adj u v then
            some ((floodAlg V).send u ((floodAlg V).run G inp t u) v) else none) =
            (floodAlg V).run G inp t v := by
          show (if _ then _ else _) = _
          rw [ite_eq_right hs]
          exact dite_eq_right hex
        rw [this]
        refine ⟨i1, ⟨fun h => absurd h hs, ?_⟩, i3, hold⟩
        rintro (h | ⟨u, h1, h2⟩)
        · exact absurd h hnot
        · exact absurd ⟨u, (hm u).2 ⟨h1, h2⟩⟩ hex

end Run

section Token

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The unit of flow on the edge to `u`, from the parent of a node and its state in the second flood. -/
def unitOf (par : Option V) (tok : Option (Option V)) (u : V) : ℤ :=
  (if tok.join = some u then 1 else 0) - (if tok.isSome = true ∧ par = some u then 1 else 0)

variable (N : Net V) (par : V → Option V) (rk : V → ℕ) {D : ℕ} {s t : V}

/-- The input of the second flood. -/
def tokenIn (par : V → Option V) (t v : V) : Bool × (V → Bool) :=
  (decide (v = t), fun w => decide (par v = some w))

/-- The state of the second flood. -/
noncomputable def tokenSt (par : V → Option V) (t : V) (D : ℕ) (v : V) : Option (Option V) :=
  ((floodAlg V).run N.G (tokenIn par t) D v).2

private abbrev TLev (par : V → Option V) (t : V) : ℕ → V → Prop :=
  Lev (floodA N.G (tokenIn par t)) (fun v => (tokenIn par t v).1 = true)

omit [Fintype V] [DecidableEq V] in
private theorem compare_step {par : V → Option V} {a b y : V}
    (h : Relation.ReflTransGen (fun a b => par a = some b) a y ∨
      Relation.ReflTransGen (fun a b => par a = some b) y a) (hab : par a = some b) :
    Relation.ReflTransGen (fun a b => par a = some b) b y ∨
      Relation.ReflTransGen (fun a b => par a = some b) y b := by
  rcases h with h | h
  · rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, hc, hcy⟩
    · exact Or.inr (.single hab)
    · have : b = c := by
        rw [hab] at hc
        exact Option.some.inj hc
      subst this
      exact Or.inl hcy
  · exact Or.inr (h.tail hab)

/-- **The second flood gives a unit of flow.** -/
theorem unitFlow_of_par (hst : s ≠ t) (hrk : ∀ v p, par v = some p → N.G.Adj v p ∧ rk p < rk v)
    (hpar : ∀ v, v ≠ s → ∃ p, par v = some p) (hs : par s = none) (htD : rk t ≤ D) :
    UnitFlow N s t (fun v u => unitOf (par v) (tokenSt N par t D v) u) := by
  have hA : ∀ u v, floodA N.G (tokenIn par t) u v ↔ par u = some v := fun u v => by
    constructor
    · rintro ⟨-, h⟩
      simpa [tokenIn] using h
    · intro h
      exact ⟨(hrk u v h).1, by simpa [tokenIn] using h⟩
  have hseed : ∀ v, (tokenIn par t v).1 = true ↔ v = t := fun v => by simp [tokenIn]
  have hrun := run_flood N.G (tokenIn par t) D
  -- the state of the flood
  have hsome : ∀ v, (tokenSt N par t D v).isSome = true ↔ TLev N par t D v := fun v => (hrun v).2.1
  have hnone : ∀ v, tokenSt N par t D v = some none ↔ v = t := fun v =>
    (hrun v).2.2.1.trans (hseed v)
  have hprev : ∀ v p, tokenSt N par t D v = some (some p) → par p = some v ∧ TLev N par t D p := by
    intro v p h
    obtain ⟨h1, t', h2, h3, -⟩ := (hrun v).2.2.2 p h
    exact ⟨(hA _ _).1 h1, h3.mono h2.le⟩
  -- arrival times
  have harr : ∀ i u, TLev N par t i u → ∃ j, j ≤ i ∧ TLev N par t j u ∧ rk u + j ≤ rk t := by
    intro i
    induction i with
    | zero =>
      intro u hu
      have : u = t := (hseed u).1 hu
      subst this
      exact ⟨0, le_rfl, hu, by omega⟩
    | succ i ih =>
      rintro u (hu | ⟨w, hw, hwu⟩)
      · obtain ⟨j, h1, h2, h3⟩ := ih u hu
        exact ⟨j, by omega, h2, h3⟩
      · obtain ⟨j, h1, h2, h3⟩ := ih w hw
        have := (hrk w u ((hA _ _).1 hwu)).2
        exact ⟨j + 1, by omega, Or.inr ⟨w, h2, hwu⟩, by omega⟩
  -- the marked nodes form a chain
  have hcmp : ∀ i x y, TLev N par t i x → TLev N par t i y →
      Relation.ReflTransGen (fun a b => par a = some b) x y ∨
        Relation.ReflTransGen (fun a b => par a = some b) y x := by
    intro i
    induction i with
    | zero =>
      intro x y hx hy
      have h1 : x = t := (hseed x).1 hx
      have h2 : y = t := (hseed y).1 hy
      rw [h1, h2]
      exact Or.inl .refl
    | succ i ih =>
      rintro x y (hx | ⟨w, hw, hwx⟩) (hy | ⟨w', hw', hwy⟩)
      · exact ih x y hx hy
      · exact (compare_step (ih w' x hw' hx) ((hA _ _).1 hwy)).symm
      · exact compare_step (ih w y hw hy) ((hA _ _).1 hwx)
      · have h1 := compare_step (ih w w' hw hw') ((hA _ _).1 hwx)
        exact (compare_step h1.symm ((hA _ _).1 hwy)).symm
  have hrkAnc : ∀ a b, Relation.ReflTransGen (fun a b => par a = some b) a b → rk b ≤ rk a := by
    intro a b h
    induction h with
    | refl => exact le_rfl
    | tail _ h ih =>
      have := (hrk _ _ h).2
      omega
  have huniq : ∀ u q v, TLev N par t D u → TLev N par t D q → par u = some v → par q = some v →
      q = u := by
    have key : ∀ u q v, Relation.ReflTransGen (fun a b => par a = some b) u q → par u = some v →
        par q = some v → q = u := by
      intro u q v h hu hq
      rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, hc, hcq⟩
      · rfl
      · have : c = v := by
          rw [hu] at hc
          exact (Option.some.inj hc).symm
        subst this
        have h1 := hrkAnc _ _ hcq
        have h2 := (hrk _ _ hq).2
        omega
    intro u q v hu hq h1 h2
    rcases hcmp D u q hu hq with h | h
    · exact key u q v h h1 h2
    · exact (key q u v h h2 h1).symm
  -- the key relation
  have hK : ∀ v u, (tokenSt N par t D v).join = some u ↔
      (tokenSt N par t D u).isSome = true ∧ par u = some v := by
    intro v u
    constructor
    · intro h
      have h' : tokenSt N par t D v = some (some u) := by
        cases hv : tokenSt N par t D v with
        | none => simp [hv] at h
        | some o =>
          rw [hv] at h
          simp only [Option.join_some] at h
          rw [h]
      obtain ⟨h1, h2⟩ := hprev v u h'
      exact ⟨(hsome u).2 h2, h1⟩
    · rintro ⟨h1, h2⟩
      have hu := (hsome u).1 h1
      obtain ⟨j, -, hj, hrj⟩ := harr D u hu
      have hvu := (hrk u v h2).2
      have hv : TLev N par t (j + 1) v := Or.inr ⟨u, hj, (hA _ _).2 h2⟩
      have hv' := (hsome v).2 (hv.mono (by omega : j + 1 ≤ D))
      cases hc : tokenSt N par t D v with
      | none => simp [hc] at hv'
      | some o =>
        cases o with
        | none =>
          have : v = t := (hnone v).1 hc
          subst this
          omega
        | some q =>
          obtain ⟨h3, h4⟩ := hprev v q hc
          have := huniq u q v hu h4 h2 h3
          subst this
          rfl
  -- the ends of the path
  have ht : TLev N par t D t := Lev.mono (Nat.zero_le _) ((hseed t).2 rfl)
  have hsReach : ∀ n u j, rk u ≤ n → TLev N par t j u → rk u + j ≤ rk t → TLev N par t (rk t) s := by
    intro n
    induction n with
    | zero =>
      intro u j hu hj hr
      by_cases hus : u = s
      · subst hus
        exact hj.mono (by omega)
      · obtain ⟨p, hp⟩ := hpar u hus
        have := (hrk _ _ hp).2
        omega
    | succ n ih =>
      intro u j hu hj hr
      by_cases hus : u = s
      · subst hus
        exact hj.mono (by omega)
      · obtain ⟨p, hp⟩ := hpar u hus
        have := (hrk _ _ hp).2
        exact ih p (j + 1) (by omega) (Or.inr ⟨u, hj, (hA _ _).2 hp⟩) (by omega)
  have hsD : TLev N par t D s :=
    (hsReach _ t 0 le_rfl ((hseed t).2 rfl) (by omega)).mono htD
  refine ⟨fun a b _ => ?_, fun v => ?_, fun a b _ => ?_⟩
  · simp only [unitOf, hK]
    ring
  · have hsum : ∀ o : Option V, (∀ q, o = some q → q ∈ N.G.neighborFinset v) →
        ∑ u ∈ N.G.neighborFinset v, (if o = some u then (1 : ℤ) else 0) =
          if o.isSome = true then 1 else 0 := by
      intro o ho
      cases o with
      | none => simp
      | some q =>
        simp only [Option.some.injEq, Option.isSome_some, ite_true]
        rw [Finset.sum_ite_eq, ite_eq_left (ho q rfl)]
    have h1 : ∑ u ∈ N.G.neighborFinset v, (if (tokenSt N par t D v).join = some u then (1 : ℤ) else 0) =
        if (tokenSt N par t D v).join.isSome = true then 1 else 0 := by
      refine hsum _ fun q hq => ?_
      have := ((hK v q).1 hq).2
      rw [SimpleGraph.mem_neighborFinset]
      exact (hrk _ _ this).1.symm
    have h2 : ∑ u ∈ N.G.neighborFinset v,
        (if (tokenSt N par t D v).isSome = true ∧ par v = some u then (1 : ℤ) else 0) =
        if (tokenSt N par t D v).isSome = true ∧ v ≠ s then 1 else 0 := by
      by_cases hhas : (tokenSt N par t D v).isSome = true
      · simp only [hhas, true_and]
        rw [hsum (par v) fun q hq => by
          rw [SimpleGraph.mem_neighborFinset]
          exact (hrk _ _ hq).1]
        by_cases hv : v = s
        · subst hv
          simp [hs]
        · obtain ⟨p, hp⟩ := hpar v hv
          simp [hp, hv]
      · simp [hhas]
    have h3 : (tokenSt N par t D v).join.isSome = true ↔
        (tokenSt N par t D v).isSome = true ∧ v ≠ t := by
      cases hc : tokenSt N par t D v with
      | none => simp
      | some o =>
        cases o with
        | none =>
          simpa using (hnone v).1 hc
        | some q =>
          have hvt : v ≠ t := fun h => by
            have := (hnone v).2 h
            rw [this] at hc
            cases hc
          simp [hvt]
    simp only [unitOf]
    rw [Finset.sum_sub_distrib, h1, h2]
    by_cases hvs : v = s
    · subst hvs
      have h4 := (hsome v).2 hsD
      have h5 : (tokenSt N par t D v).join.isSome = true := h3.2 ⟨h4, hst⟩
      simp [h5, hst]
    · by_cases hvt : v = t
      · have h4 : (tokenSt N par t D v).isSome = true := (hsome v).2 (hvt ▸ ht)
        have h5 : ¬ (tokenSt N par t D v).join.isSome = true := fun h => (h3.1 h).2 hvt
        rw [ite_eq_right h5, ite_eq_left ⟨h4, hvs⟩, ite_eq_right hvs, ite_eq_left hvt]
      · by_cases hhas : (tokenSt N par t D v).isSome = true
        · have h5 : (tokenSt N par t D v).join.isSome = true := h3.2 ⟨hhas, hvt⟩
          simp [h5, hhas, hvs, hvt]
        · have h5 : ¬ (tokenSt N par t D v).join.isSome = true := fun h => hhas (h3.1 h).1
          simp only [h5, hhas, hvs, hvt]
          simp
  · simp only [unitOf]
    split_ifs <;> simp

end Token

section First

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The input of the first flood. -/
def parentIn (s v : V) : Bool × (V → Bool) := (decide (v = s), fun _ => true)

/-- The parents after the first flood. -/
noncomputable def floodPar (N : Net V) (s : V) (D : ℕ) (v : V) : Option V :=
  ((floodAlg V).run N.G (parentIn s) D v).2.join

/-- **Two floods give a unit of flow.** -/
theorem unitFlow_of_floods (N : Net V) {D : ℕ} (hD : N.DiamLE D) {s t : V} (hst : s ≠ t) :
    UnitFlow N s t (fun v u => unitOf (floodPar N s D v) (tokenSt N (floodPar N s D) t D v) u) := by
  have hrun := run_flood N.G (parentIn s) D
  have hA : ∀ u v, floodA N.G (parentIn s) u v ↔ N.G.Adj u v := fun u v => by
    simp [floodA, parentIn]
  have hseed : ∀ v, (parentIn s v).1 = true ↔ v = s := fun v => by simp [parentIn]
  let L := Lev (floodA N.G (parentIn s)) (fun v => (parentIn s v).1 = true)
  have hwalk : ∀ {a b : V} (p : N.G.Walk a b) (k : ℕ), L k a → L (k + p.length) b := by
    intro a b p
    induction p with
    | nil => intro k h; exact h
    | cons h q ih =>
      intro k hk
      have := ih (k + 1) (Or.inr ⟨_, hk, (hA _ _).2 h⟩)
      rwa [SimpleGraph.Walk.length_cons, show k + (q.length + 1) = k + 1 + q.length by omega]
  have hall : ∀ v, L D v := fun v => by
    obtain ⟨p, hp⟩ := hD s v
    have := hwalk p 0 ((hseed s).2 rfl)
    rw [zero_add] at this
    exact this.mono hp
  classical
  have hex : ∀ v, ∃ k, L k v := fun v => ⟨D, hall v⟩
  let rk : V → ℕ := fun v => Nat.find (hex v)
  refine unitFlow_of_par N (floodPar N s D) rk hst ?_ ?_ ?_ (Nat.find_min' (hex t) (hall t))
  · intro v p hp
    have hp' : ((floodAlg V).run N.G (parentIn s) D v).2 = some (some p) := by
      cases hc : ((floodAlg V).run N.G (parentIn s) D v).2 with
      | none =>
        have : floodPar N s D v = none := by simp [floodPar, hc]
        rw [this] at hp
        cases hp
      | some o =>
        have : floodPar N s D v = o := by simp [floodPar, hc]
        rw [this] at hp
        rw [hp]
    obtain ⟨h1, t', h2, h3, h4⟩ := (hrun v).2.2.2 p hp'
    refine ⟨((hA _ _).1 h1).symm, ?_⟩
    have h5 : rk p ≤ t' := Nat.find_min' (hex p) h3
    have h6 : t' < rk v := by
      by_contra hc
      exact h4 ((Nat.find_spec (hex v)).mono (not_lt.1 hc))
    omega
  · intro v hv
    have h1 := (hrun v).2.1.2 (hall v)
    cases hc : ((floodAlg V).run N.G (parentIn s) D v).2 with
    | none => simp [hc] at h1
    | some o =>
      cases o with
      | none => exact absurd ((hseed v).1 ((hrun v).2.2.1.1 hc)) hv
      | some p => exact ⟨p, by simp [floodPar, hc]⟩
  · have := (hrun s).2.2.1.2 ((hseed s).2 rfl)
    simp [floodPar, this]

end First

end SsspFlow.Congest
