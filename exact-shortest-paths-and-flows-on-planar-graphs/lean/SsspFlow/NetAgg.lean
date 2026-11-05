import SsspFlow.NetPasses

/-!
# Calls of the aggregation primitive on the darts of a network

A call is given per node by a name for each of its darts and a list of pairs of a key and a value for each of
its darts. Each node then knows, for the name of each of its darts and each key, the least value in the bag
(`tabOf`, `encO_of_isMin`). The hypotheses of the primitive follow from the shape of the bags (`valid_of`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SsspFlow.Congest

open Cslib.Congest Cslib.Congest.Algorithm FourColor RotSystem RotSystem.RootedTree

variable {n : ℕ}

/-- The darts at a node, as seen from the node. -/
def ownL (rl : List (Fin n)) : List (Fin n × Bool) := rl.flatMap fun u => [(u, false), (u, true)]

theorem mem_ownL {rl : List (Fin n)} {y : Fin n × Bool} : y ∈ ownL rl ↔ y.1 ∈ rl := by
  rcases y with ⟨u, b⟩
  simp only [ownL, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ <;> exact ha
  · intro h
    exact ⟨u, h, by cases b <;> simp⟩

/-- The input of a node for a call. -/
def aggInOf (rl : List (Fin n)) (nm : Fin n × Bool → ℕ) (its : Fin n × Bool → List (ℕ × ℕ)) :
    AggIn (Fin n) where
  subgraphs u := if u ∈ rl then [nm (u, false), nm (u, true)] else []
  member := (ownL rl).map nm
  items := (ownL rl).flatMap fun y => (its y).map fun p => (nm y, p.1, p.2)

section Tab

variable {α : Type*} {nameD : α → ℕ} {itsD : α → List (ℕ × ℕ)}

variable (nameD itsD) in
open Classical in
/-- The answer of a call for a name and a key: the least value, plus one, or zero if there is none. -/
noncomputable def tabD (x κ : ℕ) : ℕ :=
  if ∃ a z, nameD z = x ∧ (κ, a) ∈ itsD z then
    sInf {a | ∃ z, nameD z = x ∧ (κ, a) ∈ itsD z} + 1
  else 0

theorem tabD_of_least {x κ a : ℕ} (h : ∃ z, nameD z = x ∧ (κ, a) ∈ itsD z)
    (hl : ∀ z a', nameD z = x → (κ, a') ∈ itsD z → a ≤ a') : tabD nameD itsD x κ = a + 1 := by
  obtain ⟨z, hz, hp⟩ := h
  unfold tabD
  rw [if_pos ⟨a, z, hz, hp⟩]
  congr 1
  refine le_antisymm (Nat.sInf_le ⟨z, hz, hp⟩) (le_csInf ⟨a, z, hz, hp⟩ ?_)
  rintro b ⟨y, hy, hb⟩
  exact hl y b hy hb

theorem tabD_of_unique {x κ a : ℕ} (h : ∃ z, nameD z = x ∧ (κ, a) ∈ itsD z)
    (hu : ∀ z a', nameD z = x → (κ, a') ∈ itsD z → a' = a) : tabD nameD itsD x κ = a + 1 :=
  tabD_of_least h fun z a' hz hp => (hu z a' hz hp).ge

theorem tabD_none {x κ : ℕ} (h : ∀ z a, nameD z = x → (κ, a) ∉ itsD z) : tabD nameD itsD x κ = 0 := by
  unfold tabD
  rw [if_neg]
  rintro ⟨a, z, hz, hp⟩
  exact h z a hz hp

theorem tabD_le {x κ a : ℕ} {z : α} (hz : nameD z = x) (hp : (κ, a) ∈ itsD z) :
    tabD nameD itsD x κ ≤ a + 1 := by
  unfold tabD
  rw [if_pos ⟨a, z, hz, hp⟩]
  exact Nat.succ_le_succ (Nat.sInf_le ⟨z, hz, hp⟩)

end Tab

/-- The value of an answer in the memory. -/
def encO : Option ℕ → ℕ
  | none => 0
  | some a => a + 1

variable (N : Net (Fin n))

/-- The dart of a node with a given local name. -/
def Net.dartAt (v : Fin n) (y : Fin n × Bool) (h : N.G.Adj v y.1) : N.G.Dart × Bool := (⟨(v, y.1), h⟩, y.2)

variable {N}

theorem mem_ownL_rot {v : Fin n} {y : Fin n × Bool} : y ∈ ownL (N.rotList v) ↔ N.G.Adj v y.1 :=
  mem_ownL.trans (N.mem_rotList v y.1)

theorem locN_mem_own (z : N.G.Dart × Bool) : N.locN z ∈ ownL (N.rotList z.1.fst) :=
  mem_ownL_rot.2 z.1.adj

theorem exists_dart_of_own {v : Fin n} {y : Fin n × Bool} (h : y ∈ ownL (N.rotList v)) :
    ∃ z : N.G.Dart × Bool, z.1.fst = v ∧ N.locN z = y :=
  ⟨N.dartAt v y (mem_ownL_rot.1 h), rfl, rfl⟩

section Call

variable (N) (nm : Fin n → Fin n × Bool → ℕ) (its : Fin n → Fin n × Bool → List (ℕ × ℕ))

/-- The inputs of all nodes for a call. -/
def inpOf : Fin n → AggIn (Fin n) := fun v => aggInOf (N.rotList v) (nm v) (its v)

/-- The name of a dart in a call. -/
def nameOf (z : N.G.Dart × Bool) : ℕ := nm z.1.fst (N.locN z)

/-- The pairs of a dart in a call. -/
def itsOf (z : N.G.Dart × Bool) : List (ℕ × ℕ) := its z.1.fst (N.locN z)

/-- The answer of a call for a name and a key. -/
noncomputable abbrev tabOf (x κ : ℕ) : ℕ := tabD (nameOf N nm) (itsOf N its) x κ

variable {N nm its}

theorem mem_items {v : Fin n} {x κ a : ℕ} :
    (x, κ, a) ∈ (inpOf N nm its v).items ↔
      ∃ z : N.G.Dart × Bool, z.1.fst = v ∧ nameOf N nm z = x ∧ (κ, a) ∈ itsOf N its z := by
  simp only [inpOf, aggInOf, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨y, hy, p, hp, rfl, rfl, rfl⟩
    obtain ⟨z, rfl, rfl⟩ := exists_dart_of_own hy
    exact ⟨z, rfl, rfl, hp⟩
  · rintro ⟨z, rfl, rfl, hp⟩
    exact ⟨N.locN z, locN_mem_own z, (κ, a), hp, rfl, rfl, rfl⟩

theorem mem_member {v : Fin n} {x : ℕ} :
    x ∈ (inpOf N nm its v).member ↔ ∃ z : N.G.Dart × Bool, z.1.fst = v ∧ nameOf N nm z = x := by
  simp only [inpOf, aggInOf, List.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, rfl, rfl⟩ := exists_dart_of_own hy
    exact ⟨z, rfl, rfl⟩
  · rintro ⟨z, rfl, rfl⟩
    exact ⟨N.locN z, locN_mem_own z, rfl⟩

/-- An answer of the primitive, in the memory. -/
theorem encO_of_isMin {x κ : ℕ} {o : Option ℕ} (h : AggIn.IsMin (inpOf N nm its) x κ o) :
    encO o = tabOf N nm its x κ := by
  cases o with
  | none =>
    refine (tabD_none fun z a hz hp => ?_).symm
    exact h z.1.fst a (mem_items.2 ⟨z, rfl, hz, hp⟩)
  | some a =>
    obtain ⟨⟨v, hv⟩, hl⟩ := h
    obtain ⟨z, -, hz, hp⟩ := mem_items.1 hv
    exact (tabD_of_least ⟨z, hz, hp⟩ fun y a' hy hb =>
      hl y.1.fst a' (mem_items.2 ⟨y, rfl, hy, hb⟩)).symm

/-- **The hypotheses of the primitive for a call.** -/
theorem valid_of {s k b : ℕ} (hsymm : ∀ z, nameOf N nm (N.toRot.double.rev z) = nameOf N nm z)
    (hspan : ∀ z z' : N.G.Dart × Bool, nameOf N nm z = nameOf N nm z' →
      ReachLE (fun a c => ∃ y : N.G.Dart × Bool, nameOf N nm y = nameOf N nm z ∧ y.1.fst = a ∧ y.1.snd = c)
        s z.1.fst z'.1.fst)
    (hk : ∀ z : N.G.Dart × Bool, ∃ K : Finset ℕ, K.card ≤ k ∧
      ∀ z', nameOf N nm z' = nameOf N nm z → ∀ p ∈ itsOf N its z', p.1 ∈ K)
    (hname : ∀ z : N.G.Dart × Bool, nameOf N nm z < 2 ^ b)
    (hf : ∀ z : N.G.Dart × Bool, ∀ p ∈ itsOf N its z, p.1 < 2 ^ b ∧ p.2 < 2 ^ b) :
    AggIn.Valid N (inpOf N nm its) s 2 k b where
  symm v u hadj x := by
    have hv : u ∈ N.rotList v := (N.mem_rotList v u).2 hadj
    have hu : v ∈ N.rotList u := (N.mem_rotList u v).2 hadj.symm
    have e : ∀ b : Bool, nm v (u, b) = nm u (v, !b) := fun b =>
      (hsymm (N.dartAt v (u, b) hadj)).symm
    simp only [inpOf, aggInOf, if_pos hv, if_pos hu, List.mem_cons, List.not_mem_nil, or_false]
    rw [e false, e true]
    simp only [Bool.not_false, Bool.not_true]
    exact or_comm
  span x a a' ha ha' := by
    obtain ⟨z, rfl, hz⟩ := mem_member.1 ha
    obtain ⟨z', rfl, hz'⟩ := mem_member.1 ha'
    refine ReachLE.mono_adj ?_ (hspan z z' (hz.trans hz'.symm))
    rintro c e ⟨y, hy, rfl, rfl⟩
    refine ⟨y.1.adj, ?_⟩
    have hm : y.1.snd ∈ N.rotList y.1.fst := (N.mem_rotList _ _).2 y.1.adj
    simp only [inpOf, aggInOf, if_pos hm, List.mem_cons, List.not_mem_nil, or_false]
    rw [hz] at hy
    obtain ⟨d, _ | _⟩ := y
    · exact Or.inl hy.symm
    · exact Or.inr hy.symm
  congestion v u _ := by
    simp only [inpOf, aggInOf]
    split_ifs <;> simp
  keys x := by
    by_cases hx : ∃ z, nameOf N nm z = x
    · obtain ⟨z, rfl⟩ := hx
      obtain ⟨K, hK, hm⟩ := hk z
      refine ⟨K, hK, ?_⟩
      rintro v ⟨x', κ, a⟩ ht e
      obtain ⟨y, -, hy, hp⟩ := mem_items.1 ht
      exact hm y (hy.trans e) (κ, a) hp
    · refine ⟨∅, by simp, ?_⟩
      rintro v ⟨x', κ, a⟩ ht e
      obtain ⟨y, -, hy, -⟩ := mem_items.1 ht
      exact (hx ⟨y, hy.trans e⟩).elim
  items_member v t ht := by
    obtain ⟨x', κ, a⟩ := t
    obtain ⟨y, hyv, hy, -⟩ := mem_items.1 ht
    exact mem_member.2 ⟨y, hyv, hy⟩
  fields v t ht := by
    obtain ⟨x', κ, a⟩ := t
    obtain ⟨y, -, hy, hp⟩ := mem_items.1 ht
    have := hf y (κ, a) hp
    exact ⟨hy ▸ hname y, this.1, this.2⟩
  names v u x hx := by
    simp only [inpOf, aggInOf] at hx
    split_ifs at hx with hm
    · have hadj : N.G.Adj v u := (N.mem_rotList v u).1 hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hname (N.dartAt v (u, false) hadj)
      · exact hname (N.dartAt v (u, true) hadj)
    · simp at hx

end Call

/-- The answers of a call are in the memory `M`. -/
def AggDone (N : Net (Fin n)) (nm : Fin n → Fin n × Bool → ℕ) (its : Fin n → Fin n × Bool → List (ℕ × ℕ))
    (s k b : ℕ) (M : Fin n → ℕ → ℕ) : Prop :=
  AggIn.Valid N (inpOf N nm its) s 2 k b → ∀ v, ∀ x ∈ (inpOf N nm its v).member, ∀ κ,
    ∃ o, AggIn.IsMin (inpOf N nm its) x κ o ∧ M v (Nat.pair x κ) = encO o

theorem AggDone.tab {nm : Fin n → Fin n × Bool → ℕ} {its : Fin n → Fin n × Bool → List (ℕ × ℕ)}
    {s k b : ℕ} {M : Fin n → ℕ → ℕ} (h : AggDone N nm its s k b M)
    (hV : AggIn.Valid N (inpOf N nm its) s 2 k b) (z : N.G.Dart × Bool) (κ : ℕ) :
    M z.1.fst (Nat.pair (nameOf N nm z) κ) = tabOf N nm its (nameOf N nm z) κ := by
  obtain ⟨o, ho, he⟩ := h hV z.1.fst _ (mem_member.2 ⟨z, rfl, rfl⟩) κ
  rw [he, encO_of_isMin ho]

end SsspFlow.Congest
