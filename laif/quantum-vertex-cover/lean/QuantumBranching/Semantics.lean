import Mathlib.Tactic

/-!
# The recursive procedure and its OR-tree

A procedure sends an instance to one of four cases. In the case SEQ it holds a `SeqProg`, a decision
tree of value calls in which each call may depend on the answers to the earlier ones, and which ends
by answering or by a tail call. A rank decreases along every call, which makes `Proc.answer` total.

`Proc.outcome` is what a node does once its value calls have been answered: it answers, or it has a
list of children, the single tail call being a list of length one.

`Proc.orTree` is the whole OR-tree of an instance. Below each node that answers by itself sits a new
leaf, marked by the answer. So the root is never marked, and marks occur on added leaves only.
`answer_iff_marked` states that the answer is yes iff the tree has a marked leaf.
-/

namespace QuantumBranching

variable {I : Type*}

/-- Value calls in sequence, adaptively, ending by an answer or by a tail call. -/
inductive SeqProg (I : Type*) where
  /-- Answer from the earlier answers. -/
  | ret (b : Bool)
  /-- Tail call: answer as `z` does. -/
  | tail (z : I)
  /-- Value call to `y`, then continue depending on its answer. -/
  | call (y : I) (k : Bool → SeqProg I)

namespace SeqProg

/-- What the program does, given the answers `v` to its value calls: an answer, or a tail call. -/
def run (v : I → Bool) : SeqProg I → Bool ⊕ I
  | ret b => .inl b
  | tail z => .inr z
  | call y k => run v (k (v y))

/-- The value calls actually made, given the answers `v`. -/
def calls (v : I → Bool) : SeqProg I → List I
  | ret _ => []
  | tail _ => []
  | call y k => y :: calls v (k (v y))

/-- Every instance named by the program, on any branch, satisfies `r`. -/
def Below (r : I → Prop) : SeqProg I → Prop
  | ret _ => True
  | tail z => r z
  | call y k => r y ∧ ∀ b, Below r (k b)

theorem run_congr {r : I → Prop} {v w : I → Bool} (h : ∀ y, r y → v y = w y) :
    ∀ p : SeqProg I, Below r p → run v p = run w p
  | ret _, _ => rfl
  | tail _, _ => rfl
  | call y k, hp => by
    simp only [run, h y hp.1]
    exact run_congr h _ (hp.2 _)

theorem calls_congr {r : I → Prop} {v w : I → Bool} (h : ∀ y, r y → v y = w y) :
    ∀ p : SeqProg I, Below r p → calls v p = calls w p
  | ret _, _ => rfl
  | tail _, _ => rfl
  | call y k, hp => by
    simp only [calls, h y hp.1]
    rw [calls_congr h _ (hp.2 _)]

theorem run_tail_below {r : I → Prop} {v : I → Bool} {z : I} :
    ∀ p : SeqProg I, Below r p → run v p = .inr z → r z
  | ret _, _, h => by simp [run] at h
  | tail z', hp, h => by
    simp only [run, Sum.inr.injEq] at h
    exact h ▸ hp
  | call y k, hp, h => run_tail_below _ (hp.2 _) h

theorem calls_below {r : I → Prop} {v : I → Bool} {y : I} :
    ∀ p : SeqProg I, Below r p → y ∈ calls v p → r y
  | ret _, _, h => by simp [calls] at h
  | tail _, _, h => by simp [calls] at h
  | call y' k, hp, h => by
    simp only [calls, List.mem_cons] at h
    rcases h with rfl | h
    · exact hp.1
    · exact calls_below _ (hp.2 _) h

end SeqProg

/-- The four cases of a node. In the case `box`, `b` is the answer of the subroutine. -/
inductive Case (I : Type*) where
  | leaf (b : Bool)
  | or (cs : List I)
  | seq (p : SeqProg I)
  | box (b : Bool)

/-- A recursive procedure with a rank that decreases along every call. -/
structure Proc (I : Type*) where
  /-- The case of an instance. -/
  step : I → Case I
  /-- The rank of an instance. -/
  rank : I → ℕ
  rank_or : ∀ x cs, step x = .or cs → ∀ c ∈ cs, rank c < rank x
  rank_seq : ∀ x p, step x = .seq p → p.Below (fun y => rank y < rank x)

/-- Trees with marks on added leaves. -/
inductive ORTree (I : Type*) where
  /-- An added leaf, marked if `b` holds. -/
  | mark (b : Bool)
  /-- A node with its children. -/
  | node (a : I) (cs : List (ORTree I))

namespace Proc

variable (P : Proc I)

/-- The answer of the procedure. The rank test always succeeds, by `rank_or` and `rank_seq`. -/
def answer (x : I) : Bool :=
  match P.step x with
  | .leaf b => b
  | .box b => b
  | .or cs => cs.any fun c => if P.rank c < P.rank x then answer c else false
  | .seq p =>
    match p.run (fun y => if P.rank y < P.rank x then answer y else false) with
    | .inl b => b
    | .inr z => if P.rank z < P.rank x then answer z else false
termination_by P.rank x
decreasing_by all_goals assumption

theorem answer_leaf {x : I} {b : Bool} (h : P.step x = .leaf b) : P.answer x = b := by
  rw [answer, h]

theorem answer_box {x : I} {b : Bool} (h : P.step x = .box b) : P.answer x = b := by
  rw [answer, h]

theorem answer_or {x : I} {cs : List I} (h : P.step x = .or cs) :
    P.answer x = cs.any P.answer := by
  rw [answer, h]
  simp only
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  refine exists_congr fun c => and_congr_right fun hc => ?_
  simp [P.rank_or x cs h c hc]

theorem answer_seq {x : I} {p : SeqProg I} (h : P.step x = .seq p) :
    P.answer x = match p.run P.answer with
      | .inl b => b
      | .inr z => P.answer z := by
  have hb := P.rank_seq x p h
  have hrun : p.run (fun y => if P.rank y < P.rank x then P.answer y else false)
      = p.run P.answer := SeqProg.run_congr (r := fun y => P.rank y < P.rank x)
        (fun y hy => by simp [hy]) p hb
  rw [answer, h]
  simp only
  rw [hrun]
  cases hr : p.run P.answer with
  | inl b => rfl
  | inr z =>
    have := SeqProg.run_tail_below p hb hr
    simp [this]

/-- What a node does once its value calls are answered: answer, or go to its children. -/
def outcome (x : I) : Bool ⊕ List I :=
  match P.step x with
  | .leaf b => .inl b
  | .box b => .inl b
  | .or cs => .inr cs
  | .seq p =>
    match p.run P.answer with
    | .inl b => .inl b
    | .inr z => .inr [z]

/-- The value calls made at a node, with the true answers. -/
def calls (x : I) : List I :=
  match P.step x with
  | .seq p => p.calls P.answer
  | _ => []

theorem rank_call {x y : I} (h : y ∈ P.calls x) : P.rank y < P.rank x := by
  unfold calls at h
  cases hs : P.step x with
  | seq p =>
    rw [hs] at h
    exact SeqProg.calls_below (r := fun y => P.rank y < P.rank x) p (P.rank_seq x p hs) h
  | leaf b => simp [hs] at h
  | or cs => simp [hs] at h
  | box b => simp [hs] at h

theorem rank_child {x c : I} {cs : List I} (h : P.outcome x = .inr cs) (hc : c ∈ cs) :
    P.rank c < P.rank x := by
  unfold outcome at h
  cases hs : P.step x with
  | leaf b => simp [hs] at h
  | box b => simp [hs] at h
  | or cs' =>
    simp only [hs, Sum.inr.injEq] at h
    subst h
    exact P.rank_or x _ hs c hc
  | seq p =>
    simp only [hs] at h
    cases hr : p.run P.answer with
    | inl b => simp [hr] at h
    | inr z =>
      simp only [hr, Sum.inr.injEq] at h
      subst h
      simp only [List.mem_singleton] at hc
      subst hc
      exact SeqProg.run_tail_below (r := fun y => P.rank y < P.rank x) p (P.rank_seq x p hs) hr

theorem answer_of_inl {x : I} {b : Bool} (h : P.outcome x = .inl b) : P.answer x = b := by
  unfold outcome at h
  cases hs : P.step x with
  | leaf b' =>
    simp only [hs, Sum.inl.injEq] at h
    rw [P.answer_leaf hs, h]
  | box b' =>
    simp only [hs, Sum.inl.injEq] at h
    rw [P.answer_box hs, h]
  | or cs => simp [hs] at h
  | seq p =>
    simp only [hs] at h
    rw [P.answer_seq hs]
    cases hr : p.run P.answer with
    | inl b' =>
      simp only [hr, Sum.inl.injEq] at h
      simpa using h
    | inr z => simp [hr] at h

theorem answer_of_inr {x : I} {cs : List I} (h : P.outcome x = .inr cs) :
    P.answer x = cs.any P.answer := by
  unfold outcome at h
  cases hs : P.step x with
  | leaf b => simp [hs] at h
  | box b => simp [hs] at h
  | or cs' =>
    simp only [hs, Sum.inr.injEq] at h
    subst h
    exact P.answer_or hs
  | seq p =>
    simp only [hs] at h
    rw [P.answer_seq hs]
    cases hr : p.run P.answer with
    | inl b => simp [hr] at h
    | inr z =>
      simp only [hr, Sum.inr.injEq] at h
      subst h
      simp

/-- The whole OR-tree of an instance. A node that answers by itself gets one added leaf, marked by
its answer. The rank test always succeeds, by `rank_child`. -/
def orTree (x : I) : ORTree I :=
  match P.outcome x with
  | .inl b => .node x [.mark b]
  | .inr cs => .node x (cs.map fun c => if P.rank c < P.rank x then orTree c else .mark false)
termination_by P.rank x
decreasing_by assumption

theorem orTree_inl {x : I} {b : Bool} (h : P.outcome x = .inl b) :
    P.orTree x = .node x [.mark b] := by
  rw [orTree]
  split <;> simp_all

theorem orTree_inr {x : I} {cs : List I} (h : P.outcome x = .inr cs) :
    P.orTree x = .node x (cs.map P.orTree) := by
  rw [orTree]
  split
  · simp_all
  · rename_i cs' h'
    rw [h] at h'
    simp only [Sum.inr.injEq] at h'
    subst h'
    congr 1
    refine List.map_congr_left fun c hc => ?_
    simp [P.rank_child h hc]

end Proc

namespace ORTree

/-- The tree has a marked leaf. -/
inductive HasMarked : ORTree I → Prop
  | mark : HasMarked (.mark true)
  | child {a : I} {cs : List (ORTree I)} {c : ORTree I} :
      c ∈ cs → HasMarked c → HasMarked (.node a cs)

theorem hasMarked_node_iff {a : I} {cs : List (ORTree I)} :
    HasMarked (.node a cs) ↔ ∃ c ∈ cs, HasMarked c := by
  constructor
  · intro h
    cases h with
    | child hc hm => exact ⟨_, hc, hm⟩
  · rintro ⟨c, hc, hm⟩
    exact .child hc hm

theorem hasMarked_mark_iff {b : Bool} : HasMarked (.mark b : ORTree I) ↔ b = true := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .mark

theorem flatMap_attach_val {α β : Type*} (l : List α) (f : α → List β) :
    (l.attach.flatMap fun c => f c.1) = l.flatMap f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.attach_cons, List.flatMap_cons, List.flatMap_map]
    congr 1

/-- The nodes of the tree, with repetition, added leaves excluded. -/
def nodes : ORTree I → List I
  | .mark _ => []
  | .node a cs => a :: cs.attach.flatMap fun c => nodes c.1
decreasing_by
  have := List.sizeOf_lt_of_mem c.2
  simp only [ORTree.node.sizeOf_spec]
  omega

/-- The nodes at depth `ℓ`, with repetition, added leaves excluded. -/
def levelNodes : ORTree I → ℕ → List I
  | .mark _, _ => []
  | .node a _, 0 => [a]
  | .node _ cs, ℓ + 1 => cs.attach.flatMap fun c => levelNodes c.1 ℓ
decreasing_by
  have := List.sizeOf_lt_of_mem c.2
  simp only [ORTree.node.sizeOf_spec]
  omega

@[simp] theorem nodes_mark (b : Bool) : nodes (.mark b : ORTree I) = [] := by rw [nodes]

theorem nodes_node (a : I) (cs : List (ORTree I)) :
    nodes (.node a cs) = a :: cs.flatMap nodes := by
  rw [nodes]
  congr 1
  exact flatMap_attach_val cs nodes

@[simp] theorem levelNodes_mark (b : Bool) (ℓ : ℕ) : levelNodes (.mark b : ORTree I) ℓ = [] := by
  rw [levelNodes]

@[simp] theorem levelNodes_zero (a : I) (cs : List (ORTree I)) :
    levelNodes (.node a cs) 0 = [a] := by
  rw [levelNodes]

theorem levelNodes_succ (a : I) (cs : List (ORTree I)) (ℓ : ℕ) :
    levelNodes (.node a cs) (ℓ + 1) = cs.flatMap fun c => levelNodes c ℓ := by
  rw [levelNodes]
  exact flatMap_attach_val cs fun c => levelNodes c ℓ

mutual
  /-- `l` lists the nodes of an antichain of the tree: the empty one, the root alone, or a union of
  antichains in the child subtrees. -/
  inductive IsAntichain : ORTree I → List I → Prop
    | nil (t : ORTree I) : IsAntichain t []
    | root (a : I) (cs : List (ORTree I)) : IsAntichain (.node a cs) [a]
    | sub (a : I) (cs : List (ORTree I)) (l : List I) :
        IsAntichainList cs l → IsAntichain (.node a cs) l
  /-- A union of antichains, one for each tree of a list. -/
  inductive IsAntichainList : List (ORTree I) → List I → Prop
    | nil : IsAntichainList [] []
    | cons (c : ORTree I) (cs : List (ORTree I)) (l₁ l₂ : List I) :
        IsAntichain c l₁ → IsAntichainList cs l₂ → IsAntichainList (c :: cs) (l₁ ++ l₂)
end

theorem IsAntichainList.empty : ∀ cs : List (ORTree I), IsAntichainList cs []
  | [] => .nil
  | c :: cs => by
    have := IsAntichainList.cons c cs [] [] (.nil c) (IsAntichainList.empty cs)
    simpa using this

theorem IsAntichainList.of_mem {c : ORTree I} {l : List I} (hl : IsAntichain c l) :
    ∀ {cs : List (ORTree I)}, c ∈ cs → IsAntichainList cs l
  | d :: ds, hc => by
    rcases List.mem_cons.mp hc with rfl | hc
    · have := IsAntichainList.cons c ds l [] hl (IsAntichainList.empty ds)
      simpa using this
    · have := IsAntichainList.cons d ds [] l (.nil d) (IsAntichainList.of_mem hl hc)
      simpa using this

/-- A general induction principle for trees. -/
theorem ind {M : ORTree I → Prop} (hm : ∀ b, M (.mark b))
    (hn : ∀ a cs, (∀ c ∈ cs, M c) → M (.node a cs)) : ∀ t, M t
  | .mark b => hm b
  | .node a cs => hn a cs fun c _ => ind hm hn c
decreasing_by
  have := List.sizeOf_lt_of_mem ‹c ∈ cs›
  simp only [ORTree.node.sizeOf_spec]
  omega

/-- The nodes at a fixed depth form an antichain. -/
theorem isAntichain_levelNodes (t : ORTree I) : ∀ ℓ, IsAntichain t (levelNodes t ℓ) := by
  induction t using ind with
  | hm b => intro ℓ; simpa using IsAntichain.nil (.mark b)
  | hn a cs ih =>
    intro ℓ
    cases ℓ with
    | zero => simpa using IsAntichain.root a cs
    | succ ℓ =>
      rw [levelNodes_succ]
      refine .sub _ _ _ ?_
      clear a
      induction cs with
      | nil => exact .nil
      | cons c cs ihcs =>
        rw [List.flatMap_cons]
        exact .cons _ _ _ _ (ih c (by simp) ℓ) (ihcs fun d hd => ih d (by simp [hd]))

/-- A single node forms an antichain. -/
theorem isAntichain_singleton (t : ORTree I) : ∀ v ∈ nodes t, IsAntichain t [v] := by
  induction t using ind with
  | hm b => simp
  | hn a cs ih =>
    intro v hv
    rw [nodes_node, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact .root _ _
    · obtain ⟨c, hc, hvc⟩ := List.mem_flatMap.mp hv
      exact .sub _ _ _ (IsAntichainList.of_mem (ih c hc v hvc) hc)

end ORTree

namespace Proc

variable (P : Proc I)

/-- **The search is correct.** The answer at `x` is yes iff the OR-tree of `x` has a marked leaf. -/
theorem answer_iff_marked (x : I) : P.answer x = true ↔ (P.orTree x).HasMarked := by
  induction hk : P.rank x using Nat.strong_induction_on generalizing x with
  | _ k ih =>
    cases ho : P.outcome x with
    | inl b =>
      rw [P.orTree_inl ho, P.answer_of_inl ho, ORTree.hasMarked_node_iff]
      simp [ORTree.hasMarked_mark_iff]
    | inr cs =>
      rw [P.orTree_inr ho, P.answer_of_inr ho, ORTree.hasMarked_node_iff, List.any_eq_true]
      constructor
      · rintro ⟨c, hc, hac⟩
        have hr := P.rank_child ho hc
        exact ⟨P.orTree c, List.mem_map_of_mem hc, (ih _ (hk ▸ hr) c rfl).mp hac⟩
      · rintro ⟨t, ht, hm⟩
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
        have hr := P.rank_child ho hc
        exact ⟨c, hc, (ih _ (hk ▸ hr) c rfl).mpr hm⟩

/-- The root of the OR-tree is a node, so the root of the search is unmarked. -/
theorem orTree_root (x : I) : ∃ cs, P.orTree x = .node x cs := by
  cases ho : P.outcome x with
  | inl b => exact ⟨_, P.orTree_inl ho⟩
  | inr cs => exact ⟨_, P.orTree_inr ho⟩

/-- The nodes of an OR-tree have rank at most that of its root. -/
theorem rank_le_of_mem_nodes {x v : I} (hv : v ∈ (P.orTree x).nodes) : P.rank v ≤ P.rank x := by
  induction hk : P.rank x using Nat.strong_induction_on generalizing x with
  | _ k ih =>
    subst hk
    have step : ∀ cs : List I, (∀ c ∈ cs, P.rank c < P.rank x) →
        v ∈ x :: (cs.map P.orTree).flatMap ORTree.nodes → P.rank v ≤ P.rank x := by
      intro cs hcs hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact le_rfl
      · obtain ⟨t, ht, hvt⟩ := List.mem_flatMap.mp hv
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
        exact le_trans (ih _ (hcs c hc) hvt rfl) (hcs c hc).le
    cases ho : P.outcome x with
    | inl b =>
      rw [P.orTree_inl ho, ORTree.nodes_node] at hv
      simp at hv
      rw [hv]
    | inr cs =>
      rw [P.orTree_inr ho, ORTree.nodes_node] at hv
      exact step cs (fun c hc => P.rank_child ho hc) hv

/-- A node has a Box in its case, or in the subtree of its calls. -/
inductive HasBox : I → Prop
  | here {x : I} {b : Bool} : P.step x = .box b → HasBox x
  | child {x c : I} {cs : List I} : P.outcome x = .inr cs → c ∈ cs → HasBox c → HasBox x
  | call {x y : I} : y ∈ P.calls x → HasBox y → HasBox x

end Proc

end QuantumBranching
