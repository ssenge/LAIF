import RiskRouting.MinProd

/-!
# The branch-and-bound tree of the quantum algorithm (classical part)

Nodes are simple paths `π₀ ++ [v]` from `s` in `G - t₂`; a continuation of a node is a simple path
from `v` to `t₁` that avoids `t₂` and meets the node only in `v`; a candidate is a simple path from
`s` to `t₁` avoiding `t₂`. The distance `δ` of a node is specified by `IsDist`: a lower bound on the
cost of every continuation, attained by one if finite (a shortest path computation returns it).
The bound is `β(π) = c'(π) + L + δ(π)`.

- `join`, `cont_of_cand`, `cont_child`: the path facts behind the proofs.
- `bound_mono`: `β(π) ≤ β(π x)` for every child.
- `prune_ok`: if `δ(π) = ⊤`, no candidate extends the node.
- `bound_le_leaf`: `β(π) ≤ c'(P) + L` for every candidate `P` extending the node.
- `extend_of_bound`: a node with `β(π) ≤ OPT` is a prefix of a candidate with `c'(P) + L ≤ OPT`.
- `card_good_le`: hence at most `n N` such nodes.
- `bcost_*`, `card_good_blocks`: the binary tree over the `k ≤ 2^D` children of a node, whose inner
  nodes get the minimum of the costs of the children below them, is monotone and has at most
  `D` times as many inner nodes of cost at most `OPT` as there are such children.
- `card_binarized`: over the whole tree, at most `(1 + D) T` nodes of cost at most `OPT`.
- `query_bound`: with the guarantee of quantum branch-and-bound as a stated hypothesis
  (`QBBGuarantee`), the number of queries is at most `K √((1 + D) n N) ((n - 1) max(1, D))^{3/2}`
  times `log c_max`.
-/

namespace RiskRouting.BB

open List

variable {V : Type*}

/-- The cost `Σ w(a, b)` over the links of a path. -/
def pc (w : V → V → ℚ) : List V → ℚ
  | a :: b :: l => w a b + pc w (b :: l)
  | _ => 0

theorem pc_join (w : V → V → ℚ) (v : V) (r : List V) :
    ∀ π₀ : List V, pc w (π₀ ++ v :: r) = pc w (π₀ ++ [v]) + pc w (v :: r)
  | [] => by simp [pc]
  | [a] => by simp [pc]
  | a :: b :: l => by
      have := pc_join w v r (b :: l)
      simp only [List.cons_append] at this ⊢
      simp only [pc, this]; ring

variable (G : SimpleGraph V) (s t₁ t₂ : V)

/-- A node `π₀ ++ [v]`. -/
def Node (π₀ : List V) (v : V) : Prop := IsPathL G.Adj (π₀ ++ [v]) s v ∧ t₂ ∉ π₀ ++ [v]

/-- A continuation of the node `π₀ ++ [v]`. -/
def Cont (π₀ : List V) (v : V) (ρ : List V) : Prop :=
  IsPathL G.Adj ρ v t₁ ∧ t₂ ∉ ρ ∧ ∀ y ∈ ρ, y ∈ π₀ ++ [v] → y = v

/-- A candidate first path. -/
def Cand (P : List V) : Prop := IsPathL G.Adj P s t₁ ∧ t₂ ∉ P

variable {G s t₁ t₂}

theorem head_join (π₀ r : List V) (v : V) : (π₀ ++ v :: r).head? = (π₀ ++ [v]).head? := by
  cases π₀ <;> simp

/-- A node followed by a continuation is a candidate. -/
theorem join {π₀ r : List V} {v : V} (hN : Node G s t₂ π₀ v) (hC : Cont G t₁ t₂ π₀ v (v :: r)) :
    Cand G s t₁ t₂ (π₀ ++ v :: r) := by
  obtain ⟨⟨hh, -, hc, hn⟩, ht⟩ := hN
  obtain ⟨⟨-, hl, hc', hn'⟩, ht', hmeet⟩ := hC
  rw [isChain_append] at hc
  refine ⟨⟨by rw [head_join]; exact hh, by rw [List.getLast?_append]; simp [hl],
    ?_, ?_⟩, ?_⟩
  · rw [isChain_append]
    exact ⟨hc.1, hc', fun x hx y hy => hc.2.2 x hx y (by simpa using hy)⟩
  · rw [List.nodup_append] at hn ⊢
    refine ⟨hn.1, hn', fun a ha b hb hab => ?_⟩
    subst hab
    have := hmeet a hb (by simp [ha])
    subst this
    exact hn.2.2 a ha a (by simp) rfl
  · simp only [List.mem_append, not_or] at ht ⊢
    exact ⟨ht.1, ht'⟩

/-- A candidate extending a node continues it. -/
theorem cont_of_cand {π₀ r : List V} {v : V} (hP : Cand G s t₁ t₂ (π₀ ++ v :: r)) :
    Cont G t₁ t₂ π₀ v (v :: r) := by
  obtain ⟨⟨-, hl, hc, hn⟩, ht⟩ := hP
  rw [isChain_append] at hc
  rw [List.nodup_append] at hn
  refine ⟨⟨rfl, by rw [List.getLast?_append] at hl; simpa using hl, hc.2.1, hn.2.1⟩,
    fun h => ht (by simp [h]), fun y hy hπ => ?_⟩
  rcases List.mem_append.mp hπ with h | h
  · exact absurd rfl (hn.2.2 y h y hy)
  · simpa using h

/-- A continuation of a child gives a continuation of the parent, one link longer. -/
theorem cont_child {π₀ ρ : List V} {v x : V} (hN : Node G s t₂ π₀ v) (hvx : G.Adj v x)
    (hx : x ∉ π₀ ++ [v]) (hC : Cont G t₁ t₂ (π₀ ++ [v]) x ρ) :
    Cont G t₁ t₂ π₀ v (v :: ρ) ∧ ∃ r, ρ = x :: r := by
  obtain ⟨⟨hh, hl, hc, hn⟩, ht, hmeet⟩ := hC
  obtain ⟨r, rfl⟩ : ∃ r, ρ = x :: r := by
    cases ρ with
    | nil => simp at hh
    | cons y r => simp at hh; exact ⟨r, by rw [hh]⟩
  have hvρ : v ∉ x :: r := fun h => G.ne_of_adj hvx (hmeet v h (by simp))
  refine ⟨⟨⟨rfl, by rw [getLast?_cons_cons]; exact hl, isChain_cons_cons.mpr ⟨hvx, hc⟩,
    List.nodup_cons.mpr ⟨hvρ, hn⟩⟩, ?_, ?_⟩, r, rfl⟩
  · intro h
    rcases List.mem_cons.mp h with h | h
    · exact hN.2 (by simp [← h])
    · exact ht h
  · intro y hy hπ
    rcases List.mem_cons.mp hy with h | h
    · exact h
    · have := hmeet y h (by simp at hπ ⊢; tauto)
      subst this
      exact absurd hπ hx

/-- The child `π₀ ++ [v, x]` is a node. -/
theorem node_child {π₀ : List V} {v x : V} (hN : Node G s t₂ π₀ v) (hvx : G.Adj v x)
    (hx : x ∉ π₀ ++ [v]) (hx2 : x ≠ t₂) : Node G s t₂ (π₀ ++ [v]) x := by
  obtain ⟨⟨hh, -, hc, hn⟩, ht⟩ := hN
  refine ⟨⟨?_, by simp, ?_, ?_⟩, ?_⟩
  · rw [List.append_assoc, List.singleton_append, head_join]; exact hh
  · rw [isChain_append]
    refine ⟨hc, isChain_singleton _, fun a ha b hb => ?_⟩
    simp at ha hb; subst ha; subst hb; exact hvx
  · exact List.nodup_append.mpr ⟨hn, List.nodup_singleton _, fun a ha b hb hab => by
      simp at hb; subst hb; subst hab; exact hx ha⟩
  · simp only [List.mem_append, List.mem_singleton, not_or] at ht ⊢
    exact ⟨⟨ht.1, ht.2⟩, fun h => hx2 h.symm⟩

/-! ## The bound -/

variable (G t₁ t₂) in
/-- `δ` is the distance of the node: below every continuation, attained if finite. -/
def IsDist (w : V → V → ℚ) (π₀ : List V) (v : V) (δ : WithTop ℚ) : Prop :=
  (∀ ρ, Cont G t₁ t₂ π₀ v ρ → δ ≤ pc w ρ) ∧ (δ ≠ ⊤ → ∃ ρ, Cont G t₁ t₂ π₀ v ρ ∧ (pc w ρ : WithTop ℚ) = δ)

/-- The bound `β = c'(π) + L + δ`. -/
def β (w : V → V → ℚ) (L : ℚ) (π₀ : List V) (v : V) (δ : WithTop ℚ) : WithTop ℚ :=
  ((pc w (π₀ ++ [v]) + L : ℚ) : WithTop ℚ) + δ

/-- **The bound is monotone.** -/
theorem bound_mono {w : V → V → ℚ} {L : ℚ} {π₀ : List V} {v x : V} {δ δ' : WithTop ℚ}
    (hN : Node G s t₂ π₀ v) (hvx : G.Adj v x) (hx : x ∉ π₀ ++ [v])
    (hδ : IsDist G t₁ t₂ w π₀ v δ) (hδ' : IsDist G t₁ t₂ w (π₀ ++ [v]) x δ') :
    β w L π₀ v δ ≤ β w L (π₀ ++ [v]) x δ' := by
  unfold β
  have hc : pc w (π₀ ++ [v] ++ [x]) = pc w (π₀ ++ [v]) + w v x := by
    rw [List.append_assoc, List.singleton_append, pc_join]; simp [pc]
  rcases eq_or_ne δ' ⊤ with h | h
  · simp [h]
  obtain ⟨ρ, hρ, hρd⟩ := hδ'.2 h
  obtain ⟨hC, r, rfl⟩ := cont_child hN hvx hx hρ
  have h1 := hδ.1 _ hC
  have h2 : pc w (v :: x :: r) = w v x + pc w (x :: r) := rfl
  rw [← hρd, hc]
  calc ((pc w (π₀ ++ [v]) + L : ℚ) : WithTop ℚ) + δ
      ≤ ((pc w (π₀ ++ [v]) + L : ℚ) : WithTop ℚ) + ((pc w (v :: x :: r) : ℚ) : WithTop ℚ) :=
        add_le_add le_rfl h1
    _ = ((pc w (π₀ ++ [v]) + w v x + L : ℚ) : WithTop ℚ) + ((pc w (x :: r) : ℚ) : WithTop ℚ) := by
        rw [h2, ← WithTop.coe_add, ← WithTop.coe_add]; congr 1; ring

/-- **Pruning loses no leaf.** -/
theorem prune_ok {w : V → V → ℚ} {π₀ : List V} {v : V} {δ : WithTop ℚ}
    (hδ : IsDist G t₁ t₂ w π₀ v δ) (htop : δ = ⊤) (r : List V) :
    ¬ Cand G s t₁ t₂ (π₀ ++ v :: r) := by
  intro hP
  have := hδ.1 _ (cont_of_cand hP)
  rw [htop] at this
  exact WithTop.coe_ne_top (top_le_iff.mp this)

/-- **The bound is below the leaves.** -/
theorem bound_le_leaf {w : V → V → ℚ} {L : ℚ} {π₀ r : List V} {v : V} {δ : WithTop ℚ}
    (hδ : IsDist G t₁ t₂ w π₀ v δ) (hP : Cand G s t₁ t₂ (π₀ ++ v :: r)) :
    β w L π₀ v δ ≤ ((pc w (π₀ ++ v :: r) + L : ℚ) : WithTop ℚ) := by
  unfold β
  have := hδ.1 _ (cont_of_cand hP)
  calc ((pc w (π₀ ++ [v]) + L : ℚ) : WithTop ℚ) + δ
      ≤ ((pc w (π₀ ++ [v]) + L : ℚ) : WithTop ℚ) + ((pc w (v :: r) : ℚ) : WithTop ℚ) :=
        add_le_add le_rfl this
    _ = _ := by rw [← WithTop.coe_add, pc_join w v r π₀]; congr 1; ring

/-- **A node of small bound is a prefix of a candidate of small key.** -/
theorem extend_of_bound {w : V → V → ℚ} {L OPT : ℚ} {π₀ : List V} {v : V} {δ : WithTop ℚ}
    (hN : Node G s t₂ π₀ v) (hδ : IsDist G t₁ t₂ w π₀ v δ) (hβ : β w L π₀ v δ ≤ OPT) :
    ∃ r, Cand G s t₁ t₂ (π₀ ++ v :: r) ∧ pc w (π₀ ++ v :: r) + L ≤ OPT ∧
      π₀ ++ [v] <+: π₀ ++ v :: r := by
  have hne : δ ≠ ⊤ := by
    intro h; simp [β, h] at hβ
  obtain ⟨ρ, hρ, hd⟩ := hδ.2 hne
  obtain ⟨r, rfl⟩ : ∃ r, ρ = v :: r := by
    obtain ⟨hh, -⟩ := hρ.1
    cases ρ with
    | nil => simp at hh
    | cons y r => simp at hh; exact ⟨r, by rw [hh]⟩
  refine ⟨r, join hN hρ, ?_, ⟨r, by simp⟩⟩
  unfold β at hβ
  rw [← hd, ← WithTop.coe_add, WithTop.coe_le_coe] at hβ
  rw [pc_join]; linarith

/-! ## Counting the nodes of cost at most `OPT` -/

/-- **`T ≤ n N`.** If every good node is a nonempty prefix of one of the candidates in `S`, and
every candidate has at most `n` vertices, there are at most `n |S|` good nodes. -/
theorem card_good_le [DecidableEq V] (good S : Finset (List V)) (n : ℕ)
    (hpre : ∀ π ∈ good, π ≠ [] ∧ ∃ P ∈ S, π <+: P) (hlen : ∀ P ∈ S, P.length ≤ n) :
    good.card ≤ n * S.card := by
  have hsub : good ⊆ S.biUnion fun P => (Finset.range P.length).image fun i => P.take (i + 1) := by
    intro π hπ
    obtain ⟨hne, P, hP, hpre⟩ := hpre π hπ
    refine Finset.mem_biUnion.mpr ⟨P, hP, Finset.mem_image.mpr ⟨π.length - 1, ?_, ?_⟩⟩
    · have := hpre.length_le
      have : 0 < π.length := List.length_pos_iff.mpr hne
      simp; omega
    · have : 0 < π.length := List.length_pos_iff.mpr hne
      rw [Nat.sub_add_cancel this]
      exact (List.prefix_iff_eq_take.mp hpre).symm
  calc good.card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ P ∈ S, ((Finset.range P.length).image fun i => P.take (i + 1)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _P ∈ S, n := Finset.sum_le_sum fun P hP =>
        (Finset.card_image_le.trans (by simp)).trans (hlen P hP)
    _ = n * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- Candidates have at most `n` vertices. -/
theorem cand_length [Fintype V] {P : List V} (hP : Cand G s t₁ t₂ P) :
    P.length ≤ Fintype.card V := hP.1.2.2.2.length_le_card

/-! ## Binarization -/

section Binary

variable {k : ℕ} (f : Fin k → WithTop ℚ)

/-- The children below the node `(j, i)` of the binary tree: indices `c` with `c / 2^j = i`. -/
def block (j i : ℕ) : Finset (Fin k) := Finset.univ.filter fun c => c.val / 2 ^ j = i

/-- The cost of the node `(j, i)`: the minimum of the costs of the children below it. -/
def bcost (j i : ℕ) : WithTop ℚ := (block j i).inf f

theorem bcost_zero (c : Fin k) : bcost f 0 c.val = f c := by
  have : block (k := k) 0 c.val = {c} := by
    ext d; simp [block, Fin.val_inj]
  simp [bcost, this]

/-- The node `(j + 1, i)` has the two children `(j, 2i)` and `(j, 2i + 1)`. -/
theorem block_succ (j i : ℕ) :
    block (k := k) (j + 1) i = block j (2 * i) ∪ block j (2 * i + 1) := by
  ext c
  simp only [block, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  omega

/-- **Monotone along the binary tree.** -/
theorem bcost_mono (j i : ℕ) (b : ℕ) (hb : b < 2) : bcost f (j + 1) i ≤ bcost f j (2 * i + b) := by
  apply Finset.inf_mono
  rw [block_succ]
  interval_cases b
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

/-- The root `(D, 0)` covers all children if `k ≤ 2^D`. -/
theorem block_root {D : ℕ} (hk : k ≤ 2 ^ D) : block (k := k) D 0 = Finset.univ := by
  ext c
  simp only [block, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact Nat.div_eq_of_lt (lt_of_lt_of_le c.isLt hk)

/-- **Monotone from the parent.** A parent below all its children is below the root. -/
theorem parent_le_root {D : ℕ} (hk : k ≤ 2 ^ D) {x : WithTop ℚ} (hx : ∀ c, x ≤ f c) :
    x ≤ bcost f D 0 := by
  rw [bcost, block_root hk]; exact Finset.le_inf fun c _ => hx c

theorem exists_good_of_bcost {j i : ℕ} {T : ℚ} (h : bcost f j i ≤ T) :
    ∃ c ∈ block j i, f c ≤ T := by
  by_contra hne
  push Not at hne
  have : (T : WithTop ℚ) < bcost f j i := by
    rcases (block (k := k) j i).eq_empty_or_nonempty with he | hne'
    · simp [bcost, he]
    · obtain ⟨c, hc, hmin⟩ := Finset.exists_mem_eq_inf _ hne' f
      rw [bcost, hmin]; exact hne c hc
  exact absurd h (not_le.mpr this)

/-- **Count.** The inner nodes `(j, i)`, `1 ≤ j ≤ D`, of cost at most `T` number at most `D` times
the children of cost at most `T`. -/
theorem card_good_blocks (D : ℕ) (T : ℚ) :
    ∑ j ∈ Finset.range D, ((Finset.range k).filter fun i => bcost f (j + 1) i ≤ T).card ≤
      D * (Finset.univ.filter fun c => f c ≤ T).card := by
  have h : ∀ j, ((Finset.range k).filter fun i => bcost f (j + 1) i ≤ T).card ≤
      (Finset.univ.filter fun c => f c ≤ T).card := by
    intro j
    calc _ ≤ ((Finset.univ.filter fun c => f c ≤ T).image fun c : Fin k => c.val / 2 ^ (j + 1)).card := by
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_filter] at hi
          obtain ⟨c, hc, hfc⟩ := exists_good_of_bcost f hi.2
          simp only [block, Finset.mem_filter, Finset.mem_univ, true_and] at hc
          exact Finset.mem_image.mpr ⟨c, by simp [hfc], hc⟩
      _ ≤ _ := Finset.card_image_le
  calc _ ≤ ∑ _j ∈ Finset.range D, (Finset.univ.filter fun c => f c ≤ T).card :=
        Finset.sum_le_sum fun j _ => h j
    _ = _ := by simp

end Binary

/-- **Count over the whole tree.** Nodes with parents `par`; `good` are the nodes of cost at most
`OPT`; the binary tree of a node `π` adds `inner π` inner nodes of cost at most `OPT`, at most `D`
times its good children (`card_good_blocks`). Then the binarized tree has at most `(1 + D) |good|`
nodes of cost at most `OPT`. -/
theorem card_binarized {N : Type*} [DecidableEq N] (nodes good : Finset N) (par : N → Option N)
    (inner : N → ℕ) (D : ℕ)
    (hin : ∀ π ∈ nodes, inner π ≤ D * (good.filter fun x => par x = some π).card) :
    good.card + ∑ π ∈ nodes, inner π ≤ (1 + D) * good.card := by
  have hsum : ∑ π ∈ nodes, (good.filter fun x => par x = some π).card ≤ good.card := by
    rw [← Finset.card_biUnion]
    · exact Finset.card_le_card (Finset.biUnion_subset.mpr fun _ _ => Finset.filter_subset _ _)
    · intro a _ b _ hab
      rw [Function.onFun, Finset.disjoint_left]
      intro x hxa hxb
      simp only [Finset.mem_filter] at hxa hxb
      exact hab (Option.some_injective _ (hxa.2.symm.trans hxb.2))
  calc good.card + ∑ π ∈ nodes, inner π
      ≤ good.card + ∑ π ∈ nodes, D * (good.filter fun x => par x = some π).card :=
        Nat.add_le_add_left (Finset.sum_le_sum hin) _
    _ = good.card + D * ∑ π ∈ nodes, (good.filter fun x => par x = some π).card := by
        rw [Finset.mul_sum]
    _ ≤ good.card + D * good.card := Nat.add_le_add_left (Nat.mul_le_mul_left _ hsum) _
    _ = (1 + D) * good.card := by ring

/-! ## The query bound -/

/-- The guarantee of quantum branch-and-bound, as a stated hypothesis: on a tree with at most two
children per node, depth at most `d`, a cost that is monotone along the tree and exact at the
leaves, integer costs at most `c_max ≥ 2`, and at most `T` nodes of cost at most the optimum, the
search finds a leaf of minimum cost, except with probability `ε`, with at most
`K √T d^{3/2} log₂ c_max · pl(d, c_max)` queries. Here `queries T d c` is that number of queries,
`K` is a constant, and `pl d c ≥ 0` collects the factors polylogarithmic in `d`, `log c_max` and
`1/ε` (for a fixed `ε`), nondecreasing in `d`. A. Montanaro, Quantum speedup of branch-and-bound
algorithms, Physical Review Research 2, 013056 (2020), main theorem. -/
def QBBGuarantee (queries : ℕ → ℕ → ℕ → ℝ) (K : ℝ) (pl : ℕ → ℕ → ℝ) : Prop :=
  ∀ T d c : ℕ, 2 ≤ c →
    queries T d c ≤ K * Real.sqrt T * (d : ℝ) ^ (3 / 2 : ℝ) * Real.logb 2 c * pl d c

/-- **Query bound (arithmetic).** With the guarantee, the binarized tree (at most `(1 + D) T` good
nodes, depth at most `(n - 1) max(1, D)`, `T ≤ n N`) needs at most
`K √((1 + D) n N) ((n - 1) max(1, D))^{3/2} log₂ c_max · pl((n - 1) max(1, D), c_max)` queries, for
`c_max ≥ 2`. -/
theorem query_bound {queries : ℕ → ℕ → ℕ → ℝ} {K : ℝ} {pl : ℕ → ℕ → ℝ} (hK : 0 ≤ K)
    (hpl0 : ∀ d c, 0 ≤ pl d c) (hplm : ∀ c, Monotone fun d => pl d c)
    (hQ : QBBGuarantee queries K pl) {n N D T T' d' c : ℕ} (hc : 2 ≤ c)
    (hT : T ≤ n * N) (hT' : T' ≤ (1 + D) * T) (hd : d' ≤ (n - 1) * max 1 D) :
    queries T' d' c ≤ K * Real.sqrt ((1 + D) * (n * N)) * (((n - 1) * max 1 D : ℕ) : ℝ) ^ (3 / 2 : ℝ) *
      Real.logb 2 c * pl ((n - 1) * max 1 D) c := by
  refine (hQ T' d' c hc).trans ?_
  have hlog : 0 ≤ Real.logb 2 c := Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ c))
  have h1 : Real.sqrt T' ≤ Real.sqrt ((1 + D) * (n * N)) := by
    apply Real.sqrt_le_sqrt
    have : T' ≤ (1 + D) * (n * N) := hT'.trans (Nat.mul_le_mul_left _ hT)
    exact_mod_cast this
  have h2 : (d' : ℝ) ^ (3 / 2 : ℝ) ≤ (((n - 1) * max 1 D : ℕ) : ℝ) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hd) (by norm_num)
  have h3 : pl d' c ≤ pl ((n - 1) * max 1 D) c := hplm c hd
  have h4 := mul_le_mul (mul_le_mul_of_nonneg_left h1 hK) h2 (by positivity)
    (mul_nonneg hK (Real.sqrt_nonneg _))
  have h5 := mul_le_mul_of_nonneg_right h4 hlog
  exact mul_le_mul h5 h3 (hpl0 _ _) (mul_nonneg (mul_nonneg (mul_nonneg hK (Real.sqrt_nonneg _))
    (by positivity)) hlog)

end RiskRouting.BB
