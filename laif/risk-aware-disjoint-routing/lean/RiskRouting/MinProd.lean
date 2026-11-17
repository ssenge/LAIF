import Mathlib

/-!
# Min-prod disjoint paths is NP-hard

Paths are vertex lists. A pair of paths with common ends is internally vertex-disjoint when every
common vertex is an end. The min-min problem asks for two such paths from `s` to `t` with the shorter
one of at most `ℓ` links; the min-prod problem asks for two such paths with
`(|P₁| + C) (|P₂| + C) ≤ K`, where `|P|` is the number of links.

The reduction adds a vertex `t*`, the link `t t*`, and for every neighbour `u ≠ s` of `t` a chain of
`M = ⌈(n + C + 2)²⌉` links from `u` to `t*`. In the version with two terminals the link `t t*` is
left out, and the terminals are `t` and `t*`.

- `minMin_iff_minProd`: min-min with bound `ℓ ≤ n - 1` holds iff the gadget has a min-prod pair of
  value at most `(ℓ + 1 + C)(n - 2 + M + C)`.
- `minMin_iff_minProd₂`: the same for two terminals with `(ℓ + C)(n - 2 + M + C)`.
- `card_gadget`, `card_gadget_le`: the gadget has `n + 1 + n (M - 1)` vertices, at most
  `n + 1 + n (n + C + 2)²`.
- `paper_inequalities`: the inequalities between `M`, `n`, `ℓ` and `C` that the proof uses.
- `route_unit_iff_minProd₂`: with unit latencies and a uniform joint failure probability `q`, the
  routing objective is `Bq (|P₁| + C)(|P₂| + C) - C` with `C = 1 / (Bq)`.
- `reduction_minProd`, `reduction_minProd₂`, `reduction_route`: the reductions as maps of
  instances, with the same answer and an explicit polynomial bound on the number of vertices.
-/

namespace RiskRouting

open List

section Paths

variable {W : Type*}

/-- `p` is a simple path from `a` to `b` for the adjacency relation `R`. -/
def IsPathL (R : W → W → Prop) (p : List W) (a b : W) : Prop :=
  p.head? = some a ∧ p.getLast? = some b ∧ p.IsChain R ∧ p.Nodup

/-- The number of links of a path. -/
def links (p : List W) : ℕ := p.length - 1

/-- Two paths meet only in `a` or `b`. -/
def Disj (p₁ p₂ : List W) (a b : W) : Prop := ∀ x, x ∈ p₁ → x ∈ p₂ → x = a ∨ x = b

theorem mem_of_head {p : List W} {a : W} (h : p.head? = some a) : a ∈ p := by
  cases p with
  | nil => simp at h
  | cons x p => simp at h; simp [h]

theorem mem_of_last {p : List W} {a : W} (h : p.getLast? = some a) : a ∈ p := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp h
  simp

theorem eq_pair_of_length_two {R : W → W → Prop} {p : List W} {a b : W} (hp : IsPathL R p a b)
    (h2 : p.length = 2) : p = [a, b] := by
  match p, h2, hp with
  | [x, y], _, hp =>
    obtain ⟨h1, h2, -, -⟩ := hp
    simp at h1 h2
    simp [h1, h2]

theorem two_le_length {R : W → W → Prop} {p : List W} {a b : W} (hp : IsPathL R p a b)
    (hab : a ≠ b) : 2 ≤ p.length := by
  match p, hp with
  | [], hp => simp [IsPathL] at hp
  | [x], hp =>
    obtain ⟨h1, h2, -, -⟩ := hp
    simp at h1 h2
    exact absurd (h1.symm.trans h2) hab
  | _ :: _ :: _, _ => simp

theorem getLast_cons_snoc (x b : W) (l : List W) : (x :: (l ++ [b])).getLast? = some b := by
  rw [← List.cons_append, List.getLast?_append]; simp

theorem shape_of_three {p : List W} {a b : W} (ha : p.head? = some a) (hb : p.getLast? = some b)
    (h3 : 3 ≤ p.length) : ∃ m u, p = a :: (m ++ [u, b]) := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hb
  rcases List.eq_nil_or_concat ys with rfl | ⟨L, u, rfl⟩
  · simp at h3
  cases L with
  | nil => simp at h3
  | cons x L' =>
    simp at ha
    subst ha
    exact ⟨L', u, by simp⟩

end Paths

section Problems

variable {V : Type*}

/-- Min-min, decision version: two internally vertex-disjoint paths from `s` to `t`, one of them
with at most `ℓ` links. -/
def MinMinYes (G : SimpleGraph V) (s t : V) (ℓ : ℕ) : Prop :=
  ∃ p₁ p₂, IsPathL G.Adj p₁ s t ∧ IsPathL G.Adj p₂ s t ∧ p₁ ≠ p₂ ∧ Disj p₁ p₂ s t ∧ links p₁ ≤ ℓ

/-- Min-prod, decision version: two internally vertex-disjoint paths from `a` to `b` with
`(|P₁| + C)(|P₂| + C) ≤ K`. -/
def MinProdYes {W : Type*} (H : SimpleGraph W) (a b : W) (C K : ℚ) : Prop :=
  ∃ p₁ p₂, IsPathL H.Adj p₁ a b ∧ IsPathL H.Adj p₂ a b ∧ p₁ ≠ p₂ ∧ Disj p₁ p₂ a b ∧
    ((links p₁ : ℚ) + C) * ((links p₂ : ℚ) + C) ≤ K

/-- Min-prod with two terminals: paths from `a` to `b₁` and from `a` to `b₂` that meet only in
`a`, with `(|P₁| + C)(|P₂| + C) ≤ K`. -/
def MinProd₂Yes {W : Type*} (H : SimpleGraph W) (a b₁ b₂ : W) (C K : ℚ) : Prop :=
  ∃ p₁ p₂, IsPathL H.Adj p₁ a b₁ ∧ IsPathL H.Adj p₂ a b₂ ∧ (∀ x, x ∈ p₁ → x ∈ p₂ → x = a) ∧
    ((links p₁ : ℚ) + C) * ((links p₂ : ℚ) + C) ≤ K

end Problems

/-! ## The gadget -/

/-- Vertices of the gadget: the old vertices, `t*`, and `K` inner vertices for each chain. -/
inductive GV (V : Type*) (K : ℕ) where
  | old : V → GV V K
  | sink : GV V K
  | mid : V → Fin K → GV V K
  deriving DecidableEq

namespace GV

variable {V : Type*} {K : ℕ}

/-- The vertices of the gadget as a sum type. -/
def equivSum : GV V K ≃ V ⊕ Unit ⊕ V × Fin K where
  toFun
    | old a => Sum.inl a
    | sink => Sum.inr (Sum.inl ())
    | mid u i => Sum.inr (Sum.inr (u, i))
  invFun
    | Sum.inl a => old a
    | Sum.inr (Sum.inl _) => sink
    | Sum.inr (Sum.inr (u, i)) => mid u i
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with a | _ | ⟨u, i⟩ <;> rfl

instance [Fintype V] : Fintype (GV V K) := Fintype.ofEquiv _ equivSum.symm

theorem card [Fintype V] : Fintype.card (GV V K) = Fintype.card V + 1 + Fintype.card V * K := by
  rw [Fintype.card_congr (equivSum (V := V) (K := K))]
  simp [Fintype.card_sum, Fintype.card_prod]
  omega

theorem old_injective : Function.Injective (old : V → GV V K) := fun _ _ h => by cases h; rfl

end GV

open GV

variable {V : Type*}

/-- Adjacency of the gadget. The link `t t*` is present iff `e`; the chain of a neighbour `u ≠ s`
of `t` is `u, mid u 0, …, mid u (K - 1), t*`. -/
def gadj (G : SimpleGraph V) (s t : V) (e : Bool) (K : ℕ) : GV V K → GV V K → Prop
  | old a, old b => G.Adj a b
  | old a, sink => e = true ∧ a = t
  | sink, old a => e = true ∧ a = t
  | old a, mid u i => G.Adj u t ∧ u ≠ s ∧ a = u ∧ i.val = 0
  | mid u i, old a => G.Adj u t ∧ u ≠ s ∧ a = u ∧ i.val = 0
  | mid u i, mid v j => u = v ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val)
  | mid _ i, sink => i.val + 1 = K
  | sink, mid _ i => i.val + 1 = K
  | sink, sink => False

/-- The gadget graph. -/
def gadget (G : SimpleGraph V) (s t : V) (e : Bool) (K : ℕ) : SimpleGraph (GV V K) where
  Adj := gadj G s t e K
  symm := ⟨by
    intro x y h
    cases x with
    | old a => cases y with
      | old b => exact (show G.Adj a b from h).symm
      | sink => exact h
      | mid v j => exact h
    | sink => cases y with
      | old b => exact h
      | sink => exact h
      | mid v j => exact h
    | mid u i => cases y with
      | old b => exact h
      | sink => exact h
      | mid v j => exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by
    intro x h
    cases x with
    | old a => exact G.irrefl (show G.Adj a a from h)
    | sink => exact h
    | mid u i => exact absurd h.2 (by omega)⟩

variable (G : SimpleGraph V) (s t : V) (e : Bool) (K : ℕ)

/-- Once a path enters the chain of `u`, it follows it to `t*`. -/
theorem follow (u : V) : ∀ (L : List (GV V K)) (i : Fin K) (prev : GV V K),
    (prev :: mid u i :: L).IsChain (gadj G s t e K) → (prev :: mid u i :: L).Nodup →
    (prev = old u ∨ ∃ j : Fin K, prev = mid u j ∧ j.val + 1 = i.val) →
    (∀ x, (mid u i :: L).getLast? = some x → x = sink ∨ ∃ b, x = old b) →
    ∃ L₁ L₂, L = L₁ ++ sink :: L₂ ∧ L₁.length + i.val + 1 = K
  | [], i, prev, _, _, _, hl => by
      exfalso
      rcases hl (mid u i) (by simp) with h | ⟨b, h⟩ <;> cases h
  | y :: L, i, prev, hc, hn, hp, hl => by
      rw [isChain_cons_cons, isChain_cons_cons] at hc
      obtain ⟨hpi, hiy, hc'⟩ := hc
      cases y with
      | old a =>
        exfalso
        obtain ⟨-, -, hau, hi0⟩ := (hiy : G.Adj u t ∧ u ≠ s ∧ a = u ∧ i.val = 0)
        rcases hp with rfl | ⟨j, rfl, hj⟩
        · subst hau
          simp [List.nodup_cons] at hn
        · omega
      | sink =>
        have hiy' : i.val + 1 = K := hiy
        exact ⟨[], L, rfl, by simp; omega⟩
      | mid v j =>
        obtain ⟨rfl, hij | hji⟩ := (hiy : u = v ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val))
        · obtain ⟨L₁, L₂, hL, hlen⟩ := follow u L j (mid u i)
            (isChain_cons_cons.mpr ⟨⟨rfl, Or.inl hij⟩, hc'⟩) hn.of_cons (Or.inr ⟨i, rfl, hij⟩)
            (fun x hx => hl x (by rw [getLast?_cons_cons]; exact hx))
          exact ⟨mid u j :: L₁, L₂, by simp [hL], by simp; omega⟩
        · exfalso
          rcases hp with rfl | ⟨j', rfl, hj'⟩
          · exact absurd (hpi : G.Adj u t ∧ u ≠ s ∧ u = u ∧ i.val = 0).2.2.2 (by omega)
          · have : j' = j := Fin.ext (by omega)
            subst this
            simp [List.nodup_cons] at hn

/-- A path that starts at an old vertex and ends at an old vertex or at `t*` is a path of `G`
followed by nothing, by the link to `t*`, or by a chain. -/
theorem split_old : ∀ (p : List (GV V K)) (a : V),
    (old a :: p).IsChain (gadj G s t e K) → (old a :: p).Nodup →
    (∀ x, (old a :: p).getLast? = some x → x = sink ∨ ∃ b, x = old b) →
    ∃ (q : List V) (rest : List (GV V K)), old a :: p = q.map old ++ rest ∧ q.head? = some a ∧
      q.IsChain G.Adj ∧
      (rest = [] ∨ (e = true ∧ q.getLast? = some t ∧ sink ∈ rest) ∨
        ∃ u, q.getLast? = some u ∧ G.Adj u t ∧ u ≠ s ∧ K + 1 ≤ rest.length ∧ sink ∈ rest)
  | [], a, _, _, _ => ⟨[a], [], by simp, rfl, isChain_singleton a, Or.inl rfl⟩
  | y :: p, a, hc, hn, hl => by
      have hc0 := hc
      rw [isChain_cons_cons] at hc
      obtain ⟨hay, hc'⟩ := hc
      cases y with
      | old b =>
        obtain ⟨q, rest, hq, hh, hqc, hcase⟩ := split_old p b hc' hn.of_cons
          (fun x hx => hl x (by rw [getLast?_cons_cons]; exact hx))
        cases q with
        | nil => simp at hh
        | cons b' q' =>
          simp at hh
          subst hh
          refine ⟨a :: b' :: q', rest, by simp [hq], rfl,
            isChain_cons_cons.mpr ⟨(show G.Adj a b' from hay), hqc⟩, ?_⟩
          rw [getLast?_cons_cons]
          exact hcase
      | sink =>
        obtain ⟨he, hat⟩ := (hay : e = true ∧ a = t)
        exact ⟨[a], sink :: p, by simp, rfl, isChain_singleton a,
          Or.inr (Or.inl ⟨he, by simp [hat], by simp⟩)⟩
      | mid u i =>
        obtain ⟨hut, hus, hau, hi⟩ := (hay : G.Adj u t ∧ u ≠ s ∧ a = u ∧ i.val = 0)
        obtain ⟨L₁, L₂, hL, hlen⟩ := follow G s t e K u p i (old a) hc0 hn (Or.inl (by rw [hau]))
          (fun x hx => hl x (by rw [getLast?_cons_cons]; exact hx))
        refine ⟨[a], mid u i :: p, by simp, rfl, isChain_singleton a,
          Or.inr (Or.inr ⟨u, by simp [hau], hut, hus, ?_, ?_⟩)⟩
        · rw [hL]; simp; omega
        · rw [hL]; simp

/-- The chain of `u` from `mid u i` to `t*`. -/
theorem chain_path (u : V) (hu : G.Adj u t) : ∀ (n : ℕ) (i : Fin K), i.val + n + 1 = K →
    ∃ L : List (GV V K), (mid u i :: L).IsChain (gadj G s t e K) ∧ (mid u i :: L).Nodup ∧
      (mid u i :: L).getLast? = some sink ∧ L.length = n + 1 ∧
      ∀ x ∈ L, x = sink ∨ ∃ j : Fin K, i.val < j.val ∧ x = mid u j
  | 0, i, h => ⟨[sink], isChain_pair.mpr (show i.val + 1 = K by omega), by simp, by simp, by simp,
      by simp⟩
  | n + 1, i, h => by
      obtain ⟨L, hc, hn, hl, hlen, hm⟩ := chain_path u hu n ⟨i.val + 1, by omega⟩ (by simp; omega)
      refine ⟨mid u ⟨i.val + 1, by omega⟩ :: L, isChain_cons_cons.mpr ⟨⟨rfl, Or.inl rfl⟩, hc⟩,
        ?_, by rw [getLast?_cons_cons]; exact hl, by simp [hlen], ?_⟩
      · refine List.nodup_cons.mpr ⟨?_, hn⟩
        intro hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with h1 | h1
        · simp only [mid.injEq, true_and] at h1
          have := congrArg Fin.val h1
          simp at this
        · rcases hm _ h1 with h2 | ⟨j, hj, h2⟩
          · cases h2
          · cases h2
            exact absurd hj (by simp)
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact Or.inr ⟨_, by simp, rfl⟩
        · rcases hm x hx with h2 | ⟨j, hj, h2⟩
          · exact Or.inl h2
          · exact Or.inr ⟨j, by simp at hj; omega, h2⟩

/-! ## Inequalities -/

/-- The chain length `M = ⌈(n + C + 2)²⌉`. -/
noncomputable def chainLen (n : ℕ) (C : ℚ) : ℕ := ⌈((n : ℚ) + C + 2) ^ 2⌉₊

theorem chainLen_ge (n : ℕ) (C : ℚ) : ((n : ℚ) + C + 2) ^ 2 ≤ chainLen n C := Nat.le_ceil _

theorem one_le_chainLen (n : ℕ) {C : ℚ} (hC : 0 ≤ C) : 1 ≤ chainLen n C := by
  have h := chainLen_ge n C
  have h0 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  have : (1 : ℚ) ≤ chainLen n C := by nlinarith
  exact_mod_cast this

/-- The inequalities of the proof, with `M = chainLen n C`. -/
theorem paper_inequalities (n ℓ : ℕ) {C : ℚ} (hC : 0 ≤ C) (hn : 2 ≤ n) (hℓ : ℓ ≤ n - 1) :
    let M : ℚ := chainLen n C
    (n : ℚ) < M + C ∧ 2 * ((n : ℚ) + C) < ((n : ℚ) + C + 2) ^ 2 ∧
      ((n : ℚ) + C + 2) ^ 2 ≤ M + C ∧
      0 < (M + C) - ((ℓ : ℚ) + 1 + C) * ((n : ℚ) - 2) ∧
      ((ℓ : ℚ) + 1 + C) * ((n : ℚ) - 2 + M + C) < (M + C) ^ 2 := by
  intro M
  have hM : ((n : ℚ) + C + 2) ^ 2 ≤ M := chainLen_ge n C
  have hn' : (2 : ℚ) ≤ n := by exact_mod_cast hn
  have hℓ' : (ℓ : ℚ) + 1 ≤ n := by
    have : ℓ + 1 ≤ n := by omega
    exact_mod_cast this
  set m : ℚ := (n : ℚ) + C with hm
  set x : ℚ := M + C with hx
  have hm0 : 0 ≤ m := by linarith
  have hM0 : 0 ≤ M := le_trans (sq_nonneg _) hM
  have hxm : (m + 2) ^ 2 ≤ x := by rw [hx]; nlinarith
  have ha : (ℓ : ℚ) + 1 + C ≤ m := by linarith
  have ha0 : 0 ≤ (ℓ : ℚ) + 1 + C := by positivity
  have h1 : ((ℓ : ℚ) + 1 + C) * ((n : ℚ) - 2) ≤ m * m :=
    mul_le_mul ha (by linarith) (by linarith) hm0
  have h2 : ((ℓ : ℚ) + 1 + C) * ((n : ℚ) - 2 + M + C) ≤ m * (m + x) :=
    mul_le_mul ha (by linarith) (by linarith) hm0
  refine ⟨by nlinarith, by nlinarith, by linarith, by nlinarith, ?_⟩
  have h3 : m * (m + x) < x ^ 2 := by nlinarith
  linarith

/-! ## The reduction, one terminal -/

section OneTerminal

variable [Fintype V] (C : ℚ)

/-- Number of inner vertices of a chain, `M - 1`. -/
noncomputable def innerLen : ℕ := chainLen (Fintype.card V) C - 1

/-- The min-prod threshold for min-min bound `ℓ`. -/
noncomputable def threshold (ℓ : ℕ) : ℚ :=
  ((ℓ : ℚ) + 1 + C) * ((Fintype.card V : ℚ) - 2 + chainLen (Fintype.card V) C + C)

/-- The min-prod threshold for two terminals. -/
noncomputable def threshold₂ (ℓ : ℕ) : ℚ :=
  ((ℓ : ℚ) + C) * ((Fintype.card V : ℚ) - 2 + chainLen (Fintype.card V) C + C)

end OneTerminal

theorem links_le_card [Fintype V] {R : V → V → Prop} {p : List V} {a b : V} (hp : IsPathL R p a b) :
    links p ≤ Fintype.card V - 1 := by
  have := hp.2.2.2.length_le_card
  unfold links; omega

theorem links_map_old {K : ℕ} (q : List V) : links (q.map (old : V → GV V K)) = links q := by
  simp [links]

/-- From a path `s :: m ++ [u, t]` of `G`, a path of the gadget through the chain of `u`. -/
theorem chain_pair_path [Fintype V] (hK : 1 ≤ K) {m : List V} {u : V}
    (hp : IsPathL G.Adj (s :: (m ++ [u, t])) s t) :
    ∃ B : List (GV V K), IsPathL (gadj G s t e K) B (old s) sink ∧
      links B = links (s :: (m ++ [u, t])) + K ∧
      (∀ x ∈ B, (∃ y, x = old y ∧ y ∈ s :: (m ++ [u])) ∨ x = sink ∨ ∃ j, x = mid u j) := by
  obtain ⟨-, -, hc, hn⟩ := hp
  have hsplit : s :: (m ++ [u, t]) = (s :: (m ++ [u])) ++ [t] := by simp
  rw [hsplit] at hc hn
  rw [isChain_append] at hc
  obtain ⟨hcq, -, hut⟩ := hc
  have hut' : G.Adj u t := hut u (by rw [getLast_cons_snoc]; rfl) t (by simp)
  have hus : u ≠ s := by
    intro h; subst h
    simp [List.nodup_append] at hn
  rw [List.nodup_append] at hn
  obtain ⟨hnq, -, -⟩ := hn
  obtain ⟨L, hcL, hnL, hlL, hlen, hmL⟩ :=
    chain_path G s t e K u hut' (K - 1) ⟨0, by omega⟩ (by simp; omega)
  refine ⟨(s :: (m ++ [u])).map old ++ mid u ⟨0, by omega⟩ :: L, ⟨by simp, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [getLast?_append]
    have : (mid u ⟨0, by omega⟩ :: L).getLast? = some sink := hlL
    rw [this]; rfl
  · rw [isChain_append]
    refine ⟨(isChain_map _).mpr (hcq.imp fun a b h => h), hcL, ?_⟩
    intro x hx y hy
    rw [getLast?_map, getLast_cons_snoc] at hx
    simp at hx hy
    subst hx hy
    exact ⟨hut', hus, rfl, rfl⟩
  · rw [List.nodup_append]
    refine ⟨hnq.map old_injective, hnL, ?_⟩
    intro x hx y hy hxy
    simp only [List.mem_map] at hx
    obtain ⟨z, -, rfl⟩ := hx
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · cases hxy
    · rcases hmL y hy with rfl | ⟨j, -, rfl⟩ <;> cases hxy
  · simp [links, hlen]; omega
  · intro x hx
    simp only [List.mem_append, List.mem_map, List.mem_cons] at hx
    rcases hx with ⟨y, hy, rfl⟩ | rfl | hx
    · exact Or.inl ⟨y, rfl, by simpa using hy⟩
    · exact Or.inr (Or.inr ⟨_, rfl⟩)
    · rcases hmL x hx with h | ⟨j, -, h⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨j, h⟩)

/-- A pair of `G` can be ordered so that the second path has at least two links. -/
theorem order_pair {p₁ p₂ : List V} (hst : s ≠ t) (h₁ : IsPathL G.Adj p₁ s t)
    (h₂ : IsPathL G.Adj p₂ s t) (hne : p₁ ≠ p₂) :
    3 ≤ p₂.length ∨ (3 ≤ p₁.length ∧ links p₂ ≤ links p₁) := by
  have a1 := two_le_length h₁ hst
  have a2 := two_le_length h₂ hst
  by_cases h : 3 ≤ p₂.length
  · exact Or.inl h
  · right
    have e2 : p₂.length = 2 := by omega
    refine ⟨?_, by unfold links; omega⟩
    by_contra h'
    have e1 : p₁.length = 2 := by omega
    exact hne ((eq_pair_of_length_two h₁ e1).trans (eq_pair_of_length_two h₂ e2).symm)

/-- Backward step, mixed case: the first path ends with `t t*`, the second with a chain. -/
theorem mixed_case {A B : List (GV V K)} {qA qB : List V} {rA rB : List (GV V K)} {u : V}
    (hst : s ≠ t) (hA : A = qA.map old ++ rA) (hB : B = qB.map old ++ rB)
    (hnA : A.Nodup) (hnB : B.Nodup) (hD : Disj A B (old s) sink)
    (hqA : qA.head? = some s) (hcA : qA.IsChain G.Adj) (hlA : qA.getLast? = some t)
    (hqB : qB.head? = some s) (hcB : qB.IsChain G.Adj) (hlB : qB.getLast? = some u)
    (hut : G.Adj u t) (hus : u ≠ s) :
    IsPathL G.Adj qA s t ∧ IsPathL G.Adj (qB ++ [t]) s t ∧ qA ≠ qB ++ [t] ∧
      Disj qA (qB ++ [t]) s t := by
  subst hA hB
  have common : ∀ y, y ∈ qA → y ∈ qB → y = s := by
    intro y hyA hyB
    rcases hD (old y) (by simp [hyA]) (by simp [hyB]) with h | h
    · exact old_injective h
    · cases h
  have hnqA : qA.Nodup := ((List.nodup_append.mp hnA).1).of_map _
  have hnqB : qB.Nodup := ((List.nodup_append.mp hnB).1).of_map _
  have htB : t ∉ qB := fun h => hst (common t (mem_of_last hlA) h).symm
  have huA : u ∉ qA := fun h => hus (common u h (mem_of_last hlB))
  refine ⟨⟨hqA, hlA, hcA, hnqA⟩, ⟨?_, by simp, ?_, ?_⟩, ?_, ?_⟩
  · cases qB with
    | nil => simp at hqB
    | cons x xs => simpa using hqB
  · rw [isChain_append]
    refine ⟨hcB, isChain_singleton t, ?_⟩
    intro x hx y hy
    rw [hlB] at hx
    simp at hx hy
    subst hx hy
    exact hut
  · rw [List.nodup_append]
    refine ⟨hnqB, by simp, ?_⟩
    intro x hx y hy hxy
    simp at hy
    subst hy hxy
    exact htB hx
  · intro h
    exact huA (h ▸ (by simp [mem_of_last hlB]))
  · intro x hxA hxB
    simp only [List.mem_append, List.mem_singleton] at hxB
    rcases hxB with h | h
    · exact Or.inl (common x hxA h)
    · exact Or.inr h

theorem links_ge_of_rest {q : List V} {r : List (GV V K)} (hr : r ≠ []) :
    q.length ≤ links (q.map old ++ r) := by
  have : 1 ≤ r.length := by
    cases r with
    | nil => exact absurd rfl hr
    | cons _ _ => simp
  simp [links]; omega

theorem links_ge_of_chain {q : List V} {r : List (GV V K)} (hq : q ≠ []) (hr : K + 1 ≤ r.length) :
    K + 1 ≤ links (q.map old ++ r) := by
  have : 1 ≤ q.length := by
    cases q with
    | nil => exact absurd rfl hq
    | cons _ _ => simp
  simp [links]; omega

/-- Decomposition of a path of the gadget from `old s` to `t*`. -/
theorem decomp_star {B : List (GV V K)} (hB : IsPathL (gadj G s t e K) B (old s) sink) :
    ∃ (q : List V) (r : List (GV V K)), B = q.map old ++ r ∧ q.head? = some s ∧
      q.IsChain G.Adj ∧ q ≠ [] ∧
      ((e = true ∧ q.getLast? = some t ∧ r ≠ []) ∨
        ∃ u, q.getLast? = some u ∧ G.Adj u t ∧ u ≠ s ∧ K + 1 ≤ r.length) := by
  obtain ⟨hh, hl, hc, hn⟩ := hB
  cases B with
  | nil => simp at hh
  | cons x p =>
    simp at hh
    subst hh
    obtain ⟨q, r, hq, hqh, hqc, hcase⟩ := split_old G s t e K p s hc hn
      (fun x hx => Or.inl (by rw [hl] at hx; exact (Option.some.inj hx).symm))
    have hqne : q ≠ [] := by rintro rfl; simp at hqh
    refine ⟨q, r, hq, hqh, hqc, hqne, ?_⟩
    rcases hcase with rfl | ⟨he, hlt, hr⟩ | ⟨u, h1, h2, h3, h4, -⟩
    · exfalso
      rw [hq] at hl
      simp at hl
    · exact Or.inl ⟨he, hlt, List.ne_nil_of_mem hr⟩
    · exact Or.inr ⟨u, h1, h2, h3, h4⟩

theorem cost_mono {a b a' b' C : ℚ} (hC : 0 ≤ C) (ha : 0 ≤ a') (hb : 0 ≤ b') (h1 : a' ≤ a)
    (h2 : b' ≤ b) : (a' + C) * (b' + C) ≤ (a + C) * (b + C) :=
  mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)

/-- **Theorem (one terminal).** For `ℓ ≤ n - 1` and `s ≠ t`, min-min with bound `ℓ` holds iff the
gadget with the link `t t*` has a min-prod pair from `s` to `t*` of value at most
`(ℓ + 1 + C)(n - 2 + M + C)`. -/
theorem minMin_iff_minProd [Fintype V] {C : ℚ} (hC : 0 ≤ C) (hst : s ≠ t) (ℓ : ℕ)
    (hℓ : ℓ ≤ Fintype.card V - 1) :
    MinMinYes G s t ℓ ↔
      MinProdYes (gadget G s t true (innerLen (V := V) C)) (old s) sink C (threshold (V := V) C ℓ) := by
  have hM : chainLen (Fintype.card V) C = innerLen (V := V) C + 1 := by
    have := one_le_chainLen (Fintype.card V) hC; unfold innerLen; omega
  have hK1 : 1 ≤ innerLen (V := V) C := by
    have h := chainLen_ge (Fintype.card V) C
    have h0 : (0 : ℚ) ≤ Fintype.card V := Nat.cast_nonneg _
    have : (4 : ℚ) ≤ chainLen (Fintype.card V) C := by nlinarith
    have : 4 ≤ chainLen (Fintype.card V) C := by exact_mod_cast this
    omega
  have hn2 : 2 ≤ Fintype.card V := by
    have := Fintype.card_le_of_injective (fun b : Bool => if b then s else t)
      (by intro a b h; cases a <;> cases b <;> simp_all [eq_comm])
    simpa using this
  obtain ⟨-, -, -, hI1, hI2⟩ := paper_inequalities (Fintype.card V) ℓ hC hn2 hℓ
  rw [hM] at hI1 hI2
  push_cast at hI1 hI2
  have hthr : threshold (V := V) C ℓ =
      ((ℓ : ℚ) + 1 + C) * ((Fintype.card V : ℚ) - 2 + ((innerLen (V := V) C : ℚ) + 1) + C) := by
    rw [threshold, hM]; push_cast; ring
  generalize innerLen (V := V) C = K at hK1 hI1 hI2 hthr ⊢
  rw [hthr]
  constructor
  · rintro ⟨p₁, p₂, h₁, h₂, hne, hD, hl⟩
    have key : ∀ P₁ P₂ : List V, IsPathL G.Adj P₁ s t → IsPathL G.Adj P₂ s t → Disj P₁ P₂ s t →
        links P₁ ≤ ℓ → 3 ≤ P₂.length →
        MinProdYes (gadget G s t true K) (old s) sink C
          (((ℓ : ℚ) + 1 + C) * ((Fintype.card V : ℚ) - 2 + ((K : ℚ) + 1) + C)) := by
      intro P₁ P₂ h₁ h₂ hD hl h3
      obtain ⟨m, u, rfl⟩ := shape_of_three h₂.1 h₂.2.1 h3
      obtain ⟨B, hB, hlB, hmB⟩ := chain_pair_path G s t true K hK1 h₂
      have htq : t ∉ s :: (m ++ [u]) := by
        have hn := h₂.2.2.2
        have : s :: (m ++ [u, t]) = (s :: (m ++ [u])) ++ [t] := by simp
        rw [this, List.nodup_append] at hn
        exact fun h => hn.2.2 t h t (by simp) rfl
      refine ⟨P₁.map old ++ [sink], B, ⟨?_, by simp, ?_, ?_⟩, hB, ?_, ?_, ?_⟩
      · cases P₁ with
        | nil => simp [IsPathL] at h₁
        | cons x xs => simpa using h₁.1
      · rw [isChain_append]
        refine ⟨(isChain_map _).mpr (h₁.2.2.1.imp fun a b h => h), isChain_singleton _, ?_⟩
        intro x hx y hy
        rw [getLast?_map, h₁.2.1] at hx
        simp at hx hy
        subst hx hy
        exact ⟨rfl, rfl⟩
      · rw [List.nodup_append]
        refine ⟨h₁.2.2.2.map old_injective, by simp, ?_⟩
        intro x hx y hy hxy
        simp at hx hy
        obtain ⟨z, -, rfl⟩ := hx
        subst hy
        cases hxy
      · intro h
        have : old t ∈ B := h ▸ (by simp [mem_of_last h₁.2.1])
        rcases hmB _ this with ⟨y, hy, hy'⟩ | h' | ⟨j, h'⟩
        · exact htq (old_injective hy ▸ hy')
        · cases h'
        · cases h'
      · intro x hxA hxB
        simp only [List.mem_append, List.mem_map, List.mem_singleton] at hxA
        rcases hxA with ⟨y, hyA, rfl⟩ | rfl
        · rcases hmB _ hxB with ⟨z, hz, hz'⟩ | h' | ⟨j, h'⟩
          · have hzy := old_injective hz
            subst hzy
            have hzB : y ∈ s :: (m ++ [u, t]) := by
              simp only [List.mem_cons, List.mem_append] at hz' ⊢
              tauto
            rcases hD y hyA hzB with h | h
            · exact Or.inl (by rw [h])
            · exact absurd (h ▸ hz') htq
          · cases h'
          · cases h'
        · exact Or.inr rfl
      · have e1 : links (P₁.map old ++ [sink] : List (GV V K)) = links P₁ + 1 := by
          have := two_le_length h₁ hst
          simp [links]; omega
        rw [e1, hlB]
        have hl2 := links_le_card h₂
        have c1 : ((links P₁ + 1 : ℕ) : ℚ) ≤ (ℓ : ℚ) + 1 := by
          exact_mod_cast (by omega : links P₁ + 1 ≤ ℓ + 1)
        have c2 : ((links (s :: (m ++ [u, t])) + K : ℕ) : ℚ) ≤
            (Fintype.card V : ℚ) - 2 + ((K : ℚ) + 1) := by
          have h' : links (s :: (m ++ [u, t])) + K + 1 ≤ Fintype.card V + K := by omega
          have : ((links (s :: (m ++ [u, t])) + K + 1 : ℕ) : ℚ) ≤ ((Fintype.card V + K : ℕ) : ℚ) := by
            exact_mod_cast h'
          push_cast at this ⊢; linarith
        have := cost_mono hC (by positivity) (by positivity) c1 c2
        push_cast at this ⊢
        linarith
    rcases order_pair G s t hst h₁ h₂ hne with h3 | ⟨h3, hle⟩
    · exact key p₁ p₂ h₁ h₂ hD hl h3
    · exact key p₂ p₁ h₂ h₁ (fun x a b => hD x b a) (le_trans hle hl) h3
  · rintro ⟨A, B, hA, hB, hne, hD, hcost⟩
    obtain ⟨qA, rA, eA, hqA, hcA, hneA, cA⟩ := decomp_star G s t true K hA
    obtain ⟨qB, rB, eB, hqB, hcB, hneB, cB⟩ := decomp_star G s t true K hB
    have mixed : ∀ (A B : List (GV V K)) (qA qB : List V) (rA rB : List (GV V K)) (u : V),
        A = qA.map old ++ rA → B = qB.map old ++ rB → A.Nodup → B.Nodup →
        Disj A B (old s) sink →
        qA.head? = some s → qA.IsChain G.Adj → qA.getLast? = some t → rA ≠ [] →
        qB.head? = some s → qB.IsChain G.Adj → qB.getLast? = some u → G.Adj u t → u ≠ s →
        K + 1 ≤ rB.length →
        ((links A : ℚ) + C) * ((links B : ℚ) + C) ≤
          ((ℓ : ℚ) + 1 + C) * ((Fintype.card V : ℚ) - 2 + ((K : ℚ) + 1) + C) →
        MinMinYes G s t ℓ := by
      intro A B qA qB rA rB u eA eB nA nB hD hqA hcA hlA hrA hqB hcB hlB hut hus hrB hcost
      obtain ⟨P1, P2, hne', hD'⟩ :=
        mixed_case G s t K hst eA eB nA nB hD hqA hcA hlA hqB hcB hlB hut hus
      refine ⟨qA, qB ++ [t], P1, P2, hne', hD', ?_⟩
      have lA : qA.length ≤ links A := eA ▸ links_ge_of_rest K hrA
      have hqBne : qB ≠ [] := by rintro rfl; simp at hqB
      have lB : K + 1 ≤ links B := eB ▸ links_ge_of_chain K hqBne hrB
      by_contra hbig
      have hq : ℓ + 2 ≤ qA.length := by unfold links at hbig; omega
      have c1 : (ℓ : ℚ) + 2 ≤ (links A : ℚ) := by exact_mod_cast (by omega : ℓ + 2 ≤ links A)
      have c2 : (K : ℚ) + 1 ≤ (links B : ℚ) := by exact_mod_cast lB
      have := cost_mono hC (by positivity) (by positivity) c1 c2
      nlinarith
    rcases cA with ⟨-, hlA, hrA⟩ | ⟨uA, hlA, hutA, husA, hrA⟩ <;>
      rcases cB with ⟨-, hlB, hrB⟩ | ⟨uB, hlB, hutB, husB, hrB⟩
    · exfalso
      have h1 : old t ∈ A := by rw [eA]; simp [mem_of_last hlA]
      have h2 : old t ∈ B := by rw [eB]; simp [mem_of_last hlB]
      rcases hD _ h1 h2 with h | h
      · exact hst (old_injective h).symm
      · cases h
    · exact mixed A B qA qB rA rB uB eA eB hA.2.2.2 hB.2.2.2 hD hqA hcA hlA hrA hqB hcB hlB hutB
        husB hrB hcost
    · exact mixed B A qB qA rB rA uA eB eA hB.2.2.2 hA.2.2.2 (fun x a b => hD x b a) hqB hcB hlB hrB
        hqA hcA hlA hutA husA hrA (by rw [mul_comm]; exact hcost)
    · exfalso
      have lA : K + 1 ≤ links A := eA ▸ links_ge_of_chain K hneA hrA
      have lB : K + 1 ≤ links B := eB ▸ links_ge_of_chain K hneB hrB
      have c1 : (K : ℚ) + 1 ≤ (links A : ℚ) := by exact_mod_cast lA
      have c2 : (K : ℚ) + 1 ≤ (links B : ℚ) := by exact_mod_cast lB
      have := cost_mono hC (by positivity) (by positivity) c1 c2
      nlinarith


/-! ## The reduction, two terminals -/

/-- **Theorem (two terminals).** For `ℓ ≤ n - 1` and `s ≠ t`, min-min with bound `ℓ` holds iff
the gadget without the link `t t*` has paths from `s` to `t` and from `s` to `t*`, meeting only in
`s`, of min-prod value at most `(ℓ + C)(n - 2 + M + C)`. -/
theorem minMin_iff_minProd₂ [Fintype V] {C : ℚ} (hC : 0 ≤ C) (hst : s ≠ t) (ℓ : ℕ)
    (hℓ : ℓ ≤ Fintype.card V - 1) :
    MinMinYes G s t ℓ ↔
      MinProd₂Yes (gadget G s t false (innerLen (V := V) C)) (old s) (old t) sink C
        (threshold₂ (V := V) C ℓ) := by
  have hM : chainLen (Fintype.card V) C = innerLen (V := V) C + 1 := by
    have := one_le_chainLen (Fintype.card V) hC; unfold innerLen; omega
  have hK1 : 1 ≤ innerLen (V := V) C := by
    have h := chainLen_ge (Fintype.card V) C
    have h0 : (0 : ℚ) ≤ Fintype.card V := Nat.cast_nonneg _
    have : (4 : ℚ) ≤ chainLen (Fintype.card V) C := by nlinarith
    have : 4 ≤ chainLen (Fintype.card V) C := by exact_mod_cast this
    omega
  have hn2 : 2 ≤ Fintype.card V := by
    have := Fintype.card_le_of_injective (fun b : Bool => if b then s else t)
      (by intro a b h; cases a <;> cases b <;> simp_all [eq_comm])
    simpa using this
  obtain ⟨-, -, -, hI1, -⟩ := paper_inequalities (Fintype.card V) ℓ hC hn2 hℓ
  rw [hM] at hI1
  push_cast at hI1
  have hn2' : (2 : ℚ) ≤ Fintype.card V := by exact_mod_cast hn2
  have hI : ((ℓ : ℚ) + C) * ((Fintype.card V : ℚ) - 2) <
      (innerLen (V := V) C : ℚ) + 1 + C := by
    have : ((ℓ : ℚ) + C) * ((Fintype.card V : ℚ) - 2) ≤
        ((ℓ : ℚ) + 1 + C) * ((Fintype.card V : ℚ) - 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  have hthr : threshold₂ (V := V) C ℓ =
      ((ℓ : ℚ) + C) * ((Fintype.card V : ℚ) - 2 + ((innerLen (V := V) C : ℚ) + 1) + C) := by
    rw [threshold₂, hM]; push_cast; ring
  generalize innerLen (V := V) C = K at hK1 hI hthr ⊢
  rw [hthr]
  constructor
  · rintro ⟨p₁, p₂, h₁, h₂, hne, hD, hl⟩
    have key : ∀ P₁ P₂ : List V, IsPathL G.Adj P₁ s t → IsPathL G.Adj P₂ s t → Disj P₁ P₂ s t →
        links P₁ ≤ ℓ → 3 ≤ P₂.length →
        MinProd₂Yes (gadget G s t false K) (old s) (old t) sink C
          (((ℓ : ℚ) + C) * ((Fintype.card V : ℚ) - 2 + ((K : ℚ) + 1) + C)) := by
      intro P₁ P₂ h₁ h₂ hD hl h3
      obtain ⟨m, u, rfl⟩ := shape_of_three h₂.1 h₂.2.1 h3
      obtain ⟨B, hB, hlB, hmB⟩ := chain_pair_path G s t false K hK1 h₂
      have htq : t ∉ s :: (m ++ [u]) := by
        have hn := h₂.2.2.2
        have : s :: (m ++ [u, t]) = (s :: (m ++ [u])) ++ [t] := by simp
        rw [this, List.nodup_append] at hn
        exact fun h => hn.2.2 t h t (by simp) rfl
      refine ⟨P₁.map old, B, ⟨by simp [h₁.1], by simp [h₁.2.1],
        (isChain_map _).mpr (h₁.2.2.1.imp fun a b h => h), h₁.2.2.2.map old_injective⟩, hB, ?_, ?_⟩
      · intro x hxA hxB
        simp only [List.mem_map] at hxA
        obtain ⟨y, hyA, rfl⟩ := hxA
        rcases hmB _ hxB with ⟨z, hz, hz'⟩ | h' | ⟨j, h'⟩
        · have hzy := old_injective hz
          subst hzy
          have hzB : y ∈ s :: (m ++ [u, t]) := by
            simp only [List.mem_cons, List.mem_append] at hz' ⊢
            tauto
          rcases hD y hyA hzB with h | h
          · rw [h]
          · exact absurd (h ▸ hz') htq
        · cases h'
        · cases h'
      · rw [links_map_old, hlB]
        have hl2 := links_le_card h₂
        have c1 : ((links P₁ : ℕ) : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast hl
        have c2 : ((links (s :: (m ++ [u, t])) + K : ℕ) : ℚ) ≤
            (Fintype.card V : ℚ) - 2 + ((K : ℚ) + 1) := by
          have h' : links (s :: (m ++ [u, t])) + K + 1 ≤ Fintype.card V + K := by omega
          have : ((links (s :: (m ++ [u, t])) + K + 1 : ℕ) : ℚ) ≤ ((Fintype.card V + K : ℕ) : ℚ) := by
            exact_mod_cast h'
          push_cast at this ⊢; linarith
        have := cost_mono hC (by positivity) (by positivity) c1 c2
        push_cast at this ⊢
        linarith
    rcases order_pair G s t hst h₁ h₂ hne with h3 | ⟨h3, hle⟩
    · exact key p₁ p₂ h₁ h₂ hD hl h3
    · exact key p₂ p₁ h₂ h₁ (fun x a b => hD x b a) (le_trans hle hl) h3
  · rintro ⟨A, B, hA, hB, hD, hcost⟩
    obtain ⟨qB, rB, eB, hqB, hcB, hneB, cB⟩ := decomp_star G s t false K hB
    rcases cB with ⟨hf, -, -⟩ | ⟨u, hlB, hut, hus, hrB⟩
    · exact absurd hf Bool.false_ne_true
    obtain ⟨hhA, hlA, hcA, hnA⟩ := hA
    cases A with
    | nil => simp at hhA
    | cons x p =>
      simp at hhA
      subst hhA
      obtain ⟨qA, rA, eA, hqA, hcqA, cA⟩ := split_old G s t false K p s hcA hnA
        (fun x hx => Or.inr ⟨t, by rw [hlA] at hx; exact (Option.some.inj hx).symm⟩)
      have hsinkB : sink ∈ B := mem_of_last hB.2.1
      have hrA : rA = [] := by
        rcases cA with h | ⟨-, -, h⟩ | ⟨-, -, -, -, -, h⟩
        · exact h
        all_goals
          exfalso
          have h1 : sink ∈ old s :: p := by rw [eA]; simp [h]
          cases hD _ h1 hsinkB
      subst hrA
      rw [List.append_nil] at eA
      have hlqA : qA.getLast? = some t := by
        rw [eA, getLast?_map] at hlA
        simp only [Option.map_eq_some_iff] at hlA
        obtain ⟨a, ha, hat⟩ := hlA
        rw [ha, old_injective hat]
      obtain ⟨P1, P2, hne', hD'⟩ :=
        mixed_case G s t K (A := old s :: p) (rA := []) hst (by rw [eA, List.append_nil]) eB hnA
          hB.2.2.2 (fun x a b => Or.inl (hD x a b)) hqA hcqA hlqA hqB hcB hlB hut hus
      refine ⟨qA, qB ++ [t], P1, P2, hne', hD', ?_⟩
      have lA : links (old s :: p) = links qA := by rw [eA, links_map_old]
      have lB : K + 1 ≤ links B := eB ▸ links_ge_of_chain K hneB hrB
      by_contra hbig
      have c1 : (ℓ : ℚ) + 1 ≤ (links (old s :: p) : ℚ) := by
        rw [lA]; exact_mod_cast (by omega : ℓ + 1 ≤ links qA)
      have c2 : (K : ℚ) + 1 ≤ (links B : ℚ) := by exact_mod_cast lB
      have := cost_mono hC (by positivity) (by positivity) c1 c2
      nlinarith

/-! ## Size of the gadget -/

theorem card_gadget [Fintype V] (C : ℚ) :
    Fintype.card (GV V (innerLen (V := V) C)) =
      Fintype.card V + 1 + Fintype.card V * (chainLen (Fintype.card V) C - 1) := by
  rw [GV.card]; rfl

theorem card_gadget_le [Fintype V] {C : ℚ} (hC : 0 ≤ C) :
    (Fintype.card (GV V (innerLen (V := V) C)) : ℚ) ≤
      Fintype.card V + 1 + Fintype.card V * ((Fintype.card V : ℚ) + C + 2) ^ 2 := by
  rw [GV.card]
  have h0 : (0 : ℚ) ≤ ((Fintype.card V : ℚ) + C + 2) ^ 2 := sq_nonneg _
  have hc : (chainLen (Fintype.card V) C : ℚ) < ((Fintype.card V : ℚ) + C + 2) ^ 2 + 1 :=
    Nat.ceil_lt_add_one h0
  have h1 := one_le_chainLen (Fintype.card V) hC
  have hK : (innerLen (V := V) C : ℚ) ≤ ((Fintype.card V : ℚ) + C + 2) ^ 2 := by
    unfold innerLen
    rw [Nat.cast_sub h1]; push_cast; linarith
  push_cast
  have := mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg (α := ℚ) (Fintype.card V))
  linarith

/-- The size bound as a polynomial in `n + 1` with a constant that depends only on `C`. -/
theorem card_gadget_poly [Fintype V] {C : ℚ} (hC : 0 ≤ C) :
    Fintype.card (GV V (innerLen (V := V) C)) ≤ ⌈1 + (C + 2) ^ 2⌉₊ * (Fintype.card V + 1) ^ 3 := by
  have h := card_gadget_le (V := V) hC
  set n : ℚ := (Fintype.card V : ℚ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have h1 : n + C + 2 ≤ (n + 1) * (C + 2) := by nlinarith
  have h2 : (n + C + 2) ^ 2 ≤ ((n + 1) * (C + 2)) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
  have h3 : n * (n + C + 2) ^ 2 ≤ (n + 1) ^ 3 * (C + 2) ^ 2 := by
    have : n * (n + C + 2) ^ 2 ≤ (n + 1) * ((n + 1) * (C + 2)) ^ 2 :=
      mul_le_mul (by linarith) h2 (sq_nonneg _) (by linarith)
    nlinarith
  have h4 : n + 1 ≤ (n + 1) ^ 3 := by nlinarith
  have h5 : (1 + (C + 2) ^ 2 : ℚ) ≤ ⌈1 + (C + 2) ^ 2⌉₊ := Nat.le_ceil _
  have h6 : (Fintype.card (GV V (innerLen (V := V) C)) : ℚ) ≤
      (⌈1 + (C + 2) ^ 2⌉₊ : ℚ) * (n + 1) ^ 3 := by
    have : (1 + (C + 2) ^ 2) * (n + 1) ^ 3 ≤ (⌈1 + (C + 2) ^ 2⌉₊ : ℚ) * (n + 1) ^ 3 :=
      mul_le_mul_of_nonneg_right h5 (by positivity)
    nlinarith
  rw [hn] at h6
  exact_mod_cast h6

/-! ## The routing problem with unit latencies and a uniform joint failure probability -/

section Routing

variable {W : Type*}

/-- The links of a path. -/
def linkList (p : List W) : List (W × W) := p.zip p.tail

/-- The routing objective `c(P₁) + c(P₂) + B Σ_{e ∈ P₁, f ∈ P₂} p(e, f)`. -/
def routeCost (c : W → W → ℚ) (pr : W × W → W × W → ℚ) (B : ℚ) (p₁ p₂ : List W) : ℚ :=
  ((linkList p₁).map fun e => c e.1 e.2).sum + ((linkList p₂).map fun e => c e.1 e.2).sum +
    B * ((linkList p₁).map fun e => ((linkList p₂).map fun f => pr e f).sum).sum

/-- The routing problem, decision version: paths from `s` to `t₁` and from `s` to `t₂` that meet
only in `s`, with objective at most `K`. -/
def RouteYes (H : SimpleGraph W) (s t₁ t₂ : W) (c : W → W → ℚ) (pr : W × W → W × W → ℚ)
    (B K : ℚ) : Prop :=
  ∃ p₁ p₂, IsPathL H.Adj p₁ s t₁ ∧ IsPathL H.Adj p₂ s t₂ ∧ (∀ x, x ∈ p₁ → x ∈ p₂ → x = s) ∧
    routeCost c pr B p₁ p₂ ≤ K

theorem length_linkList (p : List W) : (linkList p).length = links p := by
  simp [linkList, links]

theorem sum_map_const' {α : Type*} (l : List α) (c : ℚ) : (l.map fun _ => c).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp; ring

theorem routeCost_unit (q B : ℚ) (p₁ p₂ : List W) :
    routeCost (fun _ _ => 1) (fun _ _ => q) B p₁ p₂ =
      links p₁ + links p₂ + B * q * links p₁ * links p₂ := by
  unfold routeCost
  rw [sum_map_const', sum_map_const', sum_map_const', sum_map_const', length_linkList,
    length_linkList]
  ring

/-- **Corollary.** With unit latencies and `p(e, f) = q`, the objective is at most `K` iff
`(|P₁| + C)(|P₂| + C) ≤ (K + C) / (Bq)` with `C = 1 / (Bq)`. -/
theorem route_unit_iff_minProd₂ (H : SimpleGraph W) (s t₁ t₂ : W) {q B : ℚ} (hq : 0 < q)
    (hB : 0 < B) (K : ℚ) :
    RouteYes H s t₁ t₂ (fun _ _ => 1) (fun _ _ => q) B K ↔
      MinProd₂Yes H s t₁ t₂ (1 / (B * q)) ((K + 1 / (B * q)) / (B * q)) := by
  have hD : 0 < B * q := mul_pos hB hq
  have key : ∀ a b : ℚ, (a + b + B * q * a * b ≤ K ↔
      (a + 1 / (B * q)) * (b + 1 / (B * q)) ≤ (K + 1 / (B * q)) / (B * q)) := by
    intro a b
    rw [le_div_iff₀ hD]
    have hDC : B * q * (1 / (B * q)) = 1 := by field_simp
    have e : (a + 1 / (B * q)) * (b + 1 / (B * q)) * (B * q) =
        a + b + B * q * a * b + 1 / (B * q) := by
      linear_combination (a + b + 1 / (B * q)) * hDC
    rw [e]
    constructor <;> intro h <;> linarith
  constructor
  · rintro ⟨p₁, p₂, h₁, h₂, hD', hc⟩
    exact ⟨p₁, p₂, h₁, h₂, hD', (key _ _).mp (by rw [routeCost_unit] at hc; exact hc)⟩
  · rintro ⟨p₁, p₂, h₁, h₂, hD', hc⟩
    exact ⟨p₁, p₂, h₁, h₂, hD', by rw [routeCost_unit]; exact (key _ _).mpr hc⟩

end Routing

/-! ## The reductions as maps of instances

Instances carry a finite vertex type. The size of an instance is its number of vertices. Each
reduction below preserves the answer, and the size of its output is bounded by an explicit
polynomial in the size of its input. -/

/-- Min-min instances with `s ≠ t`. -/
structure MMInst where
  V : Type
  [fin : Fintype V]
  [dec : DecidableEq V]
  G : SimpleGraph V
  s : V
  t : V
  hst : s ≠ t
  ℓ : ℕ

/-- Min-prod instances with one terminal. -/
structure MPInst where
  V : Type
  [fin : Fintype V]
  [dec : DecidableEq V]
  H : SimpleGraph V
  a : V
  b : V
  hab : a ≠ b
  K : ℚ

/-- Min-prod instances with two terminals. -/
structure MP2Inst where
  V : Type
  [fin : Fintype V]
  [dec : DecidableEq V]
  H : SimpleGraph V
  a : V
  b₁ : V
  b₂ : V
  h₁ : a ≠ b₁
  h₂ : a ≠ b₂
  h₁₂ : b₁ ≠ b₂
  K : ℚ

attribute [instance] MMInst.fin MMInst.dec MPInst.fin MPInst.dec MP2Inst.fin MP2Inst.dec

def MMInst.yes (I : MMInst) : Prop := MinMinYes I.G I.s I.t I.ℓ
def MMInst.size (I : MMInst) : ℕ := Fintype.card I.V
def MPInst.yes (C : ℚ) (I : MPInst) : Prop := MinProdYes I.H I.a I.b C I.K
def MPInst.size (I : MPInst) : ℕ := Fintype.card I.V
def MP2Inst.yes (C : ℚ) (I : MP2Inst) : Prop := MinProd₂Yes I.H I.a I.b₁ I.b₂ C I.K
def MP2Inst.size (I : MP2Inst) : ℕ := Fintype.card I.V
/-- The routing problem with unit latencies, `p(e, f) = q` and weight `B`, on two-terminal
instances. -/
def MP2Inst.routeYes (q B : ℚ) (I : MP2Inst) : Prop :=
  RouteYes I.H I.a I.b₁ I.b₂ (fun _ _ => 1) (fun _ _ => q) B I.K

theorem minMin_clamp [Fintype V] (ℓ : ℕ) :
    MinMinYes G s t ℓ ↔ MinMinYes G s t (min ℓ (Fintype.card V - 1)) := by
  constructor
  · rintro ⟨p₁, p₂, h₁, h₂, hne, hD, hl⟩
    exact ⟨p₁, p₂, h₁, h₂, hne, hD, le_min hl (links_le_card h₁)⟩
  · rintro ⟨p₁, p₂, h₁, h₂, hne, hD, hl⟩
    exact ⟨p₁, p₂, h₁, h₂, hne, hD, le_trans hl (min_le_left _ _)⟩

/-- The one-terminal reduction as a map of instances. -/
noncomputable def toMP (C : ℚ) (I : MMInst) : MPInst where
  V := GV I.V (innerLen (V := I.V) C)
  H := gadget I.G I.s I.t true _
  a := old I.s
  b := sink
  hab := by intro h; cases h
  K := threshold (V := I.V) C (min I.ℓ (Fintype.card I.V - 1))

/-- The two-terminal reduction as a map of instances. -/
noncomputable def toMP2 (C : ℚ) (I : MMInst) : MP2Inst where
  V := GV I.V (innerLen (V := I.V) C)
  H := gadget I.G I.s I.t false _
  a := old I.s
  b₁ := old I.t
  b₂ := sink
  h₁ := fun h => I.hst (old_injective h)
  h₂ := by intro h; cases h
  h₁₂ := by intro h; cases h
  K := threshold₂ (V := I.V) C (min I.ℓ (Fintype.card I.V - 1))

/-- **Theorem 1 (reduction, one terminal).** For every rational `C ≥ 0`, the gadget maps a min-min
instance to a min-prod instance with the same answer and at most `⌈1 + (C + 2)²⌉ (n + 1)³`
vertices. -/
theorem reduction_minProd {C : ℚ} (hC : 0 ≤ C) :
    (∀ I, MMInst.yes I ↔ MPInst.yes C (toMP C I)) ∧
    ∀ I, MPInst.size (toMP C I) ≤ ⌈1 + (C + 2) ^ 2⌉₊ * (MMInst.size I + 1) ^ 3 :=
  ⟨fun I => (minMin_clamp I.G I.s I.t I.ℓ).trans
      (minMin_iff_minProd I.G I.s I.t hC I.hst _ (min_le_right _ _)),
    fun I => card_gadget_poly (V := I.V) hC⟩

/-- **Theorem 1 (reduction, two terminals).** -/
theorem reduction_minProd₂ {C : ℚ} (hC : 0 ≤ C) :
    (∀ I, MMInst.yes I ↔ MP2Inst.yes C (toMP2 C I)) ∧
    ∀ I, MP2Inst.size (toMP2 C I) ≤ ⌈1 + (C + 2) ^ 2⌉₊ * (MMInst.size I + 1) ^ 3 :=
  ⟨fun I => (minMin_clamp I.G I.s I.t I.ℓ).trans
      (minMin_iff_minProd₂ I.G I.s I.t hC I.hst _ (min_le_right _ _)),
    fun I => card_gadget_poly (V := I.V) hC⟩

/-- The routing instance with unit latencies, `p(e, f) = q` and weight `B`: the two-terminal
gadget for `C = 1 / (Bq)` with the threshold `K Bq - C`. -/
noncomputable def toRoute (q B : ℚ) (I : MMInst) : MP2Inst :=
  { toMP2 (1 / (B * q)) I with K := (toMP2 (1 / (B * q)) I).K * (B * q) - 1 / (B * q) }

/-- **Corollary 2 (reduction).** For rational `q > 0` and `B > 0`, min-min maps to the routing
problem with unit latencies and `p(e, f) = q`, with the same answer and at most
`⌈1 + (C + 2)²⌉ (n + 1)³` vertices, `C = 1 / (Bq)`. -/
theorem reduction_route {q B : ℚ} (hq : 0 < q) (hB : 0 < B) :
    (∀ I, MMInst.yes I ↔ MP2Inst.routeYes q B (toRoute q B I)) ∧
    ∀ I, MP2Inst.size (toRoute q B I) ≤ ⌈1 + (1 / (B * q) + 2) ^ 2⌉₊ * (MMInst.size I + 1) ^ 3 := by
  have hC : (0 : ℚ) ≤ 1 / (B * q) := by positivity
  obtain ⟨h1, h2⟩ := reduction_minProd₂ hC
  refine ⟨fun I => (h1 I).trans ?_, fun I => h2 I⟩
  have hD : (0 : ℚ) < B * q := mul_pos hB hq
  simp only [MP2Inst.yes, MP2Inst.routeYes, toRoute]
  rw [route_unit_iff_minProd₂ _ _ _ _ hq hB]
  have : ((toMP2 (1 / (B * q)) I).K * (B * q) - 1 / (B * q) + 1 / (B * q)) / (B * q) =
      (toMP2 (1 / (B * q)) I).K := by field_simp; ring
  rw [this]

end RiskRouting
