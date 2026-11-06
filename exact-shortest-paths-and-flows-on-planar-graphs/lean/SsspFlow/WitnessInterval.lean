import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.FinCases
import SsspFlow.Recursion

/-!
# The witness interval of Lemma S1

The metric part of Lemma S1 of `notes/RECURSION.md`, the interval form of [18, Claim 2.4].

`Annulus` is the level-one annulus `A_1` of Theorem D as a weighted graph. The faces `p_0, …, p_m`
of the dual path `P` lie at strictly increasing positions `pos t` along `P`, and each face `p_t`
has two copies `c 0 t` and `c 1 t`. The two facts of the note on `P` are fields: the copies
`B^σ[u→v]` of the parts of `P` (`copy`), and (P), that a walk between copies of `p_u` and `p_v` is
at least as long as `P[u..v]` (`short`). `lam t` is `λ_t`, the least length of a walk from `c 0 t`
to `c 1 t`. The separation fact (S_1) is the proposition `Sep`.

* `lam_le_via` is (B).
* `orient` splits a walk from `p_i^0` to `p_i^1` as `U·Q̄·R`, where `Q̄` runs from the last
  `0`-copy `p_x^0` to the first `1`-copy `p_y^1` after it. `orient_len` is part (a) of the proof:
  on a shortest walk, `U` and `R` are as long as the parts of `P` between their ends.
* `copies_eq` is part (b): the least and the greatest index of a copy of `P` on a shortest walk are
  `min(i, x, y)` and `max(i, x, y)`.
* `interval` is part (c) with its two cases, and `witness_interval` is Lemma S1: given `Sep`,
  every index `t` strictly between them has `λ_q ≤ λ_t` for all `q ∈ [i1, t]` or for all
  `q ∈ [t, i2]`.
* `dom_of_walk` is the field `dom` of `Rec.node` in `Recursion.lean` for `lam = A.lam`, and
  `nodeOfWalk` builds a node from a shortest walk.

Not here: the graph `A_1` itself, the proof of (S_1), and Lemma O.
-/

namespace SsspFlow.Recursion

open SimpleGraph

variable {V : Type*}

/-- The length of a walk under the edge weights `w`. -/
def wlen {G : SimpleGraph V} (w : Sym2 V → ℕ) {a b : V} (p : G.Walk a b) : ℕ :=
  (p.edges.map w).sum

theorem wlen_append {G : SimpleGraph V} (w : Sym2 V → ℕ) {a b c : V} (p : G.Walk a b)
    (q : G.Walk b c) : wlen w (p.append q) = wlen w p + wlen w q := by
  simp [wlen, Walk.edges_append]

theorem wlen_copy {G : SimpleGraph V} (w : Sym2 V → ℕ) {a b a' b' : V} (p : G.Walk a b)
    (ha : a = a') (hb : b = b') : wlen w (p.copy ha hb) = wlen w p := by
  simp [wlen, Walk.edges_copy]

theorem wlen_nil {G : SimpleGraph V} (w : Sym2 V → ℕ) (a : V) :
    wlen w (Walk.nil : G.Walk a a) = 0 := by
  simp [wlen]

theorem wlen_split [DecidableEq V] {G : SimpleGraph V} (w : Sym2 V → ℕ) {a b z : V}
    (p : G.Walk a b) (h : z ∈ p.support) :
    wlen w (p.takeUntil z h) + wlen w (p.dropUntil z h) = wlen w p := by
  rw [← wlen_append, Walk.take_spec]

/-- Split a walk at its last vertex in `S`. -/
theorem exists_last {G : SimpleGraph V} (S : V → Prop) : ∀ {a b : V} (p : G.Walk a b),
    (∃ v ∈ p.support, S v) → ∃ z, S z ∧ ∃ (p₁ : G.Walk a z) (p₂ : G.Walk z b),
      p = p₁.append p₂ ∧ ∀ v ∈ p₂.support, S v → v = z
  | _, _, .nil, ⟨v, hv, hS⟩ => by
      simp only [Walk.support_nil, List.mem_singleton] at hv
      subst hv
      exact ⟨_, hS, .nil, .nil, rfl, fun u hu _ => by simpa using hu⟩
  | a, _, .cons h p, hex => by
      by_cases h' : ∃ v ∈ p.support, S v
      · obtain ⟨z, hz, p₁, p₂, rfl, hlast⟩ := exists_last S p h'
        exact ⟨z, hz, .cons h p₁, p₂, rfl, hlast⟩
      · obtain ⟨v, hv, hS⟩ := hex
        have hva : v = a := by
          simp only [Walk.support_cons, List.mem_cons] at hv
          rcases hv with hv | hv
          · exact hv
          · exact absurd ⟨v, hv, hS⟩ h'
        subst hva
        refine ⟨v, hS, .nil, .cons h p, rfl, fun u hu hSu => ?_⟩
        simp only [Walk.support_cons, List.mem_cons] at hu
        rcases hu with hu | hu
        · exact hu
        · exact absurd ⟨u, hu, hSu⟩ h'

/-- Split a walk at its first vertex in `S`. -/
theorem exists_first {G : SimpleGraph V} (S : V → Prop) : ∀ {a b : V} (p : G.Walk a b), S b →
    ∃ z, S z ∧ ∃ (p₁ : G.Walk a z) (p₂ : G.Walk z b),
      p = p₁.append p₂ ∧ ∀ v ∈ p₁.support, S v → v = z
  | _, _, .nil, hb => ⟨_, hb, .nil, .nil, rfl, fun u hu _ => by simpa using hu⟩
  | a, _, .cons h p, hb => by
      by_cases ha : S a
      · exact ⟨a, ha, .nil, .cons h p, rfl, fun u hu _ => by simpa using hu⟩
      · obtain ⟨z, hz, p₁, p₂, rfl, hfirst⟩ := exists_first S p hb
        refine ⟨z, hz, .cons h p₁, p₂, rfl, fun u hu hSu => ?_⟩
        simp only [Walk.support_cons, List.mem_cons] at hu
        rcases hu with hu | hu
        · exact absurd (hu ▸ hSu) ha
        · exact hfirst u hu hSu

/-- The length `d(u, v)` of the part of `P` between the faces `p_u` and `p_v`, from their
positions along `P`. -/
def dP (pos : ℕ → ℕ) (u v : ℕ) : ℕ := pos u - pos v + (pos v - pos u)

/-- The level-one annulus `A_1` of Theorem D as a weighted graph. The faces `p_0, …, p_m` of the
dual path `P` lie at the positions `pos t` along `P`, and `c 0 t` and `c 1 t` are the two copies of
the face `p_t`. -/
structure Annulus (V : Type*) where
  /-- The graph of `A_1`. -/
  G : SimpleGraph V
  /-- The edge weights. -/
  w : Sym2 V → ℕ
  /-- The last index of a face of `P`. -/
  m : ℕ
  /-- The positions of the faces along `P`. -/
  pos : ℕ → ℕ
  /-- The two copies of each face of `P`. -/
  c : Fin 2 → ℕ → V
  /-- The edges of `P` have positive length. -/
  mono : StrictMono pos
  /-- The copies `B^σ[u→v]` of the parts of `P`. -/
  copy : ∀ σ u v, u ≤ m → v ≤ m → ∃ p : G.Walk (c σ u) (c σ v), wlen w p = dP pos u v
  /-- (P): a walk between copies of `p_u` and `p_v` is at least as long as `P[u..v]`. -/
  short : ∀ σ τ u v, u ≤ m → v ≤ m → ∀ p : G.Walk (c σ u) (c τ v), dP pos u v ≤ wlen w p

namespace Annulus

variable (A : Annulus V)

/-- `λ_t`, the least length of a walk between the two copies of `p_t`. -/
noncomputable def lam (t : ℕ) : ℕ :=
  sInf (Set.range fun W : A.G.Walk (A.c 0 t) (A.c 1 t) => wlen A.w W)

/-- The indices of the copies of `P` on a walk. -/
def copies {a b : V} (p : A.G.Walk a b) : Set ℕ := {r | r ≤ A.m ∧ ∃ σ, A.c σ r ∈ p.support}

/-- (S_1): a walk from `p_x^0` to `p_y^1` on which every copy of `P` is one of its two ends meets
every walk between the two copies of a face strictly between `p_x` and `p_y`. -/
def Sep : Prop :=
  ∀ x y, x ≤ A.m → y ≤ A.m → ∀ Q : A.G.Walk (A.c 0 x) (A.c 1 y),
    (∀ z ∈ Q.support, ∀ σ r, r ≤ A.m → z = A.c σ r → z = A.c 0 x ∨ z = A.c 1 y) →
    ∀ t, min x y < t → t < max x y → ∀ W : A.G.Walk (A.c 0 t) (A.c 1 t),
      ∃ z ∈ W.support, z ∈ Q.support

theorem lam_le {t : ℕ} (W : A.G.Walk (A.c 0 t) (A.c 1 t)) : A.lam t ≤ wlen A.w W :=
  Nat.sInf_le ⟨W, rfl⟩

theorem exists_lam {t : ℕ} (W : A.G.Walk (A.c 0 t) (A.c 1 t)) :
    ∃ W' : A.G.Walk (A.c 0 t) (A.c 1 t), wlen A.w W' = A.lam t :=
  Nat.sInf_mem (s := Set.range fun W : A.G.Walk (A.c 0 t) (A.c 1 t) => wlen A.w W) ⟨_, W, rfl⟩

theorem dP_comm (u v : ℕ) : dP A.pos u v = dP A.pos v u := by
  unfold dP
  omega

theorem dP_add {a b c : ℕ} (h1 : a ≤ b) (h2 : b ≤ c) :
    dP A.pos a b + dP A.pos b c = dP A.pos a c := by
  have := A.mono.monotone h1
  have := A.mono.monotone h2
  unfold dP
  omega

/-- A face with `d(a, r) + d(r, b) ≤ d(a, b)` lies between `p_a` and `p_b`. -/
theorem between {a b r : ℕ} (h : dP A.pos a r + dP A.pos r b ≤ dP A.pos a b) :
    min a b ≤ r ∧ r ≤ max a b := by
  constructor
  · by_contra hc
    have h1 := A.mono (show r < a by omega)
    have h2 := A.mono (show r < b by omega)
    unfold dP at h
    omega
  · by_contra hc
    have h1 := A.mono (show a < r by omega)
    have h2 := A.mono (show b < r by omega)
    unfold dP at h
    omega

/-- Two equal copies are copies of the same face. -/
theorem idx_eq {σ τ : Fin 2} {r s : ℕ} (hr : r ≤ A.m) (hs : s ≤ A.m)
    (h : A.c σ r = A.c τ s) : r = s := by
  have h1 := A.short σ τ r s hr hs ((Walk.nil : A.G.Walk (A.c σ r) (A.c σ r)).copy rfl h)
  rw [wlen_copy, wlen_nil] at h1
  have : A.pos r = A.pos s := by
    unfold dP at h1
    omega
  exact A.mono.injective this

/-- (P) through a copy: a walk between copies of `p_a` and `p_b` through a copy of `p_r` is at
least `d(a, r) + d(r, b)` long. -/
theorem short_via {σ τ ρ : Fin 2} {a b r : ℕ} (ha : a ≤ A.m) (hb : b ≤ A.m) (hr : r ≤ A.m)
    (p : A.G.Walk (A.c σ a) (A.c τ b)) (h : A.c ρ r ∈ p.support) :
    dP A.pos a r + dP A.pos r b ≤ wlen A.w p := by
  classical
  rw [← wlen_split A.w p h]
  exact Nat.add_le_add (A.short σ ρ a r ha hr _) (A.short ρ τ r b hr hb _)

/-- (B): a walk `Z` from `p_u^0` to `p_v^1` gives `λ_q ≤ d(q, u) + w(Z) + d(v, q)`. -/
theorem lam_le_via {q u v : ℕ} (hq : q ≤ A.m) (hu : u ≤ A.m) (hv : v ≤ A.m)
    (Z : A.G.Walk (A.c 0 u) (A.c 1 v)) :
    A.lam q ≤ dP A.pos q u + wlen A.w Z + dP A.pos v q := by
  obtain ⟨B0, hB0⟩ := A.copy 0 q u hq hu
  obtain ⟨B1, hB1⟩ := A.copy 1 v q hv hq
  have := A.lam_le (B0.append (Z.append B1))
  rw [wlen_append, wlen_append, hB0, hB1] at this
  omega

/-- Once one face of `P` has a walk between its copies, every face has a shortest one. -/
theorem exists_lam_of {i t : ℕ} (hi : i ≤ A.m) (ht : t ≤ A.m)
    (P : A.G.Walk (A.c 0 i) (A.c 1 i)) :
    ∃ W : A.G.Walk (A.c 0 t) (A.c 1 t), wlen A.w W = A.lam t := by
  obtain ⟨B0, -⟩ := A.copy 0 t i ht hi
  obtain ⟨B1, -⟩ := A.copy 1 i t hi ht
  exact A.exists_lam (B0.append (P.append B1))

/-- `f(q) = d(q, x) + d(q, y)` does not grow from `t` towards the far end of `[x, y]`. -/
theorem f_le_of_le {t q x y : ℕ} (h1 : t ≤ min x y) (h2 : t ≤ q) (h3 : q ≤ max x y) :
    dP A.pos q x + dP A.pos q y ≤ dP A.pos t x + dP A.pos t y := by
  have := A.mono.monotone (show t ≤ x by omega)
  have := A.mono.monotone (show t ≤ y by omega)
  have := A.mono.monotone h2
  have h4 : A.pos q ≤ A.pos x ∨ A.pos q ≤ A.pos y := by
    rcases le_or_gt q x with h | h
    · exact Or.inl (A.mono.monotone h)
    · exact Or.inr (A.mono.monotone (by omega))
  unfold dP
  omega

/-- The mirror image of `f_le_of_le`. -/
theorem f_le_of_ge {t q x y : ℕ} (h1 : max x y ≤ t) (h2 : q ≤ t) (h3 : min x y ≤ q) :
    dP A.pos q x + dP A.pos q y ≤ dP A.pos t x + dP A.pos t y := by
  have := A.mono.monotone (show x ≤ t by omega)
  have := A.mono.monotone (show y ≤ t by omega)
  have := A.mono.monotone h2
  have h4 : A.pos x ≤ A.pos q ∨ A.pos y ≤ A.pos q := by
    rcases le_or_gt x q with h | h
    · exact Or.inl (A.mono.monotone h)
    · exact Or.inr (A.mono.monotone (by omega))
  unfold dP
  omega

/-- Orientation: a walk from `p_i^0` to `p_i^1` is `U·Q̄·R`, where `Q̄` runs from the last
`0`-copy `p_x^0` on the walk to the first `1`-copy `p_y^1` after it, and every copy of `P` on `Q̄`
is one of its two ends. -/
theorem orient {i : ℕ} (hi : i ≤ A.m) (P : A.G.Walk (A.c 0 i) (A.c 1 i)) :
    ∃ x y, x ≤ A.m ∧ y ≤ A.m ∧ ∃ (U : A.G.Walk (A.c 0 i) (A.c 0 x))
      (Q : A.G.Walk (A.c 0 x) (A.c 1 y)) (R : A.G.Walk (A.c 1 y) (A.c 1 i)),
      P = U.append (Q.append R) ∧
      ∀ z ∈ Q.support, ∀ σ r, r ≤ A.m → z = A.c σ r → z = A.c 0 x ∨ z = A.c 1 y := by
  obtain ⟨z0, ⟨x, hx, rfl⟩, U, P2, rfl, hlast⟩ :=
    exists_last (fun v => ∃ r ≤ A.m, A.c 0 r = v) P ⟨_, P.start_mem_support, i, hi, rfl⟩
  obtain ⟨z1, ⟨y, hy, rfl⟩, Q, R, rfl, hfirst⟩ :=
    exists_first (fun v => ∃ r ≤ A.m, A.c 1 r = v) P2 ⟨i, hi, rfl⟩
  refine ⟨x, y, hx, hy, U, Q, R, rfl, fun z hz σ r hr hzr => ?_⟩
  fin_cases σ
  · exact Or.inl (hlast z ((Walk.mem_support_append_iff _ _).2 (Or.inl hz)) ⟨r, hr, hzr.symm⟩)
  · exact Or.inr (hfirst z hz ⟨r, hr, hzr.symm⟩)

/-- Part (a): on a shortest walk `U·Q̄·R`, `w(U) = d(i, x)` and `w(R) = d(y, i)`. -/
theorem orient_len {i x y : ℕ} (hi : i ≤ A.m) (hx : x ≤ A.m) (hy : y ≤ A.m)
    (U : A.G.Walk (A.c 0 i) (A.c 0 x)) (Q : A.G.Walk (A.c 0 x) (A.c 1 y))
    (R : A.G.Walk (A.c 1 y) (A.c 1 i)) (hP : wlen A.w (U.append (Q.append R)) = A.lam i) :
    wlen A.w U = dP A.pos i x ∧ wlen A.w R = dP A.pos y i := by
  rw [wlen_append, wlen_append] at hP
  have hU1 := A.short 0 0 i x hi hx U
  have hR1 := A.short 1 1 y i hy hi R
  obtain ⟨BU, hBU⟩ := A.copy 0 i x hi hx
  obtain ⟨BR, hBR⟩ := A.copy 1 y i hy hi
  have hU2 := A.lam_le (BU.append (Q.append R))
  have hR2 := A.lam_le (U.append (Q.append BR))
  rw [wlen_append, wlen_append, hBU] at hU2
  rw [wlen_append, wlen_append, hBR] at hR2
  constructor <;> omega

/-- Part (b): on a shortest walk `U·Q̄·R`, the least and the greatest index of a copy of `P` are
`min(i, x, y)` and `max(i, x, y)`. -/
theorem copies_eq {i x y : ℕ} (hi : i ≤ A.m) (hx : x ≤ A.m) (hy : y ≤ A.m)
    (U : A.G.Walk (A.c 0 i) (A.c 0 x)) (Q : A.G.Walk (A.c 0 x) (A.c 1 y))
    (R : A.G.Walk (A.c 1 y) (A.c 1 i)) (hP : wlen A.w (U.append (Q.append R)) = A.lam i)
    (hQ : ∀ z ∈ Q.support, ∀ σ r, r ≤ A.m → z = A.c σ r → z = A.c 0 x ∨ z = A.c 1 y) :
    IsLeast (A.copies (U.append (Q.append R))) (min i (min x y)) ∧
      IsGreatest (A.copies (U.append (Q.append R))) (max i (max x y)) := by
  obtain ⟨hU, hR⟩ := A.orient_len hi hx hy U Q R hP
  have hb : ∀ r ∈ A.copies (U.append (Q.append R)),
      min i (min x y) ≤ r ∧ r ≤ max i (max x y) := by
    rintro r ⟨hr, σ, hσ⟩
    simp only [Walk.mem_support_append_iff] at hσ
    rcases hσ with h | h | h
    · have := A.between ((A.short_via hi hx hr U h).trans hU.le)
      omega
    · rcases hQ _ h σ r hr rfl with e | e
      · have := A.idx_eq hr hx e
        omega
      · have := A.idx_eq hr hy e
        omega
    · have := A.between ((A.short_via hy hi hr R h).trans hR.le)
      omega
  have hmi : i ∈ A.copies (U.append (Q.append R)) := ⟨hi, 0, Walk.start_mem_support _⟩
  have hmx : x ∈ A.copies (U.append (Q.append R)) :=
    ⟨hx, 0, (Walk.mem_support_append_iff _ _).2 (Or.inl U.end_mem_support)⟩
  have hmy : y ∈ A.copies (U.append (Q.append R)) :=
    ⟨hy, 1, (Walk.mem_support_append_iff _ _).2
      (Or.inr ((Walk.mem_support_append_iff _ _).2 (Or.inl Q.end_mem_support)))⟩
  refine ⟨⟨?_, fun r hr => (hb r hr).1⟩, ⟨?_, fun r hr => (hb r hr).2⟩⟩
  · rcases (show min i (min x y) = i ∨ min i (min x y) = x ∨ min i (min x y) = y by omega)
      with e | e | e <;> rw [e] <;> assumption
  · rcases (show max i (max x y) = i ∨ max i (max x y) = x ∨ max i (max x y) = y by omega)
      with e | e | e <;> rw [e] <;> assumption

/-- Part (c) of the proof of Lemma S1, with its two cases: an index `t` strictly between
`min(i, x, y)` and `max(i, x, y)` is dominated by every index between `t` and one of the two. -/
theorem interval {i x y : ℕ} (hi : i ≤ A.m) (hx : x ≤ A.m) (hy : y ≤ A.m)
    (U : A.G.Walk (A.c 0 i) (A.c 0 x)) (Q : A.G.Walk (A.c 0 x) (A.c 1 y))
    (R : A.G.Walk (A.c 1 y) (A.c 1 i)) (hP : wlen A.w (U.append (Q.append R)) = A.lam i)
    (hS : ∀ t, min x y < t → t < max x y → ∀ W : A.G.Walk (A.c 0 t) (A.c 1 t),
      ∃ z ∈ W.support, z ∈ Q.support) :
    ∀ t, min i (min x y) < t → t < max i (max x y) →
      (∀ q, min i (min x y) ≤ q → q ≤ t → A.lam q ≤ A.lam t) ∨
      (∀ q, t ≤ q → q ≤ max i (max x y) → A.lam q ≤ A.lam t) := by
  classical
  obtain ⟨hU, hR⟩ := A.orient_len hi hx hy U Q R hP
  have hP' := hP
  rw [wlen_append, wlen_append] at hP'
  intro t h1 h2
  have ht : t ≤ A.m := by omega
  obtain ⟨W, hW⟩ := A.exists_lam_of hi ht (U.append (Q.append R))
  have hiW := A.lam_le_via hi ht ht W
  rw [hW] at hiW
  have cit := A.dP_comm i t
  by_cases hJ : min x y < t ∧ t < max x y
  · -- Case 2: `t` lies strictly inside `[x, y]`, so (S_1) gives a common node `z`.
    obtain ⟨z, hzW, hzQ⟩ := hS t hJ.1 hJ.2 W
    have hXY := wlen_split A.w W hzW
    have hQ12 := wlen_split A.w Q hzQ
    obtain ⟨Bit, hBit⟩ := A.copy 0 i t hi ht
    obtain ⟨Bti, hBti⟩ := A.copy 1 t i ht hi
    have hw1 := A.lam_le (Bit.append ((W.takeUntil z hzW).append ((Q.dropUntil z hzQ).append R)))
    have hw2 := A.lam_le (U.append ((Q.takeUntil z hzQ).append ((W.dropUntil z hzW).append Bti)))
    simp only [wlen_append, hBit, hBti] at hw1 hw2
    rcases le_or_gt i t with hit | hti
    · right
      intro q hq1 hq2
      have hq : q ≤ A.m := by omega
      rcases le_or_gt x y with hxy | hyx
      · have hB := A.lam_le_via hq ht hy ((W.takeUntil z hzW).append (Q.dropUntil z hzQ))
        rw [wlen_append] at hB
        have e1 := A.dP_add (show t ≤ q by omega) (show q ≤ y by omega)
        have e2 := A.dP_add hit (show t ≤ y by omega)
        have e3 := A.dP_comm q t
        have e4 := A.dP_comm y q
        have e5 := A.dP_comm y i
        omega
      · have hB := A.lam_le_via hq hx ht ((Q.takeUntil z hzQ).append (W.dropUntil z hzW))
        rw [wlen_append] at hB
        have e1 := A.dP_add (show t ≤ q by omega) (show q ≤ x by omega)
        have e2 := A.dP_add hit (show t ≤ x by omega)
        omega
    · left
      intro q hq1 hq2
      have hq : q ≤ A.m := by omega
      rcases le_or_gt x y with hxy | hyx
      · have hB := A.lam_le_via hq hx ht ((Q.takeUntil z hzQ).append (W.dropUntil z hzW))
        rw [wlen_append] at hB
        have e1 := A.dP_add (show x ≤ q by omega) (show q ≤ t by omega)
        have e2 := A.dP_add (show x ≤ t by omega) hti.le
        have e3 := A.dP_comm q x
        have e4 := A.dP_comm t q
        have e5 := A.dP_comm i x
        omega
      · have hB := A.lam_le_via hq ht hy ((W.takeUntil z hzW).append (Q.dropUntil z hzQ))
        rw [wlen_append] at hB
        have e1 := A.dP_add (show y ≤ q by omega) (show q ≤ t by omega)
        have e2 := A.dP_add (show y ≤ t by omega) hti.le
        have e3 := A.dP_comm q t
        omega
  · -- Case 1: `t` lies outside the interior of `[x, y]`, between `i` and it.
    have hQB := fun q (hq : q ≤ A.m) => A.lam_le_via hq hx hy Q
    rcases le_or_gt t (min x y) with htJ | htJ
    · right
      intro q hq1 hq2
      have hq : q ≤ A.m := by omega
      have hf := A.f_le_of_le htJ hq1 (by omega)
      have hB := hQB q hq
      have e1 := A.dP_add (show i ≤ t by omega) (show t ≤ x by omega)
      have e2 := A.dP_add (show i ≤ t by omega) (show t ≤ y by omega)
      have e3 := A.dP_comm y i
      have e4 := A.dP_comm y q
      omega
    · left
      intro q hq1 hq2
      have hq : q ≤ A.m := by omega
      have hf := A.f_le_of_ge (show max x y ≤ t by omega) hq2 (by omega)
      have hB := hQB q hq
      have e1 := A.dP_add (show x ≤ t by omega) (show t ≤ i by omega)
      have e2 := A.dP_add (show y ≤ t by omega) (show t ≤ i by omega)
      have e3 := A.dP_comm i x
      have e4 := A.dP_comm t x
      have e5 := A.dP_comm t y
      have e6 := A.dP_comm y q
      omega

/-- **Lemma S1.** Let `P` be a shortest walk from `p_i^0` to `p_i^1`, and let `i1` and `i2` be
the least and the greatest index of a copy of the dual path on it. Given (S_1), every index `t`
strictly between `i1` and `i2` has `λ_q ≤ λ_t` for all `q ∈ [i1, t]` or for all `q ∈ [t, i2]`. -/
theorem witness_interval (hS : A.Sep) {i : ℕ} (hi : i ≤ A.m) (P : A.G.Walk (A.c 0 i) (A.c 1 i))
    (hP : wlen A.w P = A.lam i) :
    ∃ i1 i2, IsLeast (A.copies P) i1 ∧ IsGreatest (A.copies P) i2 ∧ i1 ≤ i ∧ i ≤ i2 ∧
      ∀ t, i1 < t → t < i2 →
        (∀ q, i1 ≤ q → q ≤ t → A.lam q ≤ A.lam t) ∨ (∀ q, t ≤ q → q ≤ i2 → A.lam q ≤ A.lam t) := by
  obtain ⟨x, y, hx, hy, U, Q, R, rfl, hQ⟩ := A.orient hi P
  obtain ⟨h1, h2⟩ := A.copies_eq hi hx hy U Q R hP hQ
  exact ⟨_, _, h1, h2, min_le_left _ _, le_max_left _ _,
    A.interval hi hx hy U Q R hP (hS x y hx hy Q hQ)⟩

/-- The field `dom` of `Rec.node` for `lam = A.lam`, when the path of the node maps to a shortest
walk `P` of `A_1` whose least and greatest copy indices are `i1` and `i2`. -/
theorem dom_of_walk (hS : A.Sep) {i i1 i2 : ℕ} (hi : i ≤ A.m) (P : A.G.Walk (A.c 0 i) (A.c 1 i))
    (hP : wlen A.w P = A.lam i) (h1 : IsLeast (A.copies P) i1) (h2 : IsGreatest (A.copies P) i2) :
    i1 ≤ i ∧ i ≤ i2 ∧ ∀ t, i1 < t → t < i2 →
      (∀ q, i1 ≤ q → q ≤ t → A.lam q ≤ A.lam t) ∨ (∀ q, t ≤ q → q ≤ i2 → A.lam q ≤ A.lam t) := by
  obtain ⟨j1, j2, hj1, hj2, hji, hij, hdom⟩ := A.witness_interval hS hi P hP
  obtain rfl := h1.unique hj1
  obtain rfl := h2.unique hj2
  exact ⟨hji, hij, hdom⟩

/-- A node of the recursion for `lam = A.lam` whose path maps to a shortest walk `P` of `A_1`:
Lemma S1 supplies the field `dom`. -/
def nodeOfWalk (hS : A.Sep) {j k i i1 i2 : ℕ} (hji : j ≤ i) (hik : i ≤ k) (hi : i ≤ A.m)
    (P : A.G.Walk (A.c 0 i) (A.c 1 i)) (hP : wlen A.w P = A.lam i)
    (h1 : IsLeast (A.copies P) i1) (h2 : IsGreatest (A.copies P) i2)
    (left : Side A.lam j i1) (right : Side A.lam i2 k) : Rec A.lam j k :=
  .node i i1 i2 hji hik (A.dom_of_walk hS hi P hP h1 h2).1 (A.dom_of_walk hS hi P hP h1 h2).2.1
    (A.dom_of_walk hS hi P hP h1 h2).2.2 left right

end Annulus

end SsspFlow.Recursion
