import PlanarMatching.ElimRun

/-!
# The elimination in the tree of bags

`notes/GENERAL.md`, Section 3, Lemma 2. The bags are the numbers `X < T` in the order in which they are processed,
children before parents. A bag `X` forms its matrix `M_X` from the retained matrices `M″_Y` of its children and the
parts `A_e` of the edges assigned to it, on an index set `J_X`, and applies Lemma 1 with `I_X = J_X ∖ ∂X`
(`ElimData`). The facts on the tree enter as hypotheses (`ElimData.Valid`): the chain of a vertex is comparable with
every bag whose index set holds the vertex, the bag of an edge lies below the chains of its ends (Fact 1), and the home
of a vertex is the lowest bag of its chain.

* `ElimData.N_split`: before bag `t`, the global matrix is `M_t` plus a matrix that vanishes on the rows and columns
  of `I_t`, so the step of bag `t` is a local step of the global run.
* `ElimData.correct` (Lemma 2): every vertex is pivoted or dropped at exactly one bag, the rank of `A` is the number
  of pivots, and the block of `A` on the pivots is nonsingular.
-/

namespace PlanarMatching

open Matrix Relation Finset

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] {V : Type*} [Fintype V] [DecidableEq V]

theorem IsAlternating.add {M E : Matrix V V K} (hM : IsAlternating M) (hE : IsAlternating E) :
    IsAlternating (M + E) :=
  ⟨by rw [transpose_add, hM.skew, hE.skew, neg_add], fun i => by simp [hM.diag, hE.diag]⟩

theorem IsAlternating.sum {ι : Type*} (s : Finset ι) {f : ι → Matrix V V K}
    (h : ∀ i ∈ s, IsAlternating (f i)) : IsAlternating (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => exact ⟨by simp, fun _ => by simp⟩
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact (h a (Finset.mem_cons_self a s)).add (ih fun i hi => h i (Finset.mem_cons_of_mem hi))

/-- `E` vanishes on the rows and the columns of `S`. -/
def Quiet (E : Matrix V V K) (S : Finset V) : Prop := ∀ i ∈ S, ∀ j, E i j = 0 ∧ E j i = 0

theorem elim_add {M E : Matrix V V K} {P : Finset V} (hE : Quiet E P) : elim (M + E) P = elim M P + E := by
  have h1 : (M + E).submatrix id ((↑) : P → V) = M.submatrix id (↑) := by
    ext i p; simp [(hE p p.2 i).2]
  have h2 : (M + E).submatrix ((↑) : P → V) id = M.submatrix (↑) id := by
    ext p j; simp [(hE p p.2 j).1]
  have h3 : principal (M + E) P = principal M P := by
    ext a b; simp [(hE a a.2 b).1]
  unfold elim
  rw [h1, h2, h3]
  abel

theorem restrict_add {X E : Matrix V V K} {S : Finset V} (hE : ∀ i j, i ∉ S ∨ j ∉ S → E i j = 0) :
    restrict (X + E) S = restrict X S + E := by
  ext i j
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [restrict, hi, hj, hE i j]

theorem step_add {M E : Matrix V V K} {I P D : Finset V} (hPI : P ⊆ I) (hDI : D ⊆ I) (hE : Quiet E I) :
    step (M + E) P D = step M P D + E := by
  rw [step, step, elim_add (fun p hp j => hE p (hPI hp) j), restrict_add]
  intro i j hij
  rcases hij with hi | hj
  · rw [Finset.mem_compl, not_not, Finset.mem_union] at hi
    rcases hi with hi | hi
    · exact (hE i (hPI hi) j).1
    · exact (hE i (hDI hi) j).1
  · rw [Finset.mem_compl, not_not, Finset.mem_union] at hj
    rcases hj with hj | hj
    · exact (hE j (hPI hj) i).2
    · exact (hE j (hDI hj) i).2

/-- A local step stays local after adding a matrix that vanishes on the rows and columns of `I`. -/
theorem LocalStep.add {M E : Matrix V V K} {I J P Q : Finset V} (h : LocalStep M I J P Q) (hE : Quiet E I) :
    LocalStep (M + E) I J P Q := by
  have hpr : ∀ S ⊆ I, principal (M + E) S = principal M S := fun S hS => by
    ext a b; simp [(hE a (hS a.2) b).1]
  have hel : ∀ d ∈ I, ∀ j, elim (M + E) P d j = elim M P d j := by
    intro d hd j
    rw [elim_add (fun p hp j => hE p (h.piv hp) j)]
    simp [(hE d hd j).1]
  refine ⟨h.sub, fun i hi j hj => ?_, h.piv, ?_, ?_, h.ret, fun d hd => ?_⟩
  · simp [h.supp i hi j hj, (hE i hi j).1]
  · rw [hpr P h.piv]; exact h.unit
  · rw [hpr I subset_rfl]; exact h.rank
  · obtain ⟨c, hc⟩ := h.span d hd
    refine ⟨c, fun j hj => ?_⟩
    rw [hel d (Finset.mem_sdiff.1 hd).1, hc j hj]
    exact Finset.sum_congr rfl fun q _ => by rw [hel q (Finset.mem_sdiff.1 (h.ret q.2)).1]

/-- The data of one run of the elimination over the bags `X < T`, children before parents. -/
structure ElimData (K V : Type*) [Field K] [Fintype V] [DecidableEq V] where
  T : ℕ
  /-- `ch Y X`: the bag `Y` is a child of the bag `X`. -/
  ch : ℕ → ℕ → Prop
  /-- The index set `W`. -/
  W : Finset V
  /-- `∂X`. -/
  bd : ℕ → Finset V
  /-- `chain x X`: the bag `X` lies on the chain of `x`. -/
  chain : V → ℕ → Prop
  home : V → ℕ
  E : Type
  [fE : Fintype E]
  /-- The ends of an edge. -/
  en : E → Finset V
  /-- The bag an edge is assigned to. -/
  as : E → ℕ
  /-- The part `A_e` of an edge. -/
  Ae : E → Matrix V V K
  /-- The matrix `M_X` of a bag. -/
  M : ℕ → Matrix V V K
  J : ℕ → Finset V
  /-- The pivots `P_X`. -/
  P : ℕ → Finset V
  /-- The retained rows `I″_X`. -/
  Q : ℕ → Finset V

attribute [instance] ElimData.fE

namespace ElimData

open Classical

variable (S : ElimData K V)

/-- `I_X = J_X ∖ ∂X`. -/
def I (X : ℕ) : Finset V := S.J X \ S.bd X

/-- The dropped set `D_X`. -/
def D (X : ℕ) : Finset V := S.I X \ (S.P X ∪ S.Q X)

/-- `M″_X`, on all indices. -/
noncomputable def out (X : ℕ) : Matrix V V K := step (S.M X) (S.P X) (S.D X)

/-- The index set of `M″_X`. -/
def ret (X : ℕ) : Finset V := S.Q X ∪ (S.J X ∩ S.bd X)

def desc : ℕ → ℕ → Prop := TransGen S.ch

open Classical in
/-- The children of a bag. -/
noncomputable def kids (X : ℕ) : Finset ℕ := (range S.T).filter (S.ch · X)

open Classical in
/-- The edges assigned to a bag. -/
noncomputable def own (X : ℕ) : Finset S.E := univ.filter (S.as · = X)

/-- The matrix to be eliminated. -/
noncomputable def A : Matrix V V K := ∑ e, S.Ae e

/-- The hypotheses on the tree and the steps of the bags. -/
structure Valid : Prop where
  ch_lt : ∀ {c b}, S.ch c b → c < b
  ch_T : ∀ {c b}, S.ch c b → b < S.T
  par_uniq : ∀ {c b b'}, S.ch c b → S.ch c b' → b = b'
  alt : ∀ e, IsAlternating (S.Ae e)
  Ae_supp : ∀ e i j, i ∉ S.en e ∨ j ∉ S.en e → S.Ae e i j = 0
  en_W : ∀ e, S.en e ⊆ S.W
  as_T : ∀ e, S.as e < S.T
  home_T : ∀ x ∈ S.W, S.home x < S.T
  /-- The home is the lowest bag of the chain. -/
  home_low : ∀ {x X}, x ∈ S.W → S.chain x X → S.home x = X ∨ S.desc (S.home x) X
  /-- A bag whose index set holds `x` is comparable with every bag on the chain of `x`. -/
  comp : ∀ {x X Y}, S.chain x X → x ∈ S.J Y → Y = X ∨ S.desc Y X ∨ S.desc X Y
  /-- Fact 1: an edge is assigned below every bag on the chains of its ends. -/
  edge : ∀ {x X e}, x ∈ S.en e → S.chain x X → S.as e = X ∨ S.desc (S.as e) X
  /-- `I_X ⊆ X°`. -/
  off : ∀ {x X}, x ∈ S.I X → S.chain x X
  hM : ∀ X, S.M X = ∑ Y ∈ S.kids X, S.out Y + ∑ e ∈ S.own X, S.Ae e
  hJ : ∀ X, S.J X = (S.kids X).biUnion S.ret ∪ (S.own X).biUnion S.en ∪ S.W.filter (S.home · = X)
  loc : ∀ X < S.T, LocalStep (S.M X) (S.I X) (S.J X) (S.P X) (S.Q X)
  root_bd : ∀ X < S.T, (∀ b, ¬ S.ch X b) → S.bd X = ∅
  /-- The retained rows are independent on `J_X ∖ I_X`. -/
  indep : ∀ X < S.T, LinearIndependent K fun q : S.Q X => fun j : ↥(S.J X \ S.I X) => elim (S.M X) (S.P X) q j

open Classical in
/-- The bags processed before `t` whose parent is not. -/
noncomputable def front (t : ℕ) : Finset ℕ := (range t).filter fun Y => ∀ b, S.ch Y b → t ≤ b

open Classical in
noncomputable def edgesFrom (t : ℕ) : Finset S.E := univ.filter fun e => t ≤ S.as e

/-- The global matrix before bag `t`. -/
noncomputable def N (t : ℕ) : Matrix V V K := ∑ Y ∈ S.front t, S.out Y + ∑ e ∈ S.edgesFrom t, S.Ae e

open Classical in
/-- The live indices before bag `t`. -/
noncomputable def R (t : ℕ) : Finset V :=
  (S.front t).biUnion S.ret ∪ (S.edgesFrom t).biUnion S.en ∪ S.W.filter fun x => t ≤ S.home x

open Classical in
/-- The part of `N t` away from bag `t`. -/
noncomputable def rest (t : ℕ) : Matrix V V K :=
  ∑ Y ∈ (S.front t).filter (¬ S.ch · t), S.out Y + ∑ e ∈ univ.filter (fun e => t < S.as e), S.Ae e

variable {S}

theorem mem_front {t Y : ℕ} : Y ∈ S.front t ↔ Y < t ∧ ∀ b, S.ch Y b → t ≤ b := by
  simp [front]

theorem mem_R {t : ℕ} {x : V} : x ∈ S.R t ↔
    (∃ Y ∈ S.front t, x ∈ S.ret Y) ∨ (∃ e, t ≤ S.as e ∧ x ∈ S.en e) ∨ (x ∈ S.W ∧ t ≤ S.home x) := by
  simp [R, edgesFrom, or_assoc]

theorem mem_ret_of {X : ℕ} {x : V} (hx : x ∈ S.J X) (hn : x ∉ S.P X ∪ S.D X) : x ∈ S.ret X := by
  simp only [ret, D, I, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, not_or, not_and,
    not_not] at hn ⊢
  by_cases hb : x ∈ S.bd X
  · exact Or.inr ⟨hx, hb⟩
  · exact Or.inl (hn.2 ⟨hx, hb⟩ hn.1)

namespace Valid

variable (hv : S.Valid)
include hv

theorem desc_lt {c b : ℕ} (h : S.desc c b) : c < b := by
  induction h with
  | single h => exact hv.ch_lt h
  | tail _ h ih => exact ih.trans (hv.ch_lt h)

theorem mem_J {X : ℕ} {x : V} : x ∈ S.J X ↔
    (∃ Y, Y < S.T ∧ S.ch Y X ∧ x ∈ S.ret Y) ∨ (∃ e, S.as e = X ∧ x ∈ S.en e) ∨
      (x ∈ S.W ∧ S.home x = X) := by
  rw [hv.hJ]
  simp [kids, own, or_assoc, and_assoc]

theorem ret_sub {X : ℕ} (hX : X < S.T) : S.ret X ⊆ S.J X := by
  intro x hx
  rcases Finset.mem_union.1 hx with h | h
  · exact (hv.loc X hX).sub (Finset.mem_sdiff.1 ((hv.loc X hX).ret h)).1
  · exact (Finset.mem_inter.1 h).1

theorem not_mem_ret {X : ℕ} (hX : X < S.T) {x : V} (hx : x ∈ S.ret X) : x ∉ S.P X ∪ S.D X := by
  have hl := hv.loc X hX
  intro hpd
  have hI : x ∈ S.I X := by
    rcases Finset.mem_union.1 hpd with h | h
    · exact hl.piv h
    · exact (Finset.mem_sdiff.1 h).1
  rcases Finset.mem_union.1 hx with h | h
  · have hq := Finset.mem_sdiff.1 (hl.ret h)
    rcases Finset.mem_union.1 hpd with h' | h'
    · exact hq.2 h'
    · exact (Finset.mem_sdiff.1 h').2 (Finset.mem_union_right _ h)
  · exact (Finset.mem_sdiff.1 hI).2 (Finset.mem_inter.1 h).2

theorem pd_sub_I {X : ℕ} (hX : X < S.T) : S.P X ∪ S.D X ⊆ S.I X :=
  Finset.union_subset (hv.loc X hX).piv Finset.sdiff_subset

/-- `M_X` vanishes outside `J_X`, and `M″_X` outside the index set of `M″_X`. -/
theorem supp : ∀ X, (∀ i j, i ∉ S.J X ∨ j ∉ S.J X → S.M X i j = 0) ∧
    (X < S.T → ∀ i j, i ∉ S.ret X ∨ j ∉ S.ret X → S.out X i j = 0) := by
  intro X
  induction X using Nat.strong_induction_on with
  | _ X ih =>
  have hM : ∀ i j, i ∉ S.J X ∨ j ∉ S.J X → S.M X i j = 0 := by
    intro i j hij
    rw [hv.hM X, Matrix.add_apply, Matrix.sum_apply, Matrix.sum_apply]
    have hk : ∀ Y ∈ S.kids X, S.ret Y ⊆ S.J X := fun Y hY x hx => by
      rw [hv.hJ]; exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨Y, hY, hx⟩))
    have ho : ∀ e ∈ S.own X, S.en e ⊆ S.J X := fun e he x hx => by
      rw [hv.hJ]; exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨e, he, hx⟩))
    rw [Finset.sum_eq_zero fun Y hY => ?_, Finset.sum_eq_zero fun e he => ?_, add_zero]
    · refine hv.Ae_supp e i j ?_
      rcases hij with h | h
      · exact Or.inl fun h' => h (ho e he h')
      · exact Or.inr fun h' => h (ho e he h')
    · have hY' : Y < S.T ∧ S.ch Y X := by simpa [kids] using hY
      refine (ih Y (hv.ch_lt hY'.2)).2 hY'.1 i j ?_
      rcases hij with h | h
      · exact Or.inl fun h' => h (hk Y hY h')
      · exact Or.inr fun h' => h (hk Y hY h')
  refine ⟨hM, fun hX i j hij => ?_⟩
  have hl := hv.loc X hX
  unfold out step
  by_cases hc : i ∈ (S.P X ∪ S.D X)ᶜ ∧ j ∈ (S.P X ∪ S.D X)ᶜ
  · rw [restrict_apply_of_mem hc.1 hc.2]
    rcases hij with h | h
    · have hiJ : i ∉ S.J X := fun h' => h (mem_ret_of h' (Finset.mem_compl.1 hc.1))
      rw [elim_eq_of_row fun p hp => hM i p (Or.inl hiJ)]
      exact hM i j (Or.inl hiJ)
    · have hjJ : j ∉ S.J X := fun h' => h (mem_ret_of h' (Finset.mem_compl.1 hc.2))
      rw [elim_eq_of_col fun p hp => hM p j (Or.inr hjJ)]
      exact hM i j (Or.inr hjJ)
  · exact restrict_apply_of_not_mem (by tauto)

theorem out_supp {X : ℕ} (hX : X < S.T) {i j : V} (h : i ∉ S.ret X ∨ j ∉ S.ret X) : S.out X i j = 0 :=
  (hv.supp X).2 hX i j h

theorem ch_of_front {t Y : ℕ} (hY : Y ∈ S.front t) (hd : S.desc Y t) : S.ch Y t := by
  obtain ⟨b, hb, hbt⟩ := TransGen.head'_iff.1 hd
  rcases reflTransGen_iff_eq_or_transGen.1 hbt with e | h'
  · rw [← e] at hb; exact hb
  · exact absurd (hv.desc_lt h') (not_lt.2 ((mem_front.1 hY).2 b hb))

/-- The index sets of the bags in the front away from `t` miss `I_t`. -/
theorem not_ret {t : ℕ} {x : V} (hx : x ∈ S.I t) {Y : ℕ} (hY : Y ∈ S.front t) (hn : ¬ S.ch Y t) (ht : t < S.T) :
    x ∉ S.ret Y := by
  intro hr
  have hYt := (mem_front.1 hY).1
  rcases hv.comp (hv.off hx) (hv.ret_sub (hYt.trans ht) hr) with e | h | h
  · omega
  · exact hn (hv.ch_of_front hY h)
  · have := hv.desc_lt h; omega

/-- Fact 1: the edges assigned after bag `t` miss `I_t`. -/
theorem not_en {t : ℕ} {x : V} (hx : x ∈ S.I t) {e : S.E} (he : t < S.as e) : x ∉ S.en e := by
  intro h
  rcases hv.edge h (hv.off hx) with e' | h'
  · omega
  · have := hv.desc_lt h'; omega

theorem not_home {t : ℕ} {x : V} (hx : x ∈ S.I t) (hW : x ∈ S.W) (ht : t < S.home x) : False := by
  rcases hv.home_low hW (hv.off hx) with e | h
  · omega
  · have := hv.desc_lt h; omega

theorem rest_quiet {t : ℕ} (ht : t < S.T) : Quiet (S.rest t) (S.I t) := by
  intro i hi j
  have hY : ∀ Y ∈ (S.front t).filter (¬ S.ch · t), ∀ a b, (a = i ∨ b = i) → S.out Y a b = 0 := by
    intro Y hY a b hab
    have hY' := Finset.mem_filter.1 hY
    have hn := hv.not_ret hi hY'.1 hY'.2 ht
    refine hv.out_supp (((mem_front.1 hY'.1).1).trans ht) ?_
    rcases hab with rfl | rfl
    · exact Or.inl hn
    · exact Or.inr hn
  have hE : ∀ e ∈ univ.filter (fun e => t < S.as e), ∀ a b, (a = i ∨ b = i) → S.Ae e a b = 0 := by
    intro e he a b hab
    have hn := hv.not_en hi (Finset.mem_filter.1 he).2
    refine hv.Ae_supp e a b ?_
    rcases hab with rfl | rfl
    · exact Or.inl hn
    · exact Or.inr hn
  simp only [rest, Matrix.add_apply, Matrix.sum_apply]
  constructor
  · rw [Finset.sum_eq_zero fun Y h => hY Y h i j (Or.inl rfl),
      Finset.sum_eq_zero fun e h => hE e h i j (Or.inl rfl), add_zero]
  · rw [Finset.sum_eq_zero fun Y h => hY Y h j i (Or.inr rfl),
      Finset.sum_eq_zero fun e h => hE e h j i (Or.inr rfl), add_zero]

theorem front_ch {t : ℕ} (ht : t < S.T) : (S.front t).filter (S.ch · t) = S.kids t := by
  ext Y
  simp only [Finset.mem_filter, mem_front, kids, Finset.mem_range]
  constructor
  · rintro ⟨⟨hY, -⟩, hc⟩; exact ⟨hY.trans ht, hc⟩
  · rintro ⟨-, hc⟩
    exact ⟨⟨hv.ch_lt hc, fun b hb => (hv.par_uniq hc hb) ▸ le_rfl⟩, hc⟩

theorem front_succ {t : ℕ} : S.front (t + 1) = insert t ((S.front t).filter (¬ S.ch · t)) := by
  ext Y
  simp only [Finset.mem_insert, Finset.mem_filter, mem_front]
  constructor
  · rintro ⟨hY, hb⟩
    by_cases e : Y = t
    · exact Or.inl e
    · refine Or.inr ⟨⟨by omega, fun b h => by have := hb b h; omega⟩, fun h => ?_⟩
      have := hb t h; omega
  · rintro (rfl | ⟨⟨hY, hb⟩, hn⟩)
    · exact ⟨by omega, fun b h => hv.ch_lt h⟩
    · refine ⟨by omega, fun b h => ?_⟩
      have := hb b h
      rcases Nat.lt_or_ge t b with h' | h'
      · omega
      · have e : b = t := by omega
        exact absurd (e ▸ h) hn

/-- Before bag `t`, the global matrix is `M_t` plus a matrix away from `I_t`. -/
theorem N_split {t : ℕ} (ht : t < S.T) : S.N t = S.M t + S.rest t := by
  classical
  have h1 := Finset.sum_filter_add_sum_filter_not (S.front t) (S.ch · t) S.out
  have h2 := Finset.sum_filter_add_sum_filter_not (S.edgesFrom t) (fun e => S.as e = t) S.Ae
  have h3 : (S.edgesFrom t).filter (fun e => S.as e = t) = S.own t := by
    ext e; simp [edgesFrom, own]; omega
  have h4 : (S.edgesFrom t).filter (fun e => ¬ S.as e = t) = univ.filter (fun e => t < S.as e) := by
    ext e; simp [edgesFrom]; omega
  rw [hv.front_ch ht] at h1
  rw [h3, h4] at h2
  rw [N, ← h1, ← h2, hv.hM t, rest]
  abel

theorem N_succ (t : ℕ) : S.N (t + 1) = S.out t + S.rest t := by
  classical
  have h1 : t ∉ (S.front t).filter (¬ S.ch · t) := by simp [mem_front]
  have h2 : S.edgesFrom (t + 1) = univ.filter (fun e => t < S.as e) := by
    ext e; simp [edgesFrom]
  rw [N, hv.front_succ, Finset.sum_insert h1, h2, rest]
  abel

theorem J_sub_R (t : ℕ) : S.J t ⊆ S.R t := by
  intro x hx
  rw [mem_R]
  rcases (hv.mem_J).1 hx with ⟨Y, hY, hc, hr⟩ | ⟨e, he, hen⟩ | ⟨hW, hh⟩
  · refine Or.inl ⟨Y, mem_front.2 ⟨hv.ch_lt hc, fun b hb => (hv.par_uniq hc hb) ▸ le_rfl⟩, hr⟩
  · exact Or.inr (Or.inl ⟨e, he.ge, hen⟩)
  · exact Or.inr (Or.inr ⟨hW, hh.ge⟩)

theorem live {t : ℕ} (ht : t < S.T) : S.R (t + 1) = S.R t \ (S.P t ∪ S.D t) := by
  have hJret : ∀ x ∈ S.J t, x ∉ S.P t ∪ S.D t → x ∈ S.R (t + 1) := fun x hx hn =>
    mem_R.2 (Or.inl ⟨t, mem_front.2 ⟨by omega, fun b h => hv.ch_lt h⟩, mem_ret_of hx hn⟩)
  ext x
  rw [Finset.mem_sdiff]
  constructor
  · intro hx
    rcases mem_R.1 hx with ⟨Y, hY, hr⟩ | ⟨e, he, hen⟩ | ⟨hW, hh⟩
    · rw [hv.front_succ, Finset.mem_insert] at hY
      rcases hY with rfl | hY
      · exact ⟨hv.J_sub_R _ (hv.ret_sub ht hr), hv.not_mem_ret ht hr⟩
      · have hY' := Finset.mem_filter.1 hY
        exact ⟨mem_R.2 (Or.inl ⟨Y, hY'.1, hr⟩),
          fun h => hv.not_ret (hv.pd_sub_I ht h) hY'.1 hY'.2 ht hr⟩
    · exact ⟨mem_R.2 (Or.inr (Or.inl ⟨e, by omega, hen⟩)),
        fun h => hv.not_en (hv.pd_sub_I ht h) (by omega : t < S.as e) hen⟩
    · exact ⟨mem_R.2 (Or.inr (Or.inr ⟨hW, by omega⟩)),
        fun h => hv.not_home (hv.pd_sub_I ht h) hW (by omega)⟩
  · rintro ⟨hx, hn⟩
    rcases mem_R.1 hx with ⟨Y, hY, hr⟩ | ⟨e, he, hen⟩ | ⟨hW, hh⟩
    · by_cases hc : S.ch Y t
      · exact hJret x ((hv.mem_J).2 (Or.inl ⟨Y, ((mem_front.1 hY).1).trans ht, hc, hr⟩)) hn
      · refine mem_R.2 (Or.inl ⟨Y, ?_, hr⟩)
        rw [hv.front_succ]
        exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hY, hc⟩)
    · by_cases he' : S.as e = t
      · exact hJret x ((hv.mem_J).2 (Or.inr (Or.inl ⟨e, he', hen⟩))) hn
      · exact mem_R.2 (Or.inr (Or.inl ⟨e, by omega, hen⟩))
    · by_cases hh' : S.home x = t
      · exact hJret x ((hv.mem_J).2 (Or.inr (Or.inr ⟨hW, hh'⟩))) hn
      · exact mem_R.2 (Or.inr (Or.inr ⟨hW, by omega⟩))

/-- A root retains nothing. -/
theorem ret_root {Y : ℕ} (hY : Y < S.T) (hr : ∀ b, ¬ S.ch Y b) : S.ret Y = ∅ := by
  have hb := hv.root_bd Y hY hr
  have hJI : S.J Y \ S.I Y = ∅ := by simp [I, hb]
  have hQ : S.Q Y = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun q hq => ?_
    refine (hv.indep Y hY).ne_zero ⟨q, hq⟩ ?_
    funext j
    exact absurd j.2 (by simp [hJI])
  simp [ret, hQ, hb]

theorem done : S.R S.T = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
  rcases mem_R.1 hx with ⟨Y, hY, hr⟩ | ⟨e, he, -⟩ | ⟨hW, hh⟩
  · have hY' := mem_front.1 hY
    have hroot : ∀ b, ¬ S.ch Y b := fun b h => absurd (hY'.2 b h) (not_le.2 (hv.ch_T h))
    simp [hv.ret_root hY'.1 hroot] at hr
  · exact absurd he (not_le.2 (hv.as_T e))
  · exact absurd hh (not_le.2 (hv.home_T x hW))

theorem N_zero : S.N 0 = S.A := by
  classical
  have h1 : S.front 0 = ∅ := by ext Y; simp [mem_front]
  have h2 : S.edgesFrom 0 = univ := by ext e; simp [edgesFrom]
  simp [N, h1, h2, A]

/-- The bags form a run of local steps. -/
theorem run : Run S.N S.R S.I S.J S.P S.Q S.T := by
  refine ⟨?_, ?_, fun t ht => ?_, fun t ht => hv.live ht, fun t _ => hv.J_sub_R t, fun t ht => ?_, hv.done⟩
  · rw [hv.N_zero]
    exact IsAlternating.sum _ fun e _ => hv.alt e
  · intro i j hij
    rw [hv.N_zero, A, Matrix.sum_apply]
    refine Finset.sum_eq_zero fun e _ => hv.Ae_supp e i j ?_
    have : ∀ y, y ∈ S.en e → y ∈ S.R 0 := fun y hy => mem_R.2 (Or.inr (Or.inl ⟨e, Nat.zero_le _, hy⟩))
    rcases hij with h | h
    · exact Or.inl fun h' => h (this i h')
    · exact Or.inr fun h' => h (this j h')
  · rw [hv.N_succ t, hv.N_split ht, out]
    exact (step_add (hv.loc t ht).piv Finset.sdiff_subset (hv.rest_quiet ht)).symm
  · rw [hv.N_split ht]
    exact (hv.loc t ht).add (hv.rest_quiet ht)

/-- **Lemma 2.** Every vertex of `W` is pivoted or dropped at exactly one bag, the rank of `A` is the number of
pivots `B`, and `A_{B,B}` is nonsingular. -/
theorem correct : (∀ x ∈ S.W, ∃! t, t < S.T ∧ x ∈ S.P t ∪ S.D t) ∧
    S.A.rank = (Run.pivots S.P S.T).card ∧ (principal S.A (Run.pivots S.P S.T)).det ≠ 0 := by
  have hr := hv.run
  refine ⟨fun x hx => hr.partition (mem_R.2 (Or.inr (Or.inr ⟨hx, Nat.zero_le _⟩))), ?_, ?_⟩
  · rw [← hv.N_zero, hr.rank, hr.card_pivots]
  · rw [← hv.N_zero]; exact hr.det

end Valid

end ElimData

end PlanarMatching
