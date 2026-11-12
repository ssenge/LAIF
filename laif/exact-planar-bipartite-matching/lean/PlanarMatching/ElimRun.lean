import PlanarMatching.Tutte

/-!
# The elimination as a run of global steps

`notes/GENERAL.md`, Lemma 2, over a field `K` and a finite index type `V`. All matrices live on the whole of `V`.
A step eliminates a set `P` of pivots by a Schur complement (`elim`) and then sets the rows and columns of a set of
dropped indices to zero (`step`). A step is local if the rows of the indices `I` it works on vanish outside a set
`J ⊇ I`, the pivots and the retained rows are chosen as in Lemma 1 from the block on `J`, and the dropped indices are
the rest of `I` (`LocalStep`).

* `elim_eq_of_not_mem`: a step changes only the entries inside `J × J`, and there it is the Schur complement of the
  block on `J` (`elim_restrict`).
* `LocalStep.rank`: one local step keeps `rank = |P| + rank` of the next matrix.
* `run_rank`, `run_partition`, `run_det`: for a run that ends with no live index, every live index of the start is
  pivoted or dropped exactly once, the rank is the number of pivots `B`, and the block on `B` is nonsingular.
-/

namespace PlanarMatching

open Matrix

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] {V : Type*} [Fintype V] [DecidableEq V]

/-- The matrix with the rows and columns outside `S` set to zero. -/
def restrict (M : Matrix V V K) (S : Finset V) : Matrix V V K :=
  Matrix.of fun i j => if i ∈ S ∧ j ∈ S then M i j else 0

/-- The Schur complement of the block on `P`, on all indices. -/
noncomputable def elim (M : Matrix V V K) (P : Finset V) : Matrix V V K :=
  M - M.submatrix id ((↑) : P → V) * (principal M P)⁻¹ * M.submatrix ((↑) : P → V) id

/-- One step: eliminate `P`, then drop `D`. -/
noncomputable def step (M : Matrix V V K) (P D : Finset V) : Matrix V V K :=
  restrict (elim M P) (P ∪ D)ᶜ

theorem elim_eq_schurOn (M : Matrix V V K) (P : Finset V) :
    elim M P = schurOn M ((↑) : P → V) id := by
  simp [elim, schurOn]

theorem IsAlternating.restrict {M : Matrix V V K} (hM : IsAlternating M) (S : Finset V) :
    IsAlternating (restrict M S) := by
  refine ⟨?_, fun i => by simp [PlanarMatching.restrict, hM.diag]⟩
  ext i j
  have := hM.apply j i
  simp only [transpose_apply, PlanarMatching.restrict, of_apply]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [hi, hj, hM.apply i j]

theorem IsAlternating.elim {M : Matrix V V K} (hM : IsAlternating M) {P : Finset V}
    (hP : IsUnit (principal M P).det) : IsAlternating (elim M P) := by
  rw [elim_eq_schurOn]
  exact hM.schurOn _ _ hP

theorem IsAlternating.step {M : Matrix V V K} (hM : IsAlternating M) {P : Finset V}
    (hP : IsUnit (principal M P).det) (D : Finset V) : IsAlternating (step M P D) :=
  (hM.elim hP).restrict _

/-- The rank of a matrix that vanishes outside `S × S` is the rank of its block on `S`. -/
theorem rank_eq_principal {M : Matrix V V K} {S : Finset V} (h : ∀ i j, i ∉ S ∨ j ∉ S → M i j = 0) :
    M.rank = (principal M S).rank := by
  have hc : ∀ y : ↥Sᶜ, ((splitEquiv S) (Sum.inr y)) ∉ S := fun y => by
    simpa [splitEquiv] using Finset.mem_compl.mp y.2
  rw [← rank_submatrix M (splitEquiv S) (splitEquiv S), submatrix_sum_eq_fromBlocks]
  have h₁ : M.submatrix (splitEquiv S ∘ Sum.inl) (splitEquiv S ∘ Sum.inr) = 0 := by
    ext i j; exact h _ _ (Or.inr (hc j))
  have h₂ : M.submatrix (splitEquiv S ∘ Sum.inr) (splitEquiv S ∘ Sum.inl) = 0 := by
    ext i j; exact h _ _ (Or.inl (hc i))
  have h₃ : M.submatrix (splitEquiv S ∘ Sum.inr) (splitEquiv S ∘ Sum.inr) = 0 := by
    ext i j; exact h _ _ (Or.inl (hc i))
  rw [h₁, h₂, h₃, rank_fromBlocks_zero, rank_zero, add_zero]
  rfl

theorem restrict_apply_of_mem {M : Matrix V V K} {S : Finset V} {i j : V} (hi : i ∈ S) (hj : j ∈ S) :
    restrict M S i j = M i j := by
  simp [restrict, hi, hj]

theorem restrict_apply_of_not_mem {M : Matrix V V K} {S : Finset V} {i j : V} (h : i ∉ S ∨ j ∉ S) :
    restrict M S i j = 0 := by
  rcases h with h | h <;> simp [restrict, h]

theorem rank_restrict (M : Matrix V V K) (S : Finset V) : (restrict M S).rank = (principal M S).rank := by
  rw [rank_eq_principal fun i j h => restrict_apply_of_not_mem h]
  congr 1
  ext a b
  exact restrict_apply_of_mem a.2 b.2

/-- The rows of the pivots are zero after the elimination. -/
theorem elim_row {M : Matrix V V K} {P : Finset V} (hP : IsUnit (principal M P).det) {p : V} (hp : p ∈ P)
    (j : V) : elim M P p j = 0 := by
  have h : ∀ b : P, (M.submatrix id ((↑) : P → V) * (principal M P)⁻¹) p b =
      (1 : Matrix P P K) ⟨p, hp⟩ b := by
    intro b
    rw [← mul_nonsing_inv _ hP]
    rfl
  rw [elim, Matrix.sub_apply, Matrix.mul_apply]
  simp only [h, Matrix.one_apply, submatrix_apply, id]
  rw [Finset.sum_eq_single ⟨p, hp⟩ (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

/-- The columns of the pivots are zero after the elimination. -/
theorem elim_col {M : Matrix V V K} {P : Finset V} (hP : IsUnit (principal M P).det) {p : V} (hp : p ∈ P)
    (i : V) : elim M P i p = 0 := by
  have h : ∀ b : P, ((principal M P)⁻¹ * M.submatrix ((↑) : P → V) id) b p =
      (1 : Matrix P P K) b ⟨p, hp⟩ := by
    intro b
    rw [← nonsing_inv_mul _ hP]
    rfl
  rw [elim, Matrix.sub_apply, Matrix.mul_assoc, Matrix.mul_apply]
  simp only [h, Matrix.one_apply, submatrix_apply, id]
  rw [Finset.sum_eq_single ⟨p, hp⟩ (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- Outside the rows and columns that meet the pivots, the elimination changes nothing. -/
theorem elim_eq_of_col {M : Matrix V V K} {P : Finset V} {i j : V} (h : ∀ p ∈ P, M p j = 0) :
    elim M P i j = M i j := by
  simp [elim, mul_apply, h]

theorem elim_eq_of_row {M : Matrix V V K} {P : Finset V} {i j : V} (h : ∀ p ∈ P, M i p = 0) :
    elim M P i j = M i j := by
  simp [elim, Matrix.mul_assoc, mul_apply, h]

/-- Inside `S ⊇ P`, the elimination on `M` is the elimination on its block on `S`. -/
theorem elim_restrict {M : Matrix V V K} {P S : Finset V} (hPS : P ⊆ S) {i j : V} (hi : i ∈ S) (hj : j ∈ S) :
    elim (restrict M S) P i j = elim M P i j := by
  have hpr : principal (restrict M S) P = principal M P := by
    ext a b; exact restrict_apply_of_mem (hPS a.2) (hPS b.2)
  simp only [elim, Matrix.sub_apply, hpr, mul_apply, submatrix_apply, id, restrict_apply_of_mem hi hj]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [restrict_apply_of_mem (hPS b.2) hj]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [restrict_apply_of_mem hi (hPS a.2)]

theorem principal_restrict {M : Matrix V V K} {P S : Finset V} (hPS : P ⊆ S) :
    principal (restrict M S) P = principal M P := by
  ext a b; exact restrict_apply_of_mem (hPS a.2) (hPS b.2)

/-- The rank adds over the elimination of `P`. -/
theorem rank_elim {M : Matrix V V K} {P : Finset V} (hP : IsUnit (principal M P).det) :
    M.rank = P.card + (elim M P).rank := by
  have h₁ := rank_schurOn M (splitEquiv P) hP
  have h₂ : schurOn M (splitEquiv P ∘ Sum.inl) (splitEquiv P ∘ Sum.inr) = principal (elim M P) Pᶜ := by
    ext a b
    simp [schurOn, elim, splitEquiv, mul_apply]
    rfl
  rw [h₂, Fintype.card_coe] at h₁
  rw [h₁, rank_eq_principal (S := Pᶜ) (M := elim M P) fun i j h => ?_]
  rcases h with h | h
  · exact elim_row hP (by simpa using h) j
  · exact elim_col hP (by simpa using h) i

/-- One local step: on `I ⊆ J`, with the rows of `I` zero outside `J`, the pivots `P` and the retained rows `Q`
are chosen as in Lemma 1 from the block on `J`. The dropped indices are `I ∖ (P ∪ Q)`. -/
structure LocalStep (M : Matrix V V K) (I J P Q : Finset V) : Prop where
  sub : I ⊆ J
  supp : ∀ i ∈ I, ∀ j ∉ J, M i j = 0
  piv : P ⊆ I
  unit : IsUnit (principal M P).det
  rank : P.card = (principal M I).rank
  ret : Q ⊆ I \ P
  /-- The rows of `I ∖ P` of the Schur complement, on `J ∖ I`, are combinations of the rows of `Q`. -/
  span : ∀ d ∈ I \ P, ∃ c : Q → K, ∀ j ∈ J \ I, elim M P d j = ∑ q, c q * elim M P q j

namespace LocalStep

variable {M : Matrix V V K} {I J P Q : Finset V}

/-- After the pivots, the block on `I ∖ P` is zero. -/
theorem elim_zero (h : LocalStep M I J P Q) {i j : V} (hi : i ∈ I) (hj : j ∈ I) : elim M P i j = 0 := by
  have hu : IsUnit (principal (restrict M I) P).det := by rw [principal_restrict h.piv]; exact h.unit
  have hr := rank_elim hu
  rw [rank_restrict, ← h.rank] at hr
  have h0 : elim (restrict M I) P = 0 := eq_zero_of_rank_eq_zero (by omega)
  rw [← elim_restrict h.piv hi hj, h0, Matrix.zero_apply]

/-- Outside `J`, the rows of `I` stay zero. -/
theorem elim_out (h : LocalStep M I J P Q) {i j : V} (hi : i ∈ I) (hj : j ∉ J) : elim M P i j = 0 := by
  rw [elim_eq_of_col fun p hp => h.supp p (h.piv hp) j hj]
  exact h.supp i hi j hj

/-- Every row after the elimination is a combination of the rows that the step keeps. -/
theorem mem_span (h : LocalStep M I J P Q) (i : V) :
    (elim M P).row i ∈ Submodule.span K
      (Set.range fun k : ↥(P ∪ (I \ (P ∪ Q)))ᶜ => (elim M P).row k) := by
  by_cases hk : i ∈ (P ∪ (I \ (P ∪ Q)))ᶜ
  · exact Submodule.subset_span ⟨⟨i, hk⟩, rfl⟩
  by_cases hp : i ∈ P
  · have : (elim M P).row i = 0 := by ext j; exact elim_row h.unit hp j
    rw [this]; exact Submodule.zero_mem _
  have hi : i ∈ I := by
    rw [Finset.mem_compl, not_not] at hk
    rcases Finset.mem_union.1 hk with h' | h'
    · exact absurd h' hp
    · exact (Finset.mem_sdiff.1 h').1
  obtain ⟨c, hc⟩ := h.span i (Finset.mem_sdiff.2 ⟨hi, hp⟩)
  have hQ : ∀ q : Q, (q : V) ∈ (P ∪ (I \ (P ∪ Q)))ᶜ := fun q => by
    have := h.ret q.2
    simp only [Finset.mem_sdiff] at this
    simp [this.2, q.2]
  have hrow : (elim M P).row i = ∑ q : Q, c q • (elim M P).row (q : V) := by
    ext j
    simp only [row, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hj : j ∈ J
    · by_cases hjI : j ∈ I
      · rw [h.elim_zero hi hjI]
        exact (Finset.sum_eq_zero fun q _ => by
          rw [h.elim_zero (Finset.mem_sdiff.1 (h.ret q.2)).1 hjI, mul_zero]).symm
      · exact hc j (Finset.mem_sdiff.2 ⟨hj, hjI⟩)
    · rw [h.elim_out hi hj]
      exact (Finset.sum_eq_zero fun q _ => by
        rw [h.elim_out (Finset.mem_sdiff.1 (h.ret q.2)).1 hj, mul_zero]).symm
  rw [hrow]
  exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨q, hQ q⟩, rfl⟩)

/-- One local step: the rank of the matrix is `|P|` plus the rank of the next matrix. -/
theorem rank_step (h : LocalStep M I J P Q) (hM : IsAlternating M) :
    M.rank = P.card + (step M P (I \ (P ∪ Q))).rank := by
  rw [rank_elim h.unit, step, rank_restrict, rank_drop (Or.inl (hM.elim h.unit).skew) _ fun d _ => h.mem_span d]

end LocalStep

/-- A run of local steps. `R t` is the set of live indices before step `t`. -/
structure Run (N : ℕ → Matrix V V K) (R I J P Q : ℕ → Finset V) (T : ℕ) : Prop where
  alt : IsAlternating (N 0)
  supp : ∀ i j, i ∉ R 0 ∨ j ∉ R 0 → N 0 i j = 0
  next : ∀ t < T, N (t + 1) = step (N t) (P t) (I t \ (P t ∪ Q t))
  live : ∀ t < T, R (t + 1) = R t \ (P t ∪ (I t \ (P t ∪ Q t)))
  sub : ∀ t < T, J t ⊆ R t
  loc : ∀ t < T, LocalStep (N t) (I t) (J t) (P t) (Q t)
  done : R T = ∅

namespace Run

variable {N : ℕ → Matrix V V K} {R I J P Q : ℕ → Finset V} {T : ℕ}

theorem alt_t (h : Run N R I J P Q T) : ∀ t ≤ T, IsAlternating (N t)
  | 0, _ => h.alt
  | t + 1, ht => by
    rw [h.next t ht]
    exact (h.alt_t t (by omega)).step (h.loc t ht).unit _

theorem live_mono (h : Run N R I J P Q T) {s t : ℕ} (hst : s ≤ t) (ht : t ≤ T) : R t ⊆ R s := by
  induction t, hst using Nat.le_induction with
  | base => exact le_rfl
  | succ t hst ih =>
    rw [h.live t (by omega)]
    exact Finset.sdiff_subset.trans (ih (by omega))

theorem supp_t (h : Run N R I J P Q T) : ∀ t ≤ T, ∀ i j, i ∉ R t ∨ j ∉ R t → N t i j = 0
  | 0, _ => h.supp
  | t + 1, ht => fun i j hij => by
    rw [h.next t ht, step]
    by_cases hc : i ∈ (P t ∪ (I t \ (P t ∪ Q t)))ᶜ ∧ j ∈ (P t ∪ (I t \ (P t ∪ Q t)))ᶜ
    · rw [restrict_apply_of_mem hc.1 hc.2]
      have hij' : i ∉ R t ∨ j ∉ R t := by
        rw [h.live t ht] at hij
        rcases hij with hi | hj
        · left; intro hi'; exact hi (Finset.mem_sdiff.2 ⟨hi', by simpa using hc.1⟩)
        · right; intro hj'; exact hj (Finset.mem_sdiff.2 ⟨hj', by simpa using hc.2⟩)
      have h0 := h.supp_t t (by omega)
      rcases hij' with hi | hj
      · rw [elim_eq_of_row fun p _ => h0 i p (Or.inl hi)]; exact h0 i j (Or.inl hi)
      · rw [elim_eq_of_col fun p _ => h0 p j (Or.inr hj)]; exact h0 i j (Or.inr hj)
    · exact restrict_apply_of_not_mem (by tauto)

/-- The rank is the number of pivots. -/
theorem rank (h : Run N R I J P Q T) : (N 0).rank = ∑ t ∈ Finset.range T, (P t).card := by
  have key : ∀ t ≤ T, (N 0).rank = ∑ s ∈ Finset.range t, (P s).card + (N t).rank := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      intro ht
      rw [ih (by omega), (h.loc t ht).rank_step (h.alt_t t (by omega)), ← h.next t ht,
        Finset.sum_range_succ]
      ring
  have h0 : N T = 0 := by
    ext i j; exact h.supp_t T le_rfl i j (Or.inl (by simp [h.done]))
  rw [key T le_rfl, h0, rank_zero, add_zero]

theorem piv_live (h : Run N R I J P Q T) {t : ℕ} (ht : t < T) : P t ⊆ R t :=
  (h.loc t ht).piv.trans ((h.loc t ht).sub.trans (h.sub t ht))

theorem drop_live (h : Run N R I J P Q T) {t : ℕ} (ht : t < T) : I t \ (P t ∪ Q t) ⊆ R t :=
  Finset.sdiff_subset.trans ((h.loc t ht).sub.trans (h.sub t ht))

theorem not_live_of_lt (h : Run N R I J P Q T) {s t : ℕ} (hst : s < t) (ht : t ≤ T) {x : V}
    (hx : x ∈ P s ∪ (I s \ (P s ∪ Q s))) : x ∉ R t := by
  intro hxt
  have := h.live_mono (Nat.succ_le_of_lt hst) ht hxt
  rw [h.live s (by omega)] at this
  exact (Finset.mem_sdiff.1 this).2 hx

/-- Every live index of the start is pivoted or dropped in exactly one step. -/
theorem partition (h : Run N R I J P Q T) {x : V} (hx : x ∈ R 0) :
    ∃! t, t < T ∧ x ∈ P t ∪ (I t \ (P t ∪ Q t)) := by
  have hex : ∃ t, t < T ∧ x ∈ R t ∧ x ∉ R (t + 1) := by
    by_contra hne
    push_neg at hne
    have : ∀ t ≤ T, x ∈ R t := by
      intro t
      induction t with
      | zero => exact fun _ => hx
      | succ t ih => exact fun ht => hne t (by omega) (ih (by omega))
    simpa [h.done] using this T le_rfl
  obtain ⟨t, ht, hxt, hxt'⟩ := hex
  refine ⟨t, ⟨ht, ?_⟩, fun s ⟨hs, hxs⟩ => ?_⟩
  · rw [h.live t ht] at hxt'
    by_contra hn
    exact hxt' (Finset.mem_sdiff.2 ⟨hxt, hn⟩)
  · rcases lt_trichotomy s t with hlt | heq | hgt
    · exact absurd hxt (h.not_live_of_lt hlt (by omega) hxs)
    · exact heq
    · have hs' : x ∈ R s := by
        rcases Finset.mem_union.1 hxs with hp | hd
        · exact h.piv_live hs hp
        · exact h.drop_live hs hd
      exact absurd (h.live_mono (Nat.succ_le_of_lt hgt) (by omega) hs') hxt'

/-- The pivots of different steps are disjoint. -/
theorem piv_disjoint (h : Run N R I J P Q T) {s t : ℕ} (hs : s < T) (ht : t < T) (hst : s ≠ t) :
    Disjoint (P s) (P t) := by
  rw [Finset.disjoint_left]
  intro x hxs hxt
  rcases Nat.lt_or_gt_of_ne hst with hlt | hgt
  · exact h.not_live_of_lt hlt (by omega) (Finset.mem_union_left _ hxs) (h.piv_live ht hxt)
  · exact h.not_live_of_lt hgt (by omega) (Finset.mem_union_left _ hxt) (h.piv_live hs hxs)

/-- The set of all pivots. -/
def pivots (P : ℕ → Finset V) (T : ℕ) : Finset V := (Finset.range T).biUnion P

theorem card_pivots (h : Run N R I J P Q T) : (pivots P T).card = ∑ t ∈ Finset.range T, (P t).card :=
  Finset.card_biUnion fun _s hs _t ht hst =>
    h.piv_disjoint (Finset.mem_range.1 hs) (Finset.mem_range.1 ht) hst

/-- No pivot is dropped. -/
theorem not_mem_drop (h : Run N R I J P Q T) {s t : ℕ} (hs : s < T) (ht : t < T) {x : V} (hx : x ∈ P s) :
    x ∉ I t \ (P t ∪ Q t) := by
  intro hd
  have hu := (h.partition (h.live_mono (Nat.zero_le s) hs.le (h.piv_live hs hx))).unique
    ⟨hs, Finset.mem_union_left _ hx⟩ ⟨ht, Finset.mem_union_right _ hd⟩
  subst hu
  exact (Finset.mem_sdiff.1 hd).2 (Finset.mem_union_left _ hx)

/-- On the pivots, the run on the block on `B` follows the run on the whole matrix. -/
theorem restrict_next (h : Run N R I J P Q T) {t : ℕ} (ht : t < T) :
    restrict (N (t + 1)) (pivots P T) = elim (restrict (N t) (pivots P T)) (P t) := by
  have hPB : P t ⊆ pivots P T := Finset.subset_biUnion_of_mem P (Finset.mem_range.2 ht)
  ext i j
  by_cases hij : i ∈ pivots P T ∧ j ∈ pivots P T
  · rw [restrict_apply_of_mem hij.1 hij.2, elim_restrict hPB hij.1 hij.2, h.next t ht, step]
    have hk : ∀ x ∈ pivots P T, x ∉ P t → x ∈ (P t ∪ (I t \ (P t ∪ Q t)))ᶜ := fun x hx hxp => by
      obtain ⟨s, hs, hxs⟩ := Finset.mem_biUnion.1 hx
      have := h.not_mem_drop (Finset.mem_range.1 hs) ht hxs
      simp only [Finset.mem_compl, Finset.mem_union, not_or]
      exact ⟨hxp, this⟩
    by_cases hi : i ∈ P t
    · rw [elim_row (h.loc t ht).unit hi, restrict_apply_of_not_mem (Or.inl (by simp [hi]))]
    by_cases hj : j ∈ P t
    · rw [elim_col (h.loc t ht).unit hj, restrict_apply_of_not_mem (Or.inr (by simp [hj]))]
    exact restrict_apply_of_mem (hk i hij.1 hi) (hk j hij.2 hj)
  · rw [restrict_apply_of_not_mem (by tauto)]
    have h0 : ∀ x y, x ∉ pivots P T ∨ y ∉ pivots P T → restrict (N t) (pivots P T) x y = 0 :=
      fun x y hxy => restrict_apply_of_not_mem hxy
    rcases not_and_or.1 hij with hi | hj
    · rw [elim_eq_of_row fun p _ => h0 i p (Or.inl hi), h0 i j (Or.inl hi)]
    · rw [elim_eq_of_col fun p _ => h0 p j (Or.inr hj), h0 i j (Or.inr hj)]

/-- The block on the pivots is nonsingular. -/
theorem det (h : Run N R I J P Q T) : (principal (N 0) (pivots P T)).det ≠ 0 := by
  have key : ∀ t ≤ T, (restrict (N 0) (pivots P T)).rank =
      ∑ s ∈ Finset.range t, (P s).card + (restrict (N t) (pivots P T)).rank := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      intro ht
      have hPB : P t ⊆ pivots P T := Finset.subset_biUnion_of_mem P (Finset.mem_range.2 ht)
      have hu : IsUnit (principal (restrict (N t) (pivots P T)) (P t)).det := by
        rw [principal_restrict hPB]; exact (h.loc t ht).unit
      rw [ih (by omega), rank_elim hu, ← h.restrict_next ht, Finset.sum_range_succ]
      ring
  have h0 : restrict (N T) (pivots P T) = 0 := by
    ext i j
    by_cases hij : i ∈ pivots P T ∧ j ∈ pivots P T
    · rw [restrict_apply_of_mem hij.1 hij.2]
      exact h.supp_t T le_rfl i j (Or.inl (by simp [h.done]))
    · exact restrict_apply_of_not_mem (by tauto)
  have hr := key T le_rfl
  rw [h0, rank_zero, add_zero, rank_restrict, ← h.card_pivots] at hr
  have hfull : (principal (N 0) (pivots P T)).rank = Fintype.card (pivots P T) := by
    rw [hr, Fintype.card_coe]
  exact (isUnit_iff_isUnit_det _ |>.mp
    (mulVec_surjective_iff_isUnit.mp (mulVec_surjective_iff_rank_eq_card.mpr hfull))).ne_zero

end Run

end PlanarMatching
