import CutQuery.Sparsity

/-!
# The classical lower bound for minimum degree with cut queries

* `exists_small_gamma`: Lemma 5, small integer solutions for vertices outside the lattice;
* `boundary_count`: the labels near the boundary of the box are few;
* `det_core`: the counting for one deterministic algorithm;
* `classical_bound`: the theorem, by averaging the counting over a randomized algorithm.
-/

open Finset

namespace CutQuery

section Answers

variable {n : ℕ}

/-- If two weights agree on the queries asked on the first, the second produces the same answers. -/
theorem answers_congr (alg : DetAlg n) (A A' : Weights n) (T : ℕ)
    (h : ∀ t, t < T → cut A' (alg.query (alg.answers A t)) = cut A (alg.query (alg.answers A t))) :
    ∀ t, t ≤ T → alg.answers A' t = alg.answers A t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    have h1 := ih (by omega)
    simp only [DetAlg.answers]
    rw [h1, h t (by omega)]

/-- The average of the error over a finite set of weights, as a sum over the outcomes of the coins. -/
theorem sum_err_eq [NeZero n] {Ω : Type*} [Fintype Ω] (r : RandAlg n Ω) (T : ℕ) {I : Type*} (X : Finset I)
    (Af : I → Weights n) :
    ∑ a ∈ X, r.err T (Af a)
      = ∑ ω, r.p ω * ((X.filter fun a => (r.alg ω).run T (Af a) ≠ minDegree (Af a)).card : ℝ) := by
  unfold RandAlg.err
  rw [sum_comm]
  refine sum_congr rfl fun ω _ => ?_
  rw [card_filter]
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  by_cases h : (r.alg ω).run T (Af a) = minDegree (Af a) <;> simp [h]

end Answers

section SmallGamma

variable {k T : ℕ}

/-- Lemma 5: if `G w^v` lies in the lattice of the label vectors, it is a combination of them with small
integer coefficients. -/
theorem exists_small_gamma (Q : Fin T → Fin (k + 3) → Bool) (v : Fin (k + 3)) (G : ℕ)
    (hmem : (G : ℤ) • (fun s => cut (shiftVec v) (Q s)) ∈
      AddSubgroup.closure (Set.range fun (j : LabelIdx k) (s : Fin T) => cut (b j) (Q s))) :
    ∃ γ : LabelIdx k → ℤ, (∀ s, ∑ j, γ j * cut (b j) (Q s) = G * cut (shiftVec v) (Q s)) ∧
      ∀ j, |γ j| ≤ ((G : ℤ) + Fintype.card (LabelIdx k)) * ((T.factorial : ℤ) * 6 ^ T) := by
  rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
    Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨γ₀, h₀⟩ := hmem
  have hx₀ : ∀ s, ∑ j, γ₀ j * cut (b j) (Q s) = (G : ℤ) * cut (shiftVec v) (Q s) := by
    intro s
    have := congrFun h₀ s
    simpa [Finset.sum_apply] using this
  obtain ⟨k', row, P, hP, -, hM, hk', hrows⟩ :=
    exists_block (fun (j : LabelIdx k) (s : Fin T) => cut (b j) (Q s)) ∅ (by simp)
  obtain ⟨x, hx, -, hxb⟩ := exists_small_solution (fun (j : LabelIdx k) (s : Fin T) => cut (b j) (Q s)) 6
    (fun j s => by simpa using abs_cut_b_le j (Q s)) row P hP hrows hM ∅ (empty_subset _) γ₀ (by simp)
    (fun s => cut (shiftVec v) (Q s))
    (fun s => by
      have := abs_cut_shiftVec_le v (Q s)
      push_cast
      omega)
    (G : ℤ) hx₀
  refine ⟨x, hx, fun j => (hxb j).trans ?_⟩
  rw [Fintype.card_fin] at hk'
  rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ (G : ℤ))]
  have h1 : (k'.factorial : ℤ) ≤ T.factorial := by exact_mod_cast Nat.factorial_le hk'
  have h2 : ((6 : ℕ) : ℤ) ^ k' ≤ 6 ^ T := by
    push_cast
    exact pow_le_pow_right₀ (by norm_num) hk'
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

end SmallGamma

section Box

variable (J : Type*) [Fintype J] [DecidableEq J]

/-- The labels with all coordinates in `[-L, L]`. -/
def box (L : ℕ) : Finset (J → ℤ) := Fintype.piFinset fun _ => Icc (-(L : ℤ)) L

/-- The labels of the box with a coordinate within `E` of the boundary. -/
def boundary (L E : ℕ) : Finset (J → ℤ) := (box J L).filter fun a => ∃ j, (L : ℤ) - E < |a j|

variable {J}

theorem mem_box {L : ℕ} {a : J → ℤ} : a ∈ box J L ↔ ∀ j, |a j| ≤ L := by
  simp only [box, Fintype.mem_piFinset, mem_Icc, abs_le]

theorem card_box_pos (L : ℕ) : 0 < (box J L).card :=
  card_pos.mpr ⟨0, mem_box.mpr fun j => by simp⟩

/-- The count of labels near the boundary: `|boundary| (2 L + 1) ≤ 2 E |J| |box|`. -/
theorem boundary_count (L E : ℕ) :
    (boundary J L E).card * (2 * L + 1) ≤ Fintype.card J * (2 * E) * (box J L).card := by
  let D : Finset ℤ := Icc (-(L : ℤ)) L
  let C : Finset ℤ := D.filter fun z => (L : ℤ) - E < |z|
  have hDcard : D.card = 2 * L + 1 := by
    simp only [D, Int.card_Icc]
    omega
  have hCcard : C.card ≤ 2 * E := by
    have hsub : C ⊆ Icc (-(L : ℤ)) ((E : ℤ) - L - 1) ∪ Icc ((L : ℤ) - E + 1) L := by
      intro z hz
      obtain ⟨hz1, hz2⟩ := mem_filter.mp hz
      obtain ⟨h1, h2⟩ := mem_Icc.mp hz1
      rw [mem_union, mem_Icc, mem_Icc]
      rcases le_total 0 z with h | h
      · rw [abs_of_nonneg h] at hz2
        right
        omega
      · rw [abs_of_nonpos h] at hz2
        left
        omega
    refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
    simp only [Int.card_Icc]
    omega
  let Bj : J → Finset (J → ℤ) := fun j => Fintype.piFinset fun j' => if j' = j then C else D
  have hsub : boundary J L E ⊆ univ.biUnion Bj := by
    intro a ha
    obtain ⟨ha1, j, hj⟩ := mem_filter.mp ha
    have hbox := mem_box.mp ha1
    refine mem_biUnion.mpr ⟨j, mem_univ _, Fintype.mem_piFinset.mpr fun j' => ?_⟩
    have hmemD : ∀ i, a i ∈ D := fun i => mem_Icc.mpr (abs_le.mp (hbox i))
    by_cases h : j' = j
    · subst h
      simp only [↓reduceIte]
      exact mem_filter.mpr ⟨hmemD j', hj⟩
    · simp only [h, ↓reduceIte]
      exact hmemD j'
  have hBj : ∀ j, (Bj j).card * (2 * L + 1) ≤ 2 * E * (box J L).card := by
    intro j
    let Z := ∏ i ∈ univ.erase j, D.card
    have h1 : (Bj j).card = C.card * Z := by
      simp only [Bj, Fintype.card_piFinset]
      rw [← mul_prod_erase univ _ (mem_univ j)]
      simp only [↓reduceIte, Z]
      congr 1
      exact prod_congr rfl fun i hi => by simp only [ne_of_mem_erase hi, ↓reduceIte]
    have h2 : (box J L).card = D.card * Z := by
      simp only [box, Fintype.card_piFinset]
      rw [← mul_prod_erase univ _ (mem_univ j)]
    rw [h1, h2, hDcard]
    calc C.card * Z * (2 * L + 1) ≤ 2 * E * Z * (2 * L + 1) := by gcongr
      _ = 2 * E * ((2 * L + 1) * Z) := by ring
  calc (boundary J L E).card * (2 * L + 1)
      ≤ (∑ j, (Bj j).card) * (2 * L + 1) :=
        Nat.mul_le_mul_right _ ((card_le_card hsub).trans card_biUnion_le)
    _ = ∑ j, (Bj j).card * (2 * L + 1) := sum_mul _ _ _
    _ ≤ ∑ _j : J, 2 * E * (box J L).card := sum_le_sum fun j _ => hBj j
    _ = Fintype.card J * (2 * E) * (box J L).card := by
        rw [sum_const, card_univ, smul_eq_mul]
        ring

end Box

section Counting

/-- The counting of errors. `S ⊆ Bx` are the points of `Bx` where the first input is answered as if some vertex
were unset; points outside `S` are errors `e1`. For a point of `S` that does not see `v`, the map `Φ v` lands
in the errors `ev v` unless the point lies in `Bd`, and it is injective. Each point sees at most `y` vertices. -/
theorem abstract_count {X V : Type*} [DecidableEq X] [Fintype V] [DecidableEq V]
    (Bx Bd e1 S : Finset X) (ev : V → Finset X) (hS : S ⊆ Bx) (hA : ∀ a ∈ Bx, a ∉ S → a ∈ e1)
    (Y : X → Finset V) (y : ℕ) (hY : ∀ a, (Y a).card ≤ y) (Φ : V → X → X)
    (hmap : ∀ v a, a ∈ S → v ∉ Y a → a ∉ Bd → Φ v a ∈ ev v)
    (hinj : ∀ v a a', a ∈ S → v ∉ Y a → a' ∈ S → v ∉ Y a' → Φ v a = Φ v a' → a = a') :
    Fintype.card V * Bx.card
      ≤ Fintype.card V * e1.card + ∑ v, (ev v).card + Fintype.card V * Bd.card + y * Bx.card := by
  set N := Fintype.card V with hN
  let Sv : V → Finset X := fun v => S.filter fun a => v ∉ Y a
  have h1 : Bx.card ≤ S.card + e1.card := by
    refine (card_le_card ?_).trans (card_union_le S e1)
    intro a ha
    by_cases h : a ∈ S
    · exact mem_union_left _ h
    · exact mem_union_right _ (hA a ha h)
  have h2 : S.card ≤ Bx.card := card_le_card hS
  have h3 : ∀ v, (Sv v).card ≤ (ev v).card + Bd.card := by
    intro v
    have h4 : (Sv v \ Bd).card ≤ (ev v).card := by
      refine card_le_card_of_injOn (Φ v) ?_ ?_
      · intro a ha
        obtain ⟨ha1, ha2⟩ := mem_sdiff.mp (mem_coe.mp ha)
        obtain ⟨ha3, ha4⟩ := mem_filter.mp ha1
        exact hmap v a ha3 ha4 ha2
      · intro a ha a' ha' heq
        obtain ⟨ha3, ha4⟩ := mem_filter.mp (mem_sdiff.mp (mem_coe.mp ha)).1
        obtain ⟨ha3', ha4'⟩ := mem_filter.mp (mem_sdiff.mp (mem_coe.mp ha')).1
        exact hinj v a a' ha3 ha4 ha3' ha4' heq
    have h5 : (Sv v).card ≤ (Sv v \ Bd).card + Bd.card := card_le_card_sdiff_add_card
    omega
  have h6 : N * S.card ≤ ∑ v, (Sv v).card + y * S.card := by
    have h7 : ∑ v, (Sv v).card = ∑ a ∈ S, (univ.filter fun v => v ∉ Y a).card := by
      simp only [Sv, card_filter]
      rw [sum_comm]
    have h8 : ∀ a ∈ S, N ≤ (univ.filter fun v => v ∉ Y a).card + y := by
      intro a _
      have h9 : (univ.filter fun v => v ∈ Y a).card + (univ.filter fun v => v ∉ Y a).card
          = (univ : Finset V).card := card_filter_add_card_filter_not _
      have h10 : (univ.filter fun v => v ∈ Y a) = Y a := by
        ext v
        simp
      rw [h10, card_univ] at h9
      have := hY a
      omega
    have h11 := sum_le_sum h8
    rw [sum_const, smul_eq_mul, sum_add_distrib, sum_const, smul_eq_mul] at h11
    rw [h7]
    calc N * S.card = S.card * N := mul_comm _ _
      _ ≤ _ := h11
      _ = _ := by rw [mul_comm y]
  have h12 : ∑ v, (Sv v).card ≤ ∑ v, (ev v).card + N * Bd.card := by
    calc ∑ v, (Sv v).card ≤ ∑ v, ((ev v).card + Bd.card) := sum_le_sum fun v _ => h3 v
      _ = ∑ v, (ev v).card + N * Bd.card := by
          rw [sum_add_distrib, sum_const, card_univ, smul_eq_mul]
  have h13 : N * Bx.card ≤ N * S.card + N * e1.card := by
    rw [← mul_add]
    exact Nat.mul_le_mul_left _ h1
  have h14 : y * S.card ≤ y * Bx.card := Nat.mul_le_mul_left _ h2
  clear_value N
  omega

end Counting

section Core

variable {k T : ℕ}

/-- The query sets asked on the weights `A` during the first `T` steps. -/
def queriesOn {n : ℕ} (alg : DetAlg n) (A : Weights n) (T : ℕ) : Fin T → Fin n → Bool :=
  fun s => alg.query (alg.answers A s)

/-- The lattice of label vectors of the query sets `Q`. -/
def labelLattice (Q : Fin T → Fin (k + 3) → Bool) : AddSubgroup (Fin T → ℤ) :=
  AddSubgroup.closure (Set.range fun (j : LabelIdx k) (s : Fin T) => cut (b j) (Q s))

open scoped Classical in
/-- The vertices visible to the query sets `Q`. -/
noncomputable def visibleSet (G : ℕ) (Q : Fin T → Fin (k + 3) → Bool) : Finset (Fin (k + 3)) :=
  univ.filter fun v => (G : ℤ) • (fun s => cut (shiftVec v) (Q s)) ∉ labelLattice Q

theorem card_visibleSet_le (G : ℕ) (hG : ∀ d : ℕ, 1 ≤ d → d ≤ k + 3 → d ∣ G)
    (Q : Fin T → Fin (k + 3) → Bool) : (visibleSet G Q).card ≤ 2 * T + 3 :=
  visible_card Q (labelLattice Q) G hG (fun j => AddSubgroup.subset_closure ⟨j, rfl⟩)

theorem mem_lattice_of_not_visible {G : ℕ} {Q : Fin T → Fin (k + 3) → Bool} {v : Fin (k + 3)}
    (hv : v ∉ visibleSet G Q) : (G : ℤ) • (fun s => cut (shiftVec v) (Q s)) ∈ labelLattice Q := by
  by_contra h
  apply hv
  classical
  unfold visibleSet
  exact mem_filter.mpr ⟨mem_univ _, h⟩

/-- Moving the labels along a solution of Lemma 5 and clearing the bit of `v` does not change the answers. -/
theorem answers_family_update (alg : DetAlg (k + 3)) (W₀ G : ℤ) (h : Fin (k + 3) → Bool)
    (v : Fin (k + 3)) (hv : h v = true) (a γ : LabelIdx k → ℤ)
    (hγ : ∀ s : Fin T, ∑ j, γ j * cut (b j) (queriesOn alg (family W₀ G h a) T s)
      = G * cut (shiftVec v) (queriesOn alg (family W₀ G h a) T s)) :
    ∀ t, t ≤ T → alg.answers (family W₀ G (Function.update h v false) (a + γ)) t
      = alg.answers (family W₀ G h a) t :=
  answers_congr alg _ _ T fun t ht => cut_family_update W₀ G h v hv a γ _ (hγ ⟨t, ht⟩)

/-- The counting for one deterministic algorithm. Writing `e₁` for the labels of the box on which the algorithm
errs at `h = 1ⁿ` and `e_v` for those on which it errs at `h = 1ⁿ - e_v`, we get
`n |box| ≤ n e₁ + ∑ e_v + n |boundary| + (2 T + 3) |box|`. -/
theorem det_core [NeZero (k + 3)] (alg : DetAlg (k + 3)) (W₀ : ℤ) (G L E : ℕ) (hG0 : 0 < G)
    (hG : ∀ d : ℕ, 1 ≤ d → d ≤ k + 3 → d ∣ G)
    (hγ : ∀ (Q : Fin T → Fin (k + 3) → Bool) (v : Fin (k + 3)),
      (G : ℤ) • (fun s => cut (shiftVec v) (Q s)) ∈ labelLattice Q →
      ∃ γ : LabelIdx k → ℤ, (∀ s, ∑ j, γ j * cut (b j) (Q s) = G * cut (shiftVec v) (Q s)) ∧
        ∀ j, |γ j| ≤ E) :
    (k + 3) * (box (LabelIdx k) L).card
      ≤ (k + 3) * ((box (LabelIdx k) L).filter fun a =>
            alg.run T (family W₀ G (fun _ => true) a) ≠ minDegree (family W₀ G (fun _ => true) a)).card
        + ∑ v, ((box (LabelIdx k) L).filter fun a =>
            alg.run T (family W₀ G (Function.update (fun _ => true) v false) a)
              ≠ minDegree (family W₀ G (Function.update (fun _ => true) v false) a)).card
        + (k + 3) * (boundary (LabelIdx k) L E).card + (2 * T + 3) * (box (LabelIdx k) L).card := by
  classical
  have hγ' : ∀ (Q : Fin T → Fin (k + 3) → Bool) (v : Fin (k + 3)), ∃ γ : LabelIdx k → ℤ,
      (G : ℤ) • (fun s => cut (shiftVec v) (Q s)) ∈ labelLattice Q →
      (∀ s, ∑ j, γ j * cut (b j) (Q s) = G * cut (shiftVec v) (Q s)) ∧ ∀ j, |γ j| ≤ E := by
    intro Q v
    by_cases hm : (G : ℤ) • (fun s => cut (shiftVec v) (Q s)) ∈ labelLattice Q
    · obtain ⟨γ, h⟩ := hγ Q v hm
      exact ⟨γ, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hm⟩
  choose gam hgam using hγ'
  let Qa : (LabelIdx k → ℤ) → Fin T → Fin (k + 3) → Bool :=
    fun a => queriesOn alg (family W₀ G (fun _ => true) a) T
  have hc2 : ∀ c : ℤ, c = ((k : ℤ) + 2) * W₀ → c ≠ ((k : ℤ) + 2) * W₀ + 2 * G := by
    intro c hc
    have : (0 : ℤ) < G := by exact_mod_cast hG0
    omega
  have hcount := abstract_count (V := Fin (k + 3)) (box (LabelIdx k) L) (boundary (LabelIdx k) L E)
    ((box (LabelIdx k) L).filter fun a =>
      alg.run T (family W₀ G (fun _ => true) a) ≠ minDegree (family W₀ G (fun _ => true) a))
    ((box (LabelIdx k) L).filter fun a =>
      alg.run T (family W₀ G (fun _ => true) a) ≠ ((k : ℤ) + 2) * W₀)
    (fun v => (box (LabelIdx k) L).filter fun a =>
      alg.run T (family W₀ G (Function.update (fun _ => true) v false) a)
        ≠ minDegree (family W₀ G (Function.update (fun _ => true) v false) a))
    (filter_subset _ _)
    (fun a ha hn => by
      refine mem_filter.mpr ⟨ha, ?_⟩
      rw [minDegree_family_all_true]
      have h1 : alg.run T (family W₀ G (fun _ => true) a) = ((k : ℤ) + 2) * W₀ := by
        by_contra h2
        exact hn (mem_filter.mpr ⟨ha, h2⟩)
      rw [h1]
      exact hc2 _ rfl)
    (fun a => visibleSet G (Qa a)) (2 * T + 3) (fun a => card_visibleSet_le G hG _)
    (fun v a => a + gam (Qa a) v)
    (fun v a haS hv hbd => by
      obtain ⟨ha1, ha2⟩ := mem_filter.mp haS
      obtain ⟨hsol, hsmall⟩ := hgam (Qa a) v (mem_lattice_of_not_visible hv)
      have hbd' : ∀ j, |a j| ≤ (L : ℤ) - E := by
        intro j
        by_contra hj
        push Not at hj
        exact hbd (mem_filter.mpr ⟨ha1, j, hj⟩)
      have hmem : a + gam (Qa a) v ∈ box (LabelIdx k) L := by
        refine mem_box.mpr fun j => ?_
        have h3 := (abs_add_le (a j) (gam (Qa a) v j)).trans (add_le_add (hbd' j) (hsmall j))
        simpa using h3
      refine mem_filter.mpr ⟨hmem, ?_⟩
      rw [minDegree_family_of_false W₀ G (by positivity) _ _ v (Function.update_self _ _ _)]
      have hans := answers_family_update alg W₀ G (fun _ => true) v rfl a (gam (Qa a) v) hsol T le_rfl
      unfold DetAlg.run at ha2 ⊢
      rw [hans]
      exact ha2)
    (fun v a a' _ hv _ hv' heq => by
      obtain ⟨hsol, -⟩ := hgam (Qa a) v (mem_lattice_of_not_visible hv)
      obtain ⟨hsol', -⟩ := hgam (Qa a') v (mem_lattice_of_not_visible hv')
      have hans := answers_family_update alg W₀ G (fun _ => true) v rfl a (gam (Qa a) v) hsol
      have hans' := answers_family_update alg W₀ G (fun _ => true) v rfl a' (gam (Qa a') v) hsol'
      have hQ : Qa a = Qa a' := by
        funext s
        have e1 := hans s s.2.le
        have e2 := hans' s s.2.le
        rw [heq, e2] at e1
        change alg.query (alg.answers _ s) = alg.query (alg.answers _ s)
        rw [e1]
      rw [hQ] at heq
      exact add_right_cancel heq)
  rw [Fintype.card_fin] at hcount
  exact hcount

end Core

section Sizes

/-- The crude size bound for the weights of the hard family. -/
theorem size_bound (n m G J : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n < 2 ^ m) (hG : G = n.factorial)
    (hJ : J ≤ n ^ 2) :
    2 * (G * n + 1000 * J * ((G + J) * (n.factorial * 6 ^ n)) * J) ≤ 2 ^ (23 * n * m) := by
  set X := 2 ^ (n * m) with hX
  have hnm1 : 1 ≤ n * m := Nat.mul_pos hn hm
  have hX2 : 2 ≤ X := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ X := Nat.pow_le_pow_right (by norm_num) hnm1
  have hnX : n ≤ X := by
    have h1 : m ≤ n * m := Nat.le_mul_of_pos_left m hn
    exact hnm.le.trans (Nat.pow_le_pow_right (by norm_num) h1)
  have hfac : n.factorial ≤ X := by
    calc n.factorial ≤ n ^ n := Nat.factorial_le_pow n
      _ ≤ (2 ^ m) ^ n := Nat.pow_le_pow_left hnm.le n
      _ = X := by rw [hX, ← pow_mul, mul_comm]
  have h6 : 6 ^ n ≤ X ^ 3 := by
    calc 6 ^ n ≤ (2 ^ 3) ^ n := Nat.pow_le_pow_left (by norm_num) n
      _ = 2 ^ (3 * n) := by rw [← pow_mul]
      _ ≤ 2 ^ (n * m * 3) := by
          refine Nat.pow_le_pow_right (by norm_num) ?_
          nlinarith
      _ = X ^ 3 := by rw [hX, ← pow_mul]
  have hJX : J ≤ X ^ 2 := hJ.trans (Nat.pow_le_pow_left hnX 2)
  have hGX : G ≤ X := hG ▸ hfac
  have h1000 : 1000 ≤ X ^ 10 := by
    calc 1000 ≤ 2 ^ 10 := by norm_num
      _ ≤ X ^ 10 := Nat.pow_le_pow_left hX2 10
  have hsum : G + J ≤ X ^ 3 := by
    have : X + X ^ 2 ≤ X ^ 3 := by nlinarith [sq_nonneg X, pow_succ X 2]
    omega
  have hE : (G + J) * (n.factorial * 6 ^ n) ≤ X ^ 7 := by
    calc (G + J) * (n.factorial * 6 ^ n) ≤ X ^ 3 * (X * X ^ 3) := by gcongr
      _ = X ^ 7 := by ring
  have hL : 1000 * J * ((G + J) * (n.factorial * 6 ^ n)) * J ≤ X ^ 21 := by
    calc 1000 * J * ((G + J) * (n.factorial * 6 ^ n)) * J ≤ X ^ 10 * X ^ 2 * X ^ 7 * X ^ 2 := by gcongr
      _ = X ^ 21 := by ring
  have hGn : G * n ≤ X ^ 21 := by
    calc G * n ≤ X * X := Nat.mul_le_mul hGX hnX
      _ = X ^ 2 := by ring
      _ ≤ X ^ 21 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hfin : 2 ^ (23 * n * m) = X ^ 23 := by
    rw [hX, ← pow_mul]
    congr 1
    ring
  rw [hfin]
  calc 2 * (G * n + 1000 * J * ((G + J) * (n.factorial * 6 ^ n)) * J)
      ≤ 2 * (X ^ 21 + X ^ 21) := by gcongr
    _ = 4 * X ^ 21 := by ring
    _ ≤ X ^ 2 * X ^ 21 := by
        have : 4 ≤ X ^ 2 := by nlinarith
        gcongr
    _ = X ^ 23 := by ring

end Sizes

section Main

variable {k T : ℕ}

/-- The family stays in `[0, 2 W₀]` when `W₀` dominates the shifts and the labels. -/
theorem family_inClass (L : ℕ) (W₀ G : ℤ) (hG : 0 ≤ G)
    (hW₀ : W₀ = G * (k + 3) + L * Fintype.card (LabelIdx k)) (h : Fin (k + 3) → Bool)
    (a : LabelIdx k → ℤ) (ha : a ∈ box (LabelIdx k) L) (W : ℤ) (hW : 2 * W₀ ≤ W) :
    InClass W (family W₀ G h a) := by
  intro f
  have hbit : ∀ β : Bool, |bitZ β| ≤ 1 := fun β => by
    unfold bitZ
    split_ifs <;> simp
  have h1 : |∑ v, bitZ (h v) * shiftVec v f| ≤ (k : ℤ) + 3 := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ v, |bitZ (h v) * shiftVec v f| ≤ ∑ _v : Fin (k + 3), (1 : ℤ) := by
          refine sum_le_sum fun v _ => ?_
          rw [abs_mul]
          have := mul_le_mul (hbit (h v)) (abs_shiftVec_le_one v f) (abs_nonneg _) (by norm_num)
          simpa using this
      _ = (k : ℤ) + 3 := by simp
  have h2 : |∑ j, a j * b j f| ≤ (L : ℤ) * Fintype.card (LabelIdx k) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |a j * b j f| ≤ ∑ _j : LabelIdx k, (L : ℤ) := by
          refine sum_le_sum fun j _ => ?_
          rw [abs_mul]
          have := mul_le_mul (mem_box.mp ha j) (abs_b_le_one j f) (abs_nonneg _) (by positivity)
          simpa using this
      _ = (L : ℤ) * Fintype.card (LabelIdx k) := by
          rw [sum_const, card_univ, nsmul_eq_mul, mul_comm]
  have h3 : |G * ∑ v, bitZ (h v) * shiftVec v f| ≤ G * ((k : ℤ) + 3) := by
    rw [abs_mul, abs_of_nonneg hG]
    exact mul_le_mul_of_nonneg_left h1 hG
  obtain ⟨h4, h5⟩ := abs_le.mp h3
  obtain ⟨h6, h7⟩ := abs_le.mp h2
  have hval : family W₀ G h a f = W₀ + G * ∑ v, bitZ (h v) * shiftVec v f + ∑ j, a j * b j f := rfl
  rw [hval]
  constructor
  · rw [hW₀]
    linarith
  · have : W₀ + G * ∑ v, bitZ (h v) * shiftVec v f + ∑ j, a j * b j f ≤ 2 * W₀ := by
      rw [hW₀] at *
      linarith
    exact this.trans hW

/-- The averaging over the coins of a randomized algorithm. -/
theorem classical_avg [NeZero (k + 3)] (Ω : Type) [Fintype Ω] (r : RandAlg (k + 3) Ω) (W : ℤ) (W₀ : ℤ)
    (G L E : ℕ) (hG0 : 0 < G) (hG : ∀ d : ℕ, 1 ≤ d → d ≤ k + 3 → d ∣ G)
    (hγ : ∀ (Q : Fin T → Fin (k + 3) → Bool) (v : Fin (k + 3)),
      (G : ℤ) • (fun s => cut (shiftVec v) (Q s)) ∈ labelLattice Q →
      ∃ γ : LabelIdx k → ℤ, (∀ s, ∑ j, γ j * cut (b j) (Q s) = G * cut (shiftVec v) (Q s)) ∧
        ∀ j, |γ j| ≤ E)
    (hBd : 1000 * (boundary (LabelIdx k) L E).card ≤ (box (LabelIdx k) L).card)
    (hclass : ∀ (h : Fin (k + 3) → Bool) (a : LabelIdx k → ℤ), a ∈ box (LabelIdx k) L →
      InClass W (family W₀ G h a))
    (herr : ∀ A : Weights (k + 3), InClass W A → r.err T A ≤ 1 / 3) :
    ((k + 3 : ℕ) : ℝ) * (1 / 3 - 1 / 1000) ≤ 2 * T + 3 := by
  set Bx := box (LabelIdx k) L with hBx
  set Bd := boundary (LabelIdx k) L E with hBd'
  set N : ℝ := ((k + 3 : ℕ) : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hBxpos : (0 : ℝ) < Bx.card := by exact_mod_cast card_box_pos L
  have hBdle : (1000 : ℝ) * Bd.card ≤ Bx.card := by exact_mod_cast hBd
  let e1 : Ω → ℕ := fun ω => (Bx.filter fun a =>
    (r.alg ω).run T (family W₀ G (fun _ => true) a) ≠ minDegree (family W₀ G (fun _ => true) a)).card
  let ev : Ω → Fin (k + 3) → ℕ := fun ω v => (Bx.filter fun a =>
    (r.alg ω).run T (family W₀ G (Function.update (fun _ => true) v false) a)
      ≠ minDegree (family W₀ G (Function.update (fun _ => true) v false) a)).card
  have hcore : ∀ ω, N * Bx.card
      ≤ N * e1 ω + ∑ v, (ev ω v : ℝ) + N * Bd.card + (2 * T + 3) * Bx.card := by
    intro ω
    have := det_core (T := T) (r.alg ω) W₀ G L E hG0 hG hγ
    rw [hN]
    exact_mod_cast this
  have herr1 : ∑ ω, r.p ω * (e1 ω : ℝ) ≤ (Bx.card : ℝ) / 3 := by
    rw [show ∑ ω, r.p ω * (e1 ω : ℝ) = ∑ a ∈ Bx, r.err T (family W₀ G (fun _ => true) a) from
      (sum_err_eq r T Bx _).symm]
    calc ∑ a ∈ Bx, r.err T (family W₀ G (fun _ => true) a) ≤ ∑ _a ∈ Bx, (1 / 3 : ℝ) :=
          sum_le_sum fun a ha => herr _ (hclass _ a ha)
      _ = (Bx.card : ℝ) / 3 := by rw [sum_const, nsmul_eq_mul]; ring
  have herr2 : ∀ v, ∑ ω, r.p ω * (ev ω v : ℝ) ≤ (Bx.card : ℝ) / 3 := by
    intro v
    rw [show ∑ ω, r.p ω * (ev ω v : ℝ)
        = ∑ a ∈ Bx, r.err T (family W₀ G (Function.update (fun _ => true) v false) a) from
      (sum_err_eq r T Bx _).symm]
    calc ∑ a ∈ Bx, r.err T (family W₀ G (Function.update (fun _ => true) v false) a)
        ≤ ∑ _a ∈ Bx, (1 / 3 : ℝ) := sum_le_sum fun a ha => herr _ (hclass _ a ha)
      _ = (Bx.card : ℝ) / 3 := by rw [sum_const, nsmul_eq_mul]; ring
  have h3 : ∑ ω, r.p ω * (N * (e1 ω : ℝ)) ≤ N * ((Bx.card : ℝ) / 3) := by
    calc ∑ ω, r.p ω * (N * (e1 ω : ℝ)) = N * ∑ ω, r.p ω * (e1 ω : ℝ) := by
          rw [mul_sum]
          exact sum_congr rfl fun ω _ => by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left herr1 hN0
  have h4 : ∑ ω, r.p ω * ∑ v, (ev ω v : ℝ) ≤ N * ((Bx.card : ℝ) / 3) := by
    calc ∑ ω, r.p ω * ∑ v, (ev ω v : ℝ) = ∑ v, ∑ ω, r.p ω * (ev ω v : ℝ) := by
          simp only [mul_sum]
          rw [sum_comm]
      _ ≤ ∑ _v : Fin (k + 3), (Bx.card : ℝ) / 3 := sum_le_sum fun v _ => herr2 v
      _ = N * ((Bx.card : ℝ) / 3) := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have havg : N * Bx.card ≤ N * ((Bx.card : ℝ) / 3) + N * ((Bx.card : ℝ) / 3)
      + N * Bd.card + (2 * T + 3) * Bx.card := by
    have h2 : ∑ ω, r.p ω * (N * Bx.card)
        ≤ ∑ ω, r.p ω * (N * e1 ω + ∑ v, (ev ω v : ℝ) + N * Bd.card + (2 * T + 3) * Bx.card) :=
      sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hcore ω) (r.nonneg ω)
    rw [← sum_mul, r.sum_one, one_mul] at h2
    refine h2.trans ?_
    have h5 : ∑ ω, r.p ω * (N * (Bd.card : ℝ)) = N * Bd.card := by
      rw [← sum_mul, r.sum_one, one_mul]
    have h6 : ∑ ω, r.p ω * ((2 * (T : ℝ) + 3) * (Bx.card : ℝ)) = (2 * (T : ℝ) + 3) * Bx.card := by
      rw [← sum_mul, r.sum_one, one_mul]
    have hsplit : ∑ ω, r.p ω * (N * e1 ω + ∑ v, (ev ω v : ℝ) + N * Bd.card + (2 * T + 3) * Bx.card)
        = ∑ ω, r.p ω * (N * (e1 ω : ℝ)) + ∑ ω, r.p ω * ∑ v, (ev ω v : ℝ)
          + N * Bd.card + (2 * T + 3) * Bx.card := by
      calc ∑ ω, r.p ω * (N * e1 ω + ∑ v, (ev ω v : ℝ) + N * Bd.card + (2 * T + 3) * Bx.card)
          = ∑ ω, (r.p ω * (N * (e1 ω : ℝ)) + r.p ω * ∑ v, (ev ω v : ℝ) + r.p ω * (N * (Bd.card : ℝ))
              + r.p ω * ((2 * (T : ℝ) + 3) * (Bx.card : ℝ))) :=
            sum_congr rfl fun ω _ => by ring
        _ = _ := by rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, h5, h6]
    rw [hsplit]
    linarith
  have hkey : N * (1 / 3 - 1 / 1000) * Bx.card ≤ (2 * T + 3) * Bx.card := by
    have h9 : N * Bd.card ≤ N * ((Bx.card : ℝ) / 1000) :=
      mul_le_mul_of_nonneg_left (by linarith) hN0
    linarith
  exact le_of_mul_le_mul_right hkey hBxpos

/-- The theorem for `n = k + 3` and `T < n`. -/
theorem classical_bound_aux [NeZero (k + 3)] (hT : T < k + 3) (Ω : Type) [Fintype Ω]
    (r : RandAlg (k + 3) Ω)
    (herr : ∀ A : Weights (k + 3), InClass (classicalWeight (k + 3) 23) A → r.err T A ≤ 1 / 3) :
    (((k + 3 : ℕ) : ℝ)) / 7 - 2 ≤ T := by
  obtain ⟨G, hGdef⟩ : ∃ G : ℕ, G = (k + 3).factorial := ⟨_, rfl⟩
  have hG0 : 0 < G := hGdef ▸ Nat.factorial_pos _
  have hG : ∀ d : ℕ, 1 ≤ d → d ≤ k + 3 → d ∣ G := fun d h1 h2 =>
    hGdef ▸ Nat.dvd_factorial h1 h2
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, J = Fintype.card (LabelIdx k) := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℕ, E = (G + J) * ((k + 3).factorial * 6 ^ (k + 3)) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = 1000 * J * E := ⟨_, rfl⟩
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : ℤ, W₀ = (G : ℤ) * (k + 3) + (L : ℤ) * J := ⟨_, rfl⟩
  have hγ : ∀ (Q : Fin T → Fin (k + 3) → Bool) (v : Fin (k + 3)),
      (G : ℤ) • (fun s => cut (shiftVec v) (Q s)) ∈ labelLattice Q →
      ∃ γ : LabelIdx k → ℤ, (∀ s, ∑ j, γ j * cut (b j) (Q s) = G * cut (shiftVec v) (Q s)) ∧
        ∀ j, |γ j| ≤ E := by
    intro Q v hm
    obtain ⟨γ, h1, h2⟩ := exists_small_gamma Q v G hm
    refine ⟨γ, h1, fun j => (h2 j).trans ?_⟩
    have h3 : T.factorial ≤ (k + 3).factorial := Nat.factorial_le hT.le
    have h4 : 6 ^ T ≤ 6 ^ (k + 3) := Nat.pow_le_pow_right (by norm_num) hT.le
    have h5 : (G + Fintype.card (LabelIdx k)) * (T.factorial * 6 ^ T) ≤ E := by
      rw [hE, hJ]
      gcongr
    exact_mod_cast h5
  have hsize : (2 : ℤ) * W₀ ≤ classicalWeight (k + 3) 23 := by
    have h1 := size_bound (k + 3) (Nat.log 2 (k + 3) + 1) G J (by omega) (by omega)
      (Nat.lt_pow_succ_log_self (by norm_num) _) hGdef (hJ ▸ card_labelIdx_le)
    rw [← hE, ← hL] at h1
    unfold classicalWeight
    rw [hW₀]
    have h2 : ((2 * (G * (k + 3) + L * J) : ℕ) : ℤ)
        ≤ ((2 ^ (23 * (k + 3) * (Nat.log 2 (k + 3) + 1)) : ℕ) : ℤ) := by exact_mod_cast h1
    push_cast at h2 ⊢
    exact h2
  have hclass : ∀ (h : Fin (k + 3) → Bool) (a : LabelIdx k → ℤ), a ∈ box (LabelIdx k) L →
      InClass (classicalWeight (k + 3) 23) (family W₀ G h a) :=
    fun h a ha => family_inClass L W₀ G (by positivity) (by rw [hW₀, hJ]) h a ha _ hsize
  have hBd : 1000 * (boundary (LabelIdx k) L E).card ≤ (box (LabelIdx k) L).card := by
    have h2 := boundary_count (J := LabelIdx k) L E
    rw [← hJ] at h2
    have h3 : (2 * L + 1) * (1000 * (boundary (LabelIdx k) L E).card)
        ≤ (2 * L + 1) * (box (LabelIdx k) L).card := by
      calc (2 * L + 1) * (1000 * (boundary (LabelIdx k) L E).card)
          = 1000 * ((boundary (LabelIdx k) L E).card * (2 * L + 1)) := by ring
        _ ≤ 1000 * (J * (2 * E) * (box (LabelIdx k) L).card) := Nat.mul_le_mul_left _ h2
        _ = (2 * L) * (box (LabelIdx k) L).card := by rw [hL]; ring
        _ ≤ (2 * L + 1) * (box (LabelIdx k) L).card := Nat.mul_le_mul_right _ (by omega)
    exact Nat.le_of_mul_le_mul_left h3 (by omega)
  have hkey := classical_avg (T := T) Ω r _ W₀ G L E hG0 hG hγ hBd hclass herr
  have hN0 : (0 : ℝ) ≤ ((k + 3 : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

end Main

/-- The classical lower bound for minimum degree with cut queries, for weights of `O(n log n)` bits. -/
theorem classical_bound : ∃ C : ℕ, ∀ (n : ℕ) [NeZero n] (T : ℕ) (Ω : Type) [Fintype Ω] (r : RandAlg n Ω),
    (∀ A : Weights n, InClass (classicalWeight n C) A → r.err T A ≤ 1 / 3) → (n : ℝ) / 7 - 2 ≤ T := by
  refine ⟨23, ?_⟩
  intro n _ T Ω _ r herr
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  by_cases hn : n < 3
  · have : (n : ℝ) ≤ 3 := by exact_mod_cast hn.le
    linarith
  by_cases hT : n ≤ T
  · have : (n : ℝ) ≤ T := by exact_mod_cast hT
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  exact classical_bound_aux (by omega) Ω r herr

end CutQuery
