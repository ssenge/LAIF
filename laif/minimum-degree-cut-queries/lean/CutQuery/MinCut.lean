import CutQuery.QReduction

/-!
# Global minimum cut, and phase queries with any modulus

* `QAlg.toGen`, `quantum_bound_any_modulus`: a phase query with any modulus `N` is a query with a phase function
  of the cut value, so the bound covers every `N`.
* `IsMinCut`: the value of a minimum cut.
* `liftW w A`: on `Fin (n + n)`, the graph `A` on the first `n` vertices, and weight `w` on all other pairs.
* `isMinCut_liftW`: for `w = n W` and `A` with weights in `[0, W]`, the minimum cut of the lift is
  `minDegree A + n w`. A query set with `a` vertices among the first `n` and `b` among the last `n` cuts
  `(a + b)(2n - a - b) - a(n - a)` heavy pairs. This is at least `2n - 1`, unless the set or its complement is a
  single vertex among the first `n`, where it is `n` and the light part is the degree of that vertex.
* `quantum_mincut_bound`: the reduction from the minimum degree.
-/

open Finset

namespace CutQuery

variable {n T : ℕ} {S : Type*} [Fintype S] [DecidableEq S]

/-- `d` is the value of a minimum cut: the least cut value over query sets that are not constant. -/
def IsMinCut {m : ℕ} (A : Weights m) (d : ℤ) : Prop :=
  (∃ x : Fin m → Bool, (∃ u v, x u ≠ x v) ∧ cut A x = d) ∧
    ∀ x : Fin m → Bool, (∃ u v, x u ≠ x v) → d ≤ cut A x

section AnyModulus

/-- A phase query with modulus `N`, as a query with a phase function of the cut value. -/
noncomputable def QAlg.toGen (q : QAlg n T S) (N : ℕ) : GenAlg n T S where
  x := q.x
  f s y := Complex.exp (2 * Real.pi * Complex.I * (q.z s * y : ℤ) / N)
  norm_f s y := by
    have h : 2 * (Real.pi : ℂ) * Complex.I * ((q.z s * y : ℤ) : ℂ) / (N : ℂ)
        = ((2 * Real.pi * ((q.z s * y : ℤ) : ℝ) / N : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  U := q.U
  init := q.init
  out := q.out

theorem QAlg.toGen_state (q : QAlg n T S) (N : ℕ) (A : Weights n) :
    ∀ (t : ℕ) (ht : t ≤ T), (q.toGen N).state A t ht = q.state N A t ht := by
  intro t
  induction t with
  | zero => intro ht; rfl
  | succ t ih =>
    intro ht
    have h1 : (q.toGen N).state A (t + 1) ht = (q.U ⟨t + 1, Nat.succ_lt_succ ht⟩ : Matrix S S ℂ).mulVec
        fun s => q.phase N A s * (q.toGen N).state A t (Nat.le_of_succ_le ht) s := rfl
    rw [h1, ih]
    rfl

theorem QAlg.toGen_errAt (q : QAlg n T S) (N : ℕ) (A : Weights n) (d : ℤ) :
    (q.toGen N).errAt A d = q.errAt N A d := by
  unfold GenAlg.errAt QAlg.errAt
  rw [q.toGen_state]
  rfl

/-- The quantum bound for phase queries with any modulus. -/
theorem quantum_bound_any_modulus (hA : AndApproxDegree) : ∃ (C : ℕ) (c : ℝ), 0 < c ∧
    ∀ (n : ℕ) [NeZero n] (T : ℕ) (S : Type) [Fintype S] [DecidableEq S] (q : QAlg n T S) (N : ℕ),
    (∀ A : Weights n, InClass (quantumWeight n C : ℤ) A → q.errAt N A (minDegree A) ≤ 1 / 3) →
    c * Real.sqrt n ≤ 2 * T + 1 := by
  obtain ⟨C, c, hc, hb⟩ := quantum_bound_general hA
  refine ⟨C, c, hc, ?_⟩
  intro n _ T S _ _ q N h
  exact hb n T S (q.toGen N) fun A hA' => by
    rw [q.toGen_errAt]
    exact h A hA'

end AnyModulus

section Counting

variable {m : ℕ}

/-- The number of vertices on the `true` side of a query set. -/
def cnt (y : Fin m → Bool) : ℤ := ∑ u, bitZ (y u)

theorem cnt_nonneg (y : Fin m → Bool) : 0 ≤ cnt y := sum_nonneg fun _ _ => bitZ_nonneg _

theorem cnt_compl (y : Fin m → Bool) : cnt (fun u => !y u) = (m : ℤ) - cnt y := by
  have h : ∀ u, bitZ (!y u) = 1 - bitZ (y u) := by
    intro u
    cases y u <;> simp [bitZ]
  unfold cnt
  simp_rw [h]
  rw [sum_sub_distrib]
  simp

theorem cnt_le (y : Fin m → Bool) : cnt y ≤ m := by
  have := cnt_nonneg fun u => !y u
  rw [cnt_compl] at this
  linarith

theorem one_le_cnt {y : Fin m → Bool} {v : Fin m} (hv : y v = true) : 1 ≤ cnt y := by
  have h : bitZ (y v) ≤ cnt y :=
    single_le_sum (f := fun u => bitZ (y u)) (fun u _ => bitZ_nonneg (y u)) (mem_univ v)
  rw [hv] at h
  simpa [bitZ] using h

theorem cnt_eq_card (y : Fin m → Bool) : cnt y = ((univ.filter fun u => y u = true).card : ℤ) := by
  unfold cnt bitZ
  rw [card_filter]
  push_cast
  refine sum_congr rfl fun u _ => ?_
  cases y u <;> simp

/-- The number of crossing pairs. -/
theorem cut_one (y : Fin m → Bool) : cut (fun _ => (1 : ℤ)) y = cnt y * ((m : ℤ) - cnt y) := by
  have hcard : (univ.filter fun e : Edge m => y e.1.1 ≠ y e.1.2).card
      = ((univ.filter fun u => y u = true) ×ˢ (univ.filter fun u => (!y u) = true)).card := by
    refine card_bij (fun e _ => if y e.1.1 = true then (e.1.1, e.1.2) else (e.1.2, e.1.1)) ?_ ?_ ?_
    · intro e he
      have he' := (mem_filter.mp he).2
      simp only [mem_product, mem_filter, mem_univ, true_and]
      cases h1 : y e.1.1 <;> cases h2 : y e.1.2 <;> simp_all
    · intro e he e' he' h
      have hlt : e.1.1 < e.1.2 := e.2
      have hlt' : e'.1.1 < e'.1.2 := e'.2
      apply Subtype.ext
      apply Prod.ext
      · by_cases ha : y e.1.1 = true <;> by_cases hb : y e'.1.1 = true
        · simp only [ha, hb, ↓reduceIte, Prod.mk.injEq] at h
          exact h.1
        · simp only [ha, hb, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at h
          rw [h.1, h.2] at hlt
          exact absurd (hlt.trans hlt') (lt_irrefl _)
        · simp only [ha, hb, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at h
          rw [← h.1, ← h.2] at hlt'
          exact absurd (hlt.trans hlt') (lt_irrefl _)
        · simp only [ha, hb, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at h
          exact h.2
      · by_cases ha : y e.1.1 = true <;> by_cases hb : y e'.1.1 = true
        · simp only [ha, hb, ↓reduceIte, Prod.mk.injEq] at h
          exact h.2
        · simp only [ha, hb, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at h
          rw [h.1, h.2] at hlt
          exact absurd (hlt.trans hlt') (lt_irrefl _)
        · simp only [ha, hb, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at h
          rw [← h.1, ← h.2] at hlt'
          exact absurd (hlt.trans hlt') (lt_irrefl _)
        · simp only [ha, hb, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at h
          exact h.1
    · rintro ⟨v, u⟩ hp
      simp only [mem_product, mem_filter, mem_univ, true_and] at hp
      obtain ⟨hv, hu⟩ := hp
      have hu' : y u = false := by simpa using hu
      have hne : v ≠ u := by
        rintro rfl
        rw [hv] at hu'
        exact absurd hu' (by simp)
      rcases lt_or_gt_of_ne hne with h | h
      · refine ⟨⟨(v, u), h⟩, mem_filter.mpr ⟨mem_univ _, by simp [hv, hu']⟩, ?_⟩
        simp only [hv, ↓reduceIte]
      · refine ⟨⟨(u, v), h⟩, mem_filter.mpr ⟨mem_univ _, by simp [hv, hu']⟩, ?_⟩
        simp only [hu']
        simp
  have hsum : cut (fun _ => (1 : ℤ)) y = ((univ.filter fun e : Edge m => y e.1.1 ≠ y e.1.2).card : ℤ) := by
    unfold cut crosses
    rw [card_filter]
    push_cast
    exact sum_congr rfl fun e _ => one_mul _
  rw [hsum, hcard, card_product]
  push_cast
  rw [← cnt_eq_card, ← cnt_eq_card fun u => !y u, cnt_compl]

theorem cut_compl (A : Weights m) (y : Fin m → Bool) : cut A (fun u => !y u) = cut A y := by
  unfold cut
  refine sum_congr rfl fun e _ => ?_
  have h : crosses (fun u => !y u) e = crosses y e := by
    have hiff : ((!y e.1.1) ≠ (!y e.1.2)) ↔ (y e.1.1 ≠ y e.1.2) := by
      cases y e.1.1 <;> cases y e.1.2 <;> simp
    simp only [crosses, hiff]
  rw [h]

theorem exists_single_of_cnt {y : Fin m → Bool} (h : cnt y = 1) : ∃ v, y = fun u => decide (u = v) := by
  rw [cnt_eq_card] at h
  have h1 : (univ.filter fun u => y u = true).card = 1 := by exact_mod_cast h
  obtain ⟨v, hv⟩ := card_eq_one.mp h1
  refine ⟨v, funext fun u => ?_⟩
  have hu : y u = true ↔ u = v := by
    have := Finset.ext_iff.mp hv u
    simpa using this
  by_cases huv : u = v
  · subst huv
    have hy := hu.mpr rfl
    simp [hy]
  · have : y u ≠ true := fun h' => huv (hu.mp h')
    simp [huv, this]

/-- The cut of a singleton is the degree. -/
theorem cut_single (A : Weights m) (v : Fin m) : cut A (fun u => decide (u = v)) = degree A v := by
  unfold cut degree crosses
  refine sum_congr rfl fun e _ => ?_
  have hlt : e.1.1 < e.1.2 := e.2
  by_cases h1 : e.1.1 = v
  · have h2 : e.1.2 ≠ v := fun h => hlt.ne (h1.trans h.symm)
    simp [h1, h2]
  · by_cases h2 : e.1.2 = v
    · simp [h1, h2]
    · simp [h1, h2]

theorem cut_nonneg {W : ℤ} {A : Weights m} (hA : InClass W A) (y : Fin m → Bool) : 0 ≤ cut A y := by
  refine sum_nonneg fun e _ => mul_nonneg (hA e).1 ?_
  unfold crosses
  split_ifs <;> simp

/-- Degrees are at most `(m - 1) W`. -/
theorem degree_le_of_inClass {W : ℤ} {A : Weights m} (hA : InClass W A) (v : Fin m) :
    degree A v ≤ ((m : ℤ) - 1) * W := by
  have h1 : degree A v ≤ ∑ e : Edge m, W * (if e.1.1 = v ∨ e.1.2 = v then 1 else 0) := by
    unfold degree
    refine sum_le_sum fun e _ => ?_
    split_ifs
    · simpa using (hA e).2
    · simp
  have h2 := degree_const_one (n := m) v
  have h3 : ∑ e : Edge m, W * (if e.1.1 = v ∨ e.1.2 = v then (1 : ℤ) else 0)
      = W * degree (fun _ : Edge m => (1 : ℤ)) v := by
    unfold degree
    rw [mul_sum]
  rw [h3, h2] at h1
  linarith [mul_comm W ((m : ℤ) - 1)]

/-- The count of crossing heavy pairs. -/
theorem heavy_count (n a b : ℤ) (hn : 1 ≤ n) (ha0 : 0 ≤ a) (ha1 : a ≤ n) (hb0 : 0 ≤ b) (hb1 : b ≤ n)
    (h1 : 1 ≤ a + b) (h2 : a + b ≤ 2 * n - 1) :
    2 * n - 1 ≤ (a + b) * (2 * n - (a + b)) - a * (n - a) ∨
      ((a + b) * (2 * n - (a + b)) - a * (n - a) = n ∧ ((a = 1 ∧ b = 0) ∨ (a = n - 1 ∧ b = n))) := by
  by_cases hb : b = 0
  · subst hb
    by_cases ha : a = 1
    · subst ha
      right
      exact ⟨by ring, Or.inl ⟨rfl, rfl⟩⟩
    · left
      have : 2 ≤ a := by omega
      nlinarith
  by_cases hbn : b = n
  · subst hbn
    by_cases ha : a = b - 1
    · subst ha
      right
      exact ⟨by ring, Or.inr ⟨rfl, rfl⟩⟩
    · left
      have : a ≤ b - 2 := by omega
      nlinarith
  · left
    have hb' : 1 ≤ b := by omega
    have hbn' : b ≤ n - 1 := by omega
    have hp1 : 2 * n - 1 ≤ b * (2 * n - b) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hb') (by linarith : 0 ≤ 2 * n - b - 1)]
    have hp2 : 2 * n - 1 ≤ (n - b) * (n + b) := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ n - b - 1) (by linarith : 0 ≤ n + b - 1)]
    have hkey : n * ((a + b) * (2 * n - (a + b)) - a * (n - a))
        = (n - a) * (b * (2 * n - b)) + a * ((n - b) * (n + b)) := by ring
    have hmul : n * (2 * n - 1) ≤ n * ((a + b) * (2 * n - (a + b)) - a * (n - a)) := by
      rw [hkey]
      have h3 := mul_le_mul_of_nonneg_left hp1 (by linarith : 0 ≤ n - a)
      have h4 := mul_le_mul_of_nonneg_left hp2 ha0
      nlinarith
    exact le_of_mul_le_mul_left hmul (by linarith)

end Counting

section Lift

/-- A graph on the first `n` vertices, as a weight vector on `Fin (n + n)`. -/
def inner (A : Weights n) : Weights (n + n) := fun e =>
  if h : e.1.2.val < n then
    A ⟨(⟨e.1.1.val, lt_trans (Fin.lt_def.mp e.2) h⟩, ⟨e.1.2.val, h⟩), Fin.lt_def.mpr (Fin.lt_def.mp e.2)⟩
  else 0

/-- Weight `w` on the pairs that meet the last `n` vertices. -/
def heavy (w : ℤ) : Weights (n + n) := fun e => if e.1.2.val < n then 0 else w

/-- The lift: `A` on the first `n` vertices and `w` on all other pairs. -/
def liftW (w : ℤ) (A : Weights n) : Weights (n + n) := inner A + heavy w

/-- The restriction of a query set to the first `n` vertices. -/
def restr (y : Fin (n + n) → Bool) : Fin n → Bool := fun i => y (Fin.castAdd n i)

/-- The edge of the lift that corresponds to an edge of `A`. -/
def edgeUp (e : Edge n) : Edge (n + n) :=
  ⟨(Fin.castAdd n e.1.1, Fin.castAdd n e.1.2), Fin.lt_def.mpr (Fin.lt_def.mp e.2)⟩

theorem cut_inner (A : Weights n) (y : Fin (n + n) → Bool) : cut (inner A) y = cut A (restr y) := by
  unfold cut
  symm
  refine sum_of_injOn edgeUp ?_ (fun _ _ => mem_univ _) ?_ ?_
  · intro e _ e' _ h
    have h1 := congrArg (fun f : Edge (n + n) => f.1.1.val) h
    have h2 := congrArg (fun f : Edge (n + n) => f.1.2.val) h
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.ext h1
    · exact Fin.ext h2
  · intro f _ hf
    by_cases hlt : f.1.2.val < n
    · exfalso
      apply hf
      have hlt' : f.1.1.val < f.1.2.val := Fin.lt_def.mp f.2
      refine ⟨⟨(⟨f.1.1.val, lt_trans hlt' hlt⟩, ⟨f.1.2.val, hlt⟩), Fin.lt_def.mpr hlt'⟩, mem_univ _, ?_⟩
      apply Subtype.ext
      apply Prod.ext <;> exact Fin.ext rfl
    · simp [inner, hlt]
  · intro e _
    have hlt : (edgeUp e).1.2.val < n := e.1.2.2
    have h1 : inner A (edgeUp e) = A e := by
      simp only [inner, hlt, ↓reduceDIte]
      rfl
    rw [h1]
    rfl

theorem cut_liftW (w : ℤ) (A : Weights n) (y : Fin (n + n) → Bool) :
    cut (liftW w A) y = cut A (restr y) + cut (heavy w) y := by
  unfold liftW
  rw [cut_add, cut_inner]

theorem cut_heavy (w : ℤ) (y : Fin (n + n) → Bool) : cut (heavy (n := n) w) y = w * cut (heavy (n := n) 1) y := by
  have h : heavy (n := n) w = w • heavy (n := n) 1 := by
    funext e
    simp only [heavy, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [h, cut_zsmul]

/-- The number of heavy pairs across a query set. -/
theorem cut_heavy_one (y : Fin (n + n) → Bool) :
    cut (heavy (n := n) 1) y = cnt y * (2 * (n : ℤ) - cnt y) - cnt (restr y) * ((n : ℤ) - cnt (restr y)) := by
  have hsplit : (fun _ : Edge (n + n) => (1 : ℤ)) = inner (fun _ : Edge n => (1 : ℤ)) + heavy 1 := by
    funext e
    simp only [Pi.add_apply, inner, heavy]
    split_ifs <;> simp
  have h := cut_one y
  rw [hsplit, cut_add, cut_inner, cut_one] at h
  push_cast at h
  have h2 : cnt y * ((n : ℤ) + n - cnt y) = cnt y * (2 * (n : ℤ) - cnt y) := by ring
  linarith

theorem cnt_split (y : Fin (n + n) → Bool) : cnt y = cnt (restr y) + cnt fun i => y (Fin.natAdd n i) := by
  unfold cnt restr
  rw [Fin.sum_univ_add]

/-- The minimum cut of the lift. -/
theorem isMinCut_liftW [NeZero n] {W : ℤ} (hW : 0 ≤ W) {A : Weights n} (hA : InClass W A) :
    IsMinCut (liftW ((n : ℤ) * W) A) (minDegree A + (n : ℤ) * ((n : ℤ) * W)) := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hnpos
  constructor
  · obtain ⟨v, -, hv⟩ := exists_mem_eq_inf' (s := univ) ⟨(0 : Fin n), mem_univ _⟩ (degree A)
    have hmin : minDegree A = degree A v := hv
    have hrestr : restr (fun u : Fin (n + n) => decide (u = Fin.castAdd n v)) = fun i => decide (i = v) := by
      funext i
      simp only [restr, decide_eq_decide]
      constructor
      · intro h
        exact Fin.ext (by simpa using congrArg Fin.val h)
      · rintro rfl
        rfl
    have hcntR : cnt (fun i : Fin n => decide (i = v)) = 1 := by
      unfold cnt bitZ
      simp
    have hcntL : (cnt fun i : Fin n => decide (Fin.natAdd n i = Fin.castAdd n v)) = 0 := by
      unfold cnt bitZ
      refine sum_eq_zero fun i _ => ?_
      have : Fin.natAdd n i ≠ Fin.castAdd n v := by
        intro h
        have h1 := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at h1
        have := v.2
        omega
      beta_reduce
      rw [decide_eq_false this]
      simp
    refine ⟨fun u => decide (u = Fin.castAdd n v), ⟨Fin.castAdd n v, Fin.natAdd n ⟨0, hnpos⟩, ?_⟩, ?_⟩
    · have : Fin.natAdd n (⟨0, hnpos⟩ : Fin n) ≠ Fin.castAdd n v := by
        intro h
        have h1 := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at h1
        have := v.2
        omega
      beta_reduce
      rw [decide_eq_false this]
      simp
    · rw [cut_liftW, cut_heavy, cut_heavy_one, hrestr, cnt_split, hrestr, hcntR, hcntL, cut_single, hmin]
      ring
  · intro y hy
    obtain ⟨u, v, huv⟩ := hy
    set a := cnt (restr y) with ha
    set c := cnt fun i => y (Fin.natAdd n i) with hc
    have hsum : cnt y = a + c := cnt_split y
    have hup : cnt y ≤ 2 * (n : ℤ) - 1 := by
      have hne : ∃ w, y w = false := by
        cases hyu : y u
        · exact ⟨u, hyu⟩
        · cases hyv : y v
          · exact ⟨v, hyv⟩
          · rw [hyu, hyv] at huv
            exact absurd rfl huv
      obtain ⟨w, hw⟩ := hne
      have h1 := one_le_cnt (y := fun u => !y u) (v := w) (by simp [hw])
      rw [cnt_compl] at h1
      push_cast at h1
      linarith
    have hlow : 1 ≤ cnt y := by
      have hex : ∃ w, y w = true := by
        cases hyu : y u
        · cases hyv : y v
          · rw [hyu, hyv] at huv
            exact absurd rfl huv
          · exact ⟨v, hyv⟩
        · exact ⟨u, hyu⟩
      obtain ⟨w, hw⟩ := hex
      exact one_le_cnt hw
    have ha0 : 0 ≤ a := cnt_nonneg _
    have ha1 : a ≤ n := cnt_le _
    have hc0 : 0 ≤ c := cnt_nonneg _
    have hc1 : c ≤ n := cnt_le _
    have hmin : ∀ w, minDegree A ≤ degree A w := fun w => inf'_le _ (mem_univ w)
    have hcase := heavy_count (n : ℤ) a c hn1 ha0 ha1 hc0 hc1 (by rw [← hsum]; exact hlow)
      (by rw [← hsum]; exact hup)
    rw [cut_liftW, cut_heavy, cut_heavy_one, hsum]
    set w : ℤ := (n : ℤ) * W with hw
    have hw0 : 0 ≤ w := mul_nonneg (by linarith) hW
    rcases hcase with hbig | ⟨hval, hsing⟩
    · have hd : minDegree A ≤ ((n : ℤ) - 1) * w := by
        have h1 := (hmin ⟨0, hnpos⟩).trans (degree_le_of_inClass hA ⟨0, hnpos⟩)
        have h2 : ((n : ℤ) - 1) * W ≤ ((n : ℤ) - 1) * w := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          rw [hw]
          nlinarith
        linarith
      have h3 := cut_nonneg hA (restr y)
      have h4 := mul_le_mul_of_nonneg_left hbig hw0
      nlinarith
    · rw [hval]
      have hd : minDegree A ≤ cut A (restr y) := by
        rcases hsing with ⟨h1, -⟩ | ⟨h1, -⟩
        · obtain ⟨t, ht⟩ := exists_single_of_cnt h1
          rw [ht, cut_single]
          exact hmin t
        · have h2 : cnt (fun i => !restr y i) = 1 := by
            rw [cnt_compl, ← ha, h1]
            ring
          obtain ⟨t, ht⟩ := exists_single_of_cnt h2
          have h3 := cut_compl A (restr y)
          rw [← h3, ht, cut_single]
          exact hmin t
      nlinarith

theorem inClass_liftW {W : ℤ} (hW : 0 ≤ W) (hn : (1 : ℤ) ≤ n) {A : Weights n} (hA : InClass W A) :
    InClass ((n : ℤ) * W) (liftW ((n : ℤ) * W) A) := by
  intro e
  have hle : W ≤ (n : ℤ) * W := by nlinarith
  simp only [liftW, Pi.add_apply, inner, heavy]
  split_ifs with h
  · have := hA ⟨(⟨e.1.1.val, lt_trans (Fin.lt_def.mp e.2) h⟩, ⟨e.1.2.val, h⟩), Fin.lt_def.mpr (Fin.lt_def.mp e.2)⟩
    constructor <;> linarith [this.1, this.2]
  · constructor <;> linarith

end Lift

section Reduction

/-- The algorithm on `Fin n` that runs `g` on the lift of its input. -/
noncomputable def GenAlg.restrict (g : GenAlg (n + n) T S) (w : ℤ) : GenAlg n T S where
  x s := restr (g.x s)
  f s y := g.f s (y + cut (heavy w) (g.x s))
  norm_f s _ := g.norm_f s _
  U := g.U
  init := g.init
  out s := g.out s - (n : ℤ) * w

theorem GenAlg.restrict_state (g : GenAlg (n + n) T S) (w : ℤ) (A : Weights n) :
    ∀ (t : ℕ) (ht : t ≤ T), (g.restrict w).state A t ht = g.state (liftW w A) t ht := by
  intro t
  induction t with
  | zero => intro ht; rfl
  | succ t ih =>
    intro ht
    have h1 : (g.restrict w).state A (t + 1) ht = (g.U ⟨t + 1, Nat.succ_lt_succ ht⟩ : Matrix S S ℂ).mulVec
        fun s => g.f s (cut A (restr (g.x s)) + cut (heavy w) (g.x s))
          * (g.restrict w).state A t (Nat.le_of_succ_le ht) s := rfl
    have h2 : g.state (liftW w A) (t + 1) ht = (g.U ⟨t + 1, Nat.succ_lt_succ ht⟩ : Matrix S S ℂ).mulVec
        fun s => g.f s (cut (liftW w A) (g.x s)) * g.state (liftW w A) t (Nat.le_of_succ_le ht) s := rfl
    rw [h1, h2, ih]
    simp only [cut_liftW]

theorem GenAlg.restrict_errAt (g : GenAlg (n + n) T S) (w : ℤ) (A : Weights n) (d : ℤ) :
    (g.restrict w).errAt A d = g.errAt (liftW w A) (d + (n : ℤ) * w) := by
  unfold GenAlg.errAt
  rw [g.restrict_state]
  refine sum_congr rfl fun s _ => ?_
  have h : (g.restrict w).out s = d ↔ g.out s = d + (n : ℤ) * w := by
    change g.out s - (n : ℤ) * w = d ↔ _
    constructor <;> intro h <;> linarith
  simp only [h]

/-- The quantum bound for the value of a global minimum cut. -/
theorem quantum_mincut_bound (hA : AndApproxDegree) : ∃ (C : ℕ) (c : ℝ), 0 < c ∧
    ∀ (n : ℕ) [NeZero n] (T : ℕ) (S : Type) [Fintype S] [DecidableEq S] (g : GenAlg (n + n) T S),
    (∀ (A : Weights (n + n)) (d : ℤ), InClass ((n : ℤ) * (quantumWeight n C : ℤ)) A → IsMinCut A d →
      g.errAt A d ≤ 1 / 3) →
    c * Real.sqrt n ≤ 2 * T + 1 := by
  obtain ⟨C, c, hc, hb⟩ := quantum_bound_general hA
  refine ⟨C, c, hc, ?_⟩
  intro n _ T S _ _ g h
  have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hW : (0 : ℤ) ≤ (quantumWeight n C : ℤ) := by positivity
  refine hb n T S (g.restrict ((n : ℤ) * (quantumWeight n C : ℤ))) fun A hA' => ?_
  rw [g.restrict_errAt]
  exact h _ _ (inClass_liftW hW hn1 hA') (isMinCut_liftW hW hA')

end Reduction

end CutQuery
