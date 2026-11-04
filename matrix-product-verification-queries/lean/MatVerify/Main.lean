import MatVerify.Gadget

/-!
# The lower bound

For `f : [N] → [N]` and seeds `c, e`, row `x` of `A` is `a (f x) + c x · G`, column `y` of `B` is
`b (f y) + e y · H`, all other rows and columns vanish, and `C` is the identity on the first `N`
coordinates. Then `A B = C` iff `f` is injective. Averaging the acceptance probability over the
seeds gives a sum of juntas in `f`, on which the element distinctness degree bound applies.
-/

namespace MatVerify

open Finset

variable {n u d N T : ℕ} {S : Type} [Fintype S] [DecidableEq S]

abbrev Sd (N u : ℕ) := (Fin N → Fin u → ZMod 2) × (Fin N → Fin u → ZMod 2)

def rowA (g : Gadget n u d N) (f : Fin N → Fin N) (c : Fin N → Fin u → ZMod 2) (x : Fin N)
    (t : Fin n) : ZMod 2 :=
  g.a (f x) t + ∑ i, c x i * g.G i t

def colB (g : Gadget n u d N) (f : Fin N → Fin N) (e : Fin N → Fin u → ZMod 2) (y : Fin N)
    (t : Fin n) : ZMod 2 :=
  g.b (f y) t + ∑ j, e y j * g.H j t

lemma rowA_colB (g : Gadget n u d N) (f : Fin N → Fin N) (c e : Fin N → Fin u → ZMod 2)
    (x y : Fin N) :
    ∑ t, rowA g f c x t * colB g f e y t = if f x = f y then 1 else 0 := by
  have h1 : ∑ t, g.a (f x) t * ∑ j, e y j * g.H j t = 0 := by
    calc _ = ∑ j, e y j * ∑ t, g.a (f x) t * g.H j t := by
          simp only [mul_sum]
          rw [sum_comm]
          exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
      _ = 0 := by simp [g.aH]
  have h2 : ∑ t, (∑ i, c x i * g.G i t) * g.b (f y) t = 0 := by
    calc _ = ∑ i, c x i * ∑ t, g.G i t * g.b (f y) t := by
          simp only [mul_sum, sum_mul]
          rw [sum_comm]
          exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
      _ = 0 := by simp [g.Gb]
  have h3 : ∑ t, (∑ i, c x i * g.G i t) * ∑ j, e y j * g.H j t = 0 := by
    calc _ = ∑ t, ∑ i, ∑ j, c x i * (e y j * (g.G i t * g.H j t)) := sum_congr rfl fun t _ => by
          rw [sum_mul_sum]
          exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
      _ = ∑ i, ∑ j, c x i * (e y j * ∑ t, g.G i t * g.H j t) := by
          rw [sum_comm]
          refine sum_congr rfl fun i _ => ?_
          rw [sum_comm]
          simp only [mul_sum]
      _ = 0 := by simp [g.GH]
  simp only [rowA, colB, add_mul, mul_add, sum_add_distrib, h1, h2, h3, g.ab, add_zero]

/-- The instance. -/
def inst (g : Gadget n u d N) (hN : N ≤ n) (f : Fin N → Fin N) (s : Sd N u) : Input n where
  A := fun i t => ∑ x, if Fin.castLE hN x = i then rowA g f s.1 x t else 0
  B := fun t j => ∑ y, if Fin.castLE hN y = j then colB g f s.2 y t else 0
  C := fun i j => ∑ x, if Fin.castLE hN x = i ∧ Fin.castLE hN x = j then 1 else 0

lemma castLE_eq_iff (hN : N ≤ n) (x y : Fin N) : Fin.castLE hN x = Fin.castLE hN y ↔ x = y :=
  (Fin.castLE_injective hN).eq_iff

lemma inst_A_emb (g : Gadget n u d N) (hN : N ≤ n) (f : Fin N → Fin N) (s : Sd N u) (x : Fin N)
    (t : Fin n) : (inst g hN f s).A (Fin.castLE hN x) t = rowA g f s.1 x t := by
  simp [inst]

lemma inst_B_emb (g : Gadget n u d N) (hN : N ≤ n) (f : Fin N → Fin N) (s : Sd N u) (y : Fin N)
    (t : Fin n) : (inst g hN f s).B t (Fin.castLE hN y) = colB g f s.2 y t := by
  simp [inst]

lemma inst_C_emb (g : Gadget n u d N) (hN : N ≤ n) (f : Fin N → Fin N) (s : Sd N u) (x y : Fin N) :
    (inst g hN f s).C (Fin.castLE hN x) (Fin.castLE hN y) = if x = y then 1 else 0 := by
  by_cases h : x = y
  · subst h
    have h1 : ∀ z : Fin N, (Fin.castLE hN z = Fin.castLE hN x ∧
        Fin.castLE hN z = Fin.castLE hN x) ↔ z = x := fun z => by simp
    simp only [inst, h1, sum_ite_eq', mem_univ, ite_true]
  · have : ∀ z : Fin N, ¬ (z = x ∧ z = y) := fun z hz => h (hz.1.symm.trans hz.2)
    simp [inst, this, h]

theorem inst_iff (g : Gadget n u d N) (hN : N ≤ n) (f : Fin N → Fin N) (s : Sd N u) :
    (inst g hN f s).A * (inst g hN f s).B = (inst g hN f s).C ↔ Function.Injective f := by
  have hprod : ∀ x y, ((inst g hN f s).A * (inst g hN f s).B) (Fin.castLE hN x) (Fin.castLE hN y)
      = if f x = f y then 1 else 0 := by
    intro x y
    rw [Matrix.mul_apply]
    simp only [inst_A_emb, inst_B_emb]
    exact rowA_colB g f s.1 s.2 x y
  constructor
  · intro h x y hxy
    have h1 := hprod x y
    rw [h, inst_C_emb] at h1
    by_contra hne
    simp [hne, hxy] at h1
  · intro hf
    ext i j
    by_cases hi : ∃ x, Fin.castLE hN x = i
    · by_cases hj : ∃ y, Fin.castLE hN y = j
      · obtain ⟨x, rfl⟩ := hi
        obtain ⟨y, rfl⟩ := hj
        rw [hprod, inst_C_emb]
        simp only [hf.eq_iff]
      · push Not at hj
        rw [Matrix.mul_apply]
        have h0 : ∀ t, (inst g hN f s).B t j = 0 := fun t => by simp [inst, hj]
        have h1 : (inst g hN f s).C i j = 0 := by simp [inst, hj]
        simp [h0, h1]
    · push Not at hi
      rw [Matrix.mul_apply]
      have h0 : ∀ t, (inst g hN f s).A i t = 0 := fun t => by simp [inst, hi]
      have h1 : (inst g hN f s).C i j = 0 := by simp [inst, hi]
      simp [h0, h1]

/-! ### The form of `dotP` on instances -/

lemma sum_emb (hN : N ≤ n) (F : Fin n → Fin n → ZMod 2) (Rr : Fin N → Fin n → ZMod 2) :
    ∑ i, ∑ t, F i t * ∑ x, (if Fin.castLE hN x = i then Rr x t else 0) =
      ∑ x, ∑ t, F (Fin.castLE hN x) t * Rr x t := by
  simp only [mul_sum]
  calc _ = ∑ i, ∑ x, ∑ t, F i t * (if Fin.castLE hN x = i then Rr x t else 0) :=
        sum_congr rfl fun _ _ => sum_comm
    _ = ∑ x, ∑ i, ∑ t, F i t * (if Fin.castLE hN x = i then Rr x t else 0) := sum_comm
    _ = _ := by
        refine sum_congr rfl fun x _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun t _ => ?_
        simp [mul_ite]

lemma linexp (v a : Fin n → ZMod 2) (G : Fin u → Fin n → ZMod 2) (c : Fin u → ZMod 2) :
    ∑ t, v t * (a t + ∑ i, c i * G i t) = ∑ t, v t * a t + ∑ i, c i * ∑ t, G i t * v t := by
  simp only [mul_add, sum_add_distrib]
  congr 1
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

/-- The part of `dotP` coming from `C`. It depends neither on `f` nor on the seeds. -/
def constK (hN : N ≤ n) (w : Pos n → ZMod 2) : ZMod 2 :=
  ∑ i, ∑ j, w (2, i, j) *
    ∑ x : Fin N, if Fin.castLE hN x = i ∧ Fin.castLE hN x = j then 1 else 0

/-- Row `x` of the query vector on `A`. -/
def rv (hN : N ≤ n) (w : Pos n → ZMod 2) (x : Fin N) : Fin n → ZMod 2 :=
  fun t => w (0, Fin.castLE hN x, t)

/-- Column `y` of the query vector on `B`. -/
def cv (hN : N ≤ n) (w : Pos n → ZMod 2) (y : Fin N) : Fin n → ZMod 2 :=
  fun t => w (1, t, Fin.castLE hN y)

lemma dotP_inst (g : Gadget n u d N) (hN : N ≤ n) (w : Pos n → ZMod 2) (f : Fin N → Fin N)
    (s : Sd N u) :
    dotP w (inst g hN f s) =
      ∑ x, (∑ t, rv hN w x t * g.a (f x) t + ∑ i, s.1 x i * ∑ t, g.G i t * rv hN w x t) +
      ∑ y, (∑ t, cv hN w y t * g.b (f y) t + ∑ j, s.2 y j * ∑ t, g.H j t * cv hN w y t) +
      constK hN w := by
  have h0 : (0 : Fin 3) = 0 := rfl
  have h1 : ((1 : Fin 3) = 0) = False := by simp
  have h2 : ((2 : Fin 3) = 0) = False := by simp
  have h3 : ((2 : Fin 3) = 1) = False := by simp
  simp only [dotP, Fintype.sum_prod_type, Fin.sum_univ_three, Input.entry]
  simp only [↓reduceIte, h1, h2, h3]
  have hA : ∑ i, ∑ t, w (0, i, t) * (inst g hN f s).A i t =
      ∑ x, ∑ t, rv hN w x t * rowA g f s.1 x t :=
    sum_emb hN (fun i t => w (0, i, t)) (fun x t => rowA g f s.1 x t)
  have hB : ∑ t, ∑ j, w (1, t, j) * (inst g hN f s).B t j =
      ∑ y, ∑ t, cv hN w y t * colB g f s.2 y t := by
    rw [sum_comm]
    exact sum_emb hN (fun j t => w (1, t, j)) (fun y t => colB g f s.2 y t)
  rw [hA, hB]
  congr 1
  congr 1
  · exact sum_congr rfl fun x _ => linexp _ _ _ _
  · exact sum_congr rfl fun y _ => linexp _ _ _ _

/-! ### Terms vanish when a row or column of the query vector is light -/

/-- The sum over seeds of one character. -/
noncomputable def term (g : Gadget n u d N) (hN : N ≤ n) (w : Pos n → ZMod 2)
    (f : Fin N → Fin N) : ℝ :=
  ∑ s : Sd N u, sg (dotP w (inst g hN f s))

lemma dbl_delta (Γ : Fin N → Fin u → ZMod 2) (x₀ : Fin N) (i₀ : Fin u) :
    ∑ x, ∑ i, (if x = x₀ ∧ i = i₀ then (1 : ZMod 2) else 0) * Γ x i = Γ x₀ i₀ := by
  rw [Finset.sum_eq_single x₀, Finset.sum_eq_single i₀]
  · simp
  · intro i _ hi
    simp [hi]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

lemma term_zero_of_flip (g : Gadget n u d N) (hN : N ≤ n) (w : Pos n → ZMod 2) (f : Fin N → Fin N)
    (δ : Sd N u) (hδ : ∀ s, dotP w (inst g hN f (s + δ)) = dotP w (inst g hN f s) + 1) :
    term g hN w f = 0 := by
  have h1 : term g hN w f = ∑ s : Sd N u, sg (dotP w (inst g hN f (s + δ))) :=
    (Equiv.sum_comp (Equiv.addRight δ) fun s => sg (dotP w (inst g hN f s))).symm
  have h2 : ∑ s : Sd N u, sg (dotP w (inst g hN f (s + δ))) = - term g hN w f := by
    unfold term
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun s _ => ?_
    rw [hδ, sg_add, sg_one]
    ring
  linarith

lemma term_zero_row (g : Gadget n u d N) (hN : N ≤ n) (w : Pos n → ZMod 2) (f : Fin N → Fin N)
    (x₀ : Fin N) (h0 : rv hN w x₀ ≠ 0) (hw : wt (rv hN w x₀) < d) : term g hN w f = 0 := by
  obtain ⟨i₀, hi⟩ := g.Gd _ h0 hw
  refine term_zero_of_flip g hN w f (fun x i => if x = x₀ ∧ i = i₀ then 1 else 0, 0) ?_
  intro s
  simp only [dotP_inst, Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.zero_apply,
    add_zero, add_mul, sum_add_distrib]
  rw [dbl_delta (fun x i => ∑ t, g.G i t * rv hN w x t) x₀ i₀, zmod2_ne_zero hi]
  ring

lemma term_zero_col (g : Gadget n u d N) (hN : N ≤ n) (w : Pos n → ZMod 2) (f : Fin N → Fin N)
    (y₀ : Fin N) (h0 : cv hN w y₀ ≠ 0) (hw : wt (cv hN w y₀) < d) : term g hN w f = 0 := by
  obtain ⟨j₀, hj⟩ := g.Hd _ h0 hw
  refine term_zero_of_flip g hN w f (0, fun x i => if x = y₀ ∧ i = j₀ then 1 else 0) ?_
  intro s
  simp only [dotP_inst, Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.zero_apply,
    add_zero, add_mul, sum_add_distrib]
  rw [dbl_delta (fun y j => ∑ t, g.H j t * cv hN w y t) y₀ j₀, zmod2_ne_zero hj]
  ring

/-! ### Dependence on `f` -/

lemma term_congr (g : Gadget n u d N) (hN : N ≤ n) (w : Pos n → ZMod 2) (f f' : Fin N → Fin N)
    (h : ∀ x, (rv hN w x ≠ 0 ∨ cv hN w x ≠ 0) → f x = f' x) :
    term g hN w f = term g hN w f' := by
  refine sum_congr rfl fun s _ => ?_
  rw [dotP_inst, dotP_inst]
  congr 3
  · refine sum_congr rfl fun x _ => ?_
    congr 1
    by_cases h0 : rv hN w x = 0
    · simp [h0]
    · rw [h x (Or.inl h0)]
  · refine sum_congr rfl fun y _ => ?_
    congr 1
    by_cases h0 : cv hN w y = 0
    · simp [h0]
    · rw [h y (Or.inr h0)]

/-! ### Few heavy indices -/

lemma card_heavy (hN : N ≤ n) (w : Pos n → ZMod 2) (I : Finset (Fin N))
    (hI : ∀ x ∈ I, d ≤ wt (rv hN w x) ∨ d ≤ wt (cv hN w x)) :
    I.card * d ≤ (univ.filter fun p => w p ≠ 0).card := by
  classical
  let pr : Pos n → Fin n := fun p => if p.1 = 0 then p.2.1 else p.2.2
  let F : Fin N → Finset (Pos n) := fun x =>
    (univ.filter fun p => w p ≠ 0).filter fun p => pr p = Fin.castLE hN x
  have hF : ∀ x ∈ I, d ≤ (F x).card := by
    intro x hx
    rcases hI x hx with h | h
    · refine h.trans ?_
      apply card_le_card_of_injOn (fun t => ((0 : Fin 3), Fin.castLE hN x, t))
      · intro t ht
        have ht' : rv hN w x t ≠ 0 := (mem_filter.1 ht).2
        simp only [F, pr, coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq]
        exact ⟨ht', by simp⟩
      · intro t _ t' _ heq
        simpa using heq
    · refine h.trans ?_
      apply card_le_card_of_injOn (fun t => ((1 : Fin 3), t, Fin.castLE hN x))
      · intro t ht
        have ht' : cv hN w x t ≠ 0 := (mem_filter.1 ht).2
        simp only [F, pr, coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq]
        exact ⟨ht', by simp⟩
      · intro t _ t' _ heq
        simpa using heq
  have hdisj : (I : Set (Fin N)).PairwiseDisjoint F := by
    intro x _ y _ hxy
    apply disjoint_left.2
    intro p hpx hpy
    have h1 := (mem_filter.1 hpx).2
    have h2 := (mem_filter.1 hpy).2
    exact hxy ((castLE_eq_iff hN x y).1 (h1.symm.trans h2))
  calc I.card * d = ∑ _x ∈ I, d := by rw [sum_const, smul_eq_mul]
    _ ≤ ∑ x ∈ I, (F x).card := sum_le_sum hF
    _ = (I.biUnion F).card := (card_biUnion hdisj).symm
    _ ≤ _ := card_le_card (biUnion_subset.2 fun x _ => filter_subset _ _)

/-! ### The junta sum -/

/-- The acceptance probability averaged over the seeds. -/
noncomputable def avgAccept (g : Gadget n u d N) (hN : N ≤ n) (q : QAlg n T S)
    (f : Fin N → Fin N) : ℝ :=
  (∑ s : Sd N u, q.accept (inst g hN f s)) / Fintype.card (Sd N u)

theorem avgAccept_junta (g : Gadget n u d N) (hN : N ≤ n) (hd : 0 < d) (q : QAlg n T S) :
    IsJuntaSum N (2 * T / d) (avgAccept g hN q) := by
  classical
  obtain ⟨ι, _, c, w, hw, hacc⟩ := q.exists_accept_expansion
  let light : ι → Prop := fun k =>
    (∃ x, rv hN (w k) x ≠ 0 ∧ wt (rv hN (w k) x) < d) ∨
      (∃ y, cv hN (w k) y ≠ 0 ∧ wt (cv hN (w k) y) < d)
  let I : ι → Finset (Fin N) := fun k =>
    if light k then ∅ else univ.filter fun x => rv hN (w k) x ≠ 0 ∨ cv hN (w k) x ≠ 0
  refine ⟨ι, inferInstance, I,
    fun k f => c k * term g hN (w k) f / Fintype.card (Sd N u), ?_, ?_⟩
  · intro k
    by_cases hl : light k
    · have hzero : ∀ f, term g hN (w k) f = 0 := by
        intro f
        rcases hl with ⟨x, h0, h1⟩ | ⟨y, h0, h1⟩
        · exact term_zero_row g hN _ f x h0 h1
        · exact term_zero_col g hN _ f y h0 h1
      constructor
      · simp [I, hl]
      · intro f f' _
        dsimp only
        rw [hzero f, hzero f']
    · have hIk : I k = univ.filter fun x => rv hN (w k) x ≠ 0 ∨ cv hN (w k) x ≠ 0 := by
        simp only [I, hl, ↓reduceIte]
      constructor
      · rw [Nat.le_div_iff_mul_le hd]
        refine le_trans (card_heavy hN (w k) (I k) ?_) (hw k)
        intro x hx
        rw [hIk] at hx
        rcases (mem_filter.1 hx).2 with h0 | h0
        · left
          by_contra hlt
          exact hl (Or.inl ⟨x, h0, not_le.1 hlt⟩)
        · right
          by_contra hlt
          exact hl (Or.inr ⟨x, h0, not_le.1 hlt⟩)
      · intro f f' hff
        dsimp only
        rw [term_congr g hN (w k) f f' fun x hx => hff x (by
          rw [hIk]
          exact mem_filter.2 ⟨mem_univ _, hx⟩)]
  · intro f
    unfold avgAccept term
    simp only [hacc, ← sum_div, mul_sum]
    rw [sum_comm]

/-! ### Conclusion -/

theorem avgAccept_bounds (g : Gadget n u d N) (hN : N ≤ n) (q : QAlg n T S) (hq : q.Decides)
    (f : Fin N → Fin N) :
    (0 ≤ avgAccept g hN q f ∧ avgAccept g hN q f ≤ 1) ∧
      (Function.Injective f → 2 / 3 ≤ avgAccept g hN q f) ∧
      (¬ Function.Injective f → avgAccept g hN q f ≤ 1 / 3) := by
  have hpos : (0 : ℝ) < Fintype.card (Sd N u) := by
    exact_mod_cast Fintype.card_pos
  have hcard : ∑ _s : Sd N u, (1 : ℝ) = Fintype.card (Sd N u) := by simp
  have key : ∀ (a b : ℝ), (∀ s : Sd N u, a ≤ q.accept (inst g hN f s) ∧
      q.accept (inst g hN f s) ≤ b) → a ≤ avgAccept g hN q f ∧ avgAccept g hN q f ≤ b := by
    intro a b h
    unfold avgAccept
    constructor
    · rw [le_div_iff₀ hpos]
      calc a * Fintype.card (Sd N u) = ∑ _s : Sd N u, a := by simp [mul_comm]
        _ ≤ _ := sum_le_sum fun s _ => (h s).1
    · rw [div_le_iff₀ hpos]
      calc _ ≤ ∑ _s : Sd N u, b := sum_le_sum fun s _ => (h s).2
        _ = _ := by simp [mul_comm]
  refine ⟨key 0 1 fun s => ⟨q.accept_nonneg _, q.accept_le_one _⟩, ?_, ?_⟩
  · intro hf
    exact (key (2 / 3) 1 fun s =>
      ⟨(hq _).1 ((inst_iff g hN f s).2 hf), q.accept_le_one _⟩).1
  · intro hf
    exact (key 0 (1 / 3) fun s =>
      ⟨q.accept_nonneg _, (hq _).2 fun h => hf ((inst_iff g hN f s).1 h)⟩).2

/-- **Main theorem.** Assuming the degree bound for element distinctness, deciding `A B = C` over
`ZMod 2` needs `Ω(n^{5/3})` queries. -/
theorem matverify_bound (hED : EDDegree) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n T : ℕ) (S : Type) [Fintype S] [DecidableEq S] (q : QAlg n T S),
      q.Decides → c * (n : ℝ) ^ ((5 : ℝ) / 3) ≤ T + 1 := by
  obtain ⟨c₀, hc₀, hdeg⟩ := hED
  refine ⟨min (c₀ / 2) 1 / 65536, by positivity, ?_⟩
  intro n T S _ _ q hq
  have hmin1 : min (c₀ / 2) 1 ≤ 1 := min_le_right _ _
  have hmin2 : min (c₀ / 2) 1 ≤ c₀ / 2 := min_le_left _ _
  have hminpos : 0 < min (c₀ / 2) 1 := by positivity
  by_cases hn : 256 ≤ n
  · obtain ⟨d, u, N, hd2, hnd, hdN, hNn, ⟨g⟩⟩ := exists_gadget n hn
    have hdpos : 0 < d := by omega
    have h1 := hdeg N (2 * T / d) (avgAccept g hNn q) (by omega)
      (avgAccept_junta g hNn hdpos q)
      (fun f => (avgAccept_bounds g hNn q hq f).1)
      (fun f hf => (avgAccept_bounds g hNn q hq f).2.1 hf)
      (fun f hf => (avgAccept_bounds g hNn q hq f).2.2 hf)
    have hnpos : (0 : ℝ) < n := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hdR : (n : ℝ) / 256 ≤ d := by
      rw [div_le_iff₀ (by norm_num)]
      have : (n : ℝ) ≤ 256 * d := by exact_mod_cast hnd
      linarith
    have hNR : (n : ℝ) / 256 ≤ N := hdR.trans (by exact_mod_cast hdN)
    have hfloor : ((2 * T / d : ℕ) : ℝ) * d ≤ 2 * T := by
      have := Nat.div_mul_le_self (2 * T) d
      exact_mod_cast this
    have hrp : (n : ℝ) ^ ((2 : ℝ) / 3) / 256 ≤ (N : ℝ) ^ ((2 : ℝ) / 3) := by
      have h2 : ((n : ℝ) / 256) ^ ((2 : ℝ) / 3) ≤ (N : ℝ) ^ ((2 : ℝ) / 3) :=
        Real.rpow_le_rpow (by positivity) hNR (by norm_num)
      have h3 : ((n : ℝ) / 256) ^ ((2 : ℝ) / 3) =
          (n : ℝ) ^ ((2 : ℝ) / 3) / (256 : ℝ) ^ ((2 : ℝ) / 3) :=
        Real.div_rpow hnpos.le (by norm_num) _
      have h4 : (256 : ℝ) ^ ((2 : ℝ) / 3) ≤ 256 := by
        calc (256 : ℝ) ^ ((2 : ℝ) / 3) ≤ (256 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 256 := Real.rpow_one _
      have h5 : (n : ℝ) ^ ((2 : ℝ) / 3) / 256 ≤
          (n : ℝ) ^ ((2 : ℝ) / 3) / (256 : ℝ) ^ ((2 : ℝ) / 3) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) h4
      linarith
    have hsplit : (n : ℝ) ^ ((5 : ℝ) / 3) = (n : ℝ) * (n : ℝ) ^ ((2 : ℝ) / 3) := by
      rw [show (5 : ℝ) / 3 = 1 + 2 / 3 by norm_num, Real.rpow_add hnpos, Real.rpow_one]
    have hP : 0 ≤ (n : ℝ) ^ ((2 : ℝ) / 3) := by positivity
    have hmain : c₀ * ((n : ℝ) ^ ((2 : ℝ) / 3) / 256) * ((n : ℝ) / 256) ≤ 2 * T := by
      calc c₀ * ((n : ℝ) ^ ((2 : ℝ) / 3) / 256) * ((n : ℝ) / 256)
          ≤ c₀ * (N : ℝ) ^ ((2 : ℝ) / 3) * d := by
            apply mul_le_mul _ hdR (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left hrp hc₀.le
        _ ≤ ((2 * T / d : ℕ) : ℝ) * d :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ 2 * T := hfloor
    rw [hsplit]
    have hprod : 0 ≤ (n : ℝ) * (n : ℝ) ^ ((2 : ℝ) / 3) := by positivity
    have hT : (0 : ℝ) ≤ T := by positivity
    have h6 : min (c₀ / 2) 1 / 65536 * ((n : ℝ) * (n : ℝ) ^ ((2 : ℝ) / 3)) ≤
        c₀ / 2 / 65536 * ((n : ℝ) * (n : ℝ) ^ ((2 : ℝ) / 3)) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hmin2 (by norm_num)) hprod
    have h7 : c₀ / 2 / 65536 * ((n : ℝ) * (n : ℝ) ^ ((2 : ℝ) / 3)) ≤ T := by
      have : c₀ / 2 / 65536 * ((n : ℝ) * (n : ℝ) ^ ((2 : ℝ) / 3)) =
          (c₀ * ((n : ℝ) ^ ((2 : ℝ) / 3) / 256) * ((n : ℝ) / 256)) / 2 := by ring
      rw [this]
      linarith
    linarith
  · have hnlt : (n : ℝ) ≤ 256 := by
      have : n ≤ 256 := by omega
      exact_mod_cast this
    have h1 : (n : ℝ) ^ ((5 : ℝ) / 3) ≤ 65536 := by
      calc (n : ℝ) ^ ((5 : ℝ) / 3) ≤ (256 : ℝ) ^ ((5 : ℝ) / 3) :=
            Real.rpow_le_rpow (by positivity) hnlt (by norm_num)
        _ ≤ (256 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 65536 := by norm_num
    have hrp0 : 0 ≤ (n : ℝ) ^ ((5 : ℝ) / 3) := by positivity
    have hT : (0 : ℝ) ≤ T := by positivity
    calc min (c₀ / 2) 1 / 65536 * (n : ℝ) ^ ((5 : ℝ) / 3)
        ≤ 1 / 65536 * (n : ℝ) ^ ((5 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hmin1 (by norm_num)) hrp0
      _ ≤ 1 / 65536 * 65536 := mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ ≤ T + 1 := by
          have h2 : (1 : ℝ) / 65536 * 65536 = 1 := by norm_num
          linarith

end MatVerify
