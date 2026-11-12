import MinCutArray.Model

/-!
# The graph family

The vertices are four classes `A`, `B`, `D`, `C` of `t` vertices each. Each class is a clique of weight `τ`. For each
cell `(i, j)` of `ZMod t × ZMod t`, one bit selects one of the two perfect matchings of the 4-cycle
`A_i, B_{i+j}, D_i, C_j`, with weight `1`. No pair of vertices occurs in two 4-cycles, so the graph is simple for
`τ = 1`, and all degrees are fixed. Bit `1` puts both edges across the cut `{A, C} | {B, D}`, so that cut has weight
`2|x|`, and it is a minimum cut when `|x|` is small.
-/

open Finset

namespace MinCutArray

/-- The four classes. -/
inductive Cls
  | A | B | D | C
  deriving DecidableEq

instance : Fintype Cls := ⟨{.A, .B, .D, .C}, by intro c; cases c <;> simp⟩

theorem Cls.sum_univ {β : Type} [AddCommMonoid β] (f : Cls → β) :
    ∑ c, f c = f .A + (f .B + (f .D + f .C)) := by
  have h : (univ : Finset Cls) = {Cls.A, Cls.B, Cls.D, Cls.C} := rfl
  rw [h]
  simp [sum_insert]

variable {t : ℕ} [NeZero t]

/-- The vertices. -/
abbrev Vx (t : ℕ) := Cls × ZMod t

/-- The input bits. -/
abbrev Cell (t : ℕ) := ZMod t × ZMod t

/-- The weight of an edge present exactly when the bit is `1`. -/
def ind (b : Bool) : ℕ := cond b 1 0

/-- The weight of an edge present exactly when the bit is `0`. -/
def nind (b : Bool) : ℕ := cond b 0 1

/-- The weights between different classes. -/
def cross (x : Cell t → Bool) : Cls → Cls → ZMod t → ZMod t → ℕ
  | .A, .B, i, l => ind (x (i, l - i))
  | .B, .A, l, i => ind (x (i, l - i))
  | .A, .C, i, j => nind (x (i, j))
  | .C, .A, j, i => nind (x (i, j))
  | .B, .D, l, i => nind (x (i, l - i))
  | .D, .B, i, l => nind (x (i, l - i))
  | .D, .C, i, j => ind (x (i, j))
  | .C, .D, j, i => ind (x (i, j))
  | _, _, _, _ => 0

/-- The graph of an input. -/
def graph (τ : ℕ) (x : Cell t → Bool) : WGraph (Vx t) where
  w u v := if u.1 = v.1 then (if u.2 = v.2 then 0 else τ) else cross x u.1 v.1 u.2 v.2
  symm := by
    rintro ⟨c, i⟩ ⟨c', j⟩
    cases c <;> cases c' <;> simp [cross, eq_comm]
  loopless := by
    rintro ⟨c, i⟩
    simp

/-- The Hamming weight of an input. -/
def wtX (x : Cell t → Bool) : ℕ := ∑ e, ind (x e)

/-- The number of zero bits of an input. -/
def wtY (x : Cell t → Bool) : ℕ := ∑ e, nind (x e)

theorem wtX_add_wtY (x : Cell t → Bool) : wtX x + wtY x = t * t := by
  unfold wtX wtY
  rw [← sum_add_distrib]
  have h : ∀ e, ind (x e) + nind (x e) = 1 := by
    intro e
    cases x e <;> rfl
  simp [h, ZMod.card]

theorem ind_pos {b : Bool} (h : 0 < ind b) : b = true := by
  cases b
  · simp [ind] at h
  · rfl

theorem nind_pos {b : Bool} (h : 0 < nind b) : b = false := by
  cases b
  · rfl
  · simp [nind] at h

/-- The total weight between two classes. -/
def mass (x : Cell t → Bool) (c c' : Cls) : ℕ := ∑ i, ∑ j, cross x c c' i j

theorem sum_shift (f : Cell t → ℕ) : ∑ i : ZMod t, ∑ l : ZMod t, f (i, l - i) = ∑ e, f e := by
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ => ?_
  exact (Equiv.subRight i).sum_comp fun j => f (i, j)

theorem mass_ab (x : Cell t → Bool) : mass x .A .B = wtX x := sum_shift fun e => ind (x e)

theorem mass_ba (x : Cell t → Bool) : mass x .B .A = wtX x := by
  unfold mass
  rw [sum_comm]
  exact sum_shift fun e => ind (x e)

theorem mass_db (x : Cell t → Bool) : mass x .D .B = wtY x := sum_shift fun e => nind (x e)

theorem mass_bd (x : Cell t → Bool) : mass x .B .D = wtY x := by
  unfold mass
  rw [sum_comm]
  exact sum_shift fun e => nind (x e)

theorem mass_ac (x : Cell t → Bool) : mass x .A .C = wtY x := by
  unfold mass wtY
  rw [Fintype.sum_prod_type]
  rfl

theorem mass_ca (x : Cell t → Bool) : mass x .C .A = wtY x := by
  unfold mass wtY
  rw [sum_comm, Fintype.sum_prod_type]
  rfl

theorem mass_dc (x : Cell t → Bool) : mass x .D .C = wtX x := by
  unfold mass wtX
  rw [Fintype.sum_prod_type]
  rfl

theorem mass_cd (x : Cell t → Bool) : mass x .C .D = wtX x := by
  unfold mass wtX
  rw [sum_comm, Fintype.sum_prod_type]
  rfl

theorem mass_ad (x : Cell t → Bool) : mass x .A .D = 0 := by simp [mass, cross]

theorem mass_da (x : Cell t → Bool) : mass x .D .A = 0 := by simp [mass, cross]

theorem mass_bc (x : Cell t → Bool) : mass x .B .C = 0 := by simp [mass, cross]

theorem mass_cb (x : Cell t → Bool) : mass x .C .B = 0 := by simp [mass, cross]

/-! ## Cuts -/

theorem cut_eq_ite (τ : ℕ) (x : Cell t → Bool) (X : Finset (Vx t)) :
    (graph τ x).cut X = ∑ u, ∑ v, if u ∈ X ∧ v ∉ X then (graph τ x).w u v else 0 := by
  unfold WGraph.cut
  have h1 : ∀ u, ∑ v ∈ Xᶜ, (graph τ x).w u v = ∑ v, if v ∉ X then (graph τ x).w u v else 0 := by
    intro u
    rw [← sum_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext v
    simp
  have h2 : ∑ u ∈ X, ∑ v ∈ Xᶜ, (graph τ x).w u v
      = ∑ u, if u ∈ X then ∑ v ∈ Xᶜ, (graph τ x).w u v else 0 := by
    rw [← sum_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext u
    simp
  rw [h2]
  refine sum_congr rfl fun u _ => ?_
  rw [h1]
  by_cases hu : u ∈ X <;> simp [hu]

/-- A cut that splits a class has weight at least `τ (t - 1)`. -/
theorem cut_ge_split (τ : ℕ) (x : Cell t → Bool) (X : Finset (Vx t)) (c : Cls) (i j : ZMod t)
    (hi : (c, i) ∈ X) (hj : (c, j) ∉ X) : τ * (t - 1) ≤ (graph τ x).cut X := by
  classical
  let e : ZMod t ↪ Vx t := ⟨fun a => (c, a), fun a b h => (Prod.ext_iff.1 h).2⟩
  let A : Finset (ZMod t) := univ.filter fun a => (c, a) ∈ X
  have hsub : A.map e ⊆ X := by
    intro u hu
    obtain ⟨a, ha, rfl⟩ := mem_map.1 hu
    exact (mem_filter.1 ha).2
  have hsub' : Aᶜ.map e ⊆ Xᶜ := by
    intro u hu
    obtain ⟨a, ha, rfl⟩ := mem_map.1 hu
    rw [mem_compl] at ha ⊢
    intro hX
    exact ha (mem_filter.2 ⟨mem_univ _, hX⟩)
  have hw : ∀ a ∈ A, ∀ b ∈ Aᶜ, (graph τ x).w (e a) (e b) = τ := by
    intro a ha b hb
    have hne : a ≠ b := by
      rintro rfl
      exact (mem_compl.1 hb) ha
    show (graph τ x).w (c, a) (c, b) = τ
    simp [graph, hne]
  have hs : 1 ≤ A.card := card_pos.2 ⟨i, mem_filter.2 ⟨mem_univ _, hi⟩⟩
  have hs' : 1 ≤ Aᶜ.card := card_pos.2 ⟨j, mem_compl.2 fun h => hj (mem_filter.1 h).2⟩
  have hsum : A.card + Aᶜ.card = t := by
    rw [card_add_card_compl, ZMod.card]
  have hnum : t - 1 ≤ A.card * Aᶜ.card := by
    obtain ⟨p, hp⟩ := Nat.exists_eq_add_of_le hs
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hs'
    rw [hp, hr] at hsum ⊢
    have : t - 1 = p + r + 1 := by omega
    rw [this]
    nlinarith [Nat.zero_le (p * r)]
  calc τ * (t - 1) ≤ τ * (A.card * Aᶜ.card) := Nat.mul_le_mul_left _ hnum
    _ = ∑ a ∈ A, ∑ b ∈ Aᶜ, (graph τ x).w (e a) (e b) := by
      rw [sum_congr rfl fun a ha => sum_congr rfl fun b hb => hw a ha b hb]
      simp [mul_comm, mul_left_comm]
    _ = ∑ u ∈ A.map e, ∑ v ∈ Aᶜ.map e, (graph τ x).w u v := by
      simp only [sum_map]
    _ ≤ ∑ u ∈ A.map e, ∑ v ∈ Xᶜ, (graph τ x).w u v :=
      sum_le_sum fun u _ => sum_le_sum_of_subset hsub'
    _ ≤ (graph τ x).cut X := sum_le_sum_of_subset hsub

/-- The weight of a cut that contains or avoids each class. -/
theorem cut_union (τ : ℕ) (x : Cell t → Bool) (X : Finset (Vx t)) (S : Cls → Bool)
    (hX : ∀ c i, (c, i) ∈ X ↔ S c = true) :
    (graph τ x).cut X = ∑ c, ∑ c', if S c = true ∧ S c' = false then mass x c c' else 0 := by
  have key : ∀ c i c' j, (if (c, i) ∈ X ∧ (c', j) ∉ X then (graph τ x).w (c, i) (c', j) else 0)
      = if S c = true ∧ S c' = false then cross x c c' i j else 0 := by
    intro c i c' j
    by_cases h : S c = true ∧ S c' = false
    · have hc : c ≠ c' := by
        rintro rfl
        simp [h.1] at h
      simp [graph, hX, h, hc]
    · have h' : ¬ ((c, i) ∈ X ∧ (c', j) ∉ X) := by
        rw [hX, hX]
        simpa using h
      simp [h, h']
  rw [cut_eq_ite]
  simp only [Fintype.sum_prod_type, key]
  refine sum_congr rfl fun c _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun c' _ => ?_
  by_cases h : S c = true ∧ S c' = false
  · simp [h, mass]
  · simp [h]

/-- For few one bits, the weight of a minimum cut is `2|x|`. -/
theorem isMinCut (τ : ℕ) (x : Cell t → Bool) (h1 : 2 * wtX x ≤ τ * (t - 1)) (h2 : 2 * wtX x ≤ t * t) :
    (graph τ x).IsMinCut (2 * wtX x) := by
  classical
  have hsum := wtX_add_wtY x
  refine ⟨⟨univ.filter fun v => v.1 = .A ∨ v.1 = .C, ⟨(.A, 0), by simp⟩, ⟨(.B, 0), by simp⟩, ?_⟩, ?_⟩
  · rw [cut_union τ x _ (fun c => decide (c = .A ∨ c = .C)) (by intro c i; simp)]
    simp [Cls.sum_univ, mass_ab, mass_ad, mass_cb, mass_cd]
    omega
  · intro X hX hX'
    by_cases hsplit : ∃ c i j, (c, i) ∈ X ∧ (c, j) ∉ X
    · obtain ⟨c, i, j, hi, hj⟩ := hsplit
      exact h1.trans (cut_ge_split τ x X c i j hi hj)
    · push Not at hsplit
      let S : Cls → Bool := fun c => decide ((c, (0 : ZMod t)) ∈ X)
      have hS : ∀ c i, (c, i) ∈ X ↔ S c = true := by
        intro c i
        simp only [S, decide_eq_true_eq]
        exact ⟨fun h => hsplit c i 0 h, fun h => hsplit c 0 i h⟩
      obtain ⟨⟨c₁, i₁⟩, hu⟩ := hX
      obtain ⟨⟨c₂, i₂⟩, hv⟩ := hX'
      have hT : S c₁ = true := (hS c₁ i₁).1 hu
      have hF : S c₂ = false := by
        have : ¬ S c₂ = true := fun h => (mem_compl.1 hv) ((hS c₂ i₂).2 h)
        simpa using this
      rw [cut_union τ x X S hS]
      simp only [Cls.sum_univ, mass_ab, mass_ba, mass_ac, mass_ca, mass_bd, mass_db, mass_dc, mass_cd,
        mass_ad, mass_da, mass_bc, mass_cb]
      generalize t * t = N at *
      generalize wtX x = W at *
      generalize wtY x = Y at *
      have hTF : (S .A = true ∨ S .B = true ∨ S .D = true ∨ S .C = true) ∧
          (S .A = false ∨ S .B = false ∨ S .D = false ∨ S .C = false) := by
        constructor
        · cases c₁ <;> simp [hT]
        · cases c₂ <;> simp [hF]
      generalize S .A = sa at *
      generalize S .B = sb at *
      generalize S .D = sd at *
      generalize S .C = sc at *
      cases sa <;> cases sb <;> cases sd <;> cases sc <;> simp at hTF ⊢ <;> omega

/-! ## The array -/

/-- The list positions of a vertex: the rest of its clique, and its 4-cycles. -/
abbrev Slot (t : ℕ) := {z : ZMod t // z ≠ 0} ⊕ ZMod t

/-- The neighbour and the weight in a list position. -/
def slot (τ : ℕ) (x : Cell t → Bool) : Vx t → Slot t → Vx t × ℕ
  | (c, i), .inl z => ((c, i + z.1), τ)
  | (.A, i), .inr j => (if x (i, j) then (.B, i + j) else (.C, j), 1)
  | (.B, l), .inr j => (if x (l - j, j) then (.A, l - j) else (.D, l - j), 1)
  | (.D, i), .inr j => (if x (i, j) then (.C, j) else (.B, i + j), 1)
  | (.C, j), .inr i => (if x (i, j) then (.D, i) else (.A, i), 1)

/-- A fixed numbering of the list positions. -/
noncomputable def slotEquiv (t : ℕ) [NeZero t] : Fin (Fintype.card (Slot t)) ≃ Slot t :=
  (Fintype.equivFin (Slot t)).symm

/-- The adjacency array of an input. -/
noncomputable def arr (τ : ℕ) (x : Cell t → Bool) : AdjArray (Vx t) where
  deg _ := Fintype.card (Slot t)
  nbr v i := if h : i < Fintype.card (Slot t) then some (slot τ x v (slotEquiv t ⟨i, h⟩)) else none

theorem slot_weight (τ : ℕ) (hτ : 1 ≤ τ) (x : Cell t → Bool) (v : Vx t) (p : Slot t) :
    (graph τ x).w v (slot τ x v p).1 = (slot τ x v p).2 ∧ 0 < (slot τ x v p).2 := by
  obtain ⟨c, i⟩ := v
  rcases p with z | j
  · have hz : i ≠ i + z.1 := by
      intro h
      exact z.2 (by simpa using h.symm)
    simp [slot, graph, hz]
    omega
  · cases c <;> simp only [slot] <;> split_ifs with hx <;> simp [graph, cross, ind, nind, hx]

omit [NeZero t] in
theorem slot_inj (τ : ℕ) (x : Cell t → Bool) (v : Vx t) (p p' : Slot t)
    (h : (slot τ x v p).1 = (slot τ x v p').1) : p = p' := by
  obtain ⟨c, i⟩ := v
  rcases p with z | j <;> rcases p' with z' | j'
  · have : z = z' := Subtype.ext (by simpa [slot] using h)
    rw [this]
  · exfalso
    cases c <;> simp only [slot] at h <;> split_ifs at h <;> simp at h
  · exfalso
    cases c <;> simp only [slot] at h <;> split_ifs at h <;> simp at h
  · congr 1
    cases c <;> simp only [slot] at h <;> split_ifs at h <;> simp_all

theorem slot_surj (τ : ℕ) (x : Cell t → Bool) (v u : Vx t) (h : 0 < (graph τ x).w v u) :
    ∃ p, (slot τ x v p).1 = u := by
  obtain ⟨c, i⟩ := v
  obtain ⟨c', j⟩ := u
  by_cases hc : c = c'
  · subst hc
    have hij : i ≠ j := by
      rintro rfl
      simp [graph] at h
    exact ⟨.inl ⟨j - i, sub_ne_zero.2 hij.symm⟩, by simp [slot]⟩
  · have hcr : 0 < cross x c c' i j := by simpa [graph, hc] using h
    cases c <;> cases c' <;> simp only [cross] at hcr <;>
      first
        | exact absurd rfl hc
        | exact absurd hcr (lt_irrefl 0)
        | skip
    · have hx : x (i, j - i) = true := ind_pos hcr
      exact ⟨.inr (j - i), by simp [slot, hx]⟩
    · have hx : x (i, j) = false := nind_pos hcr
      exact ⟨.inr j, by simp [slot, hx]⟩
    · have hx : x (j, i - j) = true := ind_pos hcr
      exact ⟨.inr (i - j), by simp [slot, hx]⟩
    · have hx : x (j, i - j) = false := nind_pos hcr
      exact ⟨.inr (i - j), by simp [slot, hx]⟩
    · have hx : x (i, j - i) = false := nind_pos hcr
      exact ⟨.inr (j - i), by simp [slot, hx]⟩
    · have hx : x (i, j) = true := ind_pos hcr
      exact ⟨.inr j, by simp [slot, hx]⟩
    · have hx : x (j, i) = false := nind_pos hcr
      exact ⟨.inr j, by simp [slot, hx]⟩
    · have hx : x (j, i) = true := ind_pos hcr
      exact ⟨.inr j, by simp [slot, hx]⟩

theorem arr_represents (τ : ℕ) (hτ : 1 ≤ τ) (x : Cell t → Bool) : (graph τ x).Represents (arr τ x) := by
  intro v
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i < Fintype.card (Slot t) := hi
    have hs := slot_weight τ hτ x v (slotEquiv t ⟨i, hi'⟩)
    refine ⟨(slot τ x v (slotEquiv t ⟨i, hi'⟩)).1, ?_, ?_⟩
    · simp only [arr, hi', ↓reduceDIte, hs.1]
    · rw [hs.1]
      exact hs.2
  · intro i hi
    have hi' : ¬ i < Fintype.card (Slot t) := Nat.not_lt.2 hi
    simp only [arr, hi', ↓reduceDIte]
  · intro i j u c d hi hj
    simp only [arr] at hi hj
    split_ifs at hi with h
    split_ifs at hj with h'
    have h1 := congrArg Prod.fst (Option.some.inj hi)
    have h2 := congrArg Prod.fst (Option.some.inj hj)
    have := slot_inj τ x v _ _ (h1.trans h2.symm)
    exact congrArg Fin.val ((slotEquiv t).injective this)
  · intro u hu
    obtain ⟨p, hp⟩ := slot_surj τ x v u hu
    have hlt := ((slotEquiv t).symm p).2
    refine ⟨((slotEquiv t).symm p).1, (slot τ x v p).2, ?_⟩
    simp only [arr, hlt, ↓reduceDIte, Fin.eta, Equiv.apply_symm_apply]
    exact congrArg some (Prod.ext hp rfl)

theorem graph_ratio (τ : ℕ) (hτ : 1 ≤ τ) (x : Cell t → Bool) : (graph τ x).RatioAtMost τ := by
  rintro ⟨c, i⟩ ⟨c', j⟩
  by_cases hc : c = c'
  · subst hc
    by_cases hij : i = j
    · simp [graph, hij]
    · simp [graph, hij, hτ]
  · have hb : ∀ b : Bool, ind b = 0 ∨ ind b = 1 := by intro b; cases b <;> simp [ind]
    have hb' : ∀ b : Bool, nind b = 0 ∨ nind b = 1 := by intro b; cases b <;> simp [nind]
    have hcr : cross x c c' i j = 0 ∨ cross x c c' i j = 1 := by
      cases c <;> cases c' <;> simp only [cross] <;>
        first
          | exact hb _
          | exact hb' _
          | simp
    simp only [graph, hc, Prod.fst, if_neg, not_false_eq_true]
    rcases hcr with h | h
    · exact Or.inl h
    · right
      omega

/-! ## Each query reads at most one bit -/

/-- The bit read by a 4-cycle position of a vertex. -/
def cellOf : Vx t → ZMod t → Cell t
  | (.A, i), j => (i, j)
  | (.B, l), j => (l - j, j)
  | (.D, i), j => (i, j)
  | (.C, j), i => (i, j)

/-- The bit read by a query, if any. -/
noncomputable def loc : QPos (Vx t) → Option (Cell t)
  | .inl _ => none
  | .inr (v, i) =>
    if h : i < Fintype.card (Slot t) then
      match slotEquiv t ⟨i, h⟩ with
      | .inl _ => none
      | .inr j => some (cellOf v j)
    else none

theorem slot_congr (τ : ℕ) (x y : Cell t → Bool) (v : Vx t) (j : ZMod t) (h : x (cellOf v j) = y (cellOf v j)) :
    slot τ x v (.inr j) = slot τ y v (.inr j) := by
  obtain ⟨c, i⟩ := v
  cases c <;> simp only [cellOf] at h <;> simp only [slot, h]

theorem slot_inl (τ : ℕ) (x y : Cell t → Bool) (v : Vx t) (z : {z : ZMod t // z ≠ 0}) :
    slot τ x v (.inl z) = slot τ y v (.inl z) := by
  obtain ⟨c, i⟩ := v
  cases c <;> rfl

theorem loc_spec (τ : ℕ) (p : QPos (Vx t)) (x y : Cell t → Bool)
    (h : ∀ e, loc p = some e → x e = y e) : (arr τ x).entry p = (arr τ y).entry p := by
  rcases p with v | ⟨v, i⟩
  · rfl
  · simp only [AdjArray.entry, arr]
    by_cases hi : i < Fintype.card (Slot t)
    · simp only [hi, ↓reduceDIte]
      rcases hp : slotEquiv t ⟨i, hi⟩ with z | j
      · rw [slot_inl τ x y v z]
      · rw [slot_congr τ x y v j]
        apply h
        simp only [loc, hi, ↓reduceDIte, hp]
    · simp only [hi, ↓reduceDIte]

end MinCutArray
