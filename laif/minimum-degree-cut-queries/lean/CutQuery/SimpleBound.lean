import CutQuery.Family

/-!
# The bound for simple graphs, by reduction from disjointness

Vertices are `Fin (4 + k)`: four hubs, joined in a clique, and `k` leaves. Leaf `i` is joined to hubs `0` and `1`,
to hub `2` if `x i` and to hub `3` if `y i`. Its degree is `2 + x i + y i`, and hubs have degree at least `3`, so the
minimum degree is `2` if and only if some leaf has `x i` and `y i` unset.

Two players simulate a query by sending the crossing counts of the edges at hubs `2` and `3`, in binary.
-/

open Finset

namespace CutQuery

section Bits

theorem sum_testBit (ℓ m : ℕ) :
    ∑ b ∈ range ℓ, (if m.testBit b then 2 ^ b else 0) = m % 2 ^ ℓ := by
  induction ℓ with
  | zero => simp [Nat.mod_one]
  | succ ℓ ih =>
    rw [sum_range_succ, ih, Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ ℓ) with h | h <;> simp [h]

end Bits

section Simulation

variable {n : ℕ} {X Y : Type*}

/-- The number written with `ℓ` bits from position `start` of a transcript. -/
def readNum (h : List Bool) (start ℓ : ℕ) : ℕ :=
  ∑ b ∈ range ℓ, if h.getD (start + b) false then 2 ^ b else 0

/-- The first `i` answers decoded from a transcript. -/
def decodeAns (alg : DetAlg n) (pub : Weights n) (ℓ : ℕ) (h : List Bool) : ℕ → List ℤ
  | 0 => []
  | i + 1 =>
    decodeAns alg pub ℓ h i ++ [cut pub (alg.query (decodeAns alg pub ℓ h i))
      + readNum h (2 * ℓ * i) ℓ + readNum h (2 * ℓ * i + ℓ) ℓ]

/-- The protocol: in round `i`, Alice sends the crossing count of her weights in `ℓ` bits, then Bob sends his. -/
def simProtocol (alg : DetAlg n) (pub : Weights n) (wa : X → Weights n) (wb : Y → Weights n) (ℓ T : ℕ)
    (out : ℤ → Bool) : Protocol X Y where
  aliceSpeaks h := decide (h.length % (2 * ℓ) < ℓ)
  alice h x := (cut (wa x) (alg.query (decodeAns alg pub ℓ h (h.length / (2 * ℓ))))).toNat.testBit
    (h.length % (2 * ℓ))
  bob h y := (cut (wb y) (alg.query (decodeAns alg pub ℓ h (h.length / (2 * ℓ))))).toNat.testBit
    (h.length % (2 * ℓ) - ℓ)
  output h := out (alg.output (decodeAns alg pub ℓ h T))

/-- The bit at position `p` of the honest transcript. -/
def trueBit (alg : DetAlg n) (A : Weights n) (ca cb : (Fin n → Bool) → ℕ) (ℓ p : ℕ) : Bool :=
  if p % (2 * ℓ) < ℓ then (ca (alg.query (alg.answers A (p / (2 * ℓ))))).testBit (p % (2 * ℓ))
  else (cb (alg.query (alg.answers A (p / (2 * ℓ))))).testBit (p % (2 * ℓ) - ℓ)

theorem pos_div {ℓ b : ℕ} (hb : b < 2 * ℓ) (i : ℕ) : (2 * ℓ * i + b) / (2 * ℓ) = i := by
  have hpos : 0 < 2 * ℓ := by omega
  rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt hb, add_zero]

theorem pos_mod {ℓ b : ℕ} (hb : b < 2 * ℓ) (i : ℕ) : (2 * ℓ * i + b) % (2 * ℓ) = b := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hb]

/-- A transcript agreeing with the honest bits up to round `i` decodes to the true answers. -/
theorem decodeAns_eq (alg : DetAlg n) (pub A : Weights n) (ca cb : (Fin n → Bool) → ℕ) (ℓ : ℕ)
    (hca : ∀ q, ca q < 2 ^ ℓ) (hcb : ∀ q, cb q < 2 ^ ℓ)
    (hA : ∀ q, cut A q = cut pub q + ca q + cb q) (h : List Bool) :
    ∀ i, (∀ q, q < 2 * ℓ * i → h.getD q false = trueBit alg A ca cb ℓ q) →
      decodeAns alg pub ℓ h i = alg.answers A i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hσ
    have hle : 2 * ℓ * i + 2 * ℓ = 2 * ℓ * (i + 1) := by ring
    have hi := ih fun q hq => hσ q (by omega)
    simp only [decodeAns, DetAlg.answers, hi]
    congr 2
    set Q := alg.query (alg.answers A i) with hQ
    have h1 : readNum h (2 * ℓ * i) ℓ = ca Q := by
      unfold readNum
      rw [← Nat.mod_eq_of_lt (hca Q), ← sum_testBit]
      refine sum_congr rfl fun b hb => ?_
      have hb' : b < ℓ := mem_range.mp hb
      have hb2 : b < 2 * ℓ := by omega
      rw [hσ _ (by omega)]
      simp only [trueBit, pos_div hb2, pos_mod hb2, hb', ↓reduceIte, hQ]
    have h2 : readNum h (2 * ℓ * i + ℓ) ℓ = cb Q := by
      unfold readNum
      rw [← Nat.mod_eq_of_lt (hcb Q), ← sum_testBit]
      refine sum_congr rfl fun b hb => ?_
      have hb' : b < ℓ := mem_range.mp hb
      have hb2 : ℓ + b < 2 * ℓ := by omega
      rw [add_assoc, hσ _ (by omega)]
      have hnot : ¬ ℓ + b < ℓ := by omega
      have hsub : ℓ + b - ℓ = b := by omega
      simp only [trueBit, pos_div hb2, pos_mod hb2, hnot, ↓reduceIte, hsub, hQ]
    rw [h1, h2, hA Q]

/-- The transcript of the protocol is the honest one. -/
theorem transcript_spec (alg : DetAlg n) (pub : Weights n) (wa : X → Weights n) (wb : Y → Weights n) (ℓ T : ℕ)
    (hwa : ∀ x q, 0 ≤ cut (wa x) q ∧ cut (wa x) q < 2 ^ ℓ)
    (hwb : ∀ y q, 0 ≤ cut (wb y) q ∧ cut (wb y) q < 2 ^ ℓ) (out : ℤ → Bool) (x : X) (y : Y) (p : ℕ) :
    ((simProtocol alg pub wa wb ℓ T out).transcript x y p).length = p ∧
      ∀ q, q < p → ((simProtocol alg pub wa wb ℓ T out).transcript x y p).getD q false
        = trueBit alg (pub + wa x + wb y) (fun Q => (cut (wa x) Q).toNat) (fun Q => (cut (wb y) Q).toNat) ℓ q := by
  have hca : ∀ Q, (cut (wa x) Q).toNat < 2 ^ ℓ := fun Q => by
    have h := hwa x Q
    have : (cut (wa x) Q).toNat < ((2 ^ ℓ : ℕ) : ℤ) := by
      push_cast
      omega
    exact_mod_cast this
  have hcb : ∀ Q, (cut (wb y) Q).toNat < 2 ^ ℓ := fun Q => by
    have h := hwb y Q
    have : (cut (wb y) Q).toNat < ((2 ^ ℓ : ℕ) : ℤ) := by
      push_cast
      omega
    exact_mod_cast this
  have hA : ∀ Q, cut (pub + wa x + wb y) Q
      = cut pub Q + ((cut (wa x) Q).toNat : ℤ) + ((cut (wb y) Q).toNat : ℤ) := fun Q => by
    rw [cut_add, cut_add, Int.toNat_of_nonneg (hwa x Q).1, Int.toNat_of_nonneg (hwb y Q).1]
  induction p with
  | zero => exact ⟨rfl, fun q hq => absurd hq (Nat.not_lt_zero q)⟩
  | succ p ih =>
    obtain ⟨hlen, hbits⟩ := ih
    set h := (simProtocol alg pub wa wb ℓ T out).transcript x y p with hh
    have hdec := decodeAns_eq alg pub (pub + wa x + wb y) _ _ ℓ hca hcb hA h (p / (2 * ℓ)) (fun q hq =>
      hbits q (lt_of_lt_of_le hq (Nat.mul_div_le p (2 * ℓ))))
    have hbit : (if (simProtocol alg pub wa wb ℓ T out).aliceSpeaks h
          then (simProtocol alg pub wa wb ℓ T out).alice h x
          else (simProtocol alg pub wa wb ℓ T out).bob h y)
        = trueBit alg (pub + wa x + wb y) (fun Q => (cut (wa x) Q).toNat)
          (fun Q => (cut (wb y) Q).toNat) ℓ p := by
      simp only [simProtocol, hlen, hdec, trueBit, decide_eq_true_eq]
    have hstep : (simProtocol alg pub wa wb ℓ T out).transcript x y (p + 1)
        = h ++ [trueBit alg (pub + wa x + wb y) (fun Q => (cut (wa x) Q).toNat)
          (fun Q => (cut (wb y) Q).toNat) ℓ p] := by
      rw [← hbit]
      rfl
    rw [hstep]
    refine ⟨by simp [hlen], fun q hq => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq' | rfl
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
      exact hbits q hq'
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen]
      simp

/-- The simulation: a protocol of `T * (2 * ℓ)` bits computes any function of the output of the algorithm. -/
theorem sim_output (alg : DetAlg n) (pub : Weights n) (wa : X → Weights n) (wb : Y → Weights n) (ℓ T : ℕ)
    (hwa : ∀ x q, 0 ≤ cut (wa x) q ∧ cut (wa x) q < 2 ^ ℓ)
    (hwb : ∀ y q, 0 ≤ cut (wb y) q ∧ cut (wb y) q < 2 ^ ℓ) (out : ℤ → Bool) (x : X) (y : Y) :
    (simProtocol alg pub wa wb ℓ T out).output
        ((simProtocol alg pub wa wb ℓ T out).transcript x y (T * (2 * ℓ)))
      = out (alg.run T (pub + wa x + wb y)) := by
  obtain ⟨-, hbits⟩ := transcript_spec alg pub wa wb ℓ T hwa hwb out x y (T * (2 * ℓ))
  have hca : ∀ Q, (cut (wa x) Q).toNat < 2 ^ ℓ := fun Q => by
    have h := hwa x Q
    have : (cut (wa x) Q).toNat < ((2 ^ ℓ : ℕ) : ℤ) := by
      push_cast
      omega
    exact_mod_cast this
  have hcb : ∀ Q, (cut (wb y) Q).toNat < 2 ^ ℓ := fun Q => by
    have h := hwb y Q
    have : (cut (wb y) Q).toNat < ((2 ^ ℓ : ℕ) : ℤ) := by
      push_cast
      omega
    exact_mod_cast this
  have hA : ∀ Q, cut (pub + wa x + wb y) Q
      = cut pub Q + ((cut (wa x) Q).toNat : ℤ) + ((cut (wb y) Q).toNat : ℤ) := fun Q => by
    rw [cut_add, cut_add, Int.toNat_of_nonneg (hwa x Q).1, Int.toNat_of_nonneg (hwb y Q).1]
  have hdec := decodeAns_eq alg pub (pub + wa x + wb y) _ _ ℓ hca hcb hA
    ((simProtocol alg pub wa wb ℓ T out).transcript x y (T * (2 * ℓ))) T
    (fun q hq => hbits q (by rw [mul_comm T]; exact hq))
  simp only [simProtocol, DetAlg.run] at hdec ⊢
  rw [hdec]

end Simulation

section SymmetricDegree

variable {n : ℕ}

/-- The weight of a pair of vertices in either order, and `0` on the diagonal. -/
def symmOf (A : Weights n) (u v : Fin n) : ℤ :=
  if h : u < v then A ⟨(u, v), h⟩ else if h' : v < u then A ⟨(v, u), h'⟩ else 0

theorem symmOf_of_lt (A : Weights n) {u v : Fin n} (h : u < v) : symmOf A u v = A ⟨(u, v), h⟩ := by
  simp only [symmOf, h, ↓reduceDIte]

theorem symmOf_of_gt (A : Weights n) {u v : Fin n} (h : v < u) : symmOf A u v = A ⟨(v, u), h⟩ := by
  have : ¬ u < v := not_lt_of_gt h
  simp only [symmOf, h, this, ↓reduceDIte]

theorem symmOf_self (A : Weights n) (v : Fin n) : symmOf A v v = 0 := by
  simp [symmOf]

theorem symmOf_comm (A : Weights n) {u v : Fin n} (h : u ≠ v) : symmOf A u v = symmOf A v u := by
  rcases lt_or_gt_of_ne h with h' | h'
  · rw [symmOf_of_lt A h', symmOf_of_gt A h']
  · rw [symmOf_of_gt A h', symmOf_of_lt A h']

theorem symmOf_nonneg (A : Weights n) (hA : ∀ e, 0 ≤ A e) (u v : Fin n) : 0 ≤ symmOf A u v := by
  unfold symmOf
  split_ifs
  · exact hA _
  · exact hA _
  · exact le_rfl

theorem degree_eq_sum_symmOf (A : Weights n) (v : Fin n) : degree A v = ∑ u, symmOf A u v := by
  have hA : A = fun e : Edge n => symmOf A e.1.1 e.1.2 := by
    funext e
    rw [symmOf_of_lt A e.2]
  conv_lhs => rw [hA]
  rw [degree_of_symm (symmOf A) (fun a b h => symmOf_comm A h) v, sum_erase univ (f := fun u => symmOf A u v) (symmOf_self A v)]

end SymmetricDegree

section Graph

variable {k : ℕ}

/-- The bit of leaf `m`, with value `false` out of range. -/
def leafBit (x : Fin k → Bool) (m : ℕ) : Bool := if h : m < k then x ⟨m, h⟩ else false

/-- The edges known to both players: the clique on the hubs and the edges from hubs `0` and `1` to the leaves. -/
def pubW : Weights (4 + k) := fun e => if e.1.2.val < 4 ∨ e.1.1.val < 2 then 1 else 0

/-- The edges from hub `c` to the leaves whose bit in `x` is set. -/
def spokeW (c : ℕ) (x : Fin k → Bool) : Weights (4 + k) := fun e =>
  if e.1.1.val = c ∧ 4 ≤ e.1.2.val then bitZ (leafBit x (e.1.2.val - 4)) else 0

/-- The graph of the reduction. -/
def graphW (x y : Fin k → Bool) : Weights (4 + k) := pubW + spokeW 2 x + spokeW 3 y

theorem bitZ_zero_or_one (β : Bool) : bitZ β = 0 ∨ bitZ β = 1 := by
  cases β <;> simp [bitZ]

theorem graphW_simple (x y : Fin k → Bool) : IsSimple (graphW x y) := by
  intro e
  have hlt : e.1.1.val < e.1.2.val := e.2
  simp only [graphW, Pi.add_apply, pubW, spokeW]
  have h1 := bitZ_zero_or_one (leafBit x (e.1.2.val - 4))
  have h2 := bitZ_zero_or_one (leafBit y (e.1.2.val - 4))
  generalize bitZ (leafBit x (e.1.2.val - 4)) = p at h1
  generalize bitZ (leafBit y (e.1.2.val - 4)) = q at h2
  split_ifs <;> omega

theorem graphW_nonneg (x y : Fin k → Bool) (e : Edge (4 + k)) : 0 ≤ graphW x y e := by
  rcases graphW_simple x y e with h | h <;> simp [h]

theorem leafBit_val (x : Fin k → Bool) (i : Fin k) : leafBit x i.val = x i := by
  simp [leafBit]

theorem hub_lt_leaf (c : Fin 4) (i : Fin k) : Fin.castAdd k c < Fin.natAdd 4 i := by
  rw [Fin.lt_def]
  simp only [Fin.val_castAdd, Fin.val_natAdd]
  omega

/-- The degree of a leaf. -/
theorem degree_leaf (x y : Fin k → Bool) (i : Fin k) :
    degree (graphW x y) (Fin.natAdd 4 i) = 2 + bitZ (x i) + bitZ (y i) := by
  rw [degree_eq_sum_symmOf, Fin.sum_univ_add, Fin.sum_univ_four, sum_eq_zero]
  · simp only [symmOf_of_lt _ (hub_lt_leaf _ i)]
    simp [graphW, pubW, spokeW, Fin.val_castAdd, Fin.val_natAdd, leafBit_val]
  · intro j _
    have hval : ∀ e : Edge (4 + k), 4 ≤ e.1.1.val → graphW x y e = 0 := by
      intro e he
      have hlt : e.1.1.val < e.1.2.val := e.2
      simp only [graphW, Pi.add_apply, pubW, spokeW]
      have h1 : ¬ (e.1.2.val < 4 ∨ e.1.1.val < 2) := by omega
      have h2 : ¬ (e.1.1.val = 2 ∧ 4 ≤ e.1.2.val) := by omega
      have h3 : ¬ (e.1.1.val = 3 ∧ 4 ≤ e.1.2.val) := by omega
      simp only [h1, h2, h3, ↓reduceIte, add_zero]
    unfold symmOf
    split_ifs with h1 h2
    · exact hval _ (by simp [Fin.val_natAdd])
    · exact hval _ (by simp [Fin.val_natAdd])
    · rfl

/-- A hub has degree at least `3`. -/
theorem degree_hub_ge (x y : Fin k → Bool) (c : Fin 4) :
    3 ≤ degree (graphW x y) (Fin.castAdd k c) := by
  rw [degree_eq_sum_symmOf, Fin.sum_univ_add]
  have h1 : 0 ≤ ∑ j : Fin k, symmOf (graphW x y) (Fin.natAdd 4 j) (Fin.castAdd k c) :=
    sum_nonneg fun j _ => symmOf_nonneg _ (graphW_nonneg x y) _ _
  have hval : ∀ e : Edge (4 + k), e.1.2.val < 4 → graphW x y e = 1 := by
    intro e he
    have hlt : e.1.1.val < e.1.2.val := e.2
    simp only [graphW, Pi.add_apply, pubW, spokeW]
    have h2 : e.1.2.val < 4 ∨ e.1.1.val < 2 := Or.inl he
    have h3 : ¬ (e.1.1.val = 2 ∧ 4 ≤ e.1.2.val) := by omega
    have h4 : ¬ (e.1.1.val = 3 ∧ 4 ≤ e.1.2.val) := by omega
    simp only [h2, h3, h4, ↓reduceIte, add_zero]
  have hne : ∀ c' : Fin 4, c' ≠ c →
      symmOf (graphW x y) (Fin.castAdd k c') (Fin.castAdd k c) = 1 := by
    intro c' hc'
    have hc1 : (c' : ℕ) < 4 := c'.2
    have hc2 : (c : ℕ) < 4 := c.2
    have hne' : (c' : ℕ) ≠ c := fun h => hc' (Fin.ext h)
    unfold symmOf
    split_ifs with h2 h3
    · apply hval
      simp
    · apply hval
      simp
    · exfalso
      rw [Fin.lt_def] at h2 h3
      simp only [Fin.val_castAdd] at h2 h3
      omega
  have hself := symmOf_self (graphW x y) (Fin.castAdd k c)
  have hsum : ∑ c' : Fin 4, symmOf (graphW x y) (Fin.castAdd k c') (Fin.castAdd k c) = 3 := by
    rw [← add_sum_erase _ _ (mem_univ c), hself, zero_add,
      sum_congr rfl fun c' hc' => hne c' (ne_of_mem_erase hc'), sum_const,
      card_erase_of_mem (mem_univ c)]
    simp
  rw [hsum]
  omega

theorem minDegree_graphW_eq_two_iff [NeZero (4 + k)] (x y : Fin k → Bool) :
    minDegree (graphW x y) = 2 ↔ ∃ i, x i = false ∧ y i = false := by
  have hbit : ∀ β : Bool, 0 ≤ bitZ β := bitZ_nonneg
  have hall : ∀ v : Fin (4 + k), 2 ≤ degree (graphW x y) v := by
    intro v
    induction v using Fin.addCases with
    | left c => exact le_trans (by norm_num) (degree_hub_ge x y c)
    | right i =>
      rw [degree_leaf]
      have := hbit (x i)
      have := hbit (y i)
      omega
  constructor
  · intro h
    obtain ⟨v, -, hv⟩ := exists_mem_eq_inf' (s := (univ : Finset (Fin (4 + k)))) ⟨0, mem_univ _⟩
      (degree (graphW x y))
    have hv' : degree (graphW x y) v = 2 := by
      rw [← hv]
      exact h
    induction v using Fin.addCases with
    | left c =>
      have := degree_hub_ge x y c
      omega
    | right i =>
      rw [degree_leaf] at hv'
      refine ⟨i, ?_, ?_⟩
      · have h1 := hbit (y i)
        have h2 := bitZ_zero_or_one (x i)
        cases hx : x i
        · rfl
        · rw [hx] at hv'
          simp only [bitZ, ↓reduceIte] at hv'
          omega
      · have h1 := hbit (x i)
        cases hy : y i
        · rfl
        · rw [hy] at hv'
          simp only [bitZ, ↓reduceIte] at hv'
          omega
  · rintro ⟨i, hx, hy⟩
    apply le_antisymm
    · refine (inf'_le _ (mem_univ (Fin.natAdd 4 i))).trans ?_
      rw [degree_leaf, hx, hy]
      simp [bitZ]
    · exact le_inf' _ _ fun v _ => hall v

/-- The crossing count of a spoke is a nonnegative number below `2 ^ ℓ` when `4 + k < 2 ^ ℓ`. -/
theorem cut_spokeW_bounds (c : ℕ) (x : Fin k → Bool) (Q : Fin (4 + k) → Bool) (ℓ : ℕ)
    (hℓ : 4 + k < 2 ^ ℓ) : 0 ≤ cut (spokeW c x) Q ∧ cut (spokeW c x) Q < 2 ^ ℓ := by
  have hcross : ∀ e : Edge (4 + k), 0 ≤ crosses Q e ∧ crosses Q e ≤ 1 := fun e => by
    unfold crosses
    split_ifs <;> simp
  have hspoke : ∀ e : Edge (4 + k), 0 ≤ spokeW c x e := fun e => by
    unfold spokeW
    split_ifs
    · exact bitZ_nonneg _
    · exact le_rfl
  have hterm : ∀ e : Edge (4 + k), spokeW c x e * crosses Q e ≤ if e.1.1.val = c then 1 else 0 := by
    intro e
    obtain ⟨h1, h2⟩ := hcross e
    unfold spokeW
    split_ifs with h3 h4 h5
    · have h6 := bitZ_zero_or_one (leafBit x (e.1.2.val - 4))
      rcases h6 with h6 | h6 <;> rw [h6] <;> omega
    · exact absurd h3.1 h4
    · simp
    · simp
  constructor
  · exact sum_nonneg fun e _ => mul_nonneg (hspoke e) (hcross e).1
  · have h1 : cut (spokeW c x) Q ≤ ((univ.filter fun e : Edge (4 + k) => e.1.1.val = c).card : ℤ) := by
      unfold cut
      refine (sum_le_sum fun e _ => hterm e).trans ?_
      rw [card_filter]
      push_cast
      exact le_rfl
    have h2 : (univ.filter fun e : Edge (4 + k) => e.1.1.val = c).card ≤ 4 + k := by
      have h3 : (univ.filter fun e : Edge (4 + k) => e.1.1.val = c).card
          ≤ (univ : Finset (Fin (4 + k))).card := by
        refine card_le_card_of_injOn (fun e => e.1.2) (fun _ _ => mem_coe.mpr (mem_univ _)) ?_
        intro e he e' he' h
        have h4 := (mem_filter.mp (mem_coe.mp he)).2
        have h5 := (mem_filter.mp (mem_coe.mp he')).2
        apply Subtype.ext
        apply Prod.ext
        · exact Fin.ext (h4.trans h5.symm)
        · exact h
      simpa using h3
    have h3 : (((univ.filter fun e : Edge (4 + k) => e.1.1.val = c).card : ℕ) : ℤ) < ((2 ^ ℓ : ℕ) : ℤ) := by
      exact_mod_cast lt_of_le_of_lt h2 hℓ
    push_cast at h3
    exact lt_of_le_of_lt h1 h3

/-- The reduction: a randomized algorithm for simple graphs gives a public-coin protocol for disjointness. -/
theorem disj_of_alg [NeZero (4 + k)] (c : ℝ)
    (hD : ∀ (k t : ℕ) (Ω : Type) [Fintype Ω] (p : Ω → ℝ) (π : Ω → Protocol (Fin k → Bool) (Fin k → Bool)),
      (∀ ω, 0 ≤ p ω) → ∑ ω, p ω = 1 →
      (∀ a b : Fin k → Bool,
        ∑ ω, (if (π ω).output ((π ω).transcript a b t) = disjoint a b then 0 else p ω) ≤ 1 / 3) →
      c * k ≤ t)
    (T ℓ : ℕ) (hℓ : 4 + k < 2 ^ ℓ) (Ω : Type) [Fintype Ω] (r : RandAlg (4 + k) Ω)
    (herr : ∀ A : Weights (4 + k), IsSimple A → r.err T A ≤ 1 / 3) :
    c * k ≤ ((T * (2 * ℓ) : ℕ) : ℝ) := by
  let wa : (Fin k → Bool) → Weights (4 + k) := fun a => spokeW 2 fun i => !a i
  let wb : (Fin k → Bool) → Weights (4 + k) := fun b => spokeW 3 fun i => !b i
  let out : ℤ → Bool := fun d => !decide (d = 2)
  let π : Ω → Protocol (Fin k → Bool) (Fin k → Bool) := fun ω =>
    simProtocol (r.alg ω) pubW wa wb ℓ T out
  refine hD k (T * (2 * ℓ)) Ω r.p π r.nonneg r.sum_one fun a b => ?_
  have hdisj : out (minDegree (graphW (fun i => !a i) fun i => !b i)) = disjoint a b := by
    have hiff := minDegree_graphW_eq_two_iff (fun i => !a i) (fun i => !b i)
    have hb : disjoint a b = !decide (minDegree (graphW (fun i => !a i) fun i => !b i) = 2) := by
      have h2 : (∀ i, ¬ (a i = true ∧ b i = true))
          ↔ ¬ (minDegree (graphW (fun i => !a i) fun i => !b i) = 2) := by
        rw [hiff]
        simp
      unfold disjoint
      by_cases h : minDegree (graphW (fun i => !a i) fun i => !b i) = 2
      · have h3 : ¬ ∀ i, ¬ (a i = true ∧ b i = true) := fun h4 => h2.mp h4 h
        simp only [h3, h, decide_true, decide_false, Bool.not_true]
      · have h3 : ∀ i, ¬ (a i = true ∧ b i = true) := h2.mpr h
        simp only [h3, h, decide_false, Bool.not_false]
        simp
    rw [hb]
  refine le_trans ?_ (herr _ (graphW_simple (fun i => !a i) fun i => !b i))
  refine sum_le_sum fun ω _ => ?_
  have hspec := sim_output (r.alg ω) pubW wa wb ℓ T
    (fun a Q => cut_spokeW_bounds 2 _ Q ℓ hℓ) (fun b Q => cut_spokeW_bounds 3 _ Q ℓ hℓ) out a b
  change (π ω).output ((π ω).transcript a b (T * (2 * ℓ)))
    = out ((r.alg ω).run T (graphW (fun i => !a i) fun i => !b i)) at hspec
  by_cases h : (r.alg ω).run T (graphW (fun i => !a i) fun i => !b i)
      = minDegree (graphW (fun i => !a i) fun i => !b i)
  · rw [hspec, h, hdisj]
    simp
  · simp only [h, ↓reduceIte]
    split_ifs
    · exact r.nonneg ω
    · exact le_rfl

end Graph

/-- The bound for simple graphs, assuming the lower bound for disjointness. -/
theorem simple_graph_bound (hD : DisjLowerBound) : ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) [NeZero n] (T : ℕ) (Ω : Type) [Fintype Ω] (r : RandAlg n Ω),
    (∀ A : Weights n, IsSimple A → r.err T A ≤ 1 / 3) → c * n ≤ (T + 1) * (Nat.log 2 n + 2) := by
  obtain ⟨c, hc, hDis⟩ := hD
  refine ⟨min (c / 4) (1 / 4), lt_min (by linarith) (by norm_num), ?_⟩
  intro n _ T Ω _ r herr
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hlog0 : (0 : ℝ) ≤ Nat.log 2 n := Nat.cast_nonneg _
  have hmin1 : min (c / 4) (1 / 4) ≤ 1 / 4 := min_le_right _ _
  have hmin2 : min (c / 4) (1 / 4) ≤ c / 4 := min_le_left _ _
  have hminpos : 0 < min (c / 4) (1 / 4) := lt_min (by linarith) (by norm_num)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hRHS : (T + 1 : ℝ) * (Nat.log 2 n + 2) = T * Nat.log 2 n + 2 * T + Nat.log 2 n + 2 := by ring
  have hprod : (0 : ℝ) ≤ T * Nat.log 2 n := mul_nonneg hT0 hlog0
  by_cases hn : n < 8
  · have hn8 : (n : ℝ) ≤ 8 := by exact_mod_cast hn.le
    have h1 : min (c / 4) (1 / 4) * n ≤ 1 / 4 * 8 :=
      mul_le_mul hmin1 hn8 hn0 (by norm_num)
    rw [hRHS]
    linarith
  · obtain ⟨k, rfl⟩ : ∃ k, n = 4 + k := ⟨n - 4, by omega⟩
    have hbound := disj_of_alg c (fun k t Ω _ p π h1 h2 h3 => hDis k t Ω p π h1 h2 h3) T
      (Nat.log 2 (4 + k) + 1) (Nat.lt_pow_succ_log_self (by norm_num) _) Ω r herr
    have hk : (((4 + k : ℕ) : ℝ)) ≤ 2 * k := by
      have : 4 + k ≤ 2 * k := by omega
      exact_mod_cast this
    push_cast at hbound hRHS hk hprod ⊢
    set m : ℝ := (Nat.log 2 (4 + k) : ℝ) with hm
    have h1 : min (c / 4) (1 / 4) * (4 + (k : ℝ)) ≤ c / 4 * (2 * k) :=
      mul_le_mul hmin2 hk (by positivity) (by positivity)
    rw [hRHS]
    nlinarith

end CutQuery
