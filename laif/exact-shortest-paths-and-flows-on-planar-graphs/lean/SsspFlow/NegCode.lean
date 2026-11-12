import SsspFlow.NegProb
import SsspFlow.NegBox
import SsspFlow.NetPasses

/-!
# Codes and local views

Integers and values in `ℕ∞` as natural numbers (`decZ_encZ`, `decE_encE`). Six digits in one radix
name the steps of a program (`dig_addr6`). A node rebuilds the inputs of the oracle and of the
decomposition from its own input and the values of its neighbours (`mkOra_eq`, `mkLdd_eq`), since the
lengths and offsets depend at an arc only on data at its ends (`altLen_congr`, `negRelax_congr`,
`lamS_congr`, `badAt_congr`, `finLen_congr`). One round of a relaxation gives every node the values of
its neighbours (`exch_one`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal
open Cslib.Congest Cslib.Congest.Algorithm

namespace SsspFlow.Congest

/-! ### Codes -/

/-- An integer as a natural number. -/
def encZ (z : ℤ) : ℕ := if 0 ≤ z then 2 * z.toNat else 2 * (-z).toNat - 1

/-- The integer of a code. -/
def decZ (k : ℕ) : ℤ := if k % 2 = 0 then ((k / 2 : ℕ) : ℤ) else -(((k + 1) / 2 : ℕ) : ℤ)

theorem decZ_encZ (z : ℤ) : decZ (encZ z) = z := by
  unfold encZ decZ
  split_ifs <;> omega

theorem encZ_le (z : ℤ) : encZ z ≤ 2 * z.natAbs := by
  unfold encZ
  split_ifs <;> omega

/-- A value in `ℕ∞` as a natural number, `0` for `⊤`. -/
def encE (x : ℕ∞) : ℕ := if x = ⊤ then 0 else x.toNat + 1

/-- The value of a code. -/
def decE (k : ℕ) : ℕ∞ := if k = 0 then ⊤ else ((k - 1 : ℕ) : ℕ∞)

theorem decE_encE (x : ℕ∞) : decE (encE x) = x := by
  unfold encE decE
  by_cases h : x = ⊤
  · rw [ite_eq_left h, ite_eq_left rfl, h]
  · rw [ite_eq_right h, ite_eq_right (Nat.succ_ne_zero _), Nat.add_sub_cancel, ENat.natCast_toNat h]

/-! ### Names of the steps -/

/-- One more digit. -/
@[irreducible] def mixZ (Z x e : ℕ) : ℕ := x * Z + e

theorem mixZ_div {Z x e : ℕ} (h : e < Z) : mixZ Z x e / Z = x := by
  unfold mixZ
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < Z), Nat.div_eq_of_lt h, Nat.zero_add]

theorem mixZ_mod {Z x e : ℕ} (h : e < Z) : mixZ Z x e % Z = e := by
  unfold mixZ
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h]

theorem mixZ_lt_left {Z x x' e e' : ℕ} (h : e < Z) (hx : x < x') : mixZ Z x e < mixZ Z x' e' := by
  unfold mixZ
  have : (x + 1) * Z ≤ x' * Z := Nat.mul_le_mul_right Z hx
  rw [Nat.succ_mul] at this
  omega

theorem mixZ_lt_right {Z x e e' : ℕ} (h : e < e') : mixZ Z x e < mixZ Z x e' := by
  unfold mixZ
  omega

/-- A number with six digits. -/
def addr6 (Z j a b c d e : ℕ) : ℕ := mixZ Z (mixZ Z (mixZ Z (mixZ Z (mixZ Z j a) b) c) d) e

/-- The six digits of a number. -/
def dig (Z s : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  (s / Z / Z / Z / Z / Z, s / Z / Z / Z / Z % Z, s / Z / Z / Z % Z, s / Z / Z % Z, s / Z % Z, s % Z)

theorem dig_addr6 {Z j a b c d e : ℕ} (ha : a < Z) (hb : b < Z) (hc : c < Z) (hd : d < Z)
    (he : e < Z) : dig Z (addr6 Z j a b c d e) = (j, a, b, c, d, e) := by
  unfold dig addr6
  simp only [mixZ_div he, mixZ_mod he, mixZ_div hd, mixZ_mod hd, mixZ_div hc, mixZ_mod hc,
    mixZ_div hb, mixZ_mod hb, mixZ_div ha, mixZ_mod ha]

/-! ### Congruence -/

section Congr

variable {V : Type}

theorem minR_congr {f g : ℕ → ℤ} : ∀ {R : ℕ}, (∀ q ≤ R, f q = g q) → minR f R = minR g R
  | 0, h => h 0 le_rfl
  | R + 1, h => by
    show min (minR f R) (f (R + 1)) = min (minR g R) (g (R + 1))
    rw [minR_congr fun q hq => h q (by omega), h (R + 1) le_rfl]

theorem ysc_congr {n B : ℕ} {w w' : V → V → Option ℤ} {φ φ' : V → ℤ} {a b : V}
    (hw : w a b = w' a b) (ha : φ a = φ' a) (hb : φ b = φ' b) :
    ysc n w φ B a b = ysc n w' φ' B a b := by
  simp only [ysc, yr, xw, zWt, hw, ha, hb]

theorem keptS_congr {adj adj' : V → V → Prop} {n B : ℕ} {w w' : V → V → Option ℤ} {φ φ' : V → ℤ}
    {a b : V} (hadj : adj a b ↔ adj' a b) (hw : w a b = w' a b) (ha : φ a = φ' a) (hb : φ b = φ' b) :
    keptS adj n w φ B a b ↔ keptS adj' n w' φ' B a b := by
  unfold keptS zArc
  rw [ysc_congr hw ha hb, hw, hadj]

theorem clArc_congr {L ℓ r : ℕ} {kept kept' : V → V → Prop} {idx idx' : ℕ → ℕ → V → ℕ} {a b : V}
    (hk : kept a b ↔ kept' a b) (ha : idx ℓ r a = idx' ℓ r a) (hb : idx ℓ r b = idx' ℓ r b) :
    clArc L kept idx ℓ r a b ↔ clArc L kept' idx' ℓ r a b := by
  unfold clArc
  rw [hk, ha, hb]

theorem posArc_congr {E E' : V → V → Prop} {y y' : V → V → ℤ} {φ φ' : V → ℤ} {a b : V}
    (hE : E a b ↔ E' a b) (hy : y a b = y' a b) (ha : φ a = φ' a) (hb : φ b = φ' b) :
    posArc E y φ a b ↔ posArc E' y' φ' a b := by
  unfold posArc yr
  rw [hE, hy, ha, hb]

theorem posLen_congr {y y' : V → V → ℤ} {φ φ' : V → ℤ} {a b : V} (hy : y a b = y' a b)
    (ha : φ a = φ' a) (hb : φ b = φ' b) : posLen y φ a b = posLen y' φ' a b := by
  unfold posLen yr
  rw [hy, ha, hb]

theorem restrictLen_congr {E E' : V → V → Prop} {len len' : V → V → ℕ} {a b : V}
    (hE : E a b ↔ E' a b) (hl : len a b = len' a b) :
    restrictLen E len a b = restrictLen E' len' a b := by
  unfold restrictLen
  by_cases h : E a b
  · rw [ite_eq_left h, ite_eq_left (hE.1 h), hl]
  · rw [ite_eq_right h, ite_eq_right (mt hE.2 h)]

/-- The lengths of the oracle in a step of Lemma 1, at a level and a repetition. -/
noncomputable def altLen (adj : V → V → Prop) (n L : ℕ) (w : V → V → Option ℤ) (φ : V → ℤ) (B : ℕ)
    (idx : ℕ → ℕ → V → ℕ) (ℓ r : ℕ) (φ' : V → ℤ) : V → V → ℕ∞ :=
  restrictLen (posArc (clArc L (keptS adj n w φ B) idx ℓ r) (ysc n w φ B) φ') (posLen (ysc n w φ B) φ')

theorem altLen_congr {adj adj' : V → V → Prop} {n L B ℓ r : ℕ} {w w' : V → V → Option ℤ}
    {φ φ₂ φ' φ'₂ : V → ℤ} {idx idx' : ℕ → ℕ → V → ℕ} {a b : V} (hadj : adj a b ↔ adj' a b)
    (hw : w a b = w' a b) (ha : φ a = φ₂ a) (hb : φ b = φ₂ b) (hia : idx ℓ r a = idx' ℓ r a)
    (hib : idx ℓ r b = idx' ℓ r b) (ha' : φ' a = φ'₂ a) (hb' : φ' b = φ'₂ b) :
    altLen adj n L w φ B idx ℓ r φ' a b = altLen adj' n L w' φ₂ B idx' ℓ r φ'₂ a b :=
  restrictLen_congr
    (posArc_congr (clArc_congr (keptS_congr hadj hw ha hb) hia hib) (ysc_congr hw ha hb) ha' hb')
    (posLen_congr (ysc_congr hw ha hb) ha' hb')

theorem negRelax_congr [Fintype V] {E E' : V → V → Prop} {y y' : V → V → ℤ} {φ φ' A A' : V → ℤ}
    {v : V} (hE : ∀ u, E u v ↔ E' u v) (hy : ∀ u, E u v → y u v = y' u v)
    (hφ : ∀ u, E u v → φ u = φ' u) (hφv : φ v = φ' v) (hA : ∀ u, E u v → A u = A' u)
    (hAv : A v = A' v) : negRelax E y φ A v = negRelax E' y' φ' A' v := by
  classical
  unfold negRelax
  congr 1
  funext u
  by_cases h : E u v
  · have hr : yr y φ u v = yr y' φ' u v := by unfold yr; rw [hy u h, hφ u h, hφv]
    have hn : negArc E y φ u v ↔ negArc E' y' φ' u v := by
      unfold negArc
      rw [hE u, hr]
    by_cases hn' : negArc E y φ u v
    · rw [ite_eq_left hn', ite_eq_left (hn.1 hn'), hAv, hA u h, hr]
    · rw [ite_eq_right hn', ite_eq_right (mt hn.2 hn'), hAv]
  · have h₁ : ¬ negArc E y φ u v := fun h' => h h'.1
    have h₂ : ¬ negArc E' y' φ' u v := fun h' => h ((hE u).2 h'.1)
    rw [ite_eq_right h₁, ite_eq_right h₂, hAv]

theorem lamS_congr {adj adj' : V → V → Prop} {n B : ℕ} {w w' : V → V → Option ℤ} {φ φ' : V → ℤ}
    {a b : V} (hadj : adj a b ↔ adj' a b) (hw : w a b = w' a b) (ha : φ a = φ' a) (hb : φ b = φ' b) :
    lamS (keptS adj n w φ B) (ysc n w φ B) a b = lamS (keptS adj' n w' φ' B) (ysc n w' φ' B) a b :=
  restrictLen_congr (keptS_congr hadj hw ha hb) (by unfold posPart; rw [ysc_congr hw ha hb])

/-- A node with an arc of finite weight and negative reduced weight. -/
def badAt (adj : V → V → Prop) (n : ℕ) (w : V → V → Option ℤ) (φ : V → ℤ) (a : V) : Prop :=
  ∃ b, zArc adj w a b ∧ yr (xw n w) φ a b < 0

theorem badAt_congr {adj adj' : V → V → Prop} {n : ℕ} {w w' : V → V → Option ℤ} {φ φ' : V → ℤ}
    {a : V} (hadj : ∀ b, adj a b ↔ adj' a b) (hw : ∀ b, adj a b → w a b = w' a b)
    (ha : φ a = φ' a) (hb : ∀ b, adj a b → φ b = φ' b) : badAt adj n w φ a ↔ badAt adj' n w' φ' a := by
  unfold badAt
  refine exists_congr fun b => ?_
  by_cases h : adj a b
  · have hr : yr (xw n w) φ a b = yr (xw n w') φ' a b := by
      unfold yr xw zWt
      rw [hw b h, ha, hb b h]
    simp only [zArc, hr, hw b h, hadj b]
  · constructor
    · rintro ⟨⟨h', -⟩, -⟩
      exact absurd h' h
    · rintro ⟨⟨h', -⟩, -⟩
      exact absurd ((hadj b).2 h') h

/-- The lengths of the last call: the reduced weights on the arcs of finite weight. -/
noncomputable def finLen (adj : V → V → Prop) (n : ℕ) (w : V → V → Option ℤ) (φ : V → ℤ) :
    V → V → ℕ∞ :=
  restrictLen (zArc adj w) (lenX n w φ)

theorem finLen_congr {adj adj' : V → V → Prop} {n : ℕ} {w w' : V → V → Option ℤ} {φ φ' : V → ℤ}
    {a b : V} (hadj : adj a b ↔ adj' a b) (hw : w a b = w' a b) (ha : φ a = φ' a) (hb : φ b = φ' b) :
    finLen adj n w φ a b = finLen adj' n w' φ' a b := by
  unfold finLen
  refine restrictLen_congr (by unfold zArc; rw [hadj, hw]) ?_
  unfold lenX yr xw zWt
  rw [hw, ha, hb]

end Congr

/-! ### What a node knows -/

variable {n : ℕ}

/-- The input of the oracle at `v` from its neighbours, lengths and offset. -/
def mkOra (x : List (Fin n)) (v : Fin n) (len : Fin n → Fin n → ℕ∞) (off : ℕ∞) : OracleIn (Fin n) where
  nbrs := x
  lenOut u := if u ∈ x then len v u else ⊤
  lenIn u := if u ∈ x then len u v else ⊤
  offset := off

/-- The input of the decomposition at `v` from its neighbours, lengths and bound. -/
def mkLdd (x : List (Fin n)) (v : Fin n) (len : Fin n → Fin n → ℕ∞) (d : ℕ) : LddIn (Fin n) where
  nbrs := x
  lenOut u := if u ∈ x then len v u else ⊤
  lenIn u := if u ∈ x then len u v else ⊤
  d := d

section Know

variable (N : Net (Fin n))

theorem fun_nbrs_eq {v : Fin n} {f g : Fin n → ℕ∞} (h : ∀ u, N.G.Adj v u → f u = g u) :
    (fun u => if u ∈ N.rotList v then f u else ⊤) = fun u => if N.G.Adj v u then g u else ⊤ := by
  funext u
  by_cases hu : N.G.Adj v u
  · rw [ite_eq_left ((N.mem_rotList v u).2 hu), ite_eq_left hu, h u hu]
  · rw [ite_eq_right (mt (N.mem_rotList v u).1 hu), ite_eq_right hu]

theorem mkOra_eq {v : Fin n} {len ℓ : Fin n → Fin n → ℕ∞} {off : ℕ∞} {φ : Fin n → ℕ∞}
    (h : ∀ u, N.G.Adj v u → len v u = ℓ v u ∧ len u v = ℓ u v) (ho : off = φ v) :
    mkOra (N.rotList v) v len off = N.oracleIn ℓ φ v := by
  simp only [mkOra, Net.oracleIn, OracleIn.mk.injEq]
  exact ⟨trivial, fun_nbrs_eq N fun u hu => (h u hu).1, fun_nbrs_eq N fun u hu => (h u hu).2, ho⟩

theorem mkLdd_eq {v : Fin n} {len ℓ : Fin n → Fin n → ℕ∞} {d : ℕ}
    (h : ∀ u, N.G.Adj v u → len v u = ℓ v u ∧ len u v = ℓ u v) :
    mkLdd (N.rotList v) v len d = N.lddIn ℓ d v := by
  simp only [mkLdd, Net.lddIn, LddIn.mk.injEq]
  exact ⟨trivial, fun_nbrs_eq N fun u hu => (h u hu).1, fun_nbrs_eq N fun u hu => (h u hu).2, trivial⟩

/-- The weights a node knows: those of its arcs. -/
def wLoc (v : Fin n) (x : NegIn (Fin n)) (a b : Fin n) : Option ℤ :=
  if a = v then x.wOut b else if b = v then x.wIn a else none

/-- The arcs a node knows. -/
def adjLoc (v : Fin n) (x : NegIn (Fin n)) (a b : Fin n) : Prop :=
  (a = v ∧ b ∈ x.nbrs) ∨ (b = v ∧ a ∈ x.nbrs)

variable (w : Fin n → Fin n → Option ℤ) (s : Fin n)

theorem wLoc_out {v u : Fin n} (h : N.G.Adj v u) : wLoc v (N.negIn w s v) v u = w v u := by
  simp only [wLoc, Net.negIn, ite_eq_left h, ite_true]

theorem wLoc_in {v u : Fin n} (h : N.G.Adj v u) : wLoc v (N.negIn w s v) u v = w u v := by
  have hne : u ≠ v := (N.G.ne_of_adj h).symm
  simp only [wLoc, Net.negIn, ite_eq_right hne, ite_eq_left h, ite_true]

theorem adjLoc_out (v u : Fin n) : adjLoc v (N.negIn w s v) v u ↔ N.G.Adj v u := by
  simp only [adjLoc, Net.negIn, N.mem_rotList, true_and]
  constructor
  · rintro (h | ⟨rfl, h⟩)
    · exact h
    · exact h
  · exact Or.inl

theorem adjLoc_in (v u : Fin n) : adjLoc v (N.negIn w s v) u v ↔ N.G.Adj u v := by
  simp only [adjLoc, Net.negIn, N.mem_rotList, true_and]
  constructor
  · rintro (⟨rfl, h⟩ | h)
    · exact h
    · exact h.symm
  · exact fun h => Or.inr h.symm

end Know

/-- The value of step `s` that a node stores. -/
def ownV (m : Mem) (s : ℕ) : ℤ := decZ (m (3 * s + 2) 0)

/-- The values of step `s` at a node `v` and its neighbours, as `v` stores them. -/
def viewV (v : Fin n) (m : Mem) (s : ℕ) (u : Fin n) : ℤ :=
  if u = v then ownV m s else decZ (m (3 * s + 2) (u + 1))

/-- From phase `3 s + 3` on, entry `3 s + 2` holds the values `f` of a node and its neighbours. -/
def Holds (G : SimpleGraph (Fin n)) (mem : ℕ → Fin n → Mem) (s : ℕ) (f : Fin n → ℤ) : Prop :=
  ∀ k, 3 * s + 3 ≤ k → ∀ v, mem k v (3 * s + 2) 0 = encZ (f v) ∧
    ∀ u, G.Adj u v → mem k v (3 * s + 2) (u + 1) = encZ (f u)

theorem Holds.own {G : SimpleGraph (Fin n)} {mem : ℕ → Fin n → Mem} {s : ℕ} {f : Fin n → ℤ}
    (h : Holds G mem s f) {k : ℕ} (hk : 3 * s + 3 ≤ k) (v : Fin n) : ownV (mem k v) s = f v := by
  unfold ownV
  rw [(h k hk v).1, decZ_encZ]

theorem Holds.view {G : SimpleGraph (Fin n)} {mem : ℕ → Fin n → Mem} {s : ℕ} {f : Fin n → ℤ}
    (h : Holds G mem s f) {k : ℕ} (hk : 3 * s + 3 ≤ k) (v u : Fin n) (hu : u = v ∨ G.Adj v u) :
    viewV v (mem k v) s u = f u := by
  unfold viewV
  by_cases e : u = v
  · rw [ite_eq_left e, h.own hk, e]
  · rw [ite_eq_right e, (h k hk v).2 u ((hu.resolve_left e).symm), decZ_encZ]

/-- **One exchange.** After one round each node holds its value and those of its neighbours. -/
theorem exch_one {B : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℕ)
    (hx : ∀ u, x u < 2 ^ B) (v : Fin n) :
    relaxSt B G (fun v => passIn (x v) (fun y _ => y) (fun _ => x v)) 1 v 0 = x v ∧
      ∀ u, G.Adj u v → relaxSt B G (fun v => passIn (x v) (fun y _ => y) (fun _ => x v)) 1 v (u + 1) = x u :=
  ⟨rfl, fun u hu => pass_nbr (B := B) G x (fun _ y _ => y) (fun v _ => x v) 0 hu (hx u)⟩

end SsspFlow.Congest
