import SsspFlow.GHatLevelRaw

/-!
# The lengths of the network of a level from local data

* `Algorithm.exchTo`: one round in which every node sends each neighbour a number of its own for that
  neighbour (`run_exchTo`).
* `DInfo.pack`, `DInfo.unpack`: the record of a dart and three numbers below `2 ^ b` in `b * 3 + 5`
  bits (`unpack_pack`).
* `rawW`, `rawKeep`: the length of a dart of the repaired graph and whether `Ĝ_ℓ` keeps it, from the
  name of the dart and the data of its host (`RData.rawW_nameD`, `RData.rawW_rev`,
  `RData.rawKeep_nameD`).
* `rawIn`, `RData.levelNet_oracleIn_raw`: the input of every identifier for the shortest paths of a
  level, with its neighbours, the lengths to and from them and its offset, is a function of the
  rotation list of its host `w`, the records and the values `λ` of the darts at `w` and into `w`, the
  bound `M` and the identifier of the source.
-/

set_option autoImplicit false

namespace Cslib.Congest.Algorithm

variable {V : Type*} {B : ℕ}

open SsspFlow.Congest in
/-- One round in which every node sends each neighbour a number of its own for that neighbour. -/
noncomputable def exchTo (V : Type*) (B : ℕ) : Algorithm V (V → ℕ) ((V → ℕ) × (V → Option ℕ)) B where
  init _ x := (x, fun _ => none)
  send _ s w := toMsg B (s.1 w)
  step _ s m := (s.1, fun u => (m u).map ofMsg)
  out _ _ := true

open SsspFlow.Congest in
/-- After the exchange a node knows the numbers its neighbours chose for it, if they fit into `B`
bits. -/
theorem run_exchTo (G : SimpleGraph V) [DecidableRel G.Adj] (inp : V → V → ℕ)
    (h : ∀ u v, inp u v < 2 ^ B) (v : V) :
    (exchTo V B).run G inp 1 v = (inp v, fun u => if G.Adj u v then some (inp u v) else none) := by
  show (inp v, fun u => (if G.Adj u v then some (toMsg B (inp u v)) else none).map ofMsg) = _
  congr 1
  funext u
  split_ifs <;> simp [ofMsg_toMsg (h u v)]

end Cslib.Congest.Algorithm

namespace SsspFlow

open FourColor SsspFlow.Congest

namespace RotSystem

namespace DInfo

/-- The five bits of a record as a number below `32`. -/
def bits (i : DInfo) : ℕ :=
  i.inc.toNat + 2 * i.cut.toNat + 4 * i.modeL.toNat + 8 * i.hostT.toNat + 16 * i.optR.toNat

/-- The record of a number below `32`. -/
def ofBits (c : ℕ) : DInfo :=
  ⟨c.testBit 0, c.testBit 1, c.testBit 2, c.testBit 3, c.testBit 4⟩

theorem bits_lt (i : DInfo) : i.bits < 32 := by
  obtain ⟨a, b, c, d, e⟩ := i
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

theorem ofBits_bits (i : DInfo) : ofBits i.bits = i := by
  obtain ⟨a, b, c, d, e⟩ := i
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

/-- A record and three numbers below `2 ^ b`. -/
def pack (b : ℕ) (i : DInfo) (x y z : ℕ) : ℕ := i.bits + 32 * (x + 2 ^ b * (y + 2 ^ b * z))

/-- The record and the three numbers of a packed number. -/
def unpack (b c : ℕ) : DInfo × ℕ × ℕ × ℕ :=
  (ofBits (c % 32), c / 32 % 2 ^ b, c / 32 / 2 ^ b % 2 ^ b, c / 32 / 2 ^ b / 2 ^ b)

theorem unpack_pack {b x y z : ℕ} (i : DInfo) (hx : x < 2 ^ b) (hy : y < 2 ^ b) :
    unpack b (pack b i x y z) = (i, x, y, z) := by
  have hp : 0 < 2 ^ b := Nat.two_pow_pos b
  have h32 : (i.bits + 32 * (x + 2 ^ b * (y + 2 ^ b * z))) / 32 = x + 2 ^ b * (y + 2 ^ b * z) := by
    rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt i.bits_lt, zero_add]
  have h1 : (x + 2 ^ b * (y + 2 ^ b * z)) / 2 ^ b = y + 2 ^ b * z := by
    rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hx, zero_add]
  have h2 : (y + 2 ^ b * z) / 2 ^ b = z := by
    rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hy, zero_add]
  simp only [unpack, pack, h32, h1, h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt i.bits_lt, ofBits_bits]

theorem pack_lt {b x y z : ℕ} (i : DInfo) (hx : x < 2 ^ b) (hy : y < 2 ^ b) (hz : z < 2 ^ b) :
    pack b i x y z < 2 ^ (b * 3 + 5) := by
  have hp : 0 < 2 ^ b := Nat.two_pow_pos b
  have e : 2 ^ (b * 3 + 5) = 32 * (2 ^ b * (2 ^ b * 2 ^ b)) := by ring
  rw [e]
  unfold pack
  have h3 : y + 2 ^ b * z < 2 ^ b * 2 ^ b := by nlinarith
  have h4 : x + 2 ^ b * (y + 2 ^ b * z) < 2 ^ b * (2 ^ b * 2 ^ b) := by nlinarith
  have := i.bits_lt
  omega

end DInfo

section RawLen

variable {n : ℕ}

/-- The length of the dart named `p` at its host: `0` for the darts of tokens, `λ` of the rim token
for a rim from its tail, `λ` of its partner for a rim from its head, and `M` otherwise. The numbers
`lo u l` are `λ` of the tokens on the dart to `u`, and `li u l` those on the dart from `u`. -/
def rawW (f : Fin n → DInfo) (lo li : Fin n → Lab → ℕ) (M : ℕ) (p : Fin n × Fin n × Fin 21) : ℕ :=
  if 5 ≤ p.2.2 ∧ p.2.2 ≤ 10 then 0
  else if p.2.2 = 13 then lo p.2.1 (if (f p.2.1).inc then .one else .zero)
  else if p.2.2 = 14 then li p.2.1 (if (f p.2.1).inc then .two else .zero)
  else M

/-- Whether `Ĝ_ℓ` keeps the dart named `p`: all darts but the rims of unincised pairs not hosted
there. -/
def rawKeep (f : Fin n → DInfo) (p : Fin n × Fin n × Fin 21) : Bool :=
  if p.2.2 = 13 ∨ p.2.2 = 14 then (f p.2.1).inc || (f p.2.1).hostT else true

end RawLen


section RawIn

variable {n : ℕ}

/-- The length from the identifier `(w, u, k)` to `b`: `0` from a copy to a dart hosted at `w`, the
length of a kept dart to its reverse, `0` from a dart to its copy, and `∞` otherwise. -/
def rawLenOut (R : List (Fin n)) (f g : Fin n → DInfo) (lo li : Fin n → Lab → ℕ) (M : ℕ) (w : Fin n)
    (q : Fin n × Fin 21) (b : Fin (n * (n * 21))) : ℕ∞ :=
  if q.2 < 5 then
    (if RData.hostOf b = w ∧ rawReal R f g w ((RData.idEquiv.symm b).2.1, (RData.idEquiv.symm b).2.2)
      then 0 else ⊤)
  else if b = RData.idEquiv (revName (w, q.1, q.2)) then
    (if rawKeep f (w, q.1, q.2) then (rawW f lo li M (w, q.1, q.2) : ℕ∞) else ⊤)
  else 0

/-- The length from `b` to the identifier `(w, u, k)`. -/
def rawLenIn (R : List (Fin n)) (f g : Fin n → DInfo) (lo li : Fin n → Lab → ℕ) (M : ℕ) (w : Fin n)
    (q : Fin n × Fin 21) (b : Fin (n * (n * 21))) : ℕ∞ :=
  if q.2 < 5 then
    (if RData.hostOf b = w ∧ rawReal R f g w ((RData.idEquiv.symm b).2.1, (RData.idEquiv.symm b).2.2)
      then 0 else ⊤)
  else if b = RData.idEquiv (revName (w, q.1, q.2)) then
    (if rawKeep f (w, q.1, q.2) then (rawW f lo li M (revName (w, q.1, q.2)) : ℕ∞) else ⊤)
  else 0

/-- **The input of the identifier `(w, u, k)`** for the shortest paths of a level, from the data of
`w` and the source identifier `src`. -/
def rawIn (R : List (Fin n)) (f g : Fin n → DInfo) (lo li : Fin n → Lab → ℕ) (M : ℕ)
    (src : Fin (n * (n * 21))) (w : Fin n) (q : Fin n × Fin 21) : OracleIn (Fin (n * (n * 21))) where
  nbrs := rawAt R f g w q
  lenOut b := if b ∈ rawAt R f g w q ∧ rawReal R f g w q then rawLenOut R f g lo li M w q b else ⊤
  lenIn b := if b ∈ rawAt R f g w q ∧ rawReal R f g w q then rawLenIn R f g lo li M w q b else ⊤
  offset := if RData.idEquiv (w, q.1, q.2) = src then 0 else ⊤

end RawIn

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (lam : S.Tok → ℕ)

/-- `λ` of the token with label `l` on the dart `(w, u)`, `0` if there is none. -/
def lamAt (w u : Fin n) (l : Lab) : ℕ :=
  if h : N.G.Adj w u then (if ht : S.IsTok ((⟨(w, u), h⟩ : N.G.Dart), l) then lam ⟨_, ht⟩ else 0) else 0

theorem lamAt_tok (x : S.Tok) : S.lamAt lam x.1.1.fst x.1.1.snd x.1.2 = lam x := by
  obtain ⟨⟨d, l⟩, hx⟩ := x
  unfold lamAt
  rw [dite_eq_left_of_eq_true (eq_true d.adj), dite_eq_left_of_eq_true (eq_true hx)]

theorem rawW_nameD (M : ℕ) (x : S.HD) :
    rawW (S.dinfoAt (S.nameD x).1) (S.lamAt lam (S.nameD x).1) (fun u => S.lamAt lam u (S.nameD x).1) M
      (S.nameD x) = S.dartW lam M x := by
  obtain ⟨e, b⟩ := x
  rcases e with c | d | ⟨⟨c, l⟩, hc⟩ | c | c | c
  · cases b <;> rfl
  · have hd := S.dinfoAt_dart d
    by_cases hi : d ∈ S.inc
    · have hx : S.IsTok (d, .one) := S.isTok_one hi
      have hr : S.rimTok d = ⟨(d, .one), hx⟩ := by unfold rimTok; rw [dite_eq_left_of_eq_true (eq_true hi)]
      cases b
      · show rawW (S.dinfoAt d.fst) (S.lamAt lam d.fst) (fun u => S.lamAt lam u d.fst) M (d.fst, d.snd, 13) = lam (S.rimTok d)
        simp (config := {decide := true}) only [rawW, hd, dinfo, hi, decide_true, ite_true, ite_false, hr]
        exact S.lamAt_tok lam ⟨(d, .one), hx⟩
      · show rawW (S.dinfoAt d.fst) (S.lamAt lam d.fst) (fun u => S.lamAt lam u d.fst) M (d.fst, d.snd, 14) = lam (S.partnerTok (S.rimTok d))
        simp (config := {decide := true}) only [rawW, hd, dinfo, hi, decide_true, ite_true, ite_false, hr]
        exact S.lamAt_tok lam (S.partnerTok ⟨(d, .one), hx⟩)
    · have hx : S.IsTok (d, .zero) := S.isTok_zero hi
      have hr : S.rimTok d = ⟨(d, .zero), hx⟩ := by unfold rimTok; rw [dite_eq_right_of_eq_false (eq_false hi)]
      cases b
      · show rawW (S.dinfoAt d.fst) (S.lamAt lam d.fst) (fun u => S.lamAt lam u d.fst) M (d.fst, d.snd, 13) = lam (S.rimTok d)
        simp (config := {decide := true}) only [rawW, hd, dinfo, hi, decide_false, ite_true, ite_false, hr]
        exact S.lamAt_tok lam ⟨(d, .zero), hx⟩
      · show rawW (S.dinfoAt d.fst) (S.lamAt lam d.fst) (fun u => S.lamAt lam u d.fst) M (d.fst, d.snd, 14) = lam (S.partnerTok (S.rimTok d))
        simp (config := {decide := true}) only [rawW, hd, dinfo, hi, decide_false, ite_true, ite_false, hr]
        exact S.lamAt_tok lam (S.partnerTok ⟨(d, .zero), hx⟩)
  · cases l <;> cases b <;> rfl
  all_goals cases b <;> rfl

/-- The length of the reverse dart, from the data of the host of the dart. -/
theorem rawW_rev (M : ℕ) (x : S.HD) :
    rawW (S.dinfoAt (S.nameD x).1) (S.lamAt lam (S.nameD x).1) (fun u => S.lamAt lam u (S.nameD x).1) M
      (revName (S.nameD x)) = S.dartW lam M (S.hrev x) := by
  rw [← S.nameD_hrev]
  obtain ⟨e, b⟩ := x
  rcases e with c | d | ⟨⟨c, l⟩, hc⟩ | c | c | c
  · exact S.rawW_nameD lam M (S.hrev (.sp c, b))
  · exact S.rawW_nameD lam M (S.hrev (.rim d, b))
  · cases l <;> cases b <;> rfl
  all_goals exact S.rawW_nameD lam M (S.hrev (_, b))

theorem mem_keep_iff (x : S.HD) : x ∈ S.keep ↔ S.Keep x.1 := by
  unfold keep
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ _)

/-- Whether `Ĝ_ℓ` keeps a dart, from the data of its host. -/
theorem rawKeep_nameD (x : S.HD) :
    rawKeep (S.dinfoAt (S.nameD x).1) (S.nameD x) = decide (x ∈ S.keep) := by
  simp only [S.mem_keep_iff]
  obtain ⟨e, b⟩ := x
  rcases e with c | d | ⟨⟨c, l⟩, hc⟩ | c | c | c
  · cases b <;> simp (config := {decide := true}) [rawKeep, Keep, nameD]
  · have hd := S.dinfoAt_dart d
    cases b
    · show rawKeep (S.dinfoAt d.fst) (d.fst, d.snd, 13) = _
      simp (config := {decide := true}) [rawKeep, Keep, hd, dinfo]
    · show rawKeep (S.dinfoAt d.fst) (d.fst, d.snd, 14) = _
      simp (config := {decide := true}) [rawKeep, Keep, hd, dinfo]
  · cases l <;> cases b <;> simp (config := {decide := true}) [rawKeep, Keep, nameD]
  all_goals cases b <;> simp (config := {decide := true}) [rawKeep, Keep, nameD]

section Level

variable (hN : ∀ u, ∃ w, N.G.Adj u w) (M : ℕ)

theorem rawReal_host (b : Fin (n * (n * 21))) :
    rawReal (N.rotList (hostOf b)) (S.dinfoAt (hostOf b)) (fun u => S.dinfoAt u (hostOf b)) (hostOf b)
      ((idEquiv.symm b).2.1, (idEquiv.symm b).2.2) = true ↔ (S.levelPad hN).IsReal b := by
  rw [S.rawReal_iff, S.isReal_iff]
  rfl

theorem levelLen_left {a b : Fin (n * (n * 21))} (ha : ¬ (S.levelPad hN).IsReal a) :
    S.levelLen hN lam M a b = ⊤ := by
  unfold levelLen
  exact ite_eq_right_of_eq_false _ _ (eq_false fun h => ha h.1)

theorem levelLen_right {a b : Fin (n * (n * 21))} (hb : ¬ (S.levelPad hN).IsReal b) :
    S.levelLen hN lam M a b = ⊤ := by
  unfold levelLen
  exact ite_eq_right_of_eq_false _ _ (eq_false fun h => hb h.2)

theorem hostOf_inr (x : S.HD) : hostOf ((S.levelPad hN).ι (.inr x)) = (S.nameD x).1 := by
  unfold hostOf
  rw [show (S.levelPad hN).ι (.inr x) = idEquiv (S.nameD x) from rfl, Equiv.symm_apply_apply]

theorem hostOf_inl (v : S.hRot.Vertex) :
    hostOf ((S.levelPad hN).ι (.inl v)) = (N.nameC (S.vcopy v)).1 := by
  unfold hostOf
  rw [show (S.levelPad hN).ι (.inl v) = idEquiv (N.nameC (S.vcopy v)) from rfl, Equiv.symm_apply_apply]

theorem ne_inl_inr (v : S.hRot.Vertex) (x : S.HD) :
    (S.levelPad hN).ι (.inl v) ≠ (S.levelPad hN).ι (.inr x) := fun h => by
  have := (S.levelPad hN).ι_injective h
  cases this

/-- **The inputs of the shortest paths of a level from local data.** The host `w` of an identifier
computes its input from the rotation list of `w`, the records and the values `λ` of the darts at `w`
and into `w`, the bound `M` and the identifier of the source. -/
theorem levelNet_oracleIn_raw (u₀ : S.hRot.Vertex) (z : Fin (n * (n * 21))) :
    (S.levelNet hN).oracleIn (S.levelLen hN lam M) (S.levelOff hN u₀) z =
      rawIn (N.rotList (hostOf z)) (S.dinfoAt (hostOf z)) (fun u => S.dinfoAt u (hostOf z))
        (S.lamAt lam (hostOf z)) (fun u => S.lamAt lam u (hostOf z)) M ((S.levelPad hN).ι (.inl u₀))
        (hostOf z) ((idEquiv.symm z).2.1, (idEquiv.symm z).2.2) := by
  classical
  have hlist := S.levelNet_rotList_raw hN z
  have hz' : idEquiv (hostOf z, (idEquiv.symm z).2.1, (idEquiv.symm z).2.2) = z :=
    idEquiv.apply_symm_apply z
  have hreal := S.rawReal_host hN z
  unfold Net.oracleIn rawIn
  simp only [OracleIn.mk.injEq]
  refine ⟨hlist, funext fun b => ?_, funext fun b => ?_, ?_⟩
  rotate_right
  · unfold levelOff
    rw [hz']
  all_goals
    by_cases hb : b ∈ (S.levelNet hN).rotList z
    swap
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hb (((S.levelNet hN).mem_rotList _ _).2 h)),
        ite_eq_right_of_eq_false _ _ (eq_false fun h => hb (hlist ▸ h.1))]
    rw [ite_eq_left_of_eq_true _ _ (eq_true ((S.levelNet hN).mem_rotList _ _ |>.1 hb))]
    have hb' := hb
    rw [hlist] at hb'
    by_cases hzr : (S.levelPad hN).IsReal z
    swap
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hzr (hreal.1 h.2))]
      first | exact S.levelLen_left lam hN M hzr | exact S.levelLen_right lam hN M hzr
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hb', hreal.2 hzr⟩)]
    obtain ⟨y, rfl⟩ : ∃ y, z = (S.levelPad hN).ι y := ⟨_, hzr⟩
    clear hb' hlist hreal hz'
    rcases y with v | x
    · rw [S.levelNet_rotList_copy hN v, List.mem_append] at hb
      have hk : (N.nameC (S.vcopy v)).2.2 < 5 := N.nameC_kind _
      have hq : (idEquiv.symm ((S.levelPad hN).ι (.inl v))).2.2 = (N.nameC (S.vcopy v)).2.2 := by
        rw [show (S.levelPad hN).ι (.inl v) = idEquiv (N.nameC (S.vcopy v)) from rfl,
          Equiv.symm_apply_apply]
      (try unfold rawLenOut); (try unfold rawLenIn); dsimp only
      try rw [ite_eq_left_of_eq_true _ _ (eq_true (hq ▸ hk))]
      rcases hb with hb | hb
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
        have hh : hostOf ((S.levelPad hN).ι (.inr x)) = hostOf ((S.levelPad hN).ι (.inl v)) := by
          rw [S.hostOf_inr, S.hostOf_inl, ← S.nameC_tl, S.tl_of_mem_lstR hx]
        have hr := (S.rawReal_host hN ((S.levelPad hN).ι (.inr x))).2 ((S.levelPad hN).isReal_ι _)
        rw [hh] at hr
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hh, hr⟩), S.levelLen_ι]
      · have he := ((S.levelPad hN).mem_order _ _).1 hb
        rw [PadMap.mem_extras] at he
        have hh : hostOf b = hostOf ((S.levelPad hN).ι (.inl v)) := by
          rw [← S.hostOf_back hN he.1, he.2]
        rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => he.1 ((S.rawReal_host hN b).1 (by
          rw [hh]; exact h.2)))]
        first | exact S.levelLen_left lam hN M he.1 | exact S.levelLen_right lam hN M he.1
    · rw [S.levelNet_rotList_dart hN x] at hb
      have hk : ¬ (S.nameD x).2.2 < 5 := by have := S.nameD_kind x; omega
      have hn : idEquiv.symm ((S.levelPad hN).ι (.inr x)) = S.nameD x := Equiv.symm_apply_apply _ _
      rw [S.hostOf_inr]
      simp only [hn]
      (try unfold rawLenOut); (try unfold rawLenIn); dsimp only
      rw [ite_eq_right_of_eq_false _ _ (eq_false hk)]
      have hp : ((S.nameD x).1, (S.nameD x).2.1, (S.nameD x).2.2) = S.nameD x := rfl
      rw [hp, ← S.nameD_hrev]
      rw [show idEquiv (S.nameD (S.hrev x)) = (S.levelPad hN).ι (.inr (S.hrev x)) from rfl]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (S.ne_inl_inr hN _ _)), S.levelLen_ι]
      · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), S.rawKeep_nameD, S.levelLen_ι]
        dsimp only
        have hkk : S.hrev x ∈ S.keep ↔ x ∈ S.keep := by
          rw [S.mem_keep_iff, S.mem_keep_iff]; rfl
        have hrr : S.hrev (S.hrev x) = x := by obtain ⟨e, b⟩ := x; cases b <;> rfl
        by_cases hk : x ∈ S.keep
        · rw [ite_eq_left_of_eq_true _ _ (eq_true (decide_eq_true hk))]
          first
          | rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, hk⟩), S.rawW_nameD]
          | rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hrr.symm, hkk.2 hk⟩), S.nameD_hrev, S.rawW_rev]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hk (of_decide_eq_true h))]
          first
          | exact ite_eq_right_of_eq_false _ _ (eq_false fun h => hk h.2)
          | exact ite_eq_right_of_eq_false _ _ (eq_false fun h => hk (hkk.1 h.2))

end Level

end RData

end RotSystem

end SsspFlow
