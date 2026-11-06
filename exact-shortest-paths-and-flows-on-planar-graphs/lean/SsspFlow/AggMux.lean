import SsspFlow.Flood
import SsspFlow.Machine

/-!
# Typed messages and many runs at once

* `TAlg`: a synchronous algorithm whose messages are values of a type `M`. `TAlg.bits` sends the code of
  each message in `B` bits, and `run_bits` says that it runs as before if the codes of the messages fit.
* `mux`: one run of an algorithm for every name `x : ℕ`, on the graph `subG` of the edges whose lists at both
  ends hold `x`. An edge serves the names of its list in increasing order, one per round, so a block of `c`
  rounds carries one round of every run if no list has more than `c` names (`run_mux`).
-/

set_option autoImplicit false

open Cslib.Congest Cslib.Congest.Algorithm

namespace SsspFlow.Congest

/-- A synchronous algorithm whose messages are values of `M`. -/
structure TAlg (V I σ M : Type*) where
  /-- The first state from the identifier and the input. -/
  init : V → I → σ
  /-- The message to a neighbour. -/
  send : V → σ → V → M
  /-- The next state from the messages received. -/
  step : V → σ → (V → Option M) → σ

namespace TAlg

variable {V I σ M : Type*}

/-- The states after `t` rounds. -/
def run (A : TAlg V I σ M) (G : SimpleGraph V) [DecidableRel G.Adj] (inp : V → I) : ℕ → V → σ
  | 0 => fun v => A.init v (inp v)
  | t + 1 => fun v => A.step v (A.run G inp t v)
      (fun w => if G.Adj w v then some (A.send w (A.run G inp t w) v) else none)

variable (A : TAlg V I σ M)

/-- The algorithm that sends the code of a message as a number in `B` bits. -/
noncomputable def bits (code : M → ℕ) (dec : ℕ → M) (B : ℕ) : Algorithm V I σ B where
  init := A.init
  send v s w := toMsg B (code (A.send v s w))
  step v s m := A.step v s fun u => (m u).map fun x => dec (ofMsg x)
  out _ _ := true

theorem run_bits {code : M → ℕ} {dec : ℕ → M} {B : ℕ} (hcd : ∀ m, dec (code m) = m)
    (G : SimpleGraph V) [DecidableRel G.Adj] (inp : V → I)
    (hB : ∀ t u v, G.Adj u v → code (A.send u (A.run G inp t u) v) < 2 ^ B) (t : ℕ) :
    (A.bits code dec B).run G inp t = A.run G inp t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext v
    show A.step v ((A.bits code dec B).run G inp t v)
        (fun u => (if G.Adj u v then some (toMsg B (code (A.send u ((A.bits code dec B).run G inp t u) v)))
          else none).map fun x => dec (ofMsg x)) = A.step v (A.run G inp t v)
        (fun w => if G.Adj w v then some (A.send w (A.run G inp t w) v) else none)
    rw [ih]
    congr 1
    funext u
    by_cases h : G.Adj u v
    · simp only [h, ite_true, Option.map_some, ofMsg_toMsg (hB t u v h), hcd]
    · simp only [h, ite_false, Option.map_none]

end TAlg

/-- The names of a list in increasing order, each once. -/
noncomputable def slots (l : List ℕ) : List ℕ := l.toFinset.sort (· ≤ ·)

theorem mem_slots {l : List ℕ} {x : ℕ} : x ∈ slots l ↔ x ∈ l := by
  simp [slots, Finset.mem_sort]

theorem slots_eq {l l' : List ℕ} (h : ∀ x, x ∈ l ↔ x ∈ l') : slots l = slots l' := by
  unfold slots
  congr 1
  ext x
  simp [h x]

theorem length_slots_le (l : List ℕ) : (slots l).length ≤ l.length := by
  rw [slots, Finset.length_sort]
  exact List.toFinset_card_le l

/-- The state of the multiplexer: the slot of the round in its block, the state of every run, and the
messages received in the earlier slots of the block. -/
structure MuxSt (V σ : Type*) (B : ℕ) where
  /-- The slot of the next round. -/
  slot : ℕ
  /-- The state of the run of every name. -/
  comp : ℕ → σ
  /-- The message received from a neighbour in a slot. -/
  buf : V → ℕ → Option (Msg B)

variable {V I J σ : Type*} {B : ℕ}

/-- The edges whose lists at both ends hold `x`. -/
def subG (G : SimpleGraph V) (L : V → V → List ℕ) (x : ℕ) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ x ∈ L u v ∧ x ∈ L v u
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] (L : V → V → List ℕ) (x : ℕ) :
    DecidableRel (subG G L x).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj u v ∧ x ∈ L u v ∧ x ∈ L v u))

/-- Runs of `A`, one for every name. From its input a node reads the list of names of each of its edges
(`L`) and the input of each run (`Jx`). A block of `c` rounds is one round of every run. -/
noncomputable def mux (A : Algorithm V J σ B) (c : ℕ) (L : I → V → List ℕ) (Jx : I → ℕ → J) :
    Algorithm V I (I × MuxSt V σ B) B where
  init v i := (i, ⟨0, fun x => A.init v (Jx i x), fun _ _ => none⟩)
  send v s w :=
    match (slots (L s.1 w))[s.2.slot]? with
    | some x => A.send v (s.2.comp x) w
    | none => fun _ => false
  step v s m :=
    if s.2.slot + 1 = c then
      (s.1, ⟨0, fun x => A.step v (s.2.comp x) (fun u =>
        if x ∈ L s.1 u then
          (if (slots (L s.1 u)).idxOf x = s.2.slot then m u else s.2.buf u ((slots (L s.1 u)).idxOf x))
        else none), fun _ _ => none⟩)
    else (s.1, ⟨s.2.slot + 1, s.2.comp, fun u j => if j = s.2.slot then m u else s.2.buf u j⟩)
  out _ _ := true

section Mux

variable (A : Algorithm V J σ B) (c : ℕ) (L : I → V → List ℕ) (Jx : I → ℕ → J)
  (G : SimpleGraph V) [DecidableRel G.Adj] (inp : V → I)

/-- The graph of the run of `x`. -/
abbrev muxG (x : ℕ) : SimpleGraph V := subG G (fun u w => L (inp u) w) x

/-- The state of the run of `x` after `t` of its rounds. -/
def muxRun (t : ℕ) (x : ℕ) (v : V) : σ := A.run (muxG L G inp x) (fun w => Jx (inp w) x) t v

/-- The message of `u` to `v` in slot `j` of a block after `t` rounds of the runs. -/
noncomputable def muxMsg (t j : ℕ) (u v : V) : Msg B :=
  match (slots (L (inp u) v))[j]? with
  | some x => A.send u (muxRun A L Jx G inp t x u) v
  | none => fun _ => false

/-- The state in slot `r` of the block after `t` rounds of the runs. -/
noncomputable def muxState (t r : ℕ) (v : V) : I × MuxSt V σ B :=
  (inp v, ⟨r, fun x => muxRun A L Jx G inp t x v,
    fun u j => if j < r then (if G.Adj u v then some (muxMsg A L Jx G inp t j u v) else none) else none⟩)

variable {A c L Jx G inp}

theorem mux_block {t : ℕ} (h0 : (mux A c L Jx).run G inp (c * t) = muxState A L Jx G inp t 0) :
    ∀ r, r < c → (mux A c L Jx).run G inp (c * t + r) = muxState A L Jx G inp t r := by
  intro r
  induction r with
  | zero => intro _; exact h0
  | succ r ih =>
    intro hr
    funext v
    have hrun := ih (by omega)
    show (mux A c L Jx).step v ((mux A c L Jx).run G inp (c * t + r) v) (fun w => if G.Adj w v then
      some ((mux A c L Jx).send w ((mux A c L Jx).run G inp (c * t + r) w) v) else none) = _
    rw [hrun]
    show (if r + 1 = c then _ else _) = _
    rw [ite_eq_right (by omega)]
    show (inp v, (⟨r + 1, fun x => muxRun A L Jx G inp t x v, fun u j => if j = r then
      (if G.Adj u v then some (muxMsg A L Jx G inp t r u v) else none) else
      (if j < r then (if G.Adj u v then some (muxMsg A L Jx G inp t j u v) else none) else none)⟩ :
      MuxSt V σ B)) = (inp v, ⟨r + 1, fun x => muxRun A L Jx G inp t x v, fun u j => if j < r + 1 then
      (if G.Adj u v then some (muxMsg A L Jx G inp t j u v) else none) else none⟩)
    congr 3
    funext u j
    by_cases hj : j = r
    · subst hj
      simp
    · have hjr : (j < r + 1) = (j < r) := propext (by omega)
      simp only [hj, hjr, ite_false]

/-- **The multiplexer.** After `t` blocks of `c` rounds, the state of the run of every name `x` is the state
of `A` after `t` rounds on the graph of the edges whose lists hold `x`. -/
theorem run_mux (hc : 0 < c)
    (hsym : ∀ u v, G.Adj u v → ∀ x, x ∈ L (inp u) v ↔ x ∈ L (inp v) u)
    (hlen : ∀ u v, G.Adj u v → (slots (L (inp u) v)).length ≤ c) (t : ℕ) :
    (mux A c L Jx).run G inp (c * t) = muxState A L Jx G inp t 0 := by
  induction t with
  | zero =>
    funext v
    show (inp v, (⟨0, fun x => A.init v (Jx (inp v) x), fun _ _ => none⟩ : MuxSt V σ B)) = _
    rfl
  | succ t ih =>
    have hlast := mux_block ih (c - 1) (by omega)
    have ht : c * (t + 1) = c * t + (c - 1) + 1 := by
      rw [Nat.mul_succ]
      omega
    rw [ht]
    funext v
    show (mux A c L Jx).step v ((mux A c L Jx).run G inp (c * t + (c - 1)) v) (fun w => if G.Adj w v then
      some ((mux A c L Jx).send w ((mux A c L Jx).run G inp (c * t + (c - 1)) w) v) else none) = _
    rw [hlast]
    show (if c - 1 + 1 = c then _ else _) = _
    rw [ite_eq_left (by omega)]
    show (inp v, (⟨0, fun x => A.step v (muxRun A L Jx G inp t x v) (fun u => if x ∈ L (inp v) u then
      (if (slots (L (inp v) u)).idxOf x = c - 1 then
        (if G.Adj u v then some (muxMsg A L Jx G inp t (c - 1) u v) else none) else
        (if (slots (L (inp v) u)).idxOf x < c - 1 then (if G.Adj u v then
          some (muxMsg A L Jx G inp t ((slots (L (inp v) u)).idxOf x) u v) else none) else none))
      else none), fun _ _ => none⟩ : MuxSt V σ B)) = (inp v, ⟨0, fun x => muxRun A L Jx G inp (t + 1) x v,
        fun u j => if j < 0 then (if G.Adj u v then some (muxMsg A L Jx G inp (t + 1) j u v) else none)
          else none⟩)
    congr 3
    · funext x
      show A.step v (muxRun A L Jx G inp t x v) _ = A.step v (muxRun A L Jx G inp t x v) _
      congr 1
      funext u
      by_cases hx : x ∈ L (inp v) u
      · simp only [hx, ite_true]
        have hmem : x ∈ slots (L (inp v) u) := mem_slots.2 hx
        have hidx : (slots (L (inp v) u)).idxOf x < (slots (L (inp v) u)).length :=
          List.idxOf_lt_length_iff.2 hmem
        by_cases hadj : G.Adj u v
        · have hs : slots (L (inp u) v) = slots (L (inp v) u) := slots_eq (hsym u v hadj)
          have hc' := hlen v u hadj.symm
          have hget : (slots (L (inp u) v))[(slots (L (inp v) u)).idxOf x]? = some x := by
            rw [hs, List.getElem?_eq_getElem hidx, List.getElem_idxOf hidx]
          have hmsg : muxMsg A L Jx G inp t ((slots (L (inp v) u)).idxOf x) u v =
              A.send u (muxRun A L Jx G inp t x u) v := by
            unfold muxMsg
            rw [hget]
          have hG : (muxG L G inp x).Adj u v := ⟨hadj, (hsym u v hadj x).2 hx, hx⟩
          simp only [hG, hadj, ite_true]
          by_cases he : (slots (L (inp v) u)).idxOf x = c - 1
          · simp only [he, ite_true]
            rw [← he, hmsg]
            rfl
          · have hlt : (slots (L (inp v) u)).idxOf x < c - 1 := by omega
            simp only [he, hlt, ite_true, ite_false]
            rw [hmsg]
            rfl
        · have hG : ¬ (muxG L G inp x).Adj u v := fun h => hadj h.1
          simp only [hG, hadj, ite_false]
          split_ifs <;> rfl
      · have hG : ¬ (muxG L G inp x).Adj u v := fun h => hx h.2.2
        simp only [hx, hG, ite_false]

end Mux

end SsspFlow.Congest
