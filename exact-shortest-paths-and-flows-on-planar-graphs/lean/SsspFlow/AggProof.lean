import SsspFlow.AggMerge

/-!
# Aggregation in the message model

`aggBox` proves `AggBox` with the constant `5`. For each subgraph, separately:

1. The members flood the least identifier of a member for `s` rounds (`ldrT`), so the least member learns that
   it leads.
2. A flood from the leader for `s` rounds gives every node within `s` steps a parent (`floodAlg`).
3. In one round the nodes tell their neighbours their parents (`exch`).
4. The streams of minima run up to the leader along the children (`mergeT`).
5. The stream of the leader runs down along the parents.

`perName_ans` says that every member then knows the least value of every key. The runs of all subgraphs share
the edges by `mux`, so an edge in `c` subgraphs costs a factor `c`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Cslib.Congest Cslib.Congest.Algorithm

namespace SsspFlow.Congest

section Lev

variable {V : Type} {A A' : V → V → Prop} {seed seed' : V → Prop}

theorem Lev.mono_rel (hA : ∀ u v, A u v → A' u v) (hs : ∀ v, seed v → seed' v) (t : ℕ) :
    ∀ v, Lev A seed t v → Lev A' seed' t v := by
  induction t with
  | zero => exact hs
  | succ t ih =>
    rintro v (h | ⟨u, hu, huv⟩)
    · exact Or.inl (ih v h)
    · exact Or.inr ⟨u, ih u hu, hA _ _ huv⟩

theorem Lev.walk (hA : ∀ u v, A' u v → A u v) {a b : V} (p : Walk A' a b) :
    ∀ t, Lev A seed t a → Lev A seed (t + p.support.length - 1) b := by
  induction p with
  | nil a => intro t h; simpa using h
  | cons e p ih =>
    intro t h
    have h' := ih (t + 1) (Or.inr ⟨_, h, hA _ _ e⟩)
    have hl : 0 < p.support.length := List.length_pos_of_mem (Walk.start_mem p)
    rw [Walk.support_cons, List.length_cons]
    convert h' using 2
    omega

theorem Lev.mono_t {t t' : ℕ} (h : t ≤ t') {v : V} (hv : Lev A seed t v) : Lev A seed t' v :=
  Lev.mono h hv

end Lev

section Leader

variable {n : ℕ}

/-- The least identifier of a member heard so far, and `n` if there is none. -/
noncomputable def ldrT (n : ℕ) : TAlg (Fin n) Bool ℕ ℕ where
  init v b := if b = true then v.val else n
  send _ x _ := x
  step _ x m := (insert x (Finset.univ.biUnion fun u => (m u).toFinset)).min' (Finset.insert_nonempty _ _)

variable (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (mb : Fin n → Bool)

theorem ldr_succ (t : ℕ) (v : Fin n) :
    (ldrT n).run H mb (t + 1) v =
      (insert ((ldrT n).run H mb t v) (Finset.univ.biUnion fun u =>
        (if H.Adj u v then some ((ldrT n).run H mb t u) else none).toFinset)).min'
        (Finset.insert_nonempty _ _) := rfl

theorem mem_ldr_set {t : ℕ} {v : Fin n} {y : ℕ} :
    y ∈ insert ((ldrT n).run H mb t v) (Finset.univ.biUnion fun u =>
        (if H.Adj u v then some ((ldrT n).run H mb t u) else none).toFinset) ↔
      y = (ldrT n).run H mb t v ∨ ∃ u, H.Adj u v ∧ y = (ldrT n).run H mb t u := by
  simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and, Option.mem_toFinset]
  constructor
  · rintro (h | ⟨u, hu⟩)
    · exact Or.inl h
    · by_cases ha : H.Adj u v
      · rw [ite_eq_left ha, Option.mem_def, Option.some.injEq] at hu
        exact Or.inr ⟨u, ha, hu.symm⟩
      · rw [ite_eq_right ha] at hu
        exact absurd hu (by simp)
  · rintro (h | ⟨u, ha, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨u, by rw [ite_eq_left ha]; rfl⟩

/-- **The leader.** After `t` rounds a node holds the least member within `t` steps, and `n` if there is
none. -/
theorem ldr_spec (t : ℕ) (v : Fin n) :
    (∀ w, mb w = true → Lev H.Adj (· = w) t v → (ldrT n).run H mb t v ≤ w.val) ∧
      ((ldrT n).run H mb t v = n ∨
        ∃ w, mb w = true ∧ Lev H.Adj (· = w) t v ∧ (ldrT n).run H mb t v = w.val) := by
  induction t generalizing v with
  | zero =>
    show (∀ w, mb w = true → v = w → (if mb v = true then v.val else n) ≤ w.val) ∧
      ((if mb v = true then v.val else n) = n ∨
        ∃ w, mb w = true ∧ v = w ∧ (if mb v = true then v.val else n) = w.val)
    refine ⟨?_, ?_⟩
    · rintro w hw rfl
      rw [ite_eq_left hw]
    · by_cases hv : mb v = true
      · exact Or.inr ⟨v, hv, rfl, ite_eq_left hv⟩
      · exact Or.inl (ite_eq_right hv)
  | succ t ih =>
    rw [ldr_succ]
    refine ⟨fun w hw hl => ?_, ?_⟩
    · rcases hl with hl | ⟨u, hu, ha⟩
      · exact (Finset.min'_le _ _ ((mem_ldr_set H mb).2 (Or.inl rfl))).trans ((ih v).1 w hw hl)
      · exact (Finset.min'_le _ _ ((mem_ldr_set H mb).2 (Or.inr ⟨u, ha, rfl⟩))).trans ((ih u).1 w hw hu)
    · rcases (mem_ldr_set H mb).1 (Finset.min'_mem _ (Finset.insert_nonempty _ _)) with h | ⟨u, ha, h⟩
      · rw [h]
        rcases (ih v).2 with h' | ⟨w, hw, hl, h'⟩
        · exact Or.inl h'
        · exact Or.inr ⟨w, hw, Or.inl hl, h'⟩
      · rw [h]
        rcases (ih u).2 with h' | ⟨w, hw, hl, h'⟩
        · exact Or.inl h'
        · exact Or.inr ⟨w, hw, Or.inr ⟨u, hl, ha⟩, h'⟩

theorem ldr_le (t : ℕ) (v : Fin n) : (ldrT n).run H mb t v ≤ n := by
  rcases (ldr_spec H mb t v).2 with h | ⟨w, -, -, h⟩
  · exact h.le
  · rw [h]
    exact w.isLt.le

end Leader

section Phases

variable {n : ℕ}

/-- The data of a node in the aggregation over one subgraph. -/
structure Acc (n : ℕ) where
  /-- Whether the node is a member. -/
  mb : Bool
  /-- The items of the node: key and value. -/
  its : List (ℕ × ℕ)
  /-- The least member heard. -/
  ldr : ℕ
  /-- The state of the flood: `some none` at the leader, `some (some p)` with the parent `p`. -/
  fl : Option (Option (Fin n))
  /-- The numbers received in the exchange of parents. -/
  rc : Fin n → Option ℕ
  /-- The stream sent up to the leader. -/
  up : List Elt

/-- The first data of a node. -/
def Acc.mk₀ (mb : Bool) (its : List (ℕ × ℕ)) : Acc n := ⟨mb, its, 0, none, fun _ => none, []⟩

/-- The number that tells the neighbours the parent. -/
def pcode : Option (Option (Fin n)) → ℕ
  | some (some p) => p.val + 1
  | _ => 0

theorem pcode_le (o : Option (Option (Fin n))) : pcode o ≤ n := by
  rcases o with _ | _ | p
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact p.isLt

theorem pcode_eq {o : Option (Option (Fin n))} {w : Fin n} : pcode o = w.val + 1 ↔ o = some (some w) := by
  rcases o with _ | _ | p
  · simp [pcode]
  · simp [pcode]
  · simp only [pcode, Nat.add_right_cancel_iff, Option.some.injEq]
    exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩

/-- The inputs of the phases, read from the data. -/
def g1 (_ : Fin n) (a : Acc n) : Bool := a.mb

/-- The flood starts at the node that leads, and passes to all neighbours. -/
def g2 (v : Fin n) (a : Acc n) : Bool × (Fin n → Bool) := (decide (a.mb = true ∧ a.ldr = v.val), fun _ => true)

/-- The number for the exchange of parents. -/
def g3 (_ : Fin n) (a : Acc n) : ℕ := pcode a.fl

/-- Upwards, a node listens to its children and holds its items. -/
def g4 (v : Fin n) (a : Acc n) : MIn (Fin n) := ⟨fun u => decide (a.rc u = some (v.val + 1)), a.its⟩

/-- Downwards, a node listens to its parent, and the leader holds its stream. -/
def g5 (v : Fin n) (a : Acc n) : MIn (Fin n) :=
  ⟨fun u => decide (a.fl = some (some u)), if a.mb = true ∧ a.ldr = v.val then a.up.filterMap id else []⟩

/-- The data after a phase. -/
def up1 (_ : Fin n) (p : Acc n × ℕ) : Acc n := { p.1 with ldr := p.2 }

/-- The data after the flood. -/
def up2 (_ : Fin n) (p : Acc n × ((Fin n → Bool) × Option (Option (Fin n)))) : Acc n := { p.1 with fl := p.2.2 }

/-- The data after the exchange. -/
def up3 (_ : Fin n) (p : Acc n × (ℕ × (Fin n → Option ℕ))) : Acc n := { p.1 with rc := p.2.2 }

/-- The data after the streams up. -/
def up4 (_ : Fin n) (p : Acc n × MSt (Fin n)) : Acc n := { p.1 with up := p.2.E }

variable (n) (B : ℕ)

/-- Phase 1: the leader. -/
noncomputable def ph1 : Algorithm (Fin n) (Acc n) (Acc n × ℕ) B := ((ldrT n).bits id id B).keep g1

/-- Phase 2: the flood from the leader. -/
noncomputable def ph2 (h : 1 ≤ B) :
    Algorithm (Fin n) (Acc n) (Acc n × ((Fin n → Bool) × Option (Option (Fin n)))) B :=
  ((floodAlg (Fin n)).widen h).keep g2

/-- Phase 3: the parents to the neighbours. -/
noncomputable def ph3 : Algorithm (Fin n) (Acc n) (Acc n × (ℕ × (Fin n → Option ℕ))) B :=
  (exch (Fin n) B).keep g3

/-- Phase 4: the streams up along the children. -/
noncomputable def ph4 : Algorithm (Fin n) (Acc n) (Acc n × MSt (Fin n)) B :=
  ((mergeT (Fin n)).bits mcode mdec B).keep g4

/-- Phase 5: the stream of the leader down along the parents. -/
noncomputable def ph5 : Algorithm (Fin n) (Acc n) (MSt (Fin n)) B :=
  ((mergeT (Fin n)).bits mcode mdec B).premap g5

/-- Phases 4 and 5. -/
noncomputable def lay4 (s k : ℕ) := (ph4 n B).seq (s + k + 2) up4 (ph5 n B)

/-- Phases 3 to 5. -/
noncomputable def lay3 (s k : ℕ) := (ph3 n B).seq 1 up3 (lay4 n B s k)

/-- Phases 2 to 5. -/
noncomputable def lay2 (s k : ℕ) (h : 1 ≤ B) := (ph2 n B h).seq s up2 (lay3 n B s k)

/-- **The aggregation over one subgraph.** -/
noncomputable def perName (s k : ℕ) (h : 1 ≤ B) := (ph1 n B).seq s up1 (lay2 n B s k h)

/-- The stream of phase 5 in a state of `perName`. -/
def res {α β γ δ : Type*} : α ⊕ (β ⊕ (γ ⊕ (δ ⊕ MSt (Fin n)))) → List Elt
  | .inr (.inr (.inr (.inr m))) => m.E
  | _ => []

end Phases

section Runs

variable {n : ℕ} (B : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]

theorem ph1_run (hnB : n < 2 ^ B) (inp : Fin n → Acc n) (t : ℕ) :
    (ph1 n B).run H inp t = fun v => (inp v, (ldrT n).run H (fun v => g1 v (inp v)) t v) := by
  unfold ph1
  rw [run_keep]
  funext v
  rw [TAlg.run_bits (ldrT n) (fun _ => rfl) H _ (fun t u w _ => (ldr_le H _ t u).trans_lt hnB)]

theorem ph2_run (h : 1 ≤ B) (inp : Fin n → Acc n) (t : ℕ) :
    (ph2 n B h).run H inp t = fun v => (inp v, (floodAlg (Fin n)).run H (fun v => g2 v (inp v)) t v) := by
  unfold ph2
  rw [run_keep]
  funext v
  rw [run_widen]

theorem ph3_run (hnB : n < 2 ^ B) (inp : Fin n → Acc n) :
    (ph3 n B).run H inp 1 = fun v =>
      (inp v, (g3 v (inp v), fun u => if H.Adj u v then some (g3 u (inp u)) else none)) := by
  unfold ph3
  rw [run_keep]
  funext v
  exact congrArg _ (run_exch H (fun v => g3 v (inp v))
    (fun u => show pcode (inp u).fl < 2 ^ B from (pcode_le _).trans_lt hnB) v)

theorem ph4_run {b : ℕ} (hbB : 2 * b + 2 ≤ B) (inp : Fin n → Acc n)
    (hsrc : ∀ v u, (g4 v (inp v)).src u = true → H.Adj u v)
    (hb : ∀ v p, p ∈ (g4 v (inp v)).own → p.1 < 2 ^ b ∧ p.2 < 2 ^ b) (t : ℕ) :
    (ph4 n B).run H inp t = fun v => (inp v, (mergeT (Fin n)).run H (fun v => g4 v (inp v)) t v) := by
  unfold ph4
  rw [run_keep]
  funext v
  rw [TAlg.run_bits (mergeT (Fin n)) mdec_mcode H _ (fun t u w _ =>
    (mergeT_code H _ hsrc hb t u w).trans_le (Nat.pow_le_pow_right (by norm_num) hbB))]

theorem ph5_run {b : ℕ} (hbB : 2 * b + 2 ≤ B) (inp : Fin n → Acc n)
    (hsrc : ∀ v u, (g5 v (inp v)).src u = true → H.Adj u v)
    (hb : ∀ v p, p ∈ (g5 v (inp v)).own → p.1 < 2 ^ b ∧ p.2 < 2 ^ b) (t : ℕ) :
    (ph5 n B).run H inp t = (mergeT (Fin n)).run H (fun v => g5 v (inp v)) t := by
  unfold ph5
  rw [run_premap, TAlg.run_bits (mergeT (Fin n)) mdec_mcode H _ (fun t u w _ =>
    (mergeT_code H _ hsrc hb t u w).trans_le (Nat.pow_le_pow_right (by norm_num) hbB))]

end Runs

section PerName

variable {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
  (mb : Fin n → Bool) (its : Fin n → List (ℕ × ℕ)) (s k : ℕ)

/-- `r` is the least value of the key `κ` among the items, and `none` if there is no such item. -/
def IsMinL (its : Fin n → List (ℕ × ℕ)) (κ : ℕ) : Option ℕ → Prop
  | none => ∀ w m, (κ, m) ∉ its w
  | some m => (∃ w, (κ, m) ∈ its w) ∧ ∀ w m', (κ, m') ∈ its w → m ≤ m'

/-- The first data. -/
def d0 : Fin n → Acc n := fun v => Acc.mk₀ (mb v) (its v)

/-- The data after phase 1. -/
noncomputable def d1 : Fin n → Acc n := fun v =>
  up1 v (d0 mb its v, (ldrT n).run H (fun v => g1 v (d0 mb its v)) s v)

/-- The data after phase 2. -/
noncomputable def d2 : Fin n → Acc n := fun v =>
  up2 v (d1 H mb its s v, (floodAlg (Fin n)).run H (fun v => g2 v (d1 H mb its s v)) s v)

/-- The data after phase 3. -/
noncomputable def d3 : Fin n → Acc n := fun v =>
  up3 v (d2 H mb its s v, (g3 v (d2 H mb its s v), fun u => if H.Adj u v then some (g3 u (d2 H mb its s u)) else none))

/-- The data after phase 4. -/
noncomputable def d4 : Fin n → Acc n := fun v =>
  up4 v (d3 H mb its s v, (mergeT (Fin n)).run H (fun v => g4 v (d3 H mb its s v)) (s + k + 2) v)

theorem d3_src (v u : Fin n) (h : (g4 v (d3 H mb its s v)).src u = true) : H.Adj u v := by
  by_contra ha
  have : (d3 H mb its s v).rc u = none := by
    show (if H.Adj u v then some (g3 u (d2 H mb its s u)) else none) = none
    rw [ite_eq_right ha]
  simp [g4, this] at h

/-- The run of the aggregation over one subgraph, phase by phase. -/
theorem perName_run (hnB : n < 2 ^ B) {b : ℕ} (hbB : 2 * b + 2 ≤ B)
    (hb4 : ∀ v p, p ∈ (g4 v (d3 H mb its s v)).own → p.1 < 2 ^ b ∧ p.2 < 2 ^ b)
    (hsrc5 : ∀ v u, (g5 v (d4 H mb its s k v)).src u = true → H.Adj u v)
    (hb5 : ∀ v p, p ∈ (g5 v (d4 H mb its s k v)).own → p.1 < 2 ^ b ∧ p.2 < 2 ^ b) (t5 : ℕ) (v : Fin n) :
    (perName n B s k hB1).run H (d0 mb its) (s + (s + (1 + (s + k + 2 + t5)))) v =
      .inr (.inr (.inr (.inr ((mergeT (Fin n)).run H (fun v => g5 v (d4 H mb its s k v)) t5 v)))) := by
  have h1 := run_seq (ph1 n B) s up1 (lay2 n B s k hB1) H (d0 mb its) (s + (1 + (s + k + 2 + t5)))
  have e1 : (fun v => up1 v ((ph1 n B).run H (d0 mb its) s v)) = d1 H mb its s := by
    rw [ph1_run B H hnB]
    rfl
  rw [e1] at h1
  have h2 := run_seq (ph2 n B hB1) s up2 (lay3 n B s k) H (d1 H mb its s) (1 + (s + k + 2 + t5))
  have e2 : (fun v => up2 v ((ph2 n B hB1).run H (d1 H mb its s) s v)) = d2 H mb its s := by
    rw [ph2_run B H hB1]
    rfl
  rw [e2] at h2
  have h3 := run_seq (ph3 n B) 1 up3 (lay4 n B s k) H (d2 H mb its s) (s + k + 2 + t5)
  have e3 : (fun v => up3 v ((ph3 n B).run H (d2 H mb its s) 1 v)) = d3 H mb its s := by
    rw [ph3_run B H hnB]
    rfl
  rw [e3] at h3
  have h4 := run_seq (ph4 n B) (s + k + 2) up4 (ph5 n B) H (d3 H mb its s) t5
  have e4 : (fun v => up4 v ((ph4 n B).run H (d3 H mb its s) (s + k + 2) v)) = d4 H mb its s k := by
    rw [ph4_run B H hbB _ (d3_src H mb its s) hb4]
    rfl
  rw [e4] at h4
  have h5 := ph5_run B H hbB (d4 H mb its s k) hsrc5 hb5 t5
  show ((ph1 n B).seq s up1 (lay2 n B s k hB1)).run H (d0 mb its) (s + (s + (1 + (s + k + 2 + t5)))) v = _
  rw [h1]
  show Sum.inr (((ph2 n B hB1).seq s up2 (lay3 n B s k)).run H (d1 H mb its s) (s + (1 + (s + k + 2 + t5))) v) = _
  rw [h2]
  show Sum.inr (Sum.inr (((ph3 n B).seq 1 up3 (lay4 n B s k)).run H (d2 H mb its s) (1 + (s + k + 2 + t5)) v)) = _
  rw [h3]
  show Sum.inr (Sum.inr (Sum.inr (((ph4 n B).seq (s + k + 2) up4 (ph5 n B)).run H (d3 H mb its s) (s + k + 2 + t5) v))) = _
  rw [h4]
  show Sum.inr (Sum.inr (Sum.inr (Sum.inr ((ph5 n B).run H (d4 H mb its s k) t5 v)))) = _
  rw [h5]

/-- **One subgraph.** If the members are joined by walks of at most `s` steps, only members hold items, there
are at most `k` keys and all fields have `b` bits, then every member knows the least value of every key. -/
theorem perName_ans (hnB : n < 2 ^ B) {b : ℕ} (hbB : 2 * b + 2 ≤ B)
    (hspan : ∀ a a', mb a = true → mb a' = true → Lev H.Adj (· = a) s a')
    (hmem : ∀ v p, p ∈ its v → mb v = true)
    (hkeys : ∃ K : Finset ℕ, K.card ≤ k ∧ ∀ v p, p ∈ its v → p.1 ∈ K)
    (hfld : ∀ v p, p ∈ its v → p.1 < 2 ^ b ∧ p.2 < 2 ^ b)
    {v : Fin n} (hv : mb v = true) {t5 : ℕ} (ht5 : s + k + 2 ≤ t5) (κ : ℕ) :
    IsMinL its κ (ans (res n ((perName n B s k hB1).run H (d0 mb its)
      (s + (s + (1 + (s + k + 2 + t5)))) v)) κ) := by
  classical
  obtain ⟨K, hK, hKk⟩ := hkeys
  -- the leader
  obtain ⟨L, hL, hLle⟩ : ∃ L : Fin n, mb L = true ∧ ∀ w, mb w = true → L.val ≤ w.val :=
    ⟨_, (Finset.mem_filter.1 (Finset.min'_mem (Finset.univ.filter fun w => mb w = true)
      ⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ _, hv⟩⟩)).2,
      fun w hw => Fin.le_iff_val_le_val.1 (Finset.min'_le (Finset.univ.filter fun w => mb w = true) w
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hw⟩))⟩
  have hx : ∀ w, mb w = true → (ldrT n).run H mb s w = L.val := by
    intro w hw
    have h1 := (ldr_spec H mb s w).1 L hL (hspan L w hL hw)
    rcases (ldr_spec H mb s w).2 with h2 | ⟨w', hw', -, h2⟩
    · have := L.isLt
      omega
    · have := hLle w' hw'
      omega
  have hseed : ∀ w, (mb w = true ∧ (ldrT n).run H mb s w = w.val) ↔ w = L := by
    intro w
    constructor
    · rintro ⟨hw, h⟩
      exact Fin.ext (by rw [← h, hx w hw])
    · intro h
      rw [h]
      exact ⟨hL, hx L hL⟩
  -- the flood
  have hfi : ∀ w, ((fun w => g2 w (d1 H mb its s w)) w).1 = true ↔ w = L := by
    intro w
    rw [← hseed w]
    show decide (mb w = true ∧ (ldrT n).run H mb s w = w.val) = true ↔ _
    exact decide_eq_true_iff
  have hfa : ∀ u w, floodA H (fun w => g2 w (d1 H mb its s w)) u w ↔ H.Adj u w := fun u w =>
    ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩
  have rf := run_flood H (fun w => g2 w (d1 H mb its s w)) s
  -- `Lv t w`: reached after `t` rounds
  set Lv := Lev (floodA H (fun w => g2 w (d1 H mb its s w)))
    (fun w => ((fun w => g2 w (d1 H mb its s w)) w).1 = true) with hLv
  have hreach : ∀ w, mb w = true → Lv s w := fun w hw =>
    Lev.mono_rel (fun u w h => (hfa u w).2 h) (fun w h => (hfi w).2 h) s w (hspan L w hL hw)
  -- sources up and down
  have hfl : ∀ w, (d4 H mb its s k w).fl =
      ((floodAlg (Fin n)).run H (fun w => g2 w (d1 H mb its s w)) s w).2 := fun w => rfl
  have hsrc4 : ∀ w u, (g4 w (d3 H mb its s w)).src u = true ↔
      H.Adj u w ∧ ((floodAlg (Fin n)).run H (fun w => g2 w (d1 H mb its s w)) s u).2 = some (some w) := by
    intro w u
    constructor
    · intro h
      have ha := d3_src H mb its s w u h
      refine ⟨ha, pcode_eq.1 ?_⟩
      have : (d3 H mb its s w).rc u = some (w.val + 1) := by simpa [g4] using h
      have h' : (if H.Adj u w then some (g3 u (d2 H mb its s u)) else none) = some (w.val + 1) := this
      rw [ite_eq_left ha, Option.some.injEq] at h'
      exact h'
    · rintro ⟨ha, h⟩
      have : (d3 H mb its s w).rc u = some (w.val + 1) := by
        show (if H.Adj u w then some (g3 u (d2 H mb its s u)) else none) = some (w.val + 1)
        rw [ite_eq_left ha]
        exact congrArg some (pcode_eq.2 h)
      simp [g4, this]
  have hsrc5 : ∀ w u, (g5 w (d4 H mb its s k w)).src u = true ↔
      ((floodAlg (Fin n)).run H (fun w => g2 w (d1 H mb its s w)) s w).2 = some (some u) := by
    intro w u
    simp [g5, hfl]
  have hadj5 : ∀ w u, (g5 w (d4 H mb its s k w)).src u = true → H.Adj u w := fun w u h =>
    ((rf w).2.2.2 u ((hsrc5 w u).1 h)).1.1
  -- reached nodes lie below the leader along children, and above it along parents
  have hclo : ∀ t, t ≤ s → ∀ w, Lv t w →
      Clo (fun w => (g4 w (d3 H mb its s w)).src) L w ∧ Clo (fun w => (g5 w (d4 H mb its s k w)).src) w L := by
    intro t
    induction t with
    | zero =>
      intro _ w hw
      obtain rfl := (hfi w).1 hw
      exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
    | succ t ih =>
      intro ht w hw
      have hs : Lv s w := Lev.mono ht hw
      have hsome := (rf w).2.1.2 hs
      cases hst : ((floodAlg (Fin n)).run H (fun w => g2 w (d1 H mb its s w)) s w).2 with
      | none => rw [hst] at hsome; exact absurd hsome (by simp)
      | some o =>
        cases o with
        | none =>
          obtain rfl := (hfi w).1 ((rf w).2.2.1.1 hst)
          exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
        | some p =>
          obtain ⟨hpa, t', ht', hp, hnw⟩ := (rf w).2.2.2 p hst
          have htt : t' ≤ t := by
            by_contra hc
            exact hnw (Lev.mono (by omega) hw)
          obtain ⟨h4, h5⟩ := ih (by omega) p (Lev.mono htt hp)
          refine ⟨Relation.ReflTransGen.tail h4 ((hsrc4 p w).2 ⟨((hfa p w).1 hpa).symm, hst⟩),
            Relation.ReflTransGen.head ((hsrc5 w p).2 hst) h5⟩
  -- ranks
  have hlev_anti : ∀ {t t' : ℕ} {w}, t ≤ t' → Lv t w → Lv t' w := fun h hw => Lev.mono h hw
  have hh4 : ∀ w u, (g4 w (d3 H mb its s w)).src u = true →
      ((Finset.range (s + 1)).filter fun t => Lv t u).card <
        ((Finset.range (s + 1)).filter fun t => Lv t w).card := by
    intro w u h
    obtain ⟨-, hst⟩ := (hsrc4 w u).1 h
    obtain ⟨-, t', ht', hw, hnu⟩ := (rf u).2.2.2 w hst
    refine Finset.card_lt_card ⟨fun t ht => ?_, fun hsub => ?_⟩
    · obtain ⟨htr, hu⟩ := Finset.mem_filter.1 ht
      refine Finset.mem_filter.2 ⟨htr, ?_⟩
      have : t' < t := by
        by_contra hc
        exact hnu (hlev_anti (by omega) hu)
      exact hlev_anti this.le hw
    · have := hsub (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hw⟩)
      exact hnu (Finset.mem_filter.1 this).2
  have hh5 : ∀ w u, (g5 w (d4 H mb its s k w)).src u = true →
      ((Finset.range (s + 1)).filter fun t => ¬ Lv t u).card <
        ((Finset.range (s + 1)).filter fun t => ¬ Lv t w).card := by
    intro w u h
    obtain ⟨-, t', ht', hu, hnw⟩ := (rf w).2.2.2 u ((hsrc5 w u).1 h)
    refine Finset.card_lt_card ⟨fun t ht => ?_, fun hsub => ?_⟩
    · obtain ⟨htr, hnu⟩ := Finset.mem_filter.1 ht
      refine Finset.mem_filter.2 ⟨htr, fun hw => hnu ?_⟩
      have : t' < t := by
        by_contra hc
        exact hnw (hlev_anti (by omega) hw)
      exact hlev_anti this.le hu
    · have := hsub (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hnw⟩)
      exact (Finset.mem_filter.1 this).2 hu
  have hcard : ∀ (P : ℕ → Prop) [DecidablePred P], ((Finset.range (s + 1)).filter P).card ≤ s + 1 :=
    fun P _ => (Finset.card_filter_le _ _).trans (Finset.card_range _).le
  -- phase 4 at the leader
  have hR4 := mergeT_rec H (fun w => g4 w (d3 H mb its s w)) (d3_src H mb its s)
  have hCI4 : ∀ p, p ∈ CI (fun w => (g4 w (d3 H mb its s w)).own) (fun w => (g4 w (d3 H mb its s w)).src) L ↔
      ∃ w, p ∈ its w := by
    intro p
    rw [mem_CI]
    constructor
    · rintro ⟨w, -, hw⟩
      exact ⟨w, hw⟩
    · rintro ⟨w, hw⟩
      exact ⟨w, (hclo s le_rfl w (hreach w (hmem w p hw))).1, hw⟩
  have hK4 : keysC (fun w => (g4 w (d3 H mb its s w)).own) (fun w => (g4 w (d3 H mb its s w)).src) L ⊆ K := by
    intro κ' hκ'
    obtain ⟨m, hm⟩ := mem_keysC.1 hκ'
    obtain ⟨w, hw⟩ := (hCI4 _).1 hm
    exact hKk w _ hw
  have hF4 := stream_full hR4 _ hh4 (t := s + k + 2) (v := L)
    (by have := hcard (fun t => Lv t L); have := Finset.card_le_card hK4; omega)
  -- the items of phase 5
  have hown5 : ∀ w, (g5 w (d4 H mb its s k w)).own =
      if w = L then (((mergeT (Fin n)).run H (fun w => g4 w (d3 H mb its s w)) (s + k + 2) w).E).filterMap id
      else [] := by
    intro w
    show (if mb w = true ∧ (ldrT n).run H mb s w = w.val then _ else _) = _
    by_cases hw : w = L
    · rw [ite_eq_left ((hseed w).2 hw), ite_eq_left hw]
      rfl
    · rw [ite_eq_right (fun h => hw ((hseed w).1 h)), ite_eq_right hw]
  have hI4 := streamInv hR4 (s + k + 2)
  have hb5 : ∀ w p, p ∈ (g5 w (d4 H mb its s k w)).own → p.1 < 2 ^ b ∧ p.2 < 2 ^ b := by
    intro w p hp
    rw [hown5] at hp
    by_cases hw : w = L
    · rw [ite_eq_left hw] at hp
      obtain ⟨e, he, hep⟩ := List.mem_filterMap.1 hp
      rcases hI4.1 w e he with h1 | ⟨κ', hκ', h2⟩
      · rw [h1] at hep; exact absurd hep (by simp)
      · rw [h2] at hep
        simp only [id, Option.some.injEq] at hep
        subst hep
        obtain ⟨w', -, hw'⟩ := mem_CI.1 (minCl_mem hκ')
        exact hfld w' _ hw'
    · rw [ite_eq_right hw] at hp
      exact absurd hp (by simp)
  have hb4 : ∀ w p, p ∈ (g4 w (d3 H mb its s w)).own → p.1 < 2 ^ b ∧ p.2 < 2 ^ b := fun w p hp =>
    hfld w p hp
  rw [perName_run B hB1 H mb its s k hnB hbB hb4 hadj5 hb5 t5 v]
  show IsMinL its κ (ans ((mergeT (Fin n)).run H (fun v => g5 v (d4 H mb its s k v)) t5 v).E κ)
  -- phase 5 at `v`
  have hR5 := mergeT_rec H (fun w => g5 w (d4 H mb its s k w)) hadj5
  have hCI5 : ∀ p, p ∈ CI (fun w => (g5 w (d4 H mb its s k w)).own) (fun w => (g5 w (d4 H mb its s k w)).src) v ↔
      some p ∈ ((mergeT (Fin n)).run H (fun w => g4 w (d3 H mb its s w)) (s + k + 2) L).E := by
    intro p
    rw [mem_CI]
    constructor
    · rintro ⟨w, -, hw⟩
      rw [hown5] at hw
      by_cases hwL : w = L
      · subst hwL
        rw [ite_eq_left rfl] at hw
        obtain ⟨e, he, hep⟩ := List.mem_filterMap.1 hw
        simp only [id] at hep
        rw [← hep]
        exact he
      · rw [ite_eq_right hwL] at hw
        exact absurd hw (by simp)
    · intro hp
      refine ⟨L, (hclo s le_rfl v (hreach v hv)).2, ?_⟩
      rw [hown5, ite_eq_left rfl]
      exact List.mem_filterMap.2 ⟨_, hp, rfl⟩
  have hK5 : keysC (fun w => (g5 w (d4 H mb its s k w)).own) (fun w => (g5 w (d4 H mb its s k w)).src) v ⊆
      K := by
    intro κ' hκ'
    obtain ⟨m, hm⟩ := mem_keysC.1 hκ'
    rcases hI4.1 L _ ((hCI5 _).1 hm) with h1 | ⟨κ'', hκ'', h2⟩
    · exact absurd h1 (by simp)
    · simp only [Option.some.injEq, Prod.mk.injEq] at h2
      rw [h2.1]
      exact hK4 hκ''
  have hF5 := stream_full hR5 _ hh5 (t := t5) (v := v)
    (by have := hcard (fun t => ¬ Lv t v); have := Finset.card_le_card hK5; omega)
  rw [ans_eq hF5.2.1 hF5.2.2 κ]
  by_cases hκ : κ ∈ keysC (fun w => (g5 w (d4 H mb its s k w)).own) (fun w => (g5 w (d4 H mb its s k w)).src) v
  · rw [ite_eq_left hκ]
    have hm5 := (hCI5 _).1 (minCl_mem hκ)
    rcases hI4.1 L _ hm5 with h1 | ⟨κ'', hκ'', h2⟩
    · exact absurd h1 (by simp)
    · simp only [Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, h2⟩ := h2
      rw [h2]
      refine ⟨(hCI4 _).1 (minCl_mem hκ''), fun w m' hm' => minCl_le ((hCI4 _).2 ⟨w, hm'⟩)⟩
  · rw [ite_eq_right hκ]
    intro w m hm
    have hk4 : κ ∈ keysC (fun w => (g4 w (d3 H mb its s w)).own) (fun w => (g4 w (d3 H mb its s w)).src) L :=
      mem_keysC.2 ⟨m, (hCI4 _).2 ⟨w, hm⟩⟩
    exact hκ (mem_keysC.2 ⟨_, (hCI5 _).2 (hF4.2.1 κ hk4)⟩)

end PerName

section Box

variable {n : ℕ}

/-- The items of the subgraph `x` at a node: key and value. -/
def itsAt (i : AggIn (Fin n)) (x : ℕ) : List (ℕ × ℕ) := (i.items.filter fun t => t.1 = x).map fun t => t.2

theorem mem_itsAt {i : AggIn (Fin n)} {x : ℕ} {p : ℕ × ℕ} : p ∈ itsAt i x ↔ (x, p.1, p.2) ∈ i.items := by
  simp only [itsAt, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨x', p'⟩, ⟨h, rfl⟩, rfl⟩
    exact h
  · intro h
    exact ⟨(x, p), ⟨h, rfl⟩, rfl⟩

/-- The first data of the run of the subgraph `x`. -/
def accOf (i : AggIn (Fin n)) (x : ℕ) : Acc n := Acc.mk₀ (decide (x ∈ i.member)) (itsAt i x)

/-- The values of the items of the subgraph `x` with the key `κ` at a node. -/
def locSet (i : AggIn (Fin n)) (x κ : ℕ) : Finset ℕ :=
  ((i.items.filter fun t => t.1 = x ∧ t.2.1 = κ).map fun t => t.2.2).toFinset

theorem mem_locSet {i : AggIn (Fin n)} {x κ a : ℕ} : a ∈ locSet i x κ ↔ (x, κ, a) ∈ i.items := by
  simp only [locSet, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨x', κ', a'⟩, ⟨h, rfl, rfl⟩, rfl⟩
    exact h
  · intro h
    exact ⟨(x, κ, a), ⟨h, rfl, rfl⟩, rfl⟩

/-- The least value of the items of the subgraph `x` with the key `κ` at a node. -/
noncomputable def localMin (i : AggIn (Fin n)) (x κ : ℕ) : Option ℕ :=
  if h : (locSet i x κ).Nonempty then some ((locSet i x κ).min' h) else none

/-- The smaller of two optional values. -/
def minO : Option ℕ → Option ℕ → Option ℕ
  | none, r => r
  | some a, none => some a
  | some a, some m => some (min a m)

/-- The output: the smaller of the local least value and the value of the stream of phase 5. -/
noncomputable def aggOut {α β γ δ : Type} {B : ℕ} (_ : Fin n)
    (st : AggIn (Fin n) × MuxSt (Fin n) (α ⊕ (β ⊕ (γ ⊕ (δ ⊕ MSt (Fin n))))) B) (x κ : ℕ) : Option ℕ :=
  minO (localMin st.1 x κ) (ans (res n (st.2.comp x)) κ)

theorem isMin_minO {inp : Fin n → AggIn (Fin n)} {x κ : ℕ} {r : Option ℕ} (v : Fin n)
    (h : AggIn.IsMin inp x κ r) : AggIn.IsMin inp x κ (minO (localMin (inp v) x κ) r) := by
  unfold localMin
  by_cases hne : (locSet (inp v) x κ).Nonempty
  · rw [dite_eq_left hne]
    have hmem := mem_locSet.1 (Finset.min'_mem _ hne)
    rcases r with _ | m
    · exact absurd hmem (h v _)
    · obtain ⟨⟨w, hw⟩, hle⟩ := h
      have := hle v _ hmem
      show AggIn.IsMin inp x κ (some (min _ m))
      rw [min_eq_right this]
      exact ⟨⟨w, hw⟩, hle⟩
  · rw [dite_eq_right hne]
    exact h

theorem isMinL_iff {inp : Fin n → AggIn (Fin n)} {x κ : ℕ} {r : Option ℕ} :
    IsMinL (fun w => itsAt (inp w) x) κ r ↔ AggIn.IsMin inp x κ r := by
  rcases r with _ | m
  · exact ⟨fun h w m hm => h w m (mem_itsAt.2 hm), fun h w m hm => h w m (mem_itsAt.1 hm)⟩
  · exact ⟨fun ⟨⟨w, hw⟩, hl⟩ => ⟨⟨w, mem_itsAt.1 hw⟩, fun w m' hm => hl w m' (mem_itsAt.2 hm)⟩,
      fun ⟨⟨w, hw⟩, hl⟩ => ⟨⟨w, mem_itsAt.2 hw⟩, fun w m' hm => hl w m' (mem_itsAt.1 hm)⟩⟩

theorem res_init (B s k : ℕ) (h : 1 ≤ B) (v : Fin n) (a : Acc n) :
    res n ((perName n B s k h).init v a) = [] := by
  by_cases hs : s = 0
  · simp [perName, lay2, lay3, Algorithm.seq, hs, res]
  · simp [perName, Algorithm.seq, hs, res]

/-- **Aggregation**, in the message model, with the constant `5`. -/
theorem aggBox : AggBox := by
  refine ⟨5, fun n s c k b => ?_⟩
  have hlog : 1 ≤ logN n := Nat.le_add_left 1 _
  have hnB : n < 2 ^ (5 * (b + logN n)) := by
    have h1 : n + 2 < 2 ^ logN n := Nat.lt_pow_succ_log_self (by norm_num) _
    have h2 : 2 ^ logN n ≤ 2 ^ (5 * (b + logN n)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hbB : 2 * b + 2 ≤ 5 * (b + logN n) := by omega
  have hB1 : 1 ≤ 5 * (b + logN n) := by omega
  refine ⟨_, mux (perName n (5 * (b + logN n)) s k hB1) c (fun i w => i.subgraphs w) accOf, aggOut, ?_⟩
  intro N inp hV v x hx κ
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · -- No edge lies in a subgraph, so `v` is the only member of `x`.
    have hone : ∀ w m, (x, κ, m) ∈ (inp w).items → w = v := by
      intro w m hm
      obtain ⟨p, -⟩ := hV.span x v w hx (hV.items_member w _ hm)
      cases p with
      | nil => rfl
      | cons e _ =>
        have := hV.congestion _ _ e.1
        rw [Nat.le_zero, List.length_eq_zero_iff] at this
        exact absurd e.2 (by rw [this]; simp)
    rw [show 5 * 0 * (s + k + 1) = 0 by ring]
    show AggIn.IsMin inp x κ (minO (localMin (inp v) x κ)
      (ans (res n ((perName n (5 * (b + logN n)) s k hB1).init v (accOf (inp v) x))) κ))
    rw [res_init]
    unfold localMin
    by_cases hne : (locSet (inp v) x κ).Nonempty
    · rw [dite_eq_left hne]
      refine ⟨⟨v, mem_locSet.1 (Finset.min'_mem _ hne)⟩, fun w m' hm => ?_⟩
      obtain rfl := hone w m' hm
      exact Finset.min'_le _ _ (mem_locSet.2 hm)
    · rw [dite_eq_right hne]
      intro w m hm
      obtain rfl := hone w m hm
      exact hne ⟨m, mem_locSet.2 hm⟩
  · have ht : 5 * c * (s + k + 1) = c * (s + (s + (1 + (s + k + 2 + (2 * s + 4 * k + 2))))) := by ring
    rw [ht, run_mux hc (fun u w h x => hV.symm u w h x)
      (fun u w h => (length_slots_le _).trans (hV.congestion u w h))]
    show AggIn.IsMin inp x κ (minO (localMin (inp v) x κ) (ans (res n
      ((perName n (5 * (b + logN n)) s k hB1).run (muxG (fun i w => i.subgraphs w) N.G inp x)
        (d0 (fun w => decide (x ∈ (inp w).member)) (fun w => itsAt (inp w) x))
        (s + (s + (1 + (s + k + 2 + (2 * s + 4 * k + 2))))) v)) κ))
    refine isMin_minO v (isMinL_iff.1 ?_)
    obtain ⟨K, hK, hKk⟩ := hV.keys x
    refine perName_ans (5 * (b + logN n)) hB1 _ _ _ s k hnB hbB ?_ ?_ ⟨K, hK, ?_⟩ ?_
      (by simpa using hx) (by omega) κ
    · intro a a' ha ha'
      obtain ⟨p, hp⟩ := hV.span x a a' (by simpa using ha) (by simpa using ha')
      have := Lev.walk (A := (muxG (fun i w => i.subgraphs w) N.G inp x).Adj) (seed := (· = a))
        (fun u w h => ⟨h.1, h.2, (hV.symm u w h.1 x).1 h.2⟩) p 0 rfl
      exact Lev.mono (by omega) this
    · intro w p hp
      simpa using hV.items_member w _ (mem_itsAt.1 hp)
    · intro w p hp
      exact hKk w _ (mem_itsAt.1 hp) rfl
    · intro w p hp
      have := hV.fields w _ (mem_itsAt.1 hp)
      exact ⟨this.2.1, this.2.2⟩

end Box

end SsspFlow.Congest
