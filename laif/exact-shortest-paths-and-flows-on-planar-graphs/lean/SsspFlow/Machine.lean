import SsspFlow.Congest

/-!
# A machine of phases

A program of phases runs on all nodes. In each phase the nodes run one of three algorithms for a number of
rounds, with inputs read from their memory, and write the result into the entry of the phase in their memory
(`mach`). Older entries stay unchanged (`mem_stable`), so the correctness of each phase is a separate statement
about its entry (`mem_agg`, `mem_relax`, `mem_face`). One of the three algorithms is a universal relaxation
(`relaxAlg`), whose state is a function on numbers.
-/

set_option autoImplicit false

namespace Cslib.Congest.Algorithm

variable {V I₁ I₂ J σ₁ σ₂ : Type*} {B : ℕ}

/-- The first or the second algorithm, by the kind of the input. -/
def alt (A₁ : Algorithm V I₁ σ₁ B) (A₂ : Algorithm V I₂ σ₂ B) :
    Algorithm V (I₁ ⊕ I₂) (σ₁ ⊕ σ₂) B where
  init v i := Sum.elim (fun i => .inl (A₁.init v i)) (fun i => .inr (A₂.init v i)) i
  send v s w := Sum.elim (fun s => A₁.send v s w) (fun s => A₂.send v s w) s
  step v s m := Sum.elim (fun s => .inl (A₁.step v s m)) (fun s => .inr (A₂.step v s m)) s
  out v s := Sum.elim (A₁.out v) (A₂.out v) s

section Alt

variable (A₁ : Algorithm V I₁ σ₁ B) (A₂ : Algorithm V I₂ σ₂ B) (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_alt_inl (inp : V → I₁) : ∀ t, (alt A₁ A₂).run G (fun v => .inl (inp v)) t =
    fun v => .inl (A₁.run G inp t v)
  | 0 => rfl
  | t + 1 => by
    funext v
    show (alt A₁ A₂).step v ((alt A₁ A₂).run G (fun v => .inl (inp v)) t v) (fun w => if G.Adj w v then
      some ((alt A₁ A₂).send w ((alt A₁ A₂).run G (fun v => .inl (inp v)) t w) v) else none) = _
    rw [run_alt_inl inp t]
    rfl

theorem run_alt_inr (inp : V → I₂) : ∀ t, (alt A₁ A₂).run G (fun v => .inr (inp v)) t =
    fun v => .inr (A₂.run G inp t v)
  | 0 => rfl
  | t + 1 => by
    funext v
    show (alt A₁ A₂).step v ((alt A₁ A₂).run G (fun v => .inr (inp v)) t v) (fun w => if G.Adj w v then
      some ((alt A₁ A₂).send w ((alt A₁ A₂).run G (fun v => .inr (inp v)) t w) v) else none) = _
    rw [run_alt_inr inp t]
    rfl

end Alt

/-- The same algorithm with inputs mapped first. -/
def premap (A : Algorithm V J σ₁ B) (f : V → I₁ → J) : Algorithm V I₁ σ₁ B where
  init v i := A.init v (f v i)
  send := A.send
  step := A.step
  out := A.out

theorem run_premap (A : Algorithm V J σ₁ B) (f : V → I₁ → J) (G : SimpleGraph V) [DecidableRel G.Adj]
    (inp : V → I₁) : ∀ t, (A.premap f).run G inp t = A.run G (fun v => f v (inp v)) t
  | 0 => rfl
  | t + 1 => by
    funext v
    show A.step v ((A.premap f).run G inp t v) (fun w => if G.Adj w v then
      some (A.send w ((A.premap f).run G inp t w) v) else none) = _
    rw [run_premap A f G inp t]
    rfl

/-- The input of a relaxation: the first state, the message to each neighbour from a state, and the next state
from a state and the numbers received. -/
structure RelaxIn (V : Type*) where
  init : ℕ → ℕ
  msg : (ℕ → ℕ) → V → ℕ
  upd : (ℕ → ℕ) → (V → Option ℕ) → ℕ → ℕ

/-- **The universal relaxation.** -/
noncomputable def relaxAlg (V : Type*) (B : ℕ) : Algorithm V (RelaxIn V) (RelaxIn V × (ℕ → ℕ)) B where
  init _ r := (r, r.init)
  send _ s w := toMsg B (s.1.msg s.2 w)
  step _ s m := (s.1, s.1.upd s.2 (fun u => (m u).map ofMsg))
  out _ _ := true

/-- The states of the relaxation. -/
noncomputable def relaxSt (B : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] (inp : V → RelaxIn V) :
    ℕ → V → ℕ → ℕ
  | 0 => fun v => (inp v).init
  | t + 1 => fun v => (inp v).upd (relaxSt B G inp t v) fun u =>
      if G.Adj u v then some (ofMsg (toMsg B ((inp u).msg (relaxSt B G inp t u) v))) else none

theorem run_relax (G : SimpleGraph V) [DecidableRel G.Adj] (inp : V → RelaxIn V) :
    ∀ t, (relaxAlg V B).run G inp t = fun v => (inp v, relaxSt B G inp t v)
  | 0 => rfl
  | t + 1 => by
    funext v
    show (relaxAlg V B).step v ((relaxAlg V B).run G inp t v) (fun w => if G.Adj w v then
      some ((relaxAlg V B).send w ((relaxAlg V B).run G inp t w) v) else none) = _
    rw [run_relax G inp t]
    show (inp v, (inp v).upd (relaxSt B G inp t v) fun u =>
      Option.map ofMsg (if G.Adj u v then some (toMsg B ((inp u).msg (relaxSt B G inp t u) v)) else none)) = _
    congr 2
    funext u
    split_ifs <;> rfl

/-- The numbers received in a round of the relaxation, if they fit into `B` bits. -/
theorem relaxSt_succ (G : SimpleGraph V) [DecidableRel G.Adj] (inp : V → RelaxIn V) (t : ℕ) (v : V) :
    relaxSt B G inp (t + 1) v = (inp v).upd (relaxSt B G inp t v) fun u =>
      if G.Adj u v then some (ofMsg (toMsg B ((inp u).msg (relaxSt B G inp t u) v))) else none :=
  rfl

/-- The memory of a node: the entry of a phase is a function on numbers. -/
abbrev Mem := ℕ → ℕ → ℕ

section Machine

variable {L Ia If σa σf : Type*}

/-- The body of a phase. -/
noncomputable def bodyAlg (Aa : Algorithm V Ia σa B) (Af : Algorithm V If σf B) (Ta Tr Tf : ℕ) :
    Algorithm V (Ia ⊕ RelaxIn V ⊕ If)
      ((ℕ × σa) ⊕ (ℕ × (RelaxIn V × (ℕ → ℕ))) ⊕ (ℕ × σf)) B :=
  alt (Aa.stopAt Ta) (alt ((relaxAlg V B).stopAt Tr) (Af.stopAt Tf))

/-- The result of a phase. -/
def resOf (resA : V → σa → ℕ → ℕ) (resF : V → σf → ℕ → ℕ) (v : V) :
    (ℕ × σa) ⊕ (ℕ × (RelaxIn V × (ℕ → ℕ))) ⊕ (ℕ × σf) → ℕ → ℕ
  | .inl s => resA v s.2
  | .inr (.inl s) => s.2.2
  | .inr (.inr s) => resF v s.2

/-- **The machine.** -/
noncomputable def mach (Aa : Algorithm V Ia σa B) (Af : Algorithm V If σf B) (Ta Tr Tf T : ℕ)
    (prog : ℕ → V → L → Mem → Ia ⊕ RelaxIn V ⊕ If) (resA : V → σa → ℕ → ℕ)
    (resF : V → σf → ℕ → ℕ) :=
  (bodyAlg Aa Af Ta Tr Tf).iter T (fun v (j : L × ℕ × Mem) => prog j.2.1 v j.1 j.2.2)
    (fun v j s => (j.1, j.2.1 + 1, Function.update j.2.2 j.2.1 (resOf resA resF v s)))

variable (Aa : Algorithm V Ia σa B) (Af : Algorithm V If σf B) (Ta Tr Tf T : ℕ)
  (prog : ℕ → V → L → Mem → Ia ⊕ RelaxIn V ⊕ If) (resA : V → σa → ℕ → ℕ) (resF : V → σf → ℕ → ℕ)
  (G : SimpleGraph V) [DecidableRel G.Adj] (inp : V → L)

/-- The data of the machine after `k` phases. -/
noncomputable def machData (k : ℕ) (v : V) : L × ℕ × Mem :=
  iterData (bodyAlg Aa Af Ta Tr Tf) T (fun v (j : L × ℕ × Mem) => prog j.2.1 v j.1 j.2.2)
    (fun v j s => (j.1, j.2.1 + 1, Function.update j.2.2 j.2.1 (resOf resA resF v s)))
    G (fun v => (inp v, 0, fun _ _ => 0)) k v

/-- The memory of a node after `k` phases. -/
noncomputable def memAt (k : ℕ) (v : V) : Mem := (machData Aa Af Ta Tr Tf T prog resA resF G inp k v).2.2

theorem data_succ (k : ℕ) (v : V) :
    machData Aa Af Ta Tr Tf T prog resA resF G inp (k + 1) v =
      ((machData Aa Af Ta Tr Tf T prog resA resF G inp k v).1,
       (machData Aa Af Ta Tr Tf T prog resA resF G inp k v).2.1 + 1,
       Function.update (machData Aa Af Ta Tr Tf T prog resA resF G inp k v).2.2
         (machData Aa Af Ta Tr Tf T prog resA resF G inp k v).2.1
         (resOf resA resF v ((bodyAlg Aa Af Ta Tr Tf).run G
           (fun w => prog (machData Aa Af Ta Tr Tf T prog resA resF G inp k w).2.1 w
             (machData Aa Af Ta Tr Tf T prog resA resF G inp k w).1
             (machData Aa Af Ta Tr Tf T prog resA resF G inp k w).2.2) T v))) :=
  rfl

theorem data_fst : ∀ (k : ℕ) (v : V), (machData Aa Af Ta Tr Tf T prog resA resF G inp k v).1 = inp v
  | 0, _ => rfl
  | k + 1, v => by
    rw [data_succ]
    exact data_fst k v

theorem data_phase : ∀ (k : ℕ) (v : V), (machData Aa Af Ta Tr Tf T prog resA resF G inp k v).2.1 = k
  | 0, _ => rfl
  | k + 1, v => by
    rw [data_succ]
    show (machData Aa Af Ta Tr Tf T prog resA resF G inp k v).2.1 + 1 = k + 1
    rw [data_phase k v]

/-- The memory after one more phase. -/
theorem memAt_succ (k : ℕ) (v : V) :
    memAt Aa Af Ta Tr Tf T prog resA resF G inp (k + 1) v =
      Function.update (memAt Aa Af Ta Tr Tf T prog resA resF G inp k v) k
        (resOf resA resF v ((bodyAlg Aa Af Ta Tr Tf).run G
          (fun w => prog k w (inp w) (memAt Aa Af Ta Tr Tf T prog resA resF G inp k w)) T v)) := by
  unfold memAt
  rw [data_succ]
  show Function.update _ (machData Aa Af Ta Tr Tf T prog resA resF G inp k v).2.1 _ = _
  rw [data_phase]
  congr 3
  funext w
  rw [data_phase, data_fst]

/-- **Older entries of the memory stay unchanged.** -/
theorem mem_stable {j k : ℕ} (h : j < k) (v : V) :
    memAt Aa Af Ta Tr Tf T prog resA resF G inp k v j =
      memAt Aa Af Ta Tr Tf T prog resA resF G inp (j + 1) v j := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk : j = k
    · rw [hk]
    · rw [memAt_succ, Function.update_of_ne hk]
      exact ih (by omega)

/-- **The entry of a phase of the first kind.** -/
theorem mem_agg {k : ℕ} (ia : V → Ia)
    (h : ∀ w, prog k w (inp w) (memAt Aa Af Ta Tr Tf T prog resA resF G inp k w) = .inl (ia w))
    (hT : Ta ≤ T) (v : V) :
    memAt Aa Af Ta Tr Tf T prog resA resF G inp (k + 1) v k = resA v (Aa.run G ia Ta v) := by
  rw [memAt_succ, Function.update_self]
  have hfun : (fun w => prog k w (inp w) (memAt Aa Af Ta Tr Tf T prog resA resF G inp k w)) =
      fun w => (.inl (ia w) : Ia ⊕ RelaxIn V ⊕ If) := funext h
  rw [hfun]
  unfold bodyAlg
  rw [run_alt_inl, run_stopAt]
  show resA v (Aa.run G ia (min T Ta) v) = _
  rw [min_eq_right hT]

/-- **The entry of a phase of the second kind.** -/
theorem mem_relax {k : ℕ} (ir : V → RelaxIn V)
    (h : ∀ w, prog k w (inp w) (memAt Aa Af Ta Tr Tf T prog resA resF G inp k w) = .inr (.inl (ir w)))
    (hT : Tr ≤ T) (v : V) :
    memAt Aa Af Ta Tr Tf T prog resA resF G inp (k + 1) v k = relaxSt B G ir Tr v := by
  rw [memAt_succ, Function.update_self]
  have hfun : (fun w => prog k w (inp w) (memAt Aa Af Ta Tr Tf T prog resA resF G inp k w)) =
      fun w => (.inr (.inl (ir w)) : Ia ⊕ RelaxIn V ⊕ If) := funext h
  rw [hfun]
  unfold bodyAlg
  rw [run_alt_inr _ _ G (fun w => (.inl (ir w) : RelaxIn V ⊕ If)), run_alt_inl, run_stopAt, run_relax]
  show relaxSt B G ir (min T Tr) v = _
  rw [min_eq_right hT]

/-- **The entry of a phase of the third kind.** -/
theorem mem_face {k : ℕ} (ifc : V → If)
    (h : ∀ w, prog k w (inp w) (memAt Aa Af Ta Tr Tf T prog resA resF G inp k w) = .inr (.inr (ifc w)))
    (hT : Tf ≤ T) (v : V) :
    memAt Aa Af Ta Tr Tf T prog resA resF G inp (k + 1) v k = resF v (Af.run G ifc Tf v) := by
  rw [memAt_succ, Function.update_self]
  have hfun : (fun w => prog k w (inp w) (memAt Aa Af Ta Tr Tf T prog resA resF G inp k w)) =
      fun w => (.inr (.inr (ifc w)) : Ia ⊕ RelaxIn V ⊕ If) := funext h
  rw [hfun]
  unfold bodyAlg
  rw [run_alt_inr _ _ G (fun w => (.inr (ifc w) : RelaxIn V ⊕ If)), run_alt_inr, run_stopAt]
  show resF v (Af.run G ifc (min T Tf) v) = _
  rw [min_eq_right hT]

/-- **The whole run of the machine.** It reads the memory after all phases. -/
theorem run_mach (hT : 0 < T) (K : ℕ) (v : V) :
    ((mach Aa Af Ta Tr Tf T prog resA resF).run G (fun v => (inp v, 0, fun _ _ => 0)) (K * T) v).1.2.2 =
      memAt Aa Af Ta Tr Tf T prog resA resF G inp K v := by
  have h := run_iter (bodyAlg Aa Af Ta Tr Tf) (T := T)
    (fun v (j : L × ℕ × Mem) => prog j.2.1 v j.1 j.2.2)
    (fun v j s => (j.1, j.2.1 + 1, Function.update j.2.2 j.2.1 (resOf resA resF v s)))
    G (fun v => (inp v, 0, fun _ _ => 0)) hT K 0 hT
  rw [Nat.add_zero] at h
  unfold mach memAt machData
  rw [h]

end Machine

end Cslib.Congest.Algorithm
