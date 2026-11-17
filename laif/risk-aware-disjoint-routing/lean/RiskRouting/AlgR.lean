import Mathlib

/-!
# The enumeration algorithm (Algorithm R)

- `lower_bound`: every feasible pair satisfies `F(P₁, P₂) ≥ c'(P₁) + L` (used in Theorem 3),
  for link lists of the two paths, a lower bound `p₀ ≤ p(e, f)` and the hop distances `h₁, h₂`.
- `run`: the loop of Algorithm R over candidates `Q₁, Q₂, …` sorted by `c'`, with the stopping rule
  `c'(Qᵢ) + L ≥ best`, and counters for the candidates evaluated and the stopping tests reached.
  The value of a candidate is the cost of its best partner (`⊤` if it has none), which the shortest
  path step of line `l:sp` computes.
- `run_best`, `run_answer`: the loop returns the optimum, with a candidate attaining it, and none
  if no candidate has a partner.
- `run_count`: at most `N` candidates are evaluated and at most `N + 1` stopping tests are reached,
  where `N` counts the candidates with `c'(Q) + L ≤ OPT` (all candidates if `OPT = ⊤`), with ties
  in any order.
- `algR_exact`: the same for candidates with finite sets of partners and the cost `F`.
-/

namespace RiskRouting.AlgR

open List

/-! ## The lower bound -/

/-- **Lemma.** With `p ≥ p₀ ≥ 0`, `B ≥ 0`, `|P₁| ≥ h₁`, `|P₂| ≥ h₂`, and
`L ≤ c(P₂) + B p₀ h₁ |P₂| - B p₀ h₁ h₂`, the cost of the pair is at least
`c'(P₁) + L` with `c'(e) = c(e) + B p₀ h₂`. -/
theorem lower_bound {E : Type*} (c : E → ℚ) (p : E → E → ℚ) {B p₀ : ℚ} (hB : 0 ≤ B)
    (hp₀ : 0 ≤ p₀) (hp : ∀ e f, p₀ ≤ p e f) (E₁ E₂ : List E) {h₁ h₂ : ℕ}
    (hE₁ : h₁ ≤ E₁.length) (hE₂ : h₂ ≤ E₂.length) {L : ℚ}
    (hL : L ≤ (E₂.map c).sum + B * p₀ * h₁ * E₂.length - B * p₀ * h₁ * h₂) :
    (E₁.map fun e => c e + B * p₀ * h₂).sum + L ≤
      (E₁.map c).sum + (E₂.map c).sum + B * (E₁.map fun e => (E₂.map (p e)).sum).sum := by
  have hrisk : p₀ * E₁.length * E₂.length ≤ (E₁.map fun e => (E₂.map (p e)).sum).sum := by
    have h1 : ∀ e, p₀ * E₂.length ≤ (E₂.map (p e)).sum := by
      intro e
      have := List.sum_le_sum (l := E₂) (f := fun _ => p₀) (g := p e) (fun f _ => hp e f)
      simpa [mul_comm] using this
    have := List.sum_le_sum (l := E₁) (f := fun _ => p₀ * E₂.length)
      (g := fun e => (E₂.map (p e)).sum) (fun e _ => h1 e)
    simp at this
    linarith
  have hprod : (h₂ : ℚ) * E₁.length + h₁ * E₂.length - h₁ * h₂ ≤ (E₁.length : ℚ) * E₂.length := by
    have a : (h₁ : ℚ) ≤ E₁.length := by exact_mod_cast hE₁
    have b : (h₂ : ℚ) ≤ E₂.length := by exact_mod_cast hE₂
    nlinarith
  have hc' : (E₁.map fun e => c e + B * p₀ * h₂).sum = (E₁.map c).sum + B * p₀ * h₂ * E₁.length := by
    rw [List.sum_map_add]; simp [mul_comm]
  rw [hc']
  have hBp : 0 ≤ B * p₀ := mul_nonneg hB hp₀
  have := mul_le_mul_of_nonneg_left hprod hBp
  have := mul_le_mul_of_nonneg_left hrisk hB
  nlinarith

/-! ## The loop -/

variable {α : Type*} (key : α → ℚ) (val : α → WithTop ℚ) (L : ℚ)

/-- State of the loop: `best`, `answer`, candidates evaluated, stopping tests reached. -/
structure St (α : Type*) where
  best : WithTop ℚ
  ans : Option α
  evals : ℕ
  checks : ℕ

/-- The loop of Algorithm R. -/
def run : List α → St α → St α
  | [], st => st
  | q :: qs, st =>
    if st.best ≤ ((key q + L : ℚ) : WithTop ℚ) then { st with checks := st.checks + 1 }
    else
      run qs (if val q < st.best then ⟨val q, some q, st.evals + 1, st.checks + 1⟩
        else { st with evals := st.evals + 1, checks := st.checks + 1 })

/-- The initial state. -/
def init : St α := ⟨⊤, none, 0, 0⟩

/-- The optimum over a list of candidates. -/
def opt (qs : List α) : WithTop ℚ := qs.foldr (fun q m => min (val q) m) ⊤

variable {key val L}

/-- Sorted by `c'`, ties in any order. -/
def KeySorted (key : α → ℚ) (qs : List α) : Prop := qs.Pairwise fun a b => key a ≤ key b

theorem opt_ge {qs : List α} {x : WithTop ℚ} (h : ∀ q ∈ qs, x ≤ val q) : x ≤ opt val qs := by
  induction qs with
  | nil => simp [opt]
  | cons q qs ih =>
    simp only [opt, foldr_cons] at ih ⊢
    exact le_min (h q (by simp)) (ih fun q' hq' => h q' (by simp [hq']))

theorem opt_le {qs : List α} {q : α} (hq : q ∈ qs) : opt val qs ≤ val q := by
  induction qs with
  | nil => simp at hq
  | cons a qs ih =>
    simp only [opt, foldr_cons] at ih ⊢
    rcases List.mem_cons.mp hq with rfl | hq
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hq)

theorem opt_attained {qs : List α} (h : opt val qs ≠ ⊤) : ∃ q ∈ qs, val q = opt val qs := by
  induction qs with
  | nil => simp [opt] at h
  | cons a qs ih =>
    change min (val a) (opt val qs) ≠ ⊤ at h
    show ∃ q ∈ a :: qs, val q = min (val a) (opt val qs)
    rcases le_total (val a) (opt val qs) with h1 | h1
    · exact ⟨a, by simp, (min_eq_left h1).symm⟩
    · rw [min_eq_right h1] at h ⊢
      obtain ⟨q, hq, e⟩ := ih h
      exact ⟨q, by simp [hq], e⟩

/-- A candidate sorted first is cheap against the rest. -/
theorem key_le_opt {q : α} {qs : List α} (hs : KeySorted key (q :: qs))
    (hlb : ∀ q' ∈ q :: qs, ((key q' + L : ℚ) : WithTop ℚ) ≤ val q') :
    ((key q + L : ℚ) : WithTop ℚ) ≤ opt val (q :: qs) := by
  apply opt_ge
  intro q' hq'
  refine le_trans ?_ (hlb q' hq')
  rcases List.mem_cons.mp hq' with rfl | hq'
  · exact le_rfl
  · have := List.rel_of_pairwise_cons hs hq'
    exact_mod_cast (by linarith : key q + L ≤ key q' + L)

theorem run_best_gen : ∀ (qs : List α) (st : St α), KeySorted key qs →
    (∀ q ∈ qs, ((key q + L : ℚ) : WithTop ℚ) ≤ val q) →
    (run key val L qs st).best = min st.best (opt val qs)
  | [], st, _, _ => by simp [run, opt]
  | q :: qs, st, hs, hlb => by
    unfold run
    split_ifs with h1 h2
    · simp only
      exact (min_eq_left (h1.trans (key_le_opt hs hlb))).symm
    · rw [run_best_gen qs _ hs.of_cons fun q' h => hlb q' (by simp [h])]
      simp only [opt, foldr_cons]
      rw [← min_assoc, min_eq_right h2.le]
    · rw [run_best_gen qs _ hs.of_cons fun q' h => hlb q' (by simp [h])]
      simp only [opt, foldr_cons]
      rw [← min_assoc, min_eq_left (not_lt.mp h2)]

/-- **Exactness, value.** The loop returns the optimum over all candidates. -/
theorem run_best {qs : List α} (hs : KeySorted key qs)
    (hlb : ∀ q ∈ qs, ((key q + L : ℚ) : WithTop ℚ) ≤ val q) :
    (run key val L qs init).best = opt val qs := by
  rw [run_best_gen qs init hs hlb]; simp [init]

/-- Invariant of the answer. -/
def AnsInv (M : List α) (st : St α) : Prop :=
  (st.ans = none ∧ st.best = ⊤) ∨ ∃ q ∈ M, st.ans = some q ∧ val q = st.best ∧ st.best ≠ ⊤

theorem run_ans_gen (M : List α) : ∀ (qs : List α) (st : St α), (∀ q ∈ qs, q ∈ M) →
    AnsInv (val := val) M st → AnsInv (val := val) M (run key val L qs st)
  | [], st, _, h => h
  | q :: qs, st, hM, h => by
    unfold run
    split_ifs with h1 h2
    · exact h
    · refine run_ans_gen M qs _ (fun q' h => hM q' (by simp [h])) (Or.inr ⟨q, hM q (by simp), rfl,
        rfl, ne_top_of_lt h2⟩)
    · rcases h with h | ⟨q', hq', h3, h4, h5⟩
      · exact run_ans_gen M qs _ (fun q' h => hM q' (by simp [h])) (Or.inl h)
      · exact run_ans_gen M qs _ (fun q' h => hM q' (by simp [h])) (Or.inr ⟨q', hq', h3, h4, h5⟩)

/-- **Exactness, answer.** If some candidate has a partner, the loop answers with a candidate whose
value is the optimum; otherwise it answers none. -/
theorem run_answer {qs : List α} (hs : KeySorted key qs)
    (hlb : ∀ q ∈ qs, ((key q + L : ℚ) : WithTop ℚ) ≤ val q) :
    (opt val qs = ⊤ → (run key val L qs init).ans = none) ∧
    (opt val qs ≠ ⊤ → ∃ q ∈ qs, (run key val L qs init).ans = some q ∧ val q = opt val qs) := by
  have hb := run_best hs hlb
  have h := run_ans_gen (key := key) (val := val) (L := L) qs qs init (fun _ h => h) (Or.inl ⟨rfl, rfl⟩)
  constructor
  · intro ht
    rcases h with h | ⟨q, -, -, -, h5⟩
    · exact h.1
    · exact absurd (hb.trans ht) h5
  · intro ht
    rcases h with h | ⟨q, hq, h3, h4, -⟩
    · exact absurd (hb.symm.trans h.2) ht
    · exact ⟨q, hq, h3, h4.trans hb⟩

/-- The count, from any state: with `T = min best OPT`, every evaluated candidate has
`c'(Q) + L ≤ T`, and the threshold `T` does not change while the loop runs. -/
theorem run_count_gen : ∀ (qs : List α) (st : St α), KeySorted key qs →
    (∀ q ∈ qs, ((key q + L : ℚ) : WithTop ℚ) ≤ val q) →
    (run key val L qs st).evals ≤ st.evals +
        (qs.filter fun q => ((key q + L : ℚ) : WithTop ℚ) ≤ min st.best (opt val qs)).length ∧
    (run key val L qs st).checks ≤ st.checks +
        (qs.filter fun q => ((key q + L : ℚ) : WithTop ℚ) ≤ min st.best (opt val qs)).length + 1
  | [], st, _, _ => by simp [run]
  | q :: qs, st, hs, hlb => by
    have hlb' : ∀ q' ∈ qs, ((key q' + L : ℚ) : WithTop ℚ) ≤ val q' :=
      fun q' h => hlb q' (by simp [h])
    unfold run
    split_ifs with h1 h2
    · simp only; omega
    all_goals
      have hq : ((key q + L : ℚ) : WithTop ℚ) ≤ min st.best (opt val (q :: qs)) :=
        le_min (not_le.mp h1).le (key_le_opt hs hlb)
      rw [List.filter_cons_of_pos (by simpa using hq)]
    · have hT : min (val q) (opt val qs) = min st.best (opt val (q :: qs)) := by
        simp only [opt, foldr_cons]; rw [← min_assoc, min_eq_right h2.le]
      have := run_count_gen qs ⟨val q, some q, st.evals + 1, st.checks + 1⟩ hs.of_cons hlb'
      simp only [hT] at this
      simp only [List.length_cons]; omega
    · have hT : min st.best (opt val qs) = min st.best (opt val (q :: qs)) := by
        simp only [opt, foldr_cons]; rw [← min_assoc, min_eq_left (not_lt.mp h2)]
      have := run_count_gen qs { st with evals := st.evals + 1, checks := st.checks + 1 }
        hs.of_cons hlb'
      simp only [hT] at this
      simp only [List.length_cons]; omega

/-- **Count, with ties.** Let `N` be the number of candidates with `c'(Q) + L ≤ OPT`. The loop
evaluates at most `N` candidates and reaches the stopping test at most `N + 1` times. -/
theorem run_count {qs : List α} (hs : KeySorted key qs)
    (hlb : ∀ q ∈ qs, ((key q + L : ℚ) : WithTop ℚ) ≤ val q) :
    (run key val L qs init).evals ≤
        (qs.filter fun q => ((key q + L : ℚ) : WithTop ℚ) ≤ opt val qs).length ∧
    (run key val L qs init).checks ≤
        (qs.filter fun q => ((key q + L : ℚ) : WithTop ℚ) ≤ opt val qs).length + 1 := by
  have h := run_count_gen qs init hs hlb
  have e : min (init : St α).best (opt val qs) = opt val qs := min_eq_right le_top
  rw [e] at h
  exact ⟨by simpa only [init, zero_add] using h.1, by simpa only [init, zero_add] using h.2⟩

/-! ## Candidates with partners -/

/-- **Theorem (Algorithm R).** Candidates `qs` (all first paths, sorted by `c'`), each with a finite
set of feasible partners and the cost `F`, and the lower bound `F(q, p) ≥ c'(q) + L` of
`lower_bound`. The value of a candidate is the cost of its best partner, which the shortest path
step computes. Then the loop returns a pair of minimum cost over all feasible pairs, or none if
there is no feasible pair, and the count of `run_count` holds. -/
theorem algR_exact {β : Type*} (partners : α → Finset β) (F : α → β → ℚ) {qs : List α}
    (hs : KeySorted key qs) (hlb : ∀ q ∈ qs, ∀ p ∈ partners q, key q + L ≤ F q p) :
    let val := fun q => (partners q).inf fun p => ((F q p : ℚ) : WithTop ℚ)
    ((∀ q ∈ qs, partners q = ∅) → (run key val L qs init).ans = none) ∧
    (∀ q₀ ∈ qs, ∀ p₀ ∈ partners q₀, ∃ q ∈ qs, (run key val L qs init).ans = some q ∧
      ∃ p ∈ partners q, ∀ q' ∈ qs, ∀ p' ∈ partners q', F q p ≤ F q' p') ∧
    (run key val L qs init).evals ≤
      (qs.filter fun q => ((key q + L : ℚ) : WithTop ℚ) ≤ opt val qs).length ∧
    (run key val L qs init).checks ≤
      (qs.filter fun q => ((key q + L : ℚ) : WithTop ℚ) ≤ opt val qs).length + 1 := by
  intro val
  have hlb' : ∀ q ∈ qs, ((key q + L : ℚ) : WithTop ℚ) ≤ val q := by
    intro q hq
    exact Finset.le_inf fun p hp => by exact_mod_cast hlb q hq p hp
  obtain ⟨hn, hs'⟩ := run_answer hs hlb'
  refine ⟨fun h => hn ?_, ?_, run_count hs hlb'⟩
  · rw [eq_top_iff]; exact opt_ge fun q hq => by simp [val, h q hq]
  · intro q₀ hq₀ p₀ hp₀
    have hne : opt val qs ≠ ⊤ := by
      refine ne_top_of_le_ne_top (WithTop.coe_ne_top (a := F q₀ p₀)) ?_
      exact (opt_le hq₀).trans (Finset.inf_le hp₀)
    obtain ⟨q, hq, ha, hv⟩ := hs' hne
    refine ⟨q, hq, ha, ?_⟩
    have hpne : (partners q).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      simp [val, h] at hv
      exact hne hv.symm
    obtain ⟨p, hp, hpmin⟩ := (partners q).exists_min_image (F q) hpne
    refine ⟨p, hp, fun q' hq' p' hp' => ?_⟩
    have h1 : val q = ((F q p : ℚ) : WithTop ℚ) := by
      apply le_antisymm (Finset.inf_le hp)
      exact Finset.le_inf fun p'' hp'' => by exact_mod_cast hpmin p'' hp''
    have h2 : ((F q p : ℚ) : WithTop ℚ) ≤ F q' p' := by
      rw [← h1, hv]; exact (opt_le hq').trans (Finset.inf_le hp')
    exact_mod_cast h2

end RiskRouting.AlgR
