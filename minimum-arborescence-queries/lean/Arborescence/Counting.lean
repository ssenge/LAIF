import Arborescence.Lists

/-!
# Lemma 4 and Lemma 5: the accounting, on an abstract trace

The state is a multiset of containers, each with a multiset of groups, each group with a budget `K` and the
size `base` of its container at its last build. The events are:

* initial builds, one for each vertex in the list `us`;
* `AStep.contract`: a contraction with largest part `S`, moved set `M` (the union of the `others`), followed
  by the absorption of groups of `S` of the class of `H` (`Absorb`), and the build `(H, |H|)`;
* `AStep.exhaust`: a rebuild with doubled budget under the growth hypothesis of Lemma 3(c).

The events say nothing about weights, lists or TopK, in line with the claim in the proof of Theorem 1 that the
accounting does not use minimality. `Run us evs σ` says that `evs` (newest first) leads from the initial state
to `σ`. All sums are over `allBuilds us evs`.

Each bound is a potential argument, for arbitrary vertex weights `d`. Taking `d` to be the indicator of a vertex
gives the per-vertex statements Lemma 4(a), (b), (d); taking `d = 1` gives (c), (e); and taking `d` the in-degree
gives `Σ N(G)`.

The constants are slightly better than in the notes: with `ℓ = log₂ n`, so `L = ℓ + 1`, a vertex is in `M` at most
`ℓ` times and is absorbed at most `ℓ` times. We state the bounds of the notes.
-/

set_option linter.unusedSectionVars false

open Finset

namespace Arborescence

variable {V : Type*} [DecidableEq V]

/-- A group: its vertices, the budget, and the size of the container at its last build. -/
structure Grp (V : Type*) where
  verts : Finset V
  K : ℕ
  base : ℕ

/-- A container with its groups. -/
structure Cont (V : Type*) where
  verts : Finset V
  groups : Multiset (Grp V)

/-- `⌊log₂⌋`. -/
abbrev lg (x : ℕ) : ℕ := Nat.log 2 x

/-- The class of a group. -/
def Grp.cls (G : Grp V) : ℕ := lg G.verts.card

/-- The total of vertex weights on a set. `wt d G = N(G)` for `d` the in-degree. -/
def wt (d : V → ℕ) (A : Finset V) : ℕ := ∑ v ∈ A, d v

theorem wt_one (A : Finset V) : wt (fun _ => 1) A = A.card := by simp [wt]

theorem wt_union (d : V → ℕ) {A B : Finset V} (h : Disjoint A B) : wt d (A ∪ B) = wt d A + wt d B :=
  Finset.sum_union h

theorem wt_mono (d : V → ℕ) {A B : Finset V} (h : A ⊆ B) : wt d A ≤ wt d B :=
  Finset.sum_le_sum_of_subset h

/-- The absorption loop of `Contract`. `Absorb gs H A gs' H'`: starting from the groups `gs` of `S` and `H`,
the sets `A` get absorbed, one at a time and each of the class of the current `H`, and the loop stops with the
remaining groups `gs'` and `H'`, where no group of `gs'` has the class of `H'`. -/
inductive Absorb : Multiset (Grp V) → Finset V → Multiset (Finset V) → Multiset (Grp V) → Finset V → Prop
  | stop (gs : Multiset (Grp V)) (H : Finset V) :
      (∀ G ∈ gs, G.cls ≠ lg H.card) → Absorb gs H 0 gs H
  | absorb (G : Grp V) (gs : Multiset (Grp V)) (H : Finset V) (A : Multiset (Finset V))
      (gs' : Multiset (Grp V)) (H' : Finset V) :
      G.cls = lg H.card → Disjoint H G.verts → Absorb gs (H ∪ G.verts) A gs' H' →
      Absorb (G ::ₘ gs) H (G.verts ::ₘ A) gs' H'

/-- An event of the trace after the initial builds. -/
inductive Ev (V : Type*)
  /-- Contraction with moved set `M`, absorbed sets `A`, and new group `H`. -/
  | contract (M : Finset V) (A : Multiset (Finset V)) (H : Finset V)
  /-- Exhaustion rebuild of the group `G`, with new budget `K`. -/
  | exhaust (G : Finset V) (K : ℕ)

/-- The build an event performs. -/
def Ev.build : Ev V → Finset V × ℕ
  | .contract _ _ H => (H, H.card)
  | .exhaust G K => (G, K)

/-- The moved set of an event. -/
def Ev.moved : Ev V → Finset V
  | .contract M _ _ => M
  | .exhaust _ _ => ∅

/-- The absorbed sets of an event. -/
def Ev.absorbed : Ev V → Multiset (Finset V)
  | .contract _ A _ => A
  | .exhaust _ _ => 0

/-- The new budget of an exhaustion build, `0` for other events. -/
def Ev.exhaustK : Ev V → ℕ
  | .contract _ _ _ => 0
  | .exhaust _ K => K

/-- The transitions of the abstract machine. -/
inductive AStep : Multiset (Cont V) → Ev V → Multiset (Cont V) → Prop
  | contract (rest others : Multiset (Cont V)) (S : Cont V) (M H : Finset V) (A : Multiset (Finset V))
      (gs : Multiset (Grp V)) :
      (∀ C ∈ others, C.verts.card ≤ S.verts.card) → M.Nonempty →
      (∀ d : V → ℕ, wt d M = (others.map fun C => wt d C.verts).sum) →
      Disjoint S.verts M → Absorb S.groups M A gs H →
      AStep (S ::ₘ (others + rest)) (.contract M A H)
        (⟨S.verts ∪ M, ⟨H, H.card, (S.verts ∪ M).card⟩ ::ₘ gs⟩ ::ₘ rest)
  | exhaust (rest : Multiset (Cont V)) (C : Cont V) (G : Grp V) (gs : Multiset (Grp V)) :
      C.groups = G ::ₘ gs → G.K + G.base ≤ C.verts.card →
      AStep (C ::ₘ rest) (.exhaust G.verts (2 * G.K))
        (⟨C.verts, ⟨G.verts, 2 * G.K, C.verts.card⟩ ::ₘ gs⟩ ::ₘ rest)

/-- The initial state: singleton containers, each with its singleton group of budget `1`. -/
def initConts (us : List V) : Multiset (Cont V) :=
  ((us.map fun v => (⟨{v}, {⟨{v}, 1, 1⟩}⟩ : Cont V) : List (Cont V)) : Multiset (Cont V))

/-- Reachable states, with the events newest first. -/
inductive Run (us : List V) : List (Ev V) → Multiset (Cont V) → Prop
  | init : Run us [] (initConts us)
  | step {evs : List (Ev V)} {σ σ' : Multiset (Cont V)} {e : Ev V} :
      Run us evs σ → AStep σ e σ' → Run us (e :: evs) σ'

/-- All builds of a trace, newest first, the initial ones at the end. -/
def allBuilds (us : List V) (evs : List (Ev V)) : List (Finset V × ℕ) :=
  evs.map Ev.build ++ us.map fun v => (({v} : Finset V), 1)

/-! ## The absorption loop -/

theorem Absorb.spec {gs0 : Multiset (Grp V)} {H0 : Finset V} {A : Multiset (Finset V)}
    {gs' : Multiset (Grp V)} {H : Finset V} (h : Absorb gs0 H0 A gs' H) (hne : H0.Nonempty)
    (hG : ∀ G ∈ gs0, G.verts.Nonempty) :
    ∃ gA : Multiset (Grp V), gs0 = gA + gs' ∧ A = gA.map Grp.verts ∧ H0 ⊆ H ∧
      (∀ d : V → ℕ, wt d H = wt d H0 + (A.map (wt d)).sum) ∧
      (∀ G ∈ gA, G.cls + 1 ≤ lg H.card) ∧ (∀ G ∈ gs', G.cls ≠ lg H.card) := by
  induction h with
  | stop gs H hs => exact ⟨0, by simp, by simp, Finset.Subset.refl _, by simp, by simp, hs⟩
  | absorb G gs H A gs' H' hcls hdisj _ ih =>
    obtain ⟨gA, h1, h2, h3, h4, h5, h6⟩ :=
      ih (hne.mono Finset.subset_union_left) (fun G' hG' => hG G' (Multiset.mem_cons_of_mem hG'))
    refine ⟨G ::ₘ gA, by rw [h1, Multiset.cons_add], by rw [h2, Multiset.map_cons],
      Finset.subset_union_left.trans h3, ?_, ?_, h6⟩
    · intro d
      rw [h4 d, wt_union d hdisj, Multiset.map_cons, Multiset.sum_cons]
      omega
    · intro G' hG'
      rcases Multiset.mem_cons.mp hG' with rfl | hG'
      · have hGne := hG G' (Multiset.mem_cons_self _ _)
        have hc : (H ∪ G'.verts).card = H.card + G'.verts.card := Finset.card_union_of_disjoint hdisj
        have h7 : 2 ^ lg H.card ≤ H.card := Nat.pow_log_le_self 2 (Finset.card_pos.mpr hne).ne'
        have h8 : 2 ^ lg G'.verts.card ≤ G'.verts.card := Nat.pow_log_le_self 2 (Finset.card_pos.mpr hGne).ne'
        have h9 : G'.cls = lg G'.verts.card := rfl
        have h10 : lg G'.verts.card = lg H.card := h9 ▸ hcls
        have h11 : 2 ^ (G'.cls + 1) ≤ H'.card := by
          rw [pow_succ, hcls]
          rw [h10] at h8
          have := Finset.card_le_card h3
          omega
        exact Nat.le_log_of_pow_le (by norm_num) h11
      · exact h5 G' hG'

/-! ## Well-formed states -/

/-- The invariant of a container: the groups partition it, in the form `Σ wt d G = wt d C` for all `d`. They are
nonempty, have budgets in `[1, 2n]`, and distinct classes. -/
structure Cont.WF (n : ℕ) (C : Cont V) : Prop where
  cov : ∀ d : V → ℕ, (C.groups.map fun G => wt d G.verts).sum = wt d C.verts
  ne : ∀ G ∈ C.groups, G.verts.Nonempty
  K_pos : ∀ G ∈ C.groups, 1 ≤ G.K
  K_le : ∀ G ∈ C.groups, G.K ≤ 2 * n
  base_le : ∀ G ∈ C.groups, G.base ≤ C.verts.card
  cls : (C.groups.map Grp.cls).Nodup

/-- The invariant of a state: containers are well formed and disjoint, the latter in the form of the sums. -/
structure AWF [Fintype V] (σ : Multiset (Cont V)) : Prop where
  cont : ∀ C ∈ σ, Cont.WF (Fintype.card V) C
  total : ∀ d : V → ℕ, (σ.map fun C => wt d C.verts).sum ≤ wt d univ

theorem Cont.WF.card_le {n : ℕ} {C : Cont V} (hC : C.WF n) {G : Grp V} (hG : G ∈ C.groups) :
    G.verts.card ≤ C.verts.card := by
  have := hC.cov fun _ => 1
  rw [wt_one] at this
  rw [← this]
  have h2 : wt (fun _ => 1) G.verts ≤ (C.groups.map fun G => wt (fun _ => 1) G.verts).sum :=
    Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (fun G : Grp V => wt (fun _ => 1) G.verts) hG)
  simpa [wt_one] using h2

theorem card_groups_le [Fintype V] {C : Cont V} (hC : C.WF (Fintype.card V)) :
    Multiset.card C.groups ≤ lg (Fintype.card V) + 1 := by
  have h1 : (C.groups.map Grp.cls).toFinset ⊆ Finset.range (lg (Fintype.card V) + 1) := by
    intro c hc
    obtain ⟨G, _, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_toFinset.mp hc)
    have : G.verts.card ≤ Fintype.card V := Finset.card_le_univ _
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right this))
  have h2 := Finset.card_le_card h1
  rw [Multiset.toFinset_card_of_nodup hC.cls, Multiset.card_map, Finset.card_range] at h2
  exact h2

/-- The facts about a contraction used below. -/
structure CD (n : ℕ) (S : Cont V) (others : Multiset (Cont V)) (M H : Finset V) (A : Multiset (Finset V))
    (gs gA : Multiset (Grp V)) : Prop where
  hS : S.WF n
  hO : ∀ C ∈ others, C.WF n
  hle : ∀ C ∈ others, C.verts.card ≤ S.verts.card
  hM : M.Nonempty
  hwt : ∀ d : V → ℕ, wt d M = (others.map fun C => wt d C.verts).sum
  hdisj : Disjoint S.verts M
  hs : S.groups = gA + gs
  hA : A = gA.map Grp.verts
  hMH : M ⊆ H
  hH : ∀ d : V → ℕ, wt d H = wt d M + (A.map (wt d)).sum
  hcls : ∀ G ∈ gA, G.cls + 1 ≤ lg H.card
  hstop : ∀ G ∈ gs, G.cls ≠ lg H.card

namespace CD

variable {n : ℕ} {S : Cont V} {others : Multiset (Cont V)} {M H : Finset V} {A : Multiset (Finset V)}
  {gs gA : Multiset (Grp V)}

theorem card_X (h : CD n S others M H A gs gA) : (S.verts ∪ M).card = S.verts.card + M.card :=
  Finset.card_union_of_disjoint h.hdisj

theorem card_le_M (h : CD n S others M H A gs gA) {C : Cont V} (hC : C ∈ others) :
    C.verts.card ≤ M.card := by
  have h1 := h.hwt fun _ => 1
  rw [wt_one] at h1
  rw [h1]
  have h2 : wt (fun _ => 1) C.verts ≤ (others.map fun C => wt (fun _ => 1) C.verts).sum :=
    Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (fun C : Cont V => wt (fun _ => 1) C.verts) hC)
  simpa [wt_one] using h2

theorem lg_lt (h : CD n S others M H A gs gA) {C : Cont V} (hC : C ∈ others) (hne : C.verts.Nonempty) :
    lg C.verts.card + 1 ≤ lg (S.verts ∪ M).card := by
  have h1 := h.card_X
  have h2 := h.card_le_M hC
  have h3 := h.hle C hC
  have h4 : C.verts.card * 2 ≤ (S.verts ∪ M).card := by omega
  have h5 := Nat.log_mul_base (b := 2) (n := C.verts.card) (by norm_num) (Finset.card_pos.mpr hne).ne'
  have h6 := Nat.log_mono_right (b := 2) h4
  simp only [lg]
  omega

theorem lg_S (h : CD n S others M H A gs gA) : lg S.verts.card ≤ lg (S.verts ∪ M).card :=
  Nat.log_mono_right (Finset.card_le_card Finset.subset_union_left)

theorem lg_G_H (h : CD n S others M H A gs gA) {C : Cont V} (hC : C ∈ others) {G : Grp V}
    (hG : G ∈ C.groups) : lg G.verts.card ≤ lg H.card := by
  have h1 := (h.hO C hC).card_le hG
  have h2 := h.card_le_M hC
  have h3 := Finset.card_le_card h.hMH
  exact Nat.log_mono_right (by omega)

theorem H_nonempty (h : CD n S others M H A gs gA) : H.Nonempty := h.hM.mono h.hMH

/-- The weights of `S` split into absorbed and remaining groups. -/
theorem wt_S (h : CD n S others M H A gs gA) (d : V → ℕ) :
    (gA.map fun G => wt d G.verts).sum + (gs.map fun G => wt d G.verts).sum = wt d S.verts := by
  rw [← h.hS.cov d, h.hs, Multiset.map_add, Multiset.sum_add]

theorem sum_A (h : CD n S others M H A gs gA) (d : V → ℕ) :
    (A.map (wt d)).sum = (gA.map fun G => wt d G.verts).sum := by
  rw [h.hA, Multiset.map_map]
  rfl

/-- Well-formedness of the new container. -/
theorem wf_new [Fintype V] (h : CD (Fintype.card V) S others M H A gs gA) :
    Cont.WF (Fintype.card V)
      ⟨S.verts ∪ M, ⟨H, H.card, (S.verts ∪ M).card⟩ ::ₘ gs⟩ := by
  have hsub : ∀ G ∈ gs, G ∈ S.groups := fun G hG => by
    rw [h.hs]
    exact Multiset.mem_add.mpr (Or.inr hG)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [wt_union d h.hdisj, h.hH d, ← h.wt_S d, h.sum_A d]
    omega
  · intro G hG
    rcases Multiset.mem_cons.mp hG with rfl | hG
    · exact h.H_nonempty
    · exact h.hS.ne G (hsub G hG)
  · intro G hG
    rcases Multiset.mem_cons.mp hG with rfl | hG
    · exact Finset.card_pos.mpr h.H_nonempty
    · exact h.hS.K_pos G (hsub G hG)
  · intro G hG
    rcases Multiset.mem_cons.mp hG with rfl | hG
    · have : H.card ≤ Fintype.card V := Finset.card_le_univ _
      simp only
      omega
    · exact h.hS.K_le G (hsub G hG)
  · intro G hG
    rcases Multiset.mem_cons.mp hG with rfl | hG
    · exact le_rfl
    · have h1 := h.hS.base_le G (hsub G hG)
      have h2 := h.card_X
      simp only
      omega
  · simp only [Multiset.map_cons]
    refine Multiset.nodup_cons.mpr ⟨?_, ?_⟩
    · intro hmem
      obtain ⟨G, hG, hc⟩ := Multiset.mem_map.mp hmem
      exact h.hstop G hG hc
    · have h1 := h.hS.cls
      rw [h.hs, Multiset.map_add] at h1
      exact (Multiset.nodup_add.mp h1).2.1

/-- Bookkeeping of the total weight over the new container. -/
theorem wt_new (h : CD n S others M H A gs gA) (d : V → ℕ) :
    wt d (S.verts ∪ M) = wt d S.verts + (others.map fun C => wt d C.verts).sum := by
  rw [wt_union d h.hdisj, h.hwt d]

end CD

/-- From a contraction event to its facts. -/
theorem cd_of_step [Fintype V] {S : Cont V} {others rest : Multiset (Cont V)} {M H : Finset V}
    {A : Multiset (Finset V)} {gs : Multiset (Grp V)} (hσ : AWF (S ::ₘ (others + rest)))
    (h1 : ∀ C ∈ others, C.verts.card ≤ S.verts.card) (h2 : M.Nonempty)
    (h3 : ∀ d : V → ℕ, wt d M = (others.map fun C => wt d C.verts).sum)
    (h4 : Disjoint S.verts M) (h5 : Absorb S.groups M A gs H) :
    ∃ gA, CD (Fintype.card V) S others M H A gs gA := by
  have hS := hσ.cont S (Multiset.mem_cons_self _ _)
  obtain ⟨gA, a1, a2, a3, a4, a5, a6⟩ := h5.spec h2 hS.ne
  exact ⟨gA, hS, fun C hC => hσ.cont C
    (Multiset.mem_cons_of_mem (Multiset.mem_add.mpr (Or.inl hC))), h1, h2, h3, h4, a1, a2, a3,
    fun d => by rw [a4 d], a5, a6⟩

/-- `AWF` is preserved by the events. -/
theorem AStep.wf [Fintype V] {σ σ' : Multiset (Cont V)} {e : Ev V} (h : AStep σ e σ') (hσ : AWF σ) :
    AWF σ' := by
  cases h with
  | contract rest others S M H A gs h1 h2 h3 h4 h5 =>
    obtain ⟨gA, hcd⟩ := cd_of_step hσ h1 h2 h3 h4 h5
    refine ⟨?_, ?_⟩
    · intro C hC
      rcases Multiset.mem_cons.mp hC with rfl | hC
      · exact hcd.wf_new
      · exact hσ.cont C (Multiset.mem_cons_of_mem (Multiset.mem_add.mpr (Or.inr hC)))
    · intro d
      have := hσ.total d
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.map_add, Multiset.sum_add] at this ⊢
      rw [hcd.wt_new d]
      omega
  | exhaust rest C G gs hg hK =>
    have hC := hσ.cont C (Multiset.mem_cons_self _ _)
    refine ⟨?_, ?_⟩
    · intro C' hC'
      rcases Multiset.mem_cons.mp hC' with rfl | hC'
      · have hsub : ∀ G' ∈ gs, G' ∈ C.groups := fun G' hG' => by
          rw [hg]
          exact Multiset.mem_cons_of_mem hG'
        have hG : G ∈ C.groups := by
          rw [hg]
          exact Multiset.mem_cons_self _ _
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro d
          have := hC.cov d
          rw [hg] at this
          simpa using this
        · intro G' hG'
          rcases Multiset.mem_cons.mp hG' with rfl | hG'
          · exact hC.ne G hG
          · exact hC.ne G' (hsub G' hG')
        · intro G' hG'
          rcases Multiset.mem_cons.mp hG' with rfl | hG'
          · have := hC.K_pos G hG
            simp only
            omega
          · exact hC.K_pos G' (hsub G' hG')
        · intro G' hG'
          rcases Multiset.mem_cons.mp hG' with rfl | hG'
          · have : C.verts.card ≤ Fintype.card V := Finset.card_le_univ _
            simp only
            omega
          · exact hC.K_le G' (hsub G' hG')
        · intro G' hG'
          rcases Multiset.mem_cons.mp hG' with rfl | hG'
          · exact le_rfl
          · exact hC.base_le G' (hsub G' hG')
        · have := hC.cls
          rw [hg] at this
          simpa [Grp.cls] using this
      · exact hσ.cont C' (Multiset.mem_cons_of_mem hC')
    · intro d
      simpa using hσ.total d

theorem initConts_wf [Fintype V] {us : List V} (hus : us.Nodup) : AWF (initConts us) := by
  refine ⟨?_, ?_⟩
  · intro C hC
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp hC)
    have hcard : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro d
      simp
    · intro G hG
      rw [Multiset.mem_singleton.mp hG]
      simp
    · intro G hG
      rw [Multiset.mem_singleton.mp hG]
    · intro G hG
      rw [Multiset.mem_singleton.mp hG]
      show 1 ≤ 2 * Fintype.card V
      omega
    · intro G hG
      rw [Multiset.mem_singleton.mp hG]
      simp
    · simp
  · intro d
    have h1 : ((initConts us).map fun C => wt d C.verts).sum = wt d us.toFinset := by
      induction us with
      | nil => simp [initConts, wt]
      | cons a l ih =>
        have hl := (List.nodup_cons.mp hus).2
        have ha := (List.nodup_cons.mp hus).1
        have := ih hl
        simp only [initConts, List.map_cons, Multiset.map_coe, Multiset.sum_coe, List.sum_cons] at this ⊢
        rw [this, List.toFinset_cons]
        simp [wt, Finset.sum_insert, ha]
    rw [h1]
    exact wt_mono d (Finset.subset_univ _)

/-- States of a run are well formed. -/
theorem Run.wf [Fintype V] {us : List V} (hus : us.Nodup) {evs : List (Ev V)} {σ : Multiset (Cont V)}
    (h : Run us evs σ) : AWF σ := by
  induction h with
  | init => exact initConts_wf hus
  | step _ hs ih => exact hs.wf ih

/-! ## Potentials -/

/-- `Σ_v d(v) log |container of v|`. -/
def P1 (d : V → ℕ) (σ : Multiset (Cont V)) : ℕ := (σ.map fun C => wt d C.verts * lg C.verts.card).sum

/-- The part of `P2` from one container. -/
def P2c (d : V → ℕ) (C : Cont V) : ℕ := (C.groups.map fun G => wt d G.verts * lg G.verts.card).sum

/-- `Σ_v d(v) φ(v)`, where `φ(v)` is the class of the group of `v`. -/
def P2 (d : V → ℕ) (σ : Multiset (Cont V)) : ℕ := (σ.map (P2c d)).sum

/-- The credits of one container. -/
def Thc (C : Cont V) : ℕ := (C.groups.map fun G => C.verts.card - G.base).sum

/-- `Σ_G (|C_G| - base_G)`, the growth since the last build, summed over all groups: the credits of the notes. -/
def Th (σ : Multiset (Cont V)) : ℕ := (σ.map Thc).sum

/-- The factor in the potential that counts builds per vertex. -/
def fac (L c g K : ℕ) : ℕ := 1 + (L + 1) * (lg c + lg g) + lg K

/-- The part of `Bp` from one container. -/
def Bc (L : ℕ) (d : V → ℕ) (C : Cont V) : ℕ :=
  (C.groups.map fun G => wt d G.verts * fac L C.verts.card G.verts.card G.K).sum

/-- The potential that bounds the weight of the builds. -/
def Bp (L : ℕ) (d : V → ℕ) (σ : Multiset (Cont V)) : ℕ := (σ.map (Bc L d)).sum

theorem lgK_le {K n : ℕ} (hK : K ≤ 2 * n) (h1 : 1 ≤ K) : lg K ≤ lg n + 1 := by
  have hn : n ≠ 0 := by omega
  have := Nat.log_mul_base (b := 2) (n := n) (by norm_num) hn
  have h2 := Nat.log_mono_right (b := 2) (show K ≤ n * 2 by omega)
  simp only [lg]
  omega

section Steps

variable [Fintype V]

theorem step_P1 {σ σ' : Multiset (Cont V)} {e : Ev V} (h : AStep σ e σ') (hσ : AWF σ) (d : V → ℕ) :
    P1 d σ + wt d e.moved ≤ P1 d σ' := by
  cases h with
  | contract rest others S M H A gs h1 h2 h3 h4 h5 =>
    obtain ⟨gA, hcd⟩ := cd_of_step hσ h1 h2 h3 h4 h5
    simp only [P1, Ev.moved, Multiset.map_cons, Multiset.sum_cons, Multiset.map_add, Multiset.sum_add]
    set X := S.verts ∪ M
    have hstep : ∀ C ∈ others, wt d C.verts * lg C.verts.card + wt d C.verts ≤ wt d C.verts * lg X.card := by
      intro C hC
      by_cases hne : C.verts.Nonempty
      · have := hcd.lg_lt hC hne
        calc wt d C.verts * lg C.verts.card + wt d C.verts
            = wt d C.verts * (lg C.verts.card + 1) := by ring
          _ ≤ _ := Nat.mul_le_mul_left _ this
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        simp [hne, wt]
    have hsum := Multiset.sum_map_le_sum_map _ _ hstep
    rw [Multiset.sum_map_add, Multiset.sum_map_mul_right, ← hcd.hwt d] at hsum
    have hS : wt d S.verts * lg S.verts.card ≤ wt d S.verts * lg X.card :=
      Nat.mul_le_mul_left _ hcd.lg_S
    have hX : wt d X = wt d S.verts + wt d M := wt_union d hcd.hdisj
    rw [hX, add_mul]
    omega
  | exhaust rest C G gs hg hK =>
    simp [P1, Ev.moved, wt]

theorem step_P2 {σ σ' : Multiset (Cont V)} {e : Ev V} (h : AStep σ e σ') (hσ : AWF σ) (d : V → ℕ) :
    P2 d σ + (e.absorbed.map (wt d)).sum ≤ P2 d σ' := by
  cases h with
  | contract rest others S M H A gs h1 h2 h3 h4 h5 =>
    obtain ⟨gA, hcd⟩ := cd_of_step hσ h1 h2 h3 h4 h5
    simp only [P2, Ev.absorbed, Multiset.map_cons, Multiset.sum_cons, Multiset.map_add, Multiset.sum_add]
    have hP2S : P2c d S = (gA.map fun G => wt d G.verts * lg G.verts.card).sum +
        (gs.map fun G => wt d G.verts * lg G.verts.card).sum := by
      rw [P2c, hcd.hs, Multiset.map_add, Multiset.sum_add]
    have hP2new : P2c d ⟨S.verts ∪ M, ⟨H, H.card, (S.verts ∪ M).card⟩ ::ₘ gs⟩ =
        wt d H * lg H.card + (gs.map fun G => wt d G.verts * lg G.verts.card).sum := by
      simp [P2c]
    rw [hP2S, hP2new, hcd.hH d, hcd.sum_A d, add_mul]
    have hO : (others.map (P2c d)).sum ≤ wt d M * lg H.card := by
      rw [hcd.hwt d, ← Multiset.sum_map_mul_right]
      refine Multiset.sum_map_le_sum_map _ _ fun C hC => ?_
      rw [← (hcd.hO C hC).cov d, ← Multiset.sum_map_mul_right]
      exact Multiset.sum_map_le_sum_map _ _ fun G hG => Nat.mul_le_mul_left _ (hcd.lg_G_H hC hG)
    have hA : (gA.map fun G => wt d G.verts * lg G.verts.card).sum + (gA.map fun G => wt d G.verts).sum ≤
        (gA.map fun G => wt d G.verts).sum * lg H.card := by
      rw [← Multiset.sum_map_add, ← Multiset.sum_map_mul_right]
      refine Multiset.sum_map_le_sum_map _ _ fun G hG => ?_
      calc wt d G.verts * lg G.verts.card + wt d G.verts = wt d G.verts * (lg G.verts.card + 1) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ (hcd.hcls G hG)
    omega
  | exhaust rest C G gs hg hK =>
    simp [P2, P2c, Ev.absorbed, hg]

theorem step_Th {σ σ' : Multiset (Cont V)} {e : Ev V} (h : AStep σ e σ') (hσ : AWF σ) :
    e.exhaustK + 2 * Th σ' ≤ 2 * Th σ + 2 * (lg (Fintype.card V) + 1) * e.moved.card := by
  cases h with
  | contract rest others S M H A gs h1 h2 h3 h4 h5 =>
    obtain ⟨gA, hcd⟩ := cd_of_step hσ h1 h2 h3 h4 h5
    simp only [Th, Ev.exhaustK, Ev.moved, Multiset.map_cons, Multiset.sum_cons, Multiset.map_add,
      Multiset.sum_add]
    have hS : Thc S = (gA.map fun G => S.verts.card - G.base).sum +
        (gs.map fun G => S.verts.card - G.base).sum := by
      rw [Thc, hcd.hs, Multiset.map_add, Multiset.sum_add]
    have hnew : Thc ⟨S.verts ∪ M, ⟨H, H.card, (S.verts ∪ M).card⟩ ::ₘ gs⟩ =
        (gs.map fun G => (S.verts ∪ M).card - G.base).sum := by
      simp [Thc]
    have hgs : (gs.map fun G => (S.verts ∪ M).card - G.base).sum ≤
        (gs.map fun G => S.verts.card - G.base).sum + Multiset.card gs * M.card := by
      have : ∀ G ∈ gs, (S.verts ∪ M).card - G.base ≤ (S.verts.card - G.base) + M.card := by
        intro G hG
        have := hcd.card_X
        omega
      have h6 := Multiset.sum_map_le_sum_map _ _ this
      rw [Multiset.sum_map_add] at h6
      simpa using h6
    have hcard : Multiset.card gs ≤ lg (Fintype.card V) + 1 := by
      refine le_trans ?_ (card_groups_le hcd.hS)
      rw [hcd.hs, Multiset.card_add]
      omega
    have hmul : Multiset.card gs * M.card ≤ (lg (Fintype.card V) + 1) * M.card :=
      Nat.mul_le_mul_right _ hcard
    rw [hS, hnew]
    have : 2 * (lg (Fintype.card V) + 1) * M.card = 2 * ((lg (Fintype.card V) + 1) * M.card) := by ring
    omega
  | exhaust rest C G gs hg hK =>
    simp only [Th, Ev.exhaustK, Ev.moved, Multiset.map_cons, Multiset.sum_cons]
    have h1 : Thc C = (C.verts.card - G.base) + (gs.map fun G' => C.verts.card - G'.base).sum := by
      rw [Thc, hg, Multiset.map_cons, Multiset.sum_cons]
    have h2 : Thc ⟨C.verts, ⟨G.verts, 2 * G.K, C.verts.card⟩ ::ₘ gs⟩ =
        (gs.map fun G' => C.verts.card - G'.base).sum := by
      simp [Thc]
    rw [h1, h2]
    simp only [Finset.card_empty, mul_zero]
    omega

/-- The factor drops by at least one against the factor of the new group. -/
theorem fac_lt {L c c' g g' K : ℕ} (hc : lg c + 1 ≤ lg c') (hg : lg g ≤ lg g') (hK : lg K ≤ L) :
    fac L c g K + 1 ≤ fac L c' g' g' := by
  simp only [fac]
  have : (L + 1) * (lg c + 1 + lg g) ≤ (L + 1) * (lg c' + lg g') :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : (L + 1) * (lg c + 1 + lg g) = (L + 1) * (lg c + lg g) + (L + 1) := by ring
  omega

theorem fac_lt' {L c c' g g' K : ℕ} (hc : lg c ≤ lg c') (hg : lg g + 1 ≤ lg g') (hK : lg K ≤ L) :
    fac L c g K + 1 ≤ fac L c' g' g' := by
  simp only [fac]
  have : (L + 1) * (lg c + 1 + lg g) ≤ (L + 1) * (lg c' + lg g') :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : (L + 1) * (lg c + 1 + lg g) = (L + 1) * (lg c + lg g) + (L + 1) := by ring
  omega

theorem step_Bp {σ σ' : Multiset (Cont V)} {e : Ev V} (h : AStep σ e σ') (hσ : AWF σ) (d : V → ℕ) :
    Bp (lg (Fintype.card V) + 1) d σ + wt d e.build.1 ≤ Bp (lg (Fintype.card V) + 1) d σ' := by
  set L := lg (Fintype.card V) + 1 with hL
  cases h with
  | contract rest others S M H A gs h1 h2 h3 h4 h5 =>
    obtain ⟨gA, hcd⟩ := cd_of_step hσ h1 h2 h3 h4 h5
    simp only [Bp, Ev.build, Multiset.map_cons, Multiset.sum_cons, Multiset.map_add, Multiset.sum_add]
    set X := S.verts ∪ M with hX
    set F := fac L X.card H.card H.card with hF
    have hSsplit : Bc L d S = (gA.map fun G => wt d G.verts * fac L S.verts.card G.verts.card G.K).sum +
        (gs.map fun G => wt d G.verts * fac L S.verts.card G.verts.card G.K).sum := by
      rw [Bc, hcd.hs, Multiset.map_add, Multiset.sum_add]
    have hnew : Bc L d ⟨X, ⟨H, H.card, X.card⟩ ::ₘ gs⟩ =
        wt d H * F + (gs.map fun G => wt d G.verts * fac L X.card G.verts.card G.K).sum := by
      simp [Bc, hF]
    have hO : (others.map (Bc L d)).sum + wt d M ≤ wt d M * F := by
      rw [hcd.hwt d, ← Multiset.sum_map_add, ← Multiset.sum_map_mul_right]
      refine Multiset.sum_map_le_sum_map _ _ fun C hC => ?_
      rw [← (hcd.hO C hC).cov d, ← Multiset.sum_map_mul_right, Bc, ← Multiset.sum_map_add]
      refine Multiset.sum_map_le_sum_map _ _ fun G hG => ?_
      have hne := (hcd.hO C hC).ne G hG
      have hCne : C.verts.Nonempty := by
        have := (hcd.hO C hC).card_le hG
        exact Finset.card_pos.mp (lt_of_lt_of_le (Finset.card_pos.mpr hne) this)
      have hf := fac_lt (L := L) (K := G.K) (hcd.lg_lt hC hCne) (hcd.lg_G_H hC hG)
        (lgK_le ((hcd.hO C hC).K_le G hG) ((hcd.hO C hC).K_pos G hG))
      calc wt d G.verts * fac L C.verts.card G.verts.card G.K + wt d G.verts
          = wt d G.verts * (fac L C.verts.card G.verts.card G.K + 1) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ hf
    have hA : (gA.map fun G => wt d G.verts * fac L S.verts.card G.verts.card G.K).sum +
        (gA.map fun G => wt d G.verts).sum ≤ (gA.map fun G => wt d G.verts).sum * F := by
      rw [← Multiset.sum_map_add, ← Multiset.sum_map_mul_right]
      refine Multiset.sum_map_le_sum_map _ _ fun G hG => ?_
      have hGS : G ∈ S.groups := by
        rw [hcd.hs]
        exact Multiset.mem_add.mpr (Or.inl hG)
      have hf := fac_lt' (L := L) (K := G.K) hcd.lg_S (hcd.hcls G hG)
        (lgK_le (hcd.hS.K_le G hGS) (hcd.hS.K_pos G hGS))
      calc wt d G.verts * fac L S.verts.card G.verts.card G.K + wt d G.verts
          = wt d G.verts * (fac L S.verts.card G.verts.card G.K + 1) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ hf
    have hgs : (gs.map fun G => wt d G.verts * fac L S.verts.card G.verts.card G.K).sum ≤
        (gs.map fun G => wt d G.verts * fac L X.card G.verts.card G.K).sum := by
      refine Multiset.sum_map_le_sum_map _ _ fun G _ => Nat.mul_le_mul_left _ ?_
      have : lg S.verts.card ≤ lg X.card := hcd.lg_S
      have h6 : (L + 1) * (lg S.verts.card + lg G.verts.card) ≤ (L + 1) * (lg X.card + lg G.verts.card) :=
        Nat.mul_le_mul_left _ (by omega)
      simp only [fac]
      omega
    rw [hSsplit, hnew, hcd.hH d, hcd.sum_A d, add_mul]
    omega
  | exhaust rest C G gs hg hK =>
    have hC := hσ.cont C (Multiset.mem_cons_self _ _)
    have hG : G ∈ C.groups := by
      rw [hg]
      exact Multiset.mem_cons_self _ _
    simp only [Bp, Ev.build, Multiset.map_cons, Multiset.sum_cons]
    have h1 : Bc L d C = wt d G.verts * fac L C.verts.card G.verts.card G.K +
        (gs.map fun G' => wt d G'.verts * fac L C.verts.card G'.verts.card G'.K).sum := by
      rw [Bc, hg, Multiset.map_cons, Multiset.sum_cons]
    have h2 : Bc L d ⟨C.verts, ⟨G.verts, 2 * G.K, C.verts.card⟩ ::ₘ gs⟩ =
        wt d G.verts * fac L C.verts.card G.verts.card (2 * G.K) +
        (gs.map fun G' => wt d G'.verts * fac L C.verts.card G'.verts.card G'.K).sum := by
      simp [Bc]
    have h3 : fac L C.verts.card G.verts.card (2 * G.K) = fac L C.verts.card G.verts.card G.K + 1 := by
      have := Nat.log_mul_base (b := 2) (n := G.K) (by norm_num) (by have := hC.K_pos G hG; omega)
      simp only [fac, lg, mul_comm 2 G.K, this]
      omega
    rw [h1, h2, h3, mul_add]
    omega

end Steps

/-! ## Tallies over a run -/

section Run

variable [Fintype V] {us : List V} {evs : List (Ev V)} {σ : Multiset (Cont V)}

theorem run_P1 (hus : us.Nodup) (h : Run us evs σ) (d : V → ℕ) :
    (evs.map fun e => wt d e.moved).sum ≤ P1 d σ := by
  induction h with
  | init => simp [P1, initConts]
  | step hr hs ih =>
    have := step_P1 hs (hr.wf hus) d
    simp only [List.map_cons, List.sum_cons]
    omega

theorem run_P2 (hus : us.Nodup) (h : Run us evs σ) (d : V → ℕ) :
    (evs.map fun e => (e.absorbed.map (wt d)).sum).sum ≤ P2 d σ := by
  induction h with
  | init => simp [P2, P2c, initConts]
  | step hr hs ih =>
    have := step_P2 hs (hr.wf hus) d
    simp only [List.map_cons, List.sum_cons]
    omega

theorem run_Th (hus : us.Nodup) (h : Run us evs σ) :
    (evs.map Ev.exhaustK).sum + 2 * Th σ ≤
      2 * (lg (Fintype.card V) + 1) * (evs.map fun e => e.moved.card).sum := by
  induction h with
  | init =>
    have : Th (initConts us) = 0 := by
      clear hus
      induction us with
      | nil => simp [Th, initConts]
      | cons a l ih =>
        simp only [Th, initConts, List.map_cons, Multiset.map_coe, Multiset.sum_coe, List.sum_cons] at ih ⊢
        rw [ih]
        simp [Thc]
    simp [this]
  | step hr hs ih =>
    have := step_Th hs (hr.wf hus)
    simp only [List.map_cons, List.sum_cons]
    rw [Nat.mul_add (2 * (lg (Fintype.card V) + 1))]
    omega

theorem run_Bp (hus : us.Nodup) (h : Run us evs σ) (d : V → ℕ) :
    ((allBuilds us evs).map fun b => wt d b.1).sum ≤ Bp (lg (Fintype.card V) + 1) d σ := by
  induction h with
  | init =>
    simp only [allBuilds, List.map_nil, List.nil_append, List.map_map]
    induction us with
    | nil => simp [Bp, initConts]
    | cons a l ih =>
      have := ih (List.nodup_cons.mp hus).2
      simp only [initConts, List.map_cons, Multiset.map_coe, Multiset.sum_coe, List.sum_cons, Bp,
        Function.comp] at this ⊢
      simpa [Bc, fac, wt] using this
  | step hr hs ih =>
    have := step_Bp hs (hr.wf hus) d
    simp only [allBuilds, List.map_cons, List.cons_append, List.sum_cons] at ih ⊢
    omega

theorem AWF.P1_le {σ : Multiset (Cont V)} (hσ : AWF σ) (d : V → ℕ) :
    P1 d σ ≤ wt d univ * lg (Fintype.card V) := by
  calc P1 d σ ≤ (σ.map fun C => wt d C.verts * lg (Fintype.card V)).sum :=
        Multiset.sum_map_le_sum_map _ _ fun C _ =>
          Nat.mul_le_mul_left _ (Nat.log_mono_right (Finset.card_le_univ _))
    _ = (σ.map fun C => wt d C.verts).sum * lg (Fintype.card V) := Multiset.sum_map_mul_right ..
    _ ≤ _ := Nat.mul_le_mul_right _ (hσ.total d)

theorem AWF.P2_le {σ : Multiset (Cont V)} (hσ : AWF σ) (d : V → ℕ) :
    P2 d σ ≤ wt d univ * lg (Fintype.card V) := by
  calc P2 d σ ≤ (σ.map fun C => wt d C.verts * lg (Fintype.card V)).sum := by
        refine Multiset.sum_map_le_sum_map _ _ fun C hC => ?_
        rw [← (hσ.cont C hC).cov d, ← Multiset.sum_map_mul_right]
        exact Multiset.sum_map_le_sum_map _ _ fun G _ =>
          Nat.mul_le_mul_left _ (Nat.log_mono_right (Finset.card_le_univ _))
    _ = (σ.map fun C => wt d C.verts).sum * lg (Fintype.card V) := Multiset.sum_map_mul_right ..
    _ ≤ _ := Nat.mul_le_mul_right _ (hσ.total d)

/-- The bound on `Bp`: each factor is at most `1 + (L + 1) 2 (L - 1) + L = (L + 1) (2 L - 1)`, and we use the
bound `(2 L + 1) (L + 1)` of the notes. -/
theorem AWF.Bp_le {σ : Multiset (Cont V)} (hσ : AWF σ) (d : V → ℕ) :
    Bp (lg (Fintype.card V) + 1) d σ ≤
      wt d univ * ((2 * (lg (Fintype.card V) + 1) + 1) * (lg (Fintype.card V) + 1 + 1)) := by
  set ℓ := lg (Fintype.card V) with hℓ
  set B := (2 * (ℓ + 1) + 1) * (ℓ + 1 + 1) with hB
  calc Bp (ℓ + 1) d σ ≤ (σ.map fun C => wt d C.verts * B).sum := by
        refine Multiset.sum_map_le_sum_map _ _ fun C hC => ?_
        rw [← (hσ.cont C hC).cov d, ← Multiset.sum_map_mul_right]
        refine Multiset.sum_map_le_sum_map _ _ fun G hG => Nat.mul_le_mul_left _ ?_
        have h1 : lg C.verts.card ≤ ℓ := Nat.log_mono_right (Finset.card_le_univ _)
        have h2 : lg G.verts.card ≤ ℓ := Nat.log_mono_right (Finset.card_le_univ _)
        have h3 : lg G.K ≤ ℓ + 1 := lgK_le ((hσ.cont C hC).K_le G hG) ((hσ.cont C hC).K_pos G hG)
        have h4 : (ℓ + 1 + 1) * (lg C.verts.card + lg G.verts.card) ≤ (ℓ + 1 + 1) * (ℓ + ℓ) :=
          Nat.mul_le_mul_left _ (by omega)
        simp only [fac, hB]
        nlinarith
    _ = (σ.map fun C => wt d C.verts).sum * B := Multiset.sum_map_mul_right ..
    _ ≤ _ := Nat.mul_le_mul_right _ (hσ.total d)

end Run

/-! ## Lemma 4 and Lemma 5 -/

/-- `L = ⌊log₂ n⌋ + 1`. -/
abbrev logL (n : ℕ) : ℕ := Nat.log 2 n + 1

section Main

variable [Fintype V] {us : List V} {evs : List (Ev V)} {σ : Multiset (Cont V)}

/-- The indicator weight of a vertex. -/
def ind (v : V) : V → ℕ := fun x => if x = v then 1 else 0

theorem wt_ind (v : V) (A : Finset V) : wt (ind v) A = if v ∈ A then 1 else 0 := by
  simp [wt, ind]

theorem wt_ind_univ (v : V) : wt (ind v) univ = 1 := by simp [wt_ind]

/-- **Lemma 4(a).** A vertex is in `M` at most `L` times. -/
theorem lemma4a (hus : us.Nodup) (h : Run us evs σ) (v : V) :
    (evs.filter fun e => v ∈ e.moved).length ≤ logL (Fintype.card V) := by
  have h1 := (run_P1 hus h (ind v)).trans ((h.wf hus).P1_le (ind v))
  rw [wt_ind_univ, one_mul] at h1
  have h2 : (evs.filter fun e => v ∈ e.moved).length = (evs.map fun e => wt (ind v) e.moved).sum := by
    clear h h1
    induction evs with
    | nil => simp
    | cons e l ih =>
      by_cases hv : v ∈ e.moved <;> simp [List.filter_cons, wt_ind, hv, ih] <;> omega
  have h3 : logL (Fintype.card V) = lg (Fintype.card V) + 1 := rfl
  omega

/-- **Lemma 4(b).** A vertex is in a group absorbed into `H` at most `L` times. -/
theorem lemma4b (hus : us.Nodup) (h : Run us evs σ) (v : V) :
    (evs.map fun e => e.absorbed.countP fun A => v ∈ A).sum ≤ logL (Fintype.card V) := by
  have h1 := (run_P2 hus h (ind v)).trans ((h.wf hus).P2_le (ind v))
  rw [wt_ind_univ, one_mul] at h1
  have h2 : ∀ A : Multiset (Finset V), (A.map (wt (ind v))).sum = A.countP fun A => v ∈ A := by
    intro A
    induction A using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih, wt_ind]
      by_cases hv : v ∈ a <;> simp [Multiset.countP_cons, hv] <;> omega
  simp only [h2] at h1
  have h3 : logL (Fintype.card V) = lg (Fintype.card V) + 1 := rfl
  omega

/-- The budget of the build of a contraction, `0` for exhaustion events. -/
def Ev.contractK : Ev V → ℕ
  | .contract _ _ H => H.card
  | .exhaust _ _ => 0

/-- The size of the new group of a contraction, from its moved and absorbed sets. -/
theorem AStep.contractK_eq {σ σ' : Multiset (Cont V)} {e : Ev V} (h : AStep σ e σ') (hσ : AWF σ) :
    e.contractK = e.moved.card + (e.absorbed.map (wt fun _ => 1)).sum := by
  cases h with
  | contract rest others S M H A gs h1 h2 h3 h4 h5 =>
    obtain ⟨gA, hcd⟩ := cd_of_step hσ h1 h2 h3 h4 h5
    have := hcd.hH fun _ => 1
    simpa [Ev.contractK, Ev.moved, Ev.absorbed, wt_one] using this
  | exhaust rest C G gs hg hK => simp [Ev.contractK, Ev.moved, Ev.absorbed]

theorem Ev.build_K (e : Ev V) : e.build.2 = e.contractK + e.exhaustK := by
  cases e <;> simp [Ev.build, Ev.contractK, Ev.exhaustK]

theorem run_contractK (hus : us.Nodup) (h : Run us evs σ) :
    (evs.map Ev.contractK).sum =
      (evs.map fun e => e.moved.card).sum + (evs.map fun e => (e.absorbed.map (wt fun _ => 1)).sum).sum := by
  induction h with
  | init => simp
  | step hr hs ih =>
    have := hs.contractK_eq (hr.wf hus)
    simp only [List.map_cons, List.sum_cons]
    omega

theorem run_moved_le (hus : us.Nodup) (h : Run us evs σ) :
    (evs.map fun e => e.moved.card).sum ≤ Fintype.card V * lg (Fintype.card V) := by
  have h1 := (run_P1 hus h fun _ => 1).trans ((h.wf hus).P1_le fun _ => 1)
  simpa [wt_one] using h1

theorem run_absorbed_le (hus : us.Nodup) (h : Run us evs σ) :
    (evs.map fun e => (e.absorbed.map (wt fun _ => 1)).sum).sum ≤ Fintype.card V * lg (Fintype.card V) := by
  have h1 := (run_P2 hus h fun _ => 1).trans ((h.wf hus).P2_le fun _ => 1)
  simpa [wt_one] using h1

/-- **Lemma 4(c).** Summing over contraction builds, `Σ |H| ≤ 2 n L`. -/
theorem lemma4c (hus : us.Nodup) (h : Run us evs σ) :
    (evs.map Ev.contractK).sum ≤ 2 * Fintype.card V * logL (Fintype.card V) := by
  rw [run_contractK hus h]
  have h1 := run_moved_le hus h
  have h2 := run_absorbed_le hus h
  have h3 : Fintype.card V * lg (Fintype.card V) ≤ Fintype.card V * logL (Fintype.card V) :=
    Nat.mul_le_mul_left _ (by simp [logL])
  have h4 : 2 * Fintype.card V * logL (Fintype.card V) = 2 * (Fintype.card V * logL (Fintype.card V)) := by
    ring
  omega

/-- **Lemma 4(d).** Each vertex lies in at most `(2 L + 1) (L + 1)` builds. -/
theorem lemma4d (hus : us.Nodup) (h : Run us evs σ) (v : V) :
    ((allBuilds us evs).filter fun b => v ∈ b.1).length ≤
      (2 * logL (Fintype.card V) + 1) * (logL (Fintype.card V) + 1) := by
  have h1 := (run_Bp hus h (ind v)).trans ((h.wf hus).Bp_le (ind v))
  rw [wt_ind_univ, one_mul] at h1
  have h2 : ∀ l : List (Finset V × ℕ), (l.map fun b => wt (ind v) b.1).sum = (l.filter fun b => v ∈ b.1).length := by
    intro l
    induction l with
    | nil => simp
    | cons b l ih =>
      rw [List.map_cons, List.sum_cons, ih, wt_ind, List.filter_cons]
      by_cases hv : v ∈ b.1 <;> simp [hv] <;> omega
  rw [h2] at h1
  exact h1

/-- **Σ N(G).** The sum of the weights of the builds, for any vertex weights: with `d` the in-degree,
`Σ_builds N(G) ≤ m (2 L + 1) (L + 1)`. -/
theorem sum_wt_le (hus : us.Nodup) (h : Run us evs σ) (d : V → ℕ) :
    ((allBuilds us evs).map fun b => wt d b.1).sum ≤
      wt d univ * ((2 * logL (Fintype.card V) + 1) * (logL (Fintype.card V) + 1)) :=
  (run_Bp hus h d).trans ((h.wf hus).Bp_le d)

/-- **Lemma 4(e).** Summing over all builds, `Σ K ≤ n + 2 n L + 2 n L²`. -/
theorem lemma4e (hus : us.Nodup) (h : Run us evs σ) :
    ((allBuilds us evs).map Prod.snd).sum ≤
      Fintype.card V + 2 * Fintype.card V * logL (Fintype.card V) +
        2 * Fintype.card V * logL (Fintype.card V) ^ 2 := by
  set n := Fintype.card V with hn
  set L := logL n with hL
  have hsplit : ((allBuilds us evs).map Prod.snd).sum =
      (evs.map Ev.contractK).sum + (evs.map Ev.exhaustK).sum + us.length := by
    have h1 : ∀ l : List (Ev V), (l.map fun e => e.build.2).sum =
        (l.map Ev.contractK).sum + (l.map Ev.exhaustK).sum := by
      intro l
      induction l with
      | nil => simp
      | cons e l ih =>
        simp only [List.map_cons, List.sum_cons, ih, e.build_K]
        omega
    have h2 : ∀ u : List V, ((u.map fun v => (({v} : Finset V), 1)).map Prod.snd).sum = u.length := by
      intro u
      induction u with
      | nil => simp
      | cons a l ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
        omega
    simp only [allBuilds, List.map_append, List.sum_append, List.map_map, Function.comp_def]
    rw [h1]
    have := h2 us
    simp only [List.map_map, Function.comp_def] at this
    omega
  have hus' : us.length ≤ n := by
    rw [hn, ← List.toFinset_card_of_nodup hus]
    exact Finset.card_le_univ _
  have hc := lemma4c hus h
  have hm := run_moved_le hus h
  have hx := run_Th hus h
  rw [← hn] at hc hm hx
  rw [← hL] at hc
  have hx' : (evs.map Ev.exhaustK).sum ≤ 2 * L * (n * lg n) := by
    have h5 : 2 * (lg n + 1) * (evs.map fun e => e.moved.card).sum ≤ 2 * L * (n * lg n) :=
      Nat.mul_le_mul_left _ hm
    omega
  have hL2 : 2 * L * (n * lg n) ≤ 2 * n * L ^ 2 := by
    have : n * lg n ≤ n * L := Nat.mul_le_mul_left _ (by simp [hL, logL])
    calc 2 * L * (n * lg n) ≤ 2 * L * (n * L) := Nat.mul_le_mul_left _ this
      _ = 2 * n * L ^ 2 := by ring
  rw [hsplit]
  omega

/-- Cauchy-Schwarz, on a list. -/
theorem sum_topKCost_le (l : List (ℕ × ℕ)) :
    (l.map fun x => topKCost x.1 x.2).sum ≤
      Real.sqrt (((l.map Prod.fst).sum : ℕ) * ((l.map Prod.snd).sum : ℕ)) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    refine (add_le_add le_rfl ih).trans ?_
    rw [Nat.cast_add, Nat.cast_add]
    set A : ℝ := (((l.map Prod.fst).sum : ℕ) : ℝ)
    set B : ℝ := (((l.map Prod.snd).sum : ℕ) : ℝ)
    have hA : 0 ≤ A := Nat.cast_nonneg _
    have hB : 0 ≤ B := Nat.cast_nonneg _
    have ha : (0 : ℝ) ≤ x.1 := Nat.cast_nonneg _
    have hb : (0 : ℝ) ≤ x.2 := Nat.cast_nonneg _
    apply Real.le_sqrt_of_sq_le
    rw [topKCost, Real.sqrt_mul ha, Real.sqrt_mul hA, add_sq, mul_pow, mul_pow,
      Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hA, Real.sq_sqrt hB]
    have hk := sq_nonneg (Real.sqrt x.1 * Real.sqrt B - Real.sqrt A * Real.sqrt x.2)
    have e1 : (Real.sqrt x.1 * Real.sqrt B - Real.sqrt A * Real.sqrt x.2) ^ 2 =
        x.1 * B + A * x.2 - 2 * (Real.sqrt x.1 * Real.sqrt x.2) * (Real.sqrt A * Real.sqrt B) := by
      rw [sub_sq, mul_pow, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hA, Real.sq_sqrt hB]
      ring
    nlinarith

/-- **Lemma 5.** `Σ_builds √(K N(G)) ≤ √(Σ K · Σ N(G))`, for any vertex weights. -/
theorem lemma5_cs (us : List V) (evs : List (Ev V)) (d : V → ℕ) :
    ((allBuilds us evs).map fun b => topKCost b.2 (wt d b.1)).sum ≤
      Real.sqrt ((((allBuilds us evs).map Prod.snd).sum : ℕ) * (((allBuilds us evs).map fun b => wt d b.1).sum : ℕ)) := by
  have := sum_topKCost_le ((allBuilds us evs).map fun b => (b.2, wt d b.1))
  simpa [List.map_map, Function.comp_def] using this

theorem poly_bound (L : ℕ) (hL : 1 ≤ L) :
    (1 + 2 * L + 2 * L ^ 2) * ((2 * L + 1) * (L + 1)) ≤ 36 * L ^ 4 := by
  have h1 : 1 + 2 * L + 2 * L ^ 2 ≤ 5 * L ^ 2 := by nlinarith
  have h2 : (2 * L + 1) * (L + 1) ≤ 6 * L ^ 2 := by nlinarith
  calc (1 + 2 * L + 2 * L ^ 2) * ((2 * L + 1) * (L + 1)) ≤ (5 * L ^ 2) * (6 * L ^ 2) :=
        Nat.mul_le_mul h1 h2
    _ ≤ 36 * L ^ 4 := by nlinarith [Nat.zero_le (L ^ 4)]

theorem cast_bound {a b L n m : ℕ} (h : a * b ≤ 36 * L ^ 4 * (n * m)) :
    (a : ℝ) * (b : ℝ) ≤ ((6 : ℝ) * (L : ℝ) ^ 2) ^ 2 * ((n : ℝ) * (m : ℝ)) := by
  have h1 : ((a * b : ℕ) : ℝ) ≤ ((36 * L ^ 4 * (n * m) : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h1
  calc (a : ℝ) * b ≤ _ := h1
    _ = _ := by ring

/-- **Lemma 5, the final bound.** With `m = wt d univ`, which is the number of edges when `d` is the in-degree:
`Σ_builds √(K N(G)) ≤ 6 √(n m) L²`. -/
theorem lemma5 (hus : us.Nodup) (h : Run us evs σ) (d : V → ℕ) :
    ((allBuilds us evs).map fun b => topKCost b.2 (wt d b.1)).sum ≤
      6 * Real.sqrt ((Fintype.card V : ℝ) * (wt d univ : ℝ)) * (logL (Fintype.card V) : ℝ) ^ 2 := by
  set n := Fintype.card V with hn
  set m := wt d univ with hm
  set L := logL n with hL
  have hL1 : 1 ≤ L := by simp [hL, logL]
  refine (lemma5_cs us evs d).trans ?_
  have hK := lemma4e hus h
  have hN := sum_wt_le hus h d
  rw [← hn, ← hL] at hK hN
  rw [← hm] at hN
  have hprod : ((allBuilds us evs).map Prod.snd).sum * ((allBuilds us evs).map fun b => wt d b.1).sum ≤
      36 * L ^ 4 * (n * m) := by
    calc _ ≤ (n + 2 * n * L + 2 * n * L ^ 2) * (m * ((2 * L + 1) * (L + 1))) := Nat.mul_le_mul hK hN
      _ = ((1 + 2 * L + 2 * L ^ 2) * ((2 * L + 1) * (L + 1))) * (n * m) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (poly_bound L hL1)
  have hprod' := cast_bound hprod
  calc _ ≤ Real.sqrt (((6 : ℝ) * (L : ℝ) ^ 2) ^ 2 * ((n : ℝ) * (m : ℝ))) := Real.sqrt_le_sqrt hprod'
    _ = _ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      ring

end Main

end Arborescence
