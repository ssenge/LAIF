import SsspFlow.AggMux

/-!
# Streams of minima along sources

Every node holds items, pairs of a key and a value, and listens to some of its neighbours, its sources. Through
sources a node reaches other nodes (`Clo`), and it sends, in increasing order, every key of the items of these
nodes with the least value of the key (`keysC`, `minCl`), and then an end mark. It sends a key once every source
has sent this key, a larger one or its end mark (`nextE`).

With a rank `h` that drops along sources, the key of rank `r` at `v` is sent within `h v + r + 1` rounds and the
end mark within `h v + k + 1` rounds, where `k` is the number of keys at `v` (`timing`). `stream_full` sums this
up, and `ans_eq` reads the least value of a key from a complete stream.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Cslib.Congest

namespace SsspFlow.Congest

/-- An element of a stream: a key with its value, or `none` for the end mark. -/
abbrev Elt := Option (ℕ × ℕ)

/-- The keys of a stream. -/
def keysL (l : List Elt) : Finset ℕ := ((l.filterMap id).map Prod.fst).toFinset

/-- The values of a key in a stream. -/
def valsL (l : List Elt) (κ : ℕ) : Finset ℕ :=
  (((l.filterMap id).filter fun p => p.1 = κ).map Prod.snd).toFinset

theorem mem_keysL {l : List Elt} {κ : ℕ} : κ ∈ keysL l ↔ ∃ m, some (κ, m) ∈ l := by
  simp [keysL]

theorem mem_valsL {l : List Elt} {κ m : ℕ} : m ∈ valsL l κ ↔ some (κ, m) ∈ l := by
  simp [valsL]

/-- A stream has passed a key if it holds this key, a larger one or the end mark. -/
def Passed (l : List Elt) (κ : ℕ) : Prop := none ∈ l ∨ ∃ κ' ∈ keysL l, κ ≤ κ'

instance (l : List Elt) (κ : ℕ) : Decidable (Passed l κ) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem Passed.anti {l : List Elt} {κ κ' : ℕ} (h : Passed l κ') (hk : κ ≤ κ') : Passed l κ := by
  rcases h with h | ⟨a, ha, hle⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, ha, hk.trans hle⟩

theorem Passed.mono {l l' : List Elt} {κ : ℕ} (h : Passed l κ) (hl : ∀ e ∈ l, e ∈ l') : Passed l' κ := by
  rcases h with h | ⟨a, ha, hle⟩
  · exact Or.inl (hl _ h)
  · obtain ⟨m, hm⟩ := mem_keysL.1 ha
    exact Or.inr ⟨a, mem_keysL.2 ⟨m, hl _ hm⟩, hle⟩

section Next

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The streams of the sources; other nodes count as empty. -/
def view (sr : V → Bool) (R : V → List Elt) (u : V) : List Elt := if sr u = true then R u else []

/-- The keys of the items and of the streams. -/
def kset (ow : List (ℕ × ℕ)) (R : V → List Elt) : Finset ℕ :=
  (ow.map Prod.fst).toFinset ∪ Finset.univ.biUnion fun u => keysL (R u)

/-- The values of a key in the items and in the streams. -/
def vset (ow : List (ℕ × ℕ)) (R : V → List Elt) (κ : ℕ) : Finset ℕ :=
  ((ow.filter fun p => p.1 = κ).map Prod.snd).toFinset ∪ Finset.univ.biUnion fun u => valsL (R u) κ

theorem mem_kset {ow : List (ℕ × ℕ)} {R : V → List Elt} {κ : ℕ} :
    κ ∈ kset ow R ↔ (∃ m, (κ, m) ∈ ow) ∨ ∃ u, κ ∈ keysL (R u) := by
  simp [kset]

theorem mem_vset {ow : List (ℕ × ℕ)} {R : V → List Elt} {κ m : ℕ} :
    m ∈ vset ow R κ ↔ (κ, m) ∈ ow ∨ ∃ u, some (κ, m) ∈ R u := by
  simp only [vset, Finset.mem_union, List.mem_toFinset, List.mem_map, List.mem_filter,
    decide_eq_true_eq, Finset.mem_biUnion, Finset.mem_univ, true_and, mem_valsL]
  constructor
  · rintro (⟨⟨a, b⟩, ⟨h1, rfl⟩, rfl⟩ | h)
    · exact Or.inl h1
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ⟨(κ, m), ⟨h, rfl⟩, rfl⟩
    · exact Or.inr h

/-- The least value of a key in the items and in the streams, and `0` if there is none. -/
noncomputable def vmin (ow : List (ℕ × ℕ)) (R : V → List Elt) (κ : ℕ) : ℕ :=
  if h : (vset ow R κ).Nonempty then (vset ow R κ).min' h else 0

/-- The keys that may come next: above every key sent. -/
def cand (ow : List (ℕ × ℕ)) (E : List Elt) (R : V → List Elt) : Finset ℕ :=
  (kset ow R).filter fun κ => ∀ κ' ∈ keysL E, κ' < κ

/-- The next element to send, if any. `E` is the stream sent so far and `R` gives the streams of the
sources. -/
noncomputable def nextE (ow : List (ℕ × ℕ)) (sr : V → Bool) (E : List Elt) (R : V → List Elt) :
    Option Elt :=
  if none ∈ E then none
  else if h : (cand ow E R).Nonempty then
    if ∀ u, sr u = true → Passed (R u) ((cand ow E R).min' h) then
      some (some ((cand ow E R).min' h, vmin ow R ((cand ow E R).min' h)))
    else none
  else if ∀ u, sr u = true → none ∈ R u then some none else none

theorem nextE_some {ow : List (ℕ × ℕ)} {sr : V → Bool} {E : List Elt} {R : V → List Elt} {e : Elt}
    (h : nextE ow sr E R = some e) :
    none ∉ E ∧ ((∃ h : (cand ow E R).Nonempty, (∀ u, sr u = true → Passed (R u) ((cand ow E R).min' h)) ∧
      e = some ((cand ow E R).min' h, vmin ow R ((cand ow E R).min' h))) ∨
      (¬ (cand ow E R).Nonempty ∧ (∀ u, sr u = true → none ∈ R u) ∧ e = none)) := by
  unfold nextE at h
  by_cases h0 : none ∈ E
  · rw [ite_eq_left h0] at h
    exact absurd h (by simp)
  rw [ite_eq_right h0] at h
  refine ⟨h0, ?_⟩
  by_cases hc : (cand ow E R).Nonempty
  · rw [dite_eq_left hc] at h
    by_cases hp : ∀ u, sr u = true → Passed (R u) ((cand ow E R).min' hc)
    · rw [ite_eq_left hp, Option.some.injEq] at h
      exact Or.inl ⟨hc, hp, h.symm⟩
    · rw [ite_eq_right hp] at h
      exact absurd h (by simp)
  · rw [dite_eq_right hc] at h
    by_cases hn : ∀ u, sr u = true → none ∈ R u
    · rw [ite_eq_left hn, Option.some.injEq] at h
      exact Or.inr ⟨hc, hn, h.symm⟩
    · rw [ite_eq_right hn] at h
      exact absurd h (by simp)

theorem nextE_key {ow : List (ℕ × ℕ)} {sr : V → Bool} {E : List Elt} {R : V → List Elt}
    (h0 : none ∉ E) (hc : (cand ow E R).Nonempty)
    (hp : ∀ u, sr u = true → Passed (R u) ((cand ow E R).min' hc)) :
    nextE ow sr E R = some (some ((cand ow E R).min' hc, vmin ow R ((cand ow E R).min' hc))) := by
  unfold nextE
  rw [ite_eq_right h0, dite_eq_left hc, ite_eq_left hp]

theorem nextE_end {ow : List (ℕ × ℕ)} {sr : V → Bool} {E : List Elt} {R : V → List Elt}
    (h0 : none ∉ E) (hc : ¬ (cand ow E R).Nonempty) (hn : ∀ u, sr u = true → none ∈ R u) :
    nextE ow sr E R = some none := by
  unfold nextE
  rw [ite_eq_right h0, dite_eq_right hc, ite_eq_left hn]

end Next

section Closure

variable {V : Type*} [Fintype V] [DecidableEq V] (own : V → List (ℕ × ℕ)) (src : V → V → Bool)

/-- `w` is reached from `v` along sources. -/
def Clo (v w : V) : Prop := Relation.ReflTransGen (fun a b => src a b = true) v w

open Classical in
/-- The items of the nodes reached from `v`. -/
noncomputable def CI (v : V) : Finset (ℕ × ℕ) :=
  (Finset.univ.filter (Clo src v)).biUnion fun w => (own w).toFinset

/-- The keys at `v`. -/
noncomputable def keysC (v : V) : Finset ℕ := (CI own src v).image Prod.fst

/-- The least value of a key at `v`, and `0` if there is none. -/
noncomputable def minCl (v : V) (κ : ℕ) : ℕ :=
  if h : (((CI own src v).filter fun p => p.1 = κ).image Prod.snd).Nonempty then
    (((CI own src v).filter fun p => p.1 = κ).image Prod.snd).min' h else 0

/-- An element that `v` may send: the end mark, or a key at `v` with its least value. -/
def GoodE (v : V) (e : Elt) : Prop := e = none ∨ ∃ κ ∈ keysC own src v, e = some (κ, minCl own src v κ)

variable {own src}

theorem mem_CI {v : V} {p : ℕ × ℕ} : p ∈ CI own src v ↔ ∃ w, Clo src v w ∧ p ∈ own w := by
  classical
  simp [CI]

theorem mem_keysC {v : V} {κ : ℕ} : κ ∈ keysC own src v ↔ ∃ m, (κ, m) ∈ CI own src v := by
  simp [keysC]

theorem CI_step {v : V} {p : ℕ × ℕ} :
    p ∈ CI own src v ↔ p ∈ own v ∨ ∃ u, src v u = true ∧ p ∈ CI own src u := by
  rw [mem_CI]
  constructor
  · rintro ⟨w, hw, hp⟩
    rcases Relation.ReflTransGen.cases_head_iff.1 hw with rfl | ⟨u, hu, hw'⟩
    · exact Or.inl hp
    · exact Or.inr ⟨u, hu, mem_CI.2 ⟨w, hw', hp⟩⟩
  · rintro (hp | ⟨u, hu, hp⟩)
    · exact ⟨v, Relation.ReflTransGen.refl, hp⟩
    · obtain ⟨w, hw, hp⟩ := mem_CI.1 hp
      exact ⟨w, Relation.ReflTransGen.head hu hw, hp⟩

theorem CI_sub {v u : V} (h : src v u = true) {p : ℕ × ℕ} (hp : p ∈ CI own src u) : p ∈ CI own src v :=
  CI_step.2 (Or.inr ⟨u, h, hp⟩)

theorem keysC_sub {v u : V} (h : src v u = true) : keysC own src u ⊆ keysC own src v := by
  intro κ hκ
  obtain ⟨m, hm⟩ := mem_keysC.1 hκ
  exact mem_keysC.2 ⟨m, CI_sub h hm⟩

theorem minCl_mem {v : V} {κ : ℕ} (h : κ ∈ keysC own src v) : (κ, minCl own src v κ) ∈ CI own src v := by
  obtain ⟨m, hm⟩ := mem_keysC.1 h
  have hne : (((CI own src v).filter fun p => p.1 = κ).image Prod.snd).Nonempty :=
    ⟨m, Finset.mem_image.2 ⟨(κ, m), Finset.mem_filter.2 ⟨hm, rfl⟩, rfl⟩⟩
  unfold minCl
  rw [dite_eq_left hne]
  obtain ⟨p, hp, hpe⟩ := Finset.mem_image.1 (Finset.min'_mem _ hne)
  obtain ⟨hp, hpk⟩ := Finset.mem_filter.1 hp
  rw [← hpe]
  convert hp using 1
  exact Prod.ext hpk.symm rfl

theorem minCl_le {v : V} {κ m : ℕ} (h : (κ, m) ∈ CI own src v) : minCl own src v κ ≤ m := by
  have hm : m ∈ ((CI own src v).filter fun p => p.1 = κ).image Prod.snd :=
    Finset.mem_image.2 ⟨(κ, m), Finset.mem_filter.2 ⟨h, rfl⟩, rfl⟩
  unfold minCl
  rw [dite_eq_left ⟨m, hm⟩]
  exact Finset.min'_le _ _ hm

theorem minCl_eq {v : V} {κ m : ℕ} (h : (κ, m) ∈ CI own src v)
    (hl : ∀ m', (κ, m') ∈ CI own src v → m ≤ m') : minCl own src v κ = m :=
  le_antisymm (minCl_le h) (hl _ (minCl_mem (mem_keysC.2 ⟨m, h⟩)))

end Closure

section Stream

variable {V : Type*} [Fintype V] [DecidableEq V] {own : V → List (ℕ × ℕ)} {src : V → V → Bool}
  {E : ℕ → V → List Elt}

/-- The recursion of the streams. -/
def StreamRec (own : V → List (ℕ × ℕ)) (src : V → V → Bool) (E : ℕ → V → List Elt) : Prop :=
  (∀ v, E 0 v = []) ∧
    ∀ t v, E (t + 1) v = E t v ++ (nextE (own v) (src v) (E t v) (view (src v) (E t))).toList

/-- The invariant at time `t`: every element sent is good, and a stream that has passed a key holds it. -/
def StreamInv (own : V → List (ℕ × ℕ)) (src : V → V → Bool) (E : ℕ → V → List Elt) (t : ℕ) : Prop :=
  (∀ v e, e ∈ E t v → GoodE own src v e) ∧
    ∀ v κ, κ ∈ keysC own src v → Passed (E t v) κ → some (κ, minCl own src v κ) ∈ E t v

theorem mem_view {sr : V → Bool} {R : V → List Elt} {u : V} {e : Elt} :
    e ∈ view sr R u ↔ sr u = true ∧ e ∈ R u := by
  unfold view
  by_cases h : sr u = true <;> simp [h]

section Inv

variable {t : ℕ} (hI : StreamInv own src E t)
include hI

theorem key_of_recv {u : V} {κ m : ℕ} (h : some (κ, m) ∈ E t u) :
    κ ∈ keysC own src u ∧ m = minCl own src u κ := by
  rcases hI.1 u _ h with h1 | ⟨κ', hκ', h2⟩
  · exact absurd h1 (by simp)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact ⟨hκ', rfl⟩

theorem kset_sub {v : V} : kset (own v) (view (src v) (E t)) ⊆ keysC own src v := by
  intro κ hκ
  rcases mem_kset.1 hκ with ⟨m, hm⟩ | ⟨u, hu⟩
  · exact mem_keysC.2 ⟨m, CI_step.2 (Or.inl hm)⟩
  · obtain ⟨m, hm⟩ := mem_keysL.1 hu
    obtain ⟨hs, hm⟩ := mem_view.1 hm
    exact keysC_sub hs (key_of_recv hI hm).1

theorem mem_kset_of {v : V} {κ : ℕ} (hκ : κ ∈ keysC own src v)
    (hp : ∀ u, src v u = true → Passed (E t u) κ) : κ ∈ kset (own v) (view (src v) (E t)) := by
  obtain ⟨m, hm⟩ := mem_keysC.1 hκ
  rcases CI_step.1 hm with hm | ⟨u, hu, hm⟩
  · exact mem_kset.2 (Or.inl ⟨m, hm⟩)
  · have hk : κ ∈ keysC own src u := mem_keysC.2 ⟨m, hm⟩
    have := hI.2 u κ hk (hp u hu)
    exact mem_kset.2 (Or.inr ⟨u, mem_keysL.2 ⟨_, mem_view.2 ⟨hu, this⟩⟩⟩)

theorem vmin_eq {v : V} {κ : ℕ} (hκ : κ ∈ keysC own src v)
    (hp : ∀ u, src v u = true → Passed (E t u) κ) :
    vmin (own v) (view (src v) (E t)) κ = minCl own src v κ := by
  have hS : ∀ m, m ∈ vset (own v) (view (src v) (E t)) κ → (κ, m) ∈ CI own src v := by
    intro m hm
    rcases mem_vset.1 hm with hm | ⟨u, hu⟩
    · exact CI_step.2 (Or.inl hm)
    · obtain ⟨hs, hu⟩ := mem_view.1 hu
      obtain ⟨hk, rfl⟩ := key_of_recv hI hu
      exact CI_sub hs (minCl_mem hk)
  have hL : ∀ m', (κ, m') ∈ CI own src v → ∃ m ∈ vset (own v) (view (src v) (E t)) κ, m ≤ m' := by
    intro m' hm'
    rcases CI_step.1 hm' with hm' | ⟨u, hu, hm'⟩
    · exact ⟨m', mem_vset.2 (Or.inl hm'), le_rfl⟩
    · have hk : κ ∈ keysC own src u := mem_keysC.2 ⟨m', hm'⟩
      exact ⟨minCl own src u κ, mem_vset.2 (Or.inr ⟨u, mem_view.2 ⟨hu, hI.2 u κ hk (hp u hu)⟩⟩),
        minCl_le hm'⟩
  obtain ⟨m₀, hm₀, -⟩ := hL _ (minCl_mem hκ)
  have hne : (vset (own v) (view (src v) (E t)) κ).Nonempty := ⟨m₀, hm₀⟩
  unfold vmin
  rw [dite_eq_left hne]
  symm
  refine minCl_eq (hS _ (Finset.min'_mem _ hne)) fun m' hm' => ?_
  obtain ⟨m, hm, hle⟩ := hL m' hm'
  exact (Finset.min'_le _ _ hm).trans hle

end Inv

theorem passed_append {l : List Elt} {e : Elt} {κ : ℕ} (h : Passed (l ++ [e]) κ) :
    Passed l κ ∨ e = none ∨ ∃ κ' m, e = some (κ', m) ∧ κ ≤ κ' := by
  rcases h with h | ⟨a, ha, hle⟩
  · rcases List.mem_append.1 h with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl (List.mem_singleton.1 h).symm)
  · obtain ⟨m, hm⟩ := mem_keysL.1 ha
    rcases List.mem_append.1 hm with hm | hm
    · exact Or.inl (Or.inr ⟨a, mem_keysL.2 ⟨m, hm⟩, hle⟩)
    · exact Or.inr (Or.inr ⟨a, m, (List.mem_singleton.1 hm).symm, hle⟩)

theorem streamInv (hR : StreamRec own src E) : ∀ t, StreamInv own src E t := by
  intro t
  induction t with
  | zero =>
    refine ⟨fun v e he => ?_, fun v κ _ hp => ?_⟩
    · rw [hR.1 v] at he
      exact absurd he (by simp)
    · rw [hR.1 v] at hp
      rcases hp with h | ⟨a, ha, -⟩
      · exact absurd h (by simp)
      · obtain ⟨m, hm⟩ := mem_keysL.1 ha
        exact absurd hm (by simp)
  | succ t hI =>
    -- The element added at `v` is good.
    have hgood : ∀ v e, nextE (own v) (src v) (E t v) (view (src v) (E t)) = some e → GoodE own src v e := by
      intro v e he
      rcases (nextE_some he).2 with ⟨hc, hp, rfl⟩ | ⟨-, -, rfl⟩
      · have hmem := Finset.min'_mem _ hc
        have hk : (cand (own v) (E t v) (view (src v) (E t))).min' hc ∈ keysC own src v :=
          kset_sub hI (Finset.mem_filter.1 hmem).1
        have hp' : ∀ u, src v u = true →
            Passed (E t u) ((cand (own v) (E t v) (view (src v) (E t))).min' hc) := fun u hu => by
          have := hp u hu
          unfold view at this
          rwa [ite_eq_left hu] at this
        exact Or.inr ⟨_, hk, by rw [vmin_eq hI hk hp']⟩
      · exact Or.inl rfl
    refine ⟨fun v e he => ?_, fun v κ hκ hp => ?_⟩
    · rw [hR.2 t v] at he
      rcases List.mem_append.1 he with he | he
      · exact hI.1 v e he
      · cases hn : nextE (own v) (src v) (E t v) (view (src v) (E t)) with
        | none => rw [hn] at he; exact absurd he (by simp)
        | some e' =>
          rw [hn, Option.toList_some, List.mem_singleton] at he
          rw [he]
          exact hgood v e' hn
    · rw [hR.2 t v] at hp ⊢
      by_cases hp0 : Passed (E t v) κ
      · exact List.mem_append_left _ (hI.2 v κ hκ hp0)
      cases hn : nextE (own v) (src v) (E t v) (view (src v) (E t)) with
      | none =>
        rw [hn, Option.toList_none, List.append_nil] at hp
        exact absurd hp hp0
      | some e =>
        rw [hn, Option.toList_some] at hp
        rw [Option.toList_some]
        have hlow : ∀ κ' ∈ keysL (E t v), κ' < κ := fun κ' hκ' =>
          lt_of_not_ge fun hge => hp0 (Or.inr ⟨κ', hκ', hge⟩)
        obtain ⟨h0, hcase⟩ := nextE_some hn
        rcases passed_append hp with hp' | rfl | ⟨κ', m, rfl, hle⟩
        · exact absurd hp' hp0
        · -- the end mark: then no key is left, and `κ` would be one
          rcases hcase with ⟨_, _, he⟩ | ⟨hc, hn', -⟩
          · exact absurd he (by simp)
          exfalso
          refine hc ⟨κ, Finset.mem_filter.2 ⟨?_, hlow⟩⟩
          refine mem_kset_of hI hκ fun u hu => Or.inl ?_
          have := hn' u hu
          unfold view at this
          rwa [ite_eq_left hu] at this
        · rcases hcase with ⟨hc, hpc, he⟩ | ⟨-, -, he⟩
          · simp only [Option.some.injEq, Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            have hpc' : ∀ u, src v u = true →
                Passed (E t u) ((cand (own v) (E t v) (view (src v) (E t))).min' hc) := fun u hu => by
              have := hpc u hu
              unfold view at this
              rwa [ite_eq_left hu] at this
            rcases lt_or_eq_of_le hle with hlt | heq
            · exfalso
              have hin : κ ∈ cand (own v) (E t v) (view (src v) (E t)) :=
                Finset.mem_filter.2 ⟨mem_kset_of hI hκ fun u hu => (hpc' u hu).anti hle, hlow⟩
              exact absurd (Finset.min'_le _ _ hin) (not_le.2 hlt)
            · subst heq
              refine List.mem_append_right _ (List.mem_singleton.2 ?_)
              rw [vmin_eq hI hκ hpc']
          · exact absurd he (by simp)

/-- The rank of a key at `v`: the number of smaller keys. -/
noncomputable def rankC (own : V → List (ℕ × ℕ)) (src : V → V → Bool) (v : V) (κ : ℕ) : ℕ :=
  ((keysC own src v).filter fun κ' => κ' < κ).card

theorem stream_mono (hR : StreamRec own src E) {t t' : ℕ} (h : t ≤ t') {v : V} {e : Elt}
    (he : e ∈ E t v) : e ∈ E t' v := by
  induction h with
  | refl => exact he
  | step _ ih =>
    rw [hR.2]
    exact List.mem_append_left _ ih

/-- **Timing.** With a rank `h` that drops along sources, a key of rank `r` at `v` is sent within
`h v + r + 1` rounds, and the end mark within `h v + k + 1` rounds, where `k` is the number of keys at `v`. -/
theorem timing (hR : StreamRec own src E) (h : V → ℕ) (hh : ∀ v u, src v u = true → h u < h v) :
    ∀ t, (∀ v κ, κ ∈ keysC own src v → h v + rankC own src v κ + 1 ≤ t →
      some (κ, minCl own src v κ) ∈ E t v) ∧
      (∀ v, h v + (keysC own src v).card + 1 ≤ t → none ∈ E t v) := by
  intro t
  induction t with
  | zero => exact ⟨fun _ _ _ h => absurd h (by omega), fun _ h => absurd h (by omega)⟩
  | succ t ih =>
    have hI := streamInv hR t
    -- A source has passed every key whose rank at `v` is small enough.
    have hsrcP : ∀ v u κ, src v u = true → h v + rankC own src v κ + 1 ≤ t + 1 → Passed (E t u) κ := by
      intro v u κ hu ht
      have hlt := hh v u hu
      by_cases hA : ((keysC own src u).filter fun κ'' => κ ≤ κ'').Nonempty
      · set κ'' := ((keysC own src u).filter fun κ'' => κ ≤ κ'').min' hA
        have hmem := Finset.mem_filter.1 (Finset.min'_mem _ hA)
        have hrank : rankC own src u κ'' ≤ rankC own src v κ := by
          unfold rankC
          refine Finset.card_le_card fun a ha => ?_
          obtain ⟨ha, hal⟩ := Finset.mem_filter.1 ha
          refine Finset.mem_filter.2 ⟨keysC_sub hu ha, lt_of_not_ge fun hge => ?_⟩
          exact absurd (Finset.min'_le _ _ (Finset.mem_filter.2 ⟨ha, hge⟩)) (not_le.2 hal)
        have := (ih.1 u κ'' hmem.1 (by omega))
        exact Or.inr ⟨κ'', mem_keysL.2 ⟨_, this⟩, hmem.2⟩
      · have hsub : keysC own src u ⊆ (keysC own src v).filter fun κ' => κ' < κ := by
          intro a ha
          refine Finset.mem_filter.2 ⟨keysC_sub hu ha, lt_of_not_ge fun hge => hA ⟨a, ?_⟩⟩
          exact Finset.mem_filter.2 ⟨ha, hge⟩
        have hcard := Finset.card_le_card hsub
        exact Or.inl (ih.2 u (by unfold rankC at ht; omega))
    refine ⟨fun v κ hκ ht => ?_, fun v ht => ?_⟩
    · by_cases hin : some (κ, minCl own src v κ) ∈ E t v
      · exact stream_mono hR (Nat.le_succ t) hin
      have hp0 : ¬ Passed (E t v) κ := fun hp => hin (hI.2 v κ hκ hp)
      have h0 : none ∉ E t v := fun h => hp0 (Or.inl h)
      have hlow : ∀ κ' ∈ keysL (E t v), κ' < κ := fun κ' hκ' =>
        lt_of_not_ge fun hge => hp0 (Or.inr ⟨κ', hκ', hge⟩)
      have hpv : ∀ u, src v u = true → Passed (view (src v) (E t) u) κ := fun u hu => by
        unfold view
        rw [ite_eq_left hu]
        exact hsrcP v u κ hu ht
      have hin' : κ ∈ cand (own v) (E t v) (view (src v) (E t)) :=
        Finset.mem_filter.2 ⟨mem_kset_of hI hκ fun u hu => hsrcP v u κ hu ht, hlow⟩
      have hc : (cand (own v) (E t v) (view (src v) (E t))).Nonempty := ⟨κ, hin'⟩
      -- the least candidate is `κ`
      have hmin : (cand (own v) (E t v) (view (src v) (E t))).min' hc = κ := by
        refine le_antisymm (Finset.min'_le _ _ hin') (le_of_not_gt fun hlt => ?_)
        have hm := Finset.mem_filter.1 (Finset.min'_mem _ hc)
        have hk := kset_sub hI hm.1
        have hr : rankC own src v ((cand (own v) (E t v) (view (src v) (E t))).min' hc) <
            rankC own src v κ := by
          unfold rankC
          refine Finset.card_lt_card ⟨fun a ha => ?_, fun hs => ?_⟩
          · obtain ⟨ha, hal⟩ := Finset.mem_filter.1 ha
            exact Finset.mem_filter.2 ⟨ha, hal.trans hlt⟩
          · have := hs (Finset.mem_filter.2 ⟨hk, hlt⟩)
            exact absurd (Finset.mem_filter.1 this).2 (lt_irrefl _)
        have := ih.1 v _ hk (by omega)
        exact absurd (hm.2 _ (mem_keysL.2 ⟨_, this⟩)) (lt_irrefl _)
      have hpm : ∀ u, src v u = true →
          Passed (view (src v) (E t) u) ((cand (own v) (E t v) (view (src v) (E t))).min' hc) := by
        rw [hmin]
        exact hpv
      rw [hR.2 t v, nextE_key h0 hc hpm, Option.toList_some]
      refine List.mem_append_right _ (List.mem_singleton.2 ?_)
      have hpe : ∀ u, src v u = true → Passed (E t u) κ := fun u hu => hsrcP v u κ hu ht
      rw [hmin, vmin_eq hI hκ hpe]
    · by_cases hin : none ∈ E t v
      · exact stream_mono hR (Nat.le_succ t) hin
      have hall : ∀ κ ∈ keysC own src v, some (κ, minCl own src v κ) ∈ E t v := by
        intro κ hκ
        have hr : rankC own src v κ < (keysC own src v).card := by
          unfold rankC
          refine Finset.card_lt_card ⟨Finset.filter_subset _ _, fun hs => ?_⟩
          exact absurd (Finset.mem_filter.1 (hs hκ)).2 (lt_irrefl _)
        exact ih.1 v κ hκ (by omega)
      have hc : ¬ (cand (own v) (E t v) (view (src v) (E t))).Nonempty := by
        rintro ⟨κ, hκ⟩
        obtain ⟨hk, hlow⟩ := Finset.mem_filter.1 hκ
        have := hall κ (kset_sub hI hk)
        exact absurd (hlow κ (mem_keysL.2 ⟨_, this⟩)) (lt_irrefl _)
      have hn : ∀ u, src v u = true → none ∈ view (src v) (E t) u := by
        intro u hu
        unfold view
        rw [ite_eq_left hu]
        have hlt := hh v u hu
        have hcard := Finset.card_le_card (keysC_sub (own := own) hu)
        exact ih.2 u (by omega)
      rw [hR.2 t v, nextE_end hin hc hn, Option.toList_some]
      exact List.mem_append_right _ (List.mem_singleton.2 rfl)

/-- **Complete streams.** After `h v + k + 1` rounds, where `k` is the number of keys at `v`, the stream of `v`
holds the end mark and every key at `v` with its least value, and nothing else. -/
theorem stream_full (hR : StreamRec own src E) (h : V → ℕ) (hh : ∀ v u, src v u = true → h u < h v)
    {t : ℕ} {v : V} (ht : h v + (keysC own src v).card + 1 ≤ t) :
    none ∈ E t v ∧ (∀ κ ∈ keysC own src v, some (κ, minCl own src v κ) ∈ E t v) ∧
      ∀ e ∈ E t v, GoodE own src v e := by
  have h0 := (timing hR h hh t).2 v ht
  exact ⟨h0, fun κ hκ => (streamInv hR t).2 v κ hκ (Or.inl h0), (streamInv hR t).1 v⟩

/-- The value of a key in a stream. -/
def ans (l : List Elt) (κ : ℕ) : Option ℕ := ((l.filterMap id).find? fun p => p.1 == κ).map Prod.snd

theorem ans_eq {l : List Elt} {v : V} (hk : ∀ κ ∈ keysC own src v, some (κ, minCl own src v κ) ∈ l)
    (hg : ∀ e ∈ l, GoodE own src v e) (κ : ℕ) :
    ans l κ = if κ ∈ keysC own src v then some (minCl own src v κ) else none := by
  unfold ans
  cases hf : (l.filterMap id).find? fun p => p.1 == κ with
  | none =>
    rw [List.find?_eq_none] at hf
    by_cases hκ : κ ∈ keysC own src v
    · exfalso
      have := hf (κ, minCl own src v κ) (List.mem_filterMap.2 ⟨_, hk κ hκ, rfl⟩)
      simp at this
    · rw [ite_eq_right hκ]
      rfl
  | some p =>
    have hp := List.mem_of_find?_eq_some hf
    have hpk := List.find?_some hf
    simp only [beq_iff_eq] at hpk
    obtain ⟨e, he, hep⟩ := List.mem_filterMap.1 hp
    simp only [id] at hep
    subst hep
    rcases hg _ he with h1 | ⟨κ', hκ', h2⟩
    · exact absurd h1 (by simp)
    · simp only [Option.some.injEq] at h2
      subst h2
      simp only at hpk
      subst hpk
      rw [ite_eq_left hκ']
      rfl

end Stream

section Alg

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The input of a node: its sources and its items. -/
structure MIn (V : Type*) where
  /-- The neighbours the node listens to. -/
  src : V → Bool
  /-- The items, pairs of a key and a value. -/
  own : List (ℕ × ℕ)

/-- The state of a node: its input, the stream sent, the streams received, and the element sent last. -/
structure MSt (V : Type*) where
  /-- The sources. -/
  src : V → Bool
  /-- The items. -/
  own : List (ℕ × ℕ)
  /-- The stream sent so far. -/
  E : List Elt
  /-- The stream received from each neighbour. -/
  R : V → List Elt
  /-- The element sent in the last round, if any. -/
  F : Option Elt

variable (V) in
/-- **The streams.** A node sends the element it added last, and adds the next one from what it received. -/
noncomputable def mergeT : TAlg V (MIn V) (MSt V) (Option Elt) where
  init _ i := ⟨i.src, i.own, [], fun _ => [], none⟩
  send _ s _ := s.F
  step _ s m :=
    ⟨s.src, s.own,
      s.E ++ (nextE s.own s.src s.E (view s.src fun u => s.R u ++ ((m u).bind id).toList)).toList,
      fun u => s.R u ++ ((m u).bind id).toList,
      nextE s.own s.src s.E (view s.src fun u => s.R u ++ ((m u).bind id).toList)⟩

/-- The code of a message. -/
def mcode : Option Elt → ℕ
  | none => 0
  | some none => 1
  | some (some p) => Nat.pair p.1 p.2 + 2

/-- The message of a code. -/
def mdec : ℕ → Option Elt
  | 0 => none
  | 1 => some none
  | j + 2 => some (some (Nat.unpair j))

theorem mdec_mcode (m : Option Elt) : mdec (mcode m) = m := by
  rcases m with _ | _ | ⟨a, b⟩ <;> simp [mcode, mdec]

theorem mcode_lt {b : ℕ} {m : Option Elt} (h : ∀ p : ℕ × ℕ, m = some (some p) → p.1 < 2 ^ b ∧ p.2 < 2 ^ b) :
    mcode m < 2 ^ (2 * b + 2) := by
  have h4 : 4 ≤ 2 ^ (2 * b + 2) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * b + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases m with _ | _ | ⟨a, c⟩
  · simp only [mcode]; omega
  · simp only [mcode]; omega
  · obtain ⟨ha, hc⟩ := h (a, c) rfl
    have hp := Nat.pair_lt_max_add_one_sq a c
    have hmax : max a c + 1 ≤ 2 ^ b := by omega
    have hsq : (max a c + 1) ^ 2 ≤ 2 ^ (2 * b) := by
      calc (max a c + 1) ^ 2 ≤ (2 ^ b) ^ 2 := Nat.pow_le_pow_left hmax 2
        _ = 2 ^ (2 * b) := by rw [← pow_mul, mul_comm]
    have : 2 ^ (2 * b + 2) = 4 * 2 ^ (2 * b) := by rw [pow_add]; ring
    simp only [mcode]
    have h1 : 1 ≤ 2 ^ (2 * b) := Nat.one_le_two_pow
    omega

variable (H : SimpleGraph V) [DecidableRel H.Adj] (inp : V → MIn V)

theorem mergeT_src (t : ℕ) (v : V) :
    ((mergeT V).run H inp t v).src = (inp v).src ∧ ((mergeT V).run H inp t v).own = (inp v).own := by
  induction t with
  | zero => exact ⟨rfl, rfl⟩
  | succ t ih => exact ih

theorem mergeT_R (t : ℕ) (v u : V) (hu : H.Adj u v) :
    ((mergeT V).run H inp (t + 1) v).R u = ((mergeT V).run H inp t u).E := by
  induction t generalizing v u with
  | zero =>
    show ([] : List Elt) ++ ((if H.Adj u v then some (none : Option Elt) else none).bind id).toList = []
    rw [ite_eq_left hu]
    rfl
  | succ t ih =>
    show ((mergeT V).run H inp (t + 1) v).R u ++ ((if H.Adj u v then
      some ((mergeT V).run H inp (t + 1) u).F else none).bind id).toList = _
    rw [ite_eq_left hu, ih v u hu]
    rfl

/-- The streams of the algorithm follow `StreamRec`, if a node listens only to neighbours. -/
theorem mergeT_rec (hsrc : ∀ v u, (inp v).src u = true → H.Adj u v) :
    StreamRec (fun v => (inp v).own) (fun v => (inp v).src) fun t v => ((mergeT V).run H inp t v).E := by
  refine ⟨fun v => rfl, fun t v => ?_⟩
  have hview : (view ((mergeT V).run H inp t v).src fun u => ((mergeT V).run H inp t v).R u ++
      (((fun w => if H.Adj w v then some ((mergeT V).send w ((mergeT V).run H inp t w) v) else none) u).bind
        id).toList) = view (inp v).src fun u => ((mergeT V).run H inp t u).E := by
    funext u
    unfold view
    rw [(mergeT_src H inp t v).1]
    by_cases hs : (inp v).src u = true
    · rw [ite_eq_left hs, ite_eq_left hs]
      exact mergeT_R H inp t v u (hsrc v u hs)
    · rw [ite_eq_right hs, ite_eq_right hs]
  show ((mergeT V).run H inp t v).E ++ (nextE ((mergeT V).run H inp t v).own ((mergeT V).run H inp t v).src
    ((mergeT V).run H inp t v).E (view ((mergeT V).run H inp t v).src fun u =>
      ((mergeT V).run H inp t v).R u ++ (((fun w => if H.Adj w v then
        some ((mergeT V).send w ((mergeT V).run H inp t w) v) else none) u).bind id).toList)).toList = _
  rw [hview, (mergeT_src H inp t v).1, (mergeT_src H inp t v).2]

theorem mergeT_F (t : ℕ) (v : V) {e : Elt} (h : ((mergeT V).run H inp t v).F = some e) :
    e ∈ ((mergeT V).run H inp t v).E := by
  cases t with
  | zero => exact absurd h (by simp [TAlg.run, mergeT])
  | succ t =>
    have hE : ((mergeT V).run H inp (t + 1) v).E =
        ((mergeT V).run H inp t v).E ++ (((mergeT V).run H inp (t + 1) v).F).toList := rfl
    rw [hE, h, Option.toList_some]
    exact List.mem_append_right _ (List.mem_singleton.2 rfl)

/-- The codes of all messages fit into `2 b + 2` bits if all items do into `b` bits. -/
theorem mergeT_code (hsrc : ∀ v u, (inp v).src u = true → H.Adj u v) {b : ℕ}
    (hb : ∀ v p, p ∈ (inp v).own → p.1 < 2 ^ b ∧ p.2 < 2 ^ b) (t : ℕ) (u v : V) :
    mcode ((mergeT V).send u ((mergeT V).run H inp t u) v) < 2 ^ (2 * b + 2) := by
  refine mcode_lt fun p hp => ?_
  have hmem := mergeT_F H inp t u hp
  have hI := streamInv (mergeT_rec H inp hsrc) t
  rcases hI.1 u _ hmem with h1 | ⟨κ, hκ, h2⟩
  · exact absurd h1 (by simp)
  · simp only [Option.some.injEq] at h2
    subst h2
    obtain ⟨w, -, hw⟩ := mem_CI.1 (minCl_mem hκ)
    exact hb w _ hw

end Alg

end SsspFlow.Congest
