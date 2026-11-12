import PlanarMatching.LoopErase
import PlanarMatching.Requests
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Realization of requests, bottom up

`notes/MATCHING.md`, Section 3. A request `(u, v)` of a bag is split along a path `u = y 0, …, y k = v` into
segments, the segment `i` being a request of the child `lbl i`. Given a simple path `π i` for every segment
inside its interval, the walk `W` joins them at their common ends, and its loop erasure is the path of the
request.

* `realize`: the erasure of `W` is a simple directed `u`-`v` path inside the interval of the request.
* `walk_repeat` (Lemma C on the walk): on a path without shortcut, a vertex that repeats in `W` lies on the
  separator, and `realize_eraseAt` concludes that reports from the separator give the same erasure.
* `realize_tree`: by induction over the tree of bags, every request has a simple path inside its interval,
  when each request is either answered directly (a leaf) or split into requests of children.
* `SPath.disjoint`, `walk_sub`: the walk lies in the interval of the request, so requests with disjoint intervals get
  disjoint walks and paths.
* `lemmaB`: on a path of least hops, a node of `J` has at most two visits in the walk. With `walk_sub` and Lemma A, a
  vertex of the separator lies on the walk of at most one request of the bag.
-/

namespace PlanarMatching

variable {V : Type*}

/-- A simple directed `u`-`v` path inside `S`, for the arc relation `E`. -/
structure SPath (E : V → V → Prop) (S : Set V) (u v : V) (p : List V) : Prop where
  chain : p.IsChain E
  nodup : p.Nodup
  head : p.head? = some u
  last : p.getLast? = some v
  sub : ∀ x ∈ p, x ∈ S

/-- The walk through the first `i` segment paths, joined at their common ends. -/
def walk (u : V) (π : ℕ → List V) : ℕ → List V
  | 0 => [u]
  | i + 1 => walk u π i ++ (π i).tail

section

variable {E : V → V → Prop} {S : Set V} {u v : V} {p : List V}

theorem SPath.head_mem (h : SPath E S u v p) : u ∈ p := List.mem_of_mem_head? (by simp [h.head])

theorem SPath.cons (h : SPath E S u v p) : p = u :: p.tail := by
  obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp h.head
  rw [ht, List.tail_cons]

/-- Requests with disjoint intervals get disjoint paths. -/
theorem SPath.disjoint {S' : Set V} {u' v' : V} {p' : List V} (h : SPath E S u v p) (h' : SPath E S' u' v' p')
    (hd : ∀ x, x ∈ S → x ∉ S') : ∀ x ∈ p, x ∉ p' := fun x hx hx' => hd x (h.sub x hx) (h'.sub x hx')

variable {π : ℕ → List V} {y : ℕ → V} {Sg : ℕ → Set V}

theorem walk_head (i : ℕ) : (walk u π i).head? = some u := by
  induction i with
  | zero => rfl
  | succ i ih => simp [walk, ih]

theorem walk_mem {a : V} : ∀ {i : ℕ}, a ∈ walk u π i → a = u ∨ ∃ j < i, a ∈ π j
  | 0, h => by simp only [walk, List.mem_singleton] at h; exact Or.inl h
  | i + 1, h => by
    rw [walk, List.mem_append] at h
    rcases h with h | h
    · rcases walk_mem h with h | ⟨j, hj, hm⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, by omega, hm⟩
    · exact Or.inr ⟨i, by omega, List.mem_of_mem_tail h⟩

theorem walk_last (h0 : y 0 = u) {i : ℕ} (hπ : ∀ j < i, SPath E (Sg j) (y j) (y (j + 1)) (π j)) :
    (walk u π i).getLast? = some (y i) := by
  induction i with
  | zero => simp [walk, h0]
  | succ i ih =>
    have ih := ih (fun j hj => hπ j (by omega))
    have hp := hπ i (by omega)
    have hl := hp.last
    rw [hp.cons] at hl
    rw [walk, List.getLast?_append]
    cases ht : (π i).tail with
    | nil => rw [ht] at hl; simp only [List.getLast?_singleton, Option.some.injEq] at hl; simp [ih, hl]
    | cons b t => rw [ht, List.getLast?_cons_cons] at hl; rw [hl]; rfl

theorem walk_chain (h0 : y 0 = u) {i : ℕ} (hπ : ∀ j < i, SPath E (Sg j) (y j) (y (j + 1)) (π j)) :
    (walk u π i).IsChain E := by
  induction i with
  | zero => simp [walk]
  | succ i ih =>
    have hl := walk_last (π := π) h0 (fun j (hj : j < i) => hπ j (by omega))
    have ih := ih (fun j hj => hπ j (by omega))
    have hp := hπ i (by omega)
    have hc := hp.chain
    rw [hp.cons] at hc
    rw [walk, List.isChain_append]
    refine ⟨ih, hc.tail, fun x hx z hz => ?_⟩
    rw [hl, Option.mem_some_iff] at hx
    subst hx
    exact (List.isChain_cons.mp hc).1 z hz

/-- The walk lies in the interval of the request, when the reachability of each child used is contained in that of
the bag. -/
theorem walk_sub {C : Type*} {R : C → V → V → Prop} {RY : V → V → Prop} {k : ℕ} {lbl : ℕ → C}
    (mono : ∀ i < k, ∀ a d, R (lbl i) a d → RY a d) (reflY : ∀ a, RY a a)
    (transY : ∀ a b d, RY a b → RY b d → RY a d) (h0 : y 0 = u) (hk : y k = v)
    (hπ : ∀ i < k, SPath E (Interval (R (lbl i)) (y i) (y (i + 1))) (y i) (y (i + 1)) (π i)) :
    ∀ x ∈ walk u π k, x ∈ Interval RY u v := by
  have hP : JPath Set.univ (fun j a d => j < k ∧ R (lbl j) a d) u v k y :=
    ⟨h0, hk, fun _ _ => trivial, fun i hi => ⟨i, hi, ((hπ i hi).sub _ (hπ i hi).head_mem).2⟩⟩
  obtain ⟨reachU, reachV⟩ := path_reach hP (fun j a d h => mono j h.1 a d h.2) reflY transY
  intro x hx
  rcases walk_mem hx with rfl | ⟨j, hj, hm⟩
  · exact ⟨reflY _, by simpa [h0] using reachV 0 (Nat.zero_le _)⟩
  · have hxj := (hπ j hj).sub x hm
    exact ⟨transY _ _ _ (reachU j (by omega)) (mono j hj _ _ hxj.1),
      transY _ _ _ (mono j hj _ _ hxj.2) (reachV (j + 1) (by omega))⟩

/-- The erasure of the walk is a simple directed `u`-`v` path inside the interval of the request, when the
reachability of each child used is contained in that of the bag. -/
theorem realize [DecidableEq V] {C : Type*} {R : C → V → V → Prop} {RY : V → V → Prop} {k : ℕ} {lbl : ℕ → C}
    (mono : ∀ i < k, ∀ a d, R (lbl i) a d → RY a d) (reflY : ∀ a, RY a a)
    (transY : ∀ a b d, RY a b → RY b d → RY a d) (h0 : y 0 = u) (hk : y k = v)
    (hπ : ∀ i < k, SPath E (Interval (R (lbl i)) (y i) (y (i + 1))) (y i) (y (i + 1)) (π i)) :
    SPath E (Interval RY u v) u v (loopErase (walk u π k)) :=
  ⟨isChain_loopErase (walk_chain h0 hπ), nodup_loopErase _, by rw [head?_loopErase, walk_head],
    by rw [getLast?_loopErase, walk_last h0 hπ, hk],
    fun x hx => walk_sub mono reflY transY h0 hk hπ x (mem_of_mem_loopErase hx)⟩

/-- Lemma C on the walk: on a path without shortcut, a vertex that repeats in the walk lies on the
separator. -/
theorem walk_repeat {C : Type*} {R : C → V → V → Prop} (trans : ∀ c a b d, R c a b → R c b d → R c a d)
    {inBag : C → V → Prop} (mem : ∀ c a b, R c a b → inBag c a)
    {sep : Set V} (uniq : ∀ x, x ∉ sep → ∀ c c', inBag c x → inBag c' x → c = c')
    {k : ℕ} {lbl : ℕ → C} (hS : NoShortcut R k y) (h0 : y 0 = u)
    (hπ : ∀ i < k, SPath E (Interval (R (lbl i)) (y i) (y (i + 1))) (y i) (y (i + 1)) (π i))
    [DecidableEq V] : ∀ a, 1 < (walk u π k).count a → a ∈ sep := by
  suffices ∀ i ≤ k, ∀ a, 1 < (walk u π i).count a → a ∈ sep from this k le_rfl
  intro i
  induction i with
  | zero => intro _ a h; simp only [walk, List.count_singleton] at h; split_ifs at h <;> omega
  | succ i ih =>
    intro hi a h
    have hp := hπ i (by omega)
    have hnd := hp.nodup
    rw [hp.cons, List.nodup_cons] at hnd
    rw [walk, List.count_append] at h
    have h1 := List.nodup_iff_count_le_one.mp hnd.2 a
    by_cases hw : 1 < (walk u π i).count a
    · exact ih (by omega) a hw
    have hwa : a ∈ walk u π i := List.count_pos_iff.mp (by omega)
    have hta : a ∈ (π i).tail := List.count_pos_iff.mp (by omega)
    have hne : a ≠ y i := fun e => hnd.1 (e ▸ hta)
    have hai := hp.sub a (List.mem_of_mem_tail hta)
    rcases walk_mem hwa with rfl | ⟨j, hj, hm⟩
    · have hi0 : 0 < i := Nat.pos_of_ne_zero fun e => hne (by rw [e, h0])
      have hp0 := hπ 0 (by omega)
      have h0a : a ∈ Interval (R (lbl 0)) (y 0) (y (0 + 1)) := by rw [← h0]; exact hp0.sub _ hp0.head_mem
      exact lemmaC trans mem uniq hS hi0 (by omega) _ h0a hai
    · exact lemmaC trans mem uniq hS hj (by omega) a ((hπ j (by omega)).sub a hm) hai

/-- Reports from the separator give the same erasure. -/
theorem realize_eraseAt [DecidableEq V] {C : Type*} {R : C → V → V → Prop}
    (trans : ∀ c a b d, R c a b → R c b d → R c a d) {inBag : C → V → Prop} (mem : ∀ c a b, R c a b → inBag c a)
    {H : Finset V} (uniq : ∀ x, x ∉ H → ∀ c c', inBag c x → inBag c' x → c = c')
    {k : ℕ} {lbl : ℕ → C} (hS : NoShortcut R k y) (h0 : y 0 = u)
    (hπ : ∀ i < k, SPath E (Interval (R (lbl i)) (y i) (y (i + 1))) (y i) (y (i + 1)) (π i)) :
    eraseAt H (walk u π k) = loopErase (walk u π k) :=
  eraseAt_eq_loopErase H _ fun a ha =>
    Finset.mem_coe.mp (walk_repeat trans mem (sep := ↑H) (fun x hx => uniq x (by simpa using hx)) hS h0 hπ a ha)

/-- Every request has a simple directed path inside its interval, by induction over the tree of bags: a request
is either answered directly, as in a leaf, or split along a path into requests of children of its bag. -/
theorem realize_tree {B : Type*} {child : B → B → Prop} (wf : WellFounded child)
    {RB : B → V → V → Prop} {Req : B → V → V → Prop}
    (refl : ∀ b a, RB b a a) (trans : ∀ b a c d, RB b a c → RB b c d → RB b a d)
    (mono : ∀ c b, child c b → ∀ a d, RB c a d → RB b a d)
    (step : ∀ b u v, Req b u v → (∃ p, SPath E (Interval (RB b) u v) u v p) ∨
      ∃ (k : ℕ) (y : ℕ → V) (lbl : ℕ → B), y 0 = u ∧ y k = v ∧
        ∀ i < k, child (lbl i) b ∧ Req (lbl i) (y i) (y (i + 1))) :
    ∀ b u v, Req b u v → ∃ p, SPath E (Interval (RB b) u v) u v p := by
  intro b
  induction b using wf.induction with
  | _ b ih =>
  intro u v hR
  rcases step b u v hR with h | ⟨k, y, lbl, h0, hk, hs⟩
  · exact h
  have hex : ∀ i, ∃ p : List V, i < k →
      SPath E (Interval (RB (lbl i)) (y i) (y (i + 1))) (y i) (y (i + 1)) p := by
    intro i
    by_cases hi : i < k
    · obtain ⟨p, hp⟩ := ih (lbl i) (hs i hi).1 (y i) (y (i + 1)) (hs i hi).2
      exact ⟨p, fun _ => hp⟩
    · exact ⟨[], fun h => absurd h hi⟩
  choose π hπ using hex
  classical
  exact ⟨_, realize (fun i hi a d h => mono (lbl i) b (hs i hi).1 a d h) (refl b) (trans b) h0 hk hπ⟩

/-- The visits of `x` in the walk: one for the start, and one for each segment path whose tail holds `x`. -/
theorem count_walk [DecidableEq V] (x : V) (i : ℕ) :
    (walk u π i).count x = [u].count x + ∑ j ∈ Finset.range i, ((π j).tail).count x := by
  induction i with
  | zero => simp [walk]
  | succ i ih => rw [walk, List.count_append, ih, Finset.sum_range_succ, add_assoc]

/-- On a path of least hops, a node of `J` on two segments lies on consecutive ones: otherwise it would shorten the
path to two hops across. -/
theorem window {C : Type*} {N : Set V} {R : C → V → V → Prop} {k : ℕ} {lbl : ℕ → C}
    (hP : JPath N R u v k y) (hmin : ∀ k' y', JPath N R u v k' y' → k ≤ k') {x : V} (hx : x ∈ N)
    {a b : ℕ} (hab : a < b) (hb : b < k)
    (h1 : x ∈ Interval (R (lbl a)) (y a) (y (a + 1))) (h2 : x ∈ Interval (R (lbl b)) (y b) (y (b + 1))) :
    b = a + 1 := by
  by_contra hne
  let y' : ℕ → V := fun i => if i ≤ a then y i else if i = a + 1 then x else y (i + (b - a - 1))
  have hP' : JPath N R u v (k - (b - a - 1)) y' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [y', hP.start]
    · have h3 : ¬ (k - (b - a - 1) ≤ a) := by omega
      have h4 : ¬ (k - (b - a - 1) = a + 1) := by omega
      simp only [y', h3, h4, ite_false]
      rw [show k - (b - a - 1) + (b - a - 1) = k by omega, hP.stop]
    · intro i hi
      by_cases h : i ≤ a
      · simp only [y', h, ite_true]; exact hP.mem i (by omega)
      · by_cases h' : i = a + 1
        · subst h'; simp only [y', show ¬ (a + 1 ≤ a) by omega, ite_false, ite_true]; exact hx
        · simp only [y', h, h', ite_false]; exact hP.mem _ (by omega)
    · intro i hi
      by_cases h : i < a
      · have e1 : i ≤ a := by omega
        have e2 : i + 1 ≤ a := by omega
        simp only [y', e1, e2, ite_true]
        exact hP.arc i (by omega)
      · by_cases h' : i = a
        · subst h'
          simp only [y', le_refl, ite_true, show ¬ (i + 1 ≤ i) by omega, ite_false]
          exact ⟨lbl i, h1.1⟩
        · by_cases h'' : i = a + 1
          · subst h''
            simp only [y', show ¬ (a + 1 ≤ a) by omega, show ¬ (a + 1 + 1 ≤ a) by omega,
              show ¬ (a + 1 + 1 = a + 1) by omega, ite_false, ite_true]
            rw [show a + 1 + 1 + (b - a - 1) = b + 1 by omega]
            exact ⟨lbl b, h2.2⟩
          · simp only [y', show ¬ (i ≤ a) by omega, show ¬ (i + 1 ≤ a) by omega, h'',
              show ¬ (i + 1 = a + 1) by omega, ite_false]
            rw [show i + 1 + (b - a - 1) = i + (b - a - 1) + 1 by omega]
            exact hP.arc _ (by omega)
  have := hmin _ _ hP'
  omega

/-- **Lemma B.** On a path of least hops in `J`, a node of `J` has at most two visits in the walk of the
request. -/
theorem lemmaB [DecidableEq V] {C : Type*} {N : Set V} {R : C → V → V → Prop} {k : ℕ} {lbl : ℕ → C}
    (hP : JPath N R u v k y) (hmin : ∀ k' y', JPath N R u v k' y' → k ≤ k')
    (hπ : ∀ i < k, SPath E (Interval (R (lbl i)) (y i) (y (i + 1))) (y i) (y (i + 1)) (π i))
    {x : V} (hx : x ∈ N) : (walk u π k).count x ≤ 2 := by
  classical
  have tail_ne : ∀ j < k, x ∈ (π j).tail → x ≠ y j := fun j hj ht e => by
    have hnd := (hπ j hj).nodup
    rw [(hπ j hj).cons, List.nodup_cons] at hnd
    exact hnd.1 (e ▸ ht)
  have inI : ∀ j < k, x ∈ π j → x ∈ Interval (R (lbl j)) (y j) (y (j + 1)) := fun j hj h => (hπ j hj).sub x h
  set F := (Finset.range k).filter fun j => x ∈ (π j).tail with hF
  have hsum : ∑ j ∈ Finset.range k, ((π j).tail).count x ≤ F.card := by
    rw [hF, Finset.card_filter]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    split_ifs with h
    · have hnd := (hπ j hj').nodup
      rw [(hπ j hj').cons, List.nodup_cons] at hnd
      exact List.nodup_iff_count_le_one.mp hnd.2 x
    · exact (List.count_eq_zero_of_not_mem h).le
  have memF : ∀ j ∈ F, j < k ∧ x ∈ π j := fun j hj => by
    rw [hF, Finset.mem_filter, Finset.mem_range] at hj
    exact ⟨hj.1, List.mem_of_mem_tail hj.2⟩
  rw [count_walk]
  by_cases hxu : x = u
  · -- the start is visited once more only on the segment `1`
    have h0 : x = y 0 := by rw [hxu, hP.start]
    have hF1 : F ⊆ {1} := fun j hj => by
      obtain ⟨hjk, hjm⟩ := memF j hj
      have ht : x ∈ (π j).tail := by rw [hF, Finset.mem_filter] at hj; exact hj.2
      have hj0 : 0 < j := Nat.pos_of_ne_zero fun e => tail_ne j hjk ht (by rw [e]; exact h0)
      have hk0 : 0 < k := by omega
      have h0m : x ∈ π 0 := h0 ▸ (hπ 0 hk0).head_mem
      have := window hP hmin hx hj0 hjk (inI 0 hk0 h0m) (inI j hjk hjm)
      simp [this]
    have h1 := Finset.card_le_card hF1
    rw [Finset.card_singleton] at h1
    have hu1 : [u].count x = 1 := by subst hxu; simp
    omega
  · have hF2 : F.card ≤ 2 := by
      rcases F.eq_empty_or_nonempty with h | hne
      · simp [h]
      · have hex : ∃ j, j ∈ F := hne
        let a := Nat.find hex
        have hsub : F ⊆ {a, a + 1} := fun j hj => by
          have ha : a ≤ j := Nat.find_min' hex hj
          rcases Nat.lt_or_ge a j with hlt | hle
          · obtain ⟨hjk, hjm⟩ := memF j hj
            obtain ⟨hak, ham⟩ := memF a (Nat.find_spec hex)
            have := window hP hmin hx hlt hjk (inI a hak ham) (inI j hjk hjm)
            simp [this]
          · simp [show j = a by omega]
        exact (Finset.card_le_card hsub).trans Finset.card_le_two
    have hu0 : [u].count x = 0 := List.count_eq_zero_of_not_mem (by simpa using hxu)
    omega

end

end PlanarMatching
