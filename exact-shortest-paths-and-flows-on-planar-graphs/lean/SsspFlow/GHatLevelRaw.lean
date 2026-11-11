import SsspFlow.GHatTableRaw

/-!
# The lists of the network of a level from local data

A node `w` of `N` hosts the identifiers `(w, u, k)`. From its rotation list,
  the records of the darts
at `w` and the records of the darts into `w` it computes, for each of them, the rotation list of the
network of a level at that identifier (`rawAt`):

* at the name of a copy, the names in its list of Table R (`rawCopy`), and at the star centre then
  the identifiers that name nothing, in increasing order;
* at the name of a dart, the name of the copy in whose list it lies,
  and the name of the reverse dart
  (`revName`);
* at an identifier that names nothing, the star centre `(w, w, 0)`.

* `RData.levelNet_rotList_raw`: these are the rotation lists of the network of a level.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest

namespace RotSystem

section Raw

variable {n : ℕ}

/-- The raw list at the copy named `(w, u, k)` with `k < 5`. -/
def rawCopy (R : List (Fin n)) (f g : Fin n → DInfo) (w u : Fin n) (k : Fin 21) :
    List (Fin n × Fin n × Fin 21) :=
  if k = 0 then (if u = w then R.map fun x => (w, x, 11) else [])
  else if u ∈ R then
    (if k = 1 then rawDList f g w u (R.formPerm u)
    else if k = 2 then rawLList f w u
    else if k = 3 then rawRList f w (R.formPerm u)
    else if k = 4 then rawXList f w u (R.formPerm u) else [])
  else []

/-- The places of the copies at a node. -/
def copyCands (R : List (Fin n)) (w : Fin n) : List (Fin n × Fin 21) :=
  (w :: R).flatMap fun u => [(u, 0), (u, 1), (u, 2), (u, 3), (u, 4)]

/-- The place of the copy in whose list a name lies. -/
def rawTail (R : List (Fin n)) (f g : Fin n → DInfo) (w : Fin n) (p : Fin n × Fin n × Fin 21) :
    Option (Fin n × Fin 21) :=
  (copyCands R w).find? fun q => decide (p ∈ rawCopy R f g w q.1 q.2)

/-- The name of the reverse dart. -/
def revName (p : Fin n × Fin n × Fin 21) : Fin n × Fin n × Fin 21 :=
  match p.2.2.val with
  | 5 => (p.2.1, p.1, 8)
  | 6 => (p.2.1, p.1, 9)
  | 7 => (p.2.1, p.1, 10)
  | 8 => (p.2.1, p.1, 5)
  | 9 => (p.2.1, p.1, 6)
  | 10 => (p.2.1, p.1, 7)
  | 11 => (p.1, p.2.1, 12)
  | 12 => (p.1, p.2.1, 11)
  | 13 => (p.1, p.2.1, 14)
  | 14 => (p.1, p.2.1, 13)
  | 15 => (p.1, p.2.1, 16)
  | 16 => (p.1, p.2.1, 15)
  | 17 => (p.1, p.2.1, 18)
  | 18 => (p.1, p.2.1, 17)
  | 19 => (p.1, p.2.1, 20)
  | 20 => (p.1, p.2.1, 19)
  | _ => p

/-- The identifier `(w, u, k)` names a node. -/
def rawReal (R : List (Fin n)) (f g : Fin n → DInfo) (w : Fin n) (q : Fin n × Fin 21) : Bool :=
  if q.2 < 5 then !(rawCopy R f g w q.1 q.2).isEmpty else (rawTail R f g w (w, q.1, q.2)).isSome

/-- The identifiers at `w` that name nothing, in increasing order. -/
def rawPend (R : List (Fin n)) (f g : Fin n → DInfo) (w : Fin n) : List (Fin (n * (n * 21))) :=
  ((Finset.univ.filter fun q : Fin n × Fin 21 => rawReal R f g w q = false).image
    fun q => RData.idEquiv (w, q.1, q.2)).sort (· ≤ ·)

/-- The raw rotation list at the identifier `(w, u, k)`. -/
def rawAt (R : List (Fin n)) (f g : Fin n → DInfo) (w : Fin n) (q : Fin n × Fin 21) :
    List (Fin (n * (n * 21))) :=
  if rawReal R f g w q then
    if q.2 < 5 then
      (rawCopy R f g w q.1 q.2).map RData.idEquiv ++
        (if q.1 = w ∧ q.2 = 0 then rawPend R f g w else [])
    else
      match rawTail R f g w (w, q.1, q.2) with
      | some t => [RData.idEquiv (w, t.1, t.2), RData.idEquiv (revName (w, q.1, q.2))]
      | none => []
  else [RData.idEquiv (w, w, 0)]

end Raw

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData)

/-- The raw list at a copy of the node `w`, from the data of `w`. -/
def rCopy (w : Fin n) : Fin n → Fin 21 → List (Fin n × Fin n × Fin 21) :=
  rawCopy (N.rotList w) (S.dinfoAt w) (fun u => S.dinfoAt u w) w

/-- The raw place of the tail copy, from the data of `w`. -/
def rTail (w : Fin n) : Fin n × Fin n × Fin 21 → Option (Fin n × Fin 21) :=
  rawTail (N.rotList w) (S.dinfoAt w) (fun u => S.dinfoAt u w) w

theorem nameD_hrev (x : S.HD) : S.nameD (S.hrev x) = revName (S.nameD x) := by
  obtain ⟨e, b⟩ := x
  rcases e with c | c | ⟨⟨c, l⟩, hc⟩ | c | c | c <;> (try cases l) <;> cases b <;> rfl

theorem nameC_tl (x : S.HD) : (N.nameC (S.tl x)).1 = (S.nameD x).1 := by
  rw [nameC_fst, nameD_fst, S.owner_tl]
  rfl

/-- **The raw list at the name of a copy** is the list of Table R, read as names. -/
theorem rCopy_name (c : Copy N.toRot.Vertex N.G.Dart) :
    S.rCopy (N.nameC c).1 (N.nameC c).2.1 (N.nameC c).2.2 = (S.lstR c).map S.nameD := by
  cases c with
  | star v =>
    obtain ⟨d, rfl⟩ := N.toRot.exists_tail_eq v
    show S.rCopy d.fst d.fst 0 = _
    unfold rCopy
    simp only [rawCopy, ite_true]
    simp only [lstR, Net.vnode_tail, starDarts, List.map_map]
    conv_lhs => rw [← List.attach_map_subtype_val (N.rotList d.fst), List.map_map]
    rfl
  | dc c =>
    have hc : c.snd ∈ N.rotList c.fst := (N.mem_rotList _ _).2 c.adj
    show S.rCopy c.fst c.snd 1 = (S.dList c).map S.nameD
    unfold rCopy
    rw [S.dList_raw c]
    unfold rawCopy
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide)),
      ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    rfl
  | lc c =>
    have hc : c.snd ∈ N.rotList c.fst := (N.mem_rotList _ _).2 c.adj
    show S.rCopy c.fst c.snd 2 = (S.lList c).map S.nameD
    unfold rCopy
    rw [S.lList_raw c]
    unfold rawCopy
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide)),
      ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_right_of_eq_false _ _ (eq_false (by decide)),
        ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  | rc c =>
    have hc : c.snd ∈ N.rotList c.fst := (N.mem_rotList _ _).2 c.adj
    show S.rCopy c.fst c.snd 3 = (S.rList c).map S.nameD
    unfold rCopy
    rw [S.rList_raw c]
    unfold rawCopy
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide)),
      ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_right_of_eq_false _ _ (eq_false (by decide)),
        ite_eq_right_of_eq_false _ _ (eq_false (by decide)),
          ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    rfl
  | xc c =>
    have hc : c.snd ∈ N.rotList c.fst := (N.mem_rotList _ _).2 c.adj
    show S.rCopy c.fst c.snd 4 = (S.xList c).map S.nameD
    unfold rCopy
    rw [S.xList_raw c]
    unfold rawCopy
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide)),
      ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_right_of_eq_false _ _ (eq_false (by decide)),
        ite_eq_right_of_eq_false _ _ (eq_false (by decide)),
      ite_eq_right_of_eq_false _ _ (eq_false (by decide)), ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    rfl

/-- A raw list at a place of a copy is empty or that of a copy. -/
theorem rCopy_cases (w u : Fin n) {k : Fin 21} (hk : k < 5) :
    S.rCopy w u k = [] ∨ ∃ c, N.nameC c = (w, u, k) := by
  by_cases h0 : k = 0
  · subst h0
    by_cases hu : u = w
    · subst hu
      cases hR : N.rotList u with
      | nil => left; simp [rCopy, rawCopy, hR]
      | cons x l =>
        have hx : N.G.Adj u x := (N.mem_rotList _ _).1 (by rw [hR]; exact List.mem_cons_self ..)
        exact .inr ⟨.star (N.toRot.tail ⟨(u, x), hx⟩), rfl⟩
    · left
      simp [rCopy, rawCopy, hu]
  · by_cases hu : u ∈ N.rotList w
    · have hadj : N.G.Adj w u := (N.mem_rotList _ _).1 hu
      right
      have : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · exact ⟨.dc ⟨(w, u), hadj⟩, rfl⟩
      · exact ⟨.lc ⟨(w, u), hadj⟩, rfl⟩
      · exact ⟨.rc ⟨(w, u), hadj⟩, rfl⟩
      · exact ⟨.xc ⟨(w, u), hadj⟩, rfl⟩
    · left
      simp [rCopy, rawCopy, h0, hu]

/-- A copy is a vertex of the repaired graph exactly when its list is not empty. -/
theorem vertex_iff (c : Copy N.toRot.Vertex N.G.Dart) : (∃ v, S.vcopy v = c) ↔ S.lstR c ≠ [] := by
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨x, rfl⟩ := S.hRot.exists_tail_eq v
    exact List.ne_nil_of_mem ((S.lstR_rot _).mem_iff.2 (S.mem_lst_tl x))
  · intro h
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ h
    exact ⟨S.hRot.tail x, S.tl_of_mem _ x ((S.lstR_rot _).mem_iff.1 hx)⟩

theorem tl_of_mem_lstR {c : Copy N.toRot.Vertex N.G.Dart} {x : S.HD} (hx : x ∈ S.lstR c) : S.tl x = c :=
  S.tl_of_mem _ x ((S.lstR_rot _).mem_iff.1 hx)

theorem mem_copyCands (c : Copy N.toRot.Vertex N.G.Dart) :
    (N.nameC c).2 ∈ copyCands (N.rotList (N.nameC c).1) (N.nameC c).1 := by
  have h : ∀ (w u : Fin n) (k : Fin 21), (u = w ∨ u ∈ N.rotList w) → k < 5 →
      (u, k) ∈ copyCands (N.rotList w) w := fun w u k hu hk => by
    simp only [copyCands, List.mem_flatMap, List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false]
    refine ⟨u, hu, ?_⟩
    simp only [true_and]
    omega
  have hk := N.nameC_kind c
  cases c with
  | star v => exact h _ _ _ (.inl rfl) hk
  | _ c => exact h _ _ _ (.inr ((N.mem_rotList _ _).2 c.adj)) hk

/-- **The raw place of the tail copy** of a dart. -/
theorem rTail_nameD (x : S.HD) : S.rTail (S.nameD x).1 (S.nameD x) = some (N.nameC (S.tl x)).2 := by
  set w := (S.nameD x).1
  have hw : (N.nameC (S.tl x)).1 = w := S.nameC_tl x
  have key : ∀ q ∈ copyCands (N.rotList w) w, S.nameD x ∈ S.rCopy w q.1 q.2 →
      q = (N.nameC (S.tl x)).2 := by
    intro q hq hx
    have hk : q.2 < 5 := by
      simp only [copyCands, List.mem_flatMap, List.mem_cons,
        List.not_mem_nil, or_false] at hq
      obtain ⟨u, -, hq⟩ := hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
    rcases S.rCopy_cases w q.1 hk with h | ⟨c, hc⟩
    · rw [h] at hx; simp at hx
    · have e : S.rCopy w q.1 q.2 = (S.lstR c).map S.nameD := by
        rw [← S.rCopy_name c, hc]
      rw [e] at hx
      obtain ⟨x', hx', hxx⟩ := List.mem_map.1 hx
      obtain rfl := S.nameD_injective hxx
      rw [S.tl_of_mem_lstR hx', hc]
  have hmem : S.nameD x ∈ S.rCopy w (N.nameC (S.tl x)).2.1 (N.nameC (S.tl x)).2.2 := by
    have e := S.rCopy_name (S.tl x)
    rw [hw] at e
    rw [e]
    exact List.mem_map.2 ⟨x, (S.lstR_rot _).mem_iff.2 (S.mem_lst_tl x), rfl⟩
  have hc : (N.nameC (S.tl x)).2 ∈ copyCands (N.rotList w) w := by
    have := mem_copyCands (S.tl x)
    rwa [hw] at this
  have hsome : (S.rTail w (S.nameD x)).isSome := by
    unfold rTail rawTail
    rw [List.find?_isSome]
    exact ⟨_, hc, decide_eq_true hmem⟩
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 hsome
  rw [hq]
  unfold rTail rawTail at hq
  have hp := List.find?_some hq
  exact congrArg some (key q (List.mem_of_find?_eq_some hq) (of_decide_eq_true hp))

/-- A name found by the raw tail is the name of a dart. -/
theorem rTail_some {w : Fin n} {p : Fin n × Fin n × Fin 21} {q : Fin n × Fin 21}
    (h : S.rTail w p = some q) : ∃ x, S.nameD x = p := by
  unfold rTail rawTail at h
  have hq := List.mem_of_find?_eq_some h
  have hp' := List.find?_some h
  have hp := of_decide_eq_true hp'
  have hk : q.2 < 5 := by
    simp only [copyCands, List.mem_flatMap, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    obtain ⟨u, -, hq⟩ := hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  rcases S.rCopy_cases w q.1 hk with h0 | ⟨c, hc⟩
  · exact absurd hp (by unfold rCopy at h0; rw [h0]; simp)
  · have e : rawCopy (N.rotList w) (S.dinfoAt w) (fun u => S.dinfoAt u w) w q.1 q.2 =
        (S.lstR c).map S.nameD := by
      rw [← S.rCopy_name c, hc]; rfl
    rw [e] at hp
    obtain ⟨x, -, hx⟩ := List.mem_map.1 hp
    exact ⟨x, hx⟩

/-- **Which identifiers name a node**, from the data of their host. -/
theorem rawReal_iff (w u : Fin n) (k : Fin 21) :
    rawReal (N.rotList w) (S.dinfoAt w) (fun u => S.dinfoAt u w) w (u, k) = true ↔
      ∃ y, S.name y = (w, u, k) := by
  unfold rawReal
  by_cases hk : k < 5
  · simp only [hk, ite_true, Bool.not_eq_true', List.isEmpty_eq_false_iff]
    change S.rCopy w u k ≠ [] ↔ _
    constructor
    · intro h
      rcases S.rCopy_cases w u hk with h0 | ⟨c, hc⟩
      · exact absurd h0 h
      · have e := S.rCopy_name c
        rw [hc] at e
        rw [e] at h
        obtain ⟨v, hv⟩ := (S.vertex_iff c).2 (fun h' => h (by rw [h']; rfl))
        exact ⟨.inl v, by rw [← hc, ← hv]; rfl⟩
    · rintro ⟨y | x, hy⟩
      · have e := S.rCopy_name (S.vcopy y)
        have hy' : N.nameC (S.vcopy y) = (w, u, k) := hy
        rw [hy'] at e
        rw [e]
        intro h0
        exact (S.vertex_iff _).1 ⟨y, rfl⟩ (List.map_eq_nil_iff.1 h0)
      · have := S.nameD_kind x
        have hy' : S.nameD x = (w, u, k) := hy
        rw [hy'] at this
        exact absurd hk (by simp only at this; omega)
  · simp only [hk, ite_false, Option.isSome_iff_exists]
    constructor
    · rintro ⟨q, hq⟩
      obtain ⟨x, hx⟩ := S.rTail_some hq
      exact ⟨.inr x, hx⟩
    · rintro ⟨y | x, hy⟩
      · have := N.nameC_kind (S.vcopy y)
        have hy' : N.nameC (S.vcopy y) = (w, u, k) := hy
        rw [hy'] at this
        exact absurd this hk
      · have hy' : S.nameD x = (w, u, k) := hy
        have := S.rTail_nameD x
        rw [hy'] at this
        exact ⟨_, this⟩

variable (hN : ∀ u, ∃ w, N.G.Adj u w)

theorem isReal_iff (z : Fin (n * (n * 21))) : (S.levelPad hN).IsReal z ↔ ∃ y,
  S.name y = idEquiv.symm z := by
  constructor
  · intro h
    exact ⟨_, (Equiv.eq_symm_apply idEquiv).2 h.symm⟩
  · rintro ⟨y, hy⟩
    have : z = (S.levelPad hN).ι y := by
      show z = idEquiv (S.name y)
      rw [hy, Equiv.apply_symm_apply]
    rw [this]
    exact (S.levelPad hN).isReal_ι y

/-- The star centre of `u` is the vertex whose copy is named `(u, u, 0)`. -/
theorem starV_eq_iff (u : Fin n) (v : S.hRot.Vertex) :
    S.starV hN u = v ↔ N.nameC (S.vcopy v) = (u, u, 0) := by
  have h0 : N.nameC (S.vcopy (S.starV hN u)) = (u, u, 0) := rfl
  constructor
  · rintro rfl
    exact h0
  · intro h
    exact S.vcopy_injective (N.nameC_injective (h0.trans h.symm))

/-- **The identifiers that hang at a vertex.** -/
theorem extras_inl (v : S.hRot.Vertex) :
    (S.levelPad hN).extras (.inl v) =
      if (N.nameC (S.vcopy v)).2.2 = 0 then
        ((Finset.univ.filter fun q : Fin n × Fin 21 =>
          rawReal (N.rotList (N.nameC (S.vcopy v)).1) (S.dinfoAt (N.nameC (S.vcopy v)).1)
            (fun u => S.dinfoAt u (N.nameC (S.vcopy v)).1) (N.nameC (S.vcopy v)).1 q = false).image
          fun q => idEquiv ((N.nameC (S.vcopy v)).1, q.1, q.2))
      else ∅ := by
  classical
  set w := (N.nameC (S.vcopy v)).1
  have hstar : (N.nameC (S.vcopy v)).2.2 = 0 → N.nameC (S.vcopy v) = (w, w, 0) := by
    intro h
    obtain ⟨d, rfl⟩ := S.hRot.exists_tail_eq v
    revert h
    show (N.nameC (S.tl d)).2.2 = 0 → N.nameC (S.tl d) = ((N.nameC (S.tl d)).1,
      (N.nameC (S.tl d)).1, 0)
    cases S.tl d with
    | star v => intro; rfl
    | _ c => intro h; exact absurd h (by simp [Net.nameC])
  ext z
  rw [PadMap.mem_extras]
  constructor
  · rintro ⟨hz, hb⟩
    rw [S.back_of_not_real hN hz, Sum.inl.injEq, S.starV_eq_iff] at hb
    have hk : (N.nameC (S.vcopy v)).2.2 = 0 := by rw [hb]
    rw [ite_eq_left_of_eq_true _ _ (eq_true hk), Finset.mem_image]
    have hw : hostOf z = w := by
      show hostOf z = (N.nameC (S.vcopy v)).1
      rw [hb]
    refine ⟨((idEquiv.symm z).2.1, (idEquiv.symm z).2.2), ?_, ?_⟩
    · rw [Finset.mem_filter, Bool.eq_false_iff]
      refine ⟨Finset.mem_univ _, fun h => hz ((S.isReal_iff hN z).2 ?_)⟩
      obtain ⟨y, hy⟩ := (S.rawReal_iff _ _ _).1 h
      exact ⟨y, by rw [hy, ← hw]; rfl⟩
    · rw [← hw]
      exact idEquiv.apply_symm_apply z
  · intro hz
    by_cases hk : (N.nameC (S.vcopy v)).2.2 = 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hk), Finset.mem_image] at hz
      obtain ⟨q, hq, rfl⟩ := hz
      rw [Finset.mem_filter, Bool.eq_false_iff] at hq
      have hnr : ¬ (S.levelPad hN).IsReal (idEquiv (w, q.1, q.2)) := by
        rw [S.isReal_iff, Equiv.symm_apply_apply]
        exact fun h => hq.2 ((S.rawReal_iff _ _ _).2 h)
      refine ⟨hnr, ?_⟩
      have hh : hostOf (idEquiv (w, q.1, q.2)) = w := by
        unfold hostOf; rw [Equiv.symm_apply_apply]
      rw [S.back_of_not_real hN hnr, Sum.inl.injEq, S.starV_eq_iff, hstar hk, hh]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hk)] at hz
      exact absurd hz (Finset.notMem_empty _)

/-- **The rotation lists of the network of a level from local data.** The host `w` of an identifier
computes its list from the rotation list of `w`, the records of the darts at `w` and the records of
the darts into `w`. -/
theorem levelNet_rotList_raw (z : Fin (n * (n * 21))) :
    (S.levelNet hN).rotList z =
      rawAt (N.rotList (hostOf z)) (S.dinfoAt (hostOf z)) (fun u => S.dinfoAt u (hostOf z)) (hostOf z)
        ((idEquiv.symm z).2.1, (idEquiv.symm z).2.2) := by
  classical
  by_cases hz : (S.levelPad hN).IsReal z
  · obtain ⟨y, rfl⟩ : ∃ y, z = (S.levelPad hN).ι y := ⟨_, hz⟩
    have hname : idEquiv.symm ((S.levelPad hN).ι y) = S.name y := idEquiv.symm_apply_apply _
    have hhost : hostOf ((S.levelPad hN).ι y) = (S.name y).1 := by
      unfold hostOf; rw [hname]
    rw [hhost, hname]
    have hreal : rawReal (N.rotList (S.name y).1) (S.dinfoAt (S.name y).1)
        (fun u => S.dinfoAt u (S.name y).1) (S.name y).1 ((S.name y).2.1, (S.name y).2.2) = true :=
      (S.rawReal_iff _ _ _).2 ⟨y, rfl⟩
    rcases y with v | x
    · rw [show S.name (Sum.inl v) = N.nameC (S.vcopy v) from rfl] at hreal ⊢
      have hk : (N.nameC (S.vcopy v)).2.2 < 5 := N.nameC_kind _
      unfold rawAt
      rw [ite_eq_left_of_eq_true _ _ (eq_true hreal)]
      dsimp only
      rw [ite_eq_left_of_eq_true _ _ (eq_true hk), S.levelNet_rotList_copy hN v, S.extras_inl hN v]
      have e := S.rCopy_name (S.vcopy v)
      unfold rCopy at e
      rw [e, List.map_map]
      congr 1
      by_cases h0 : (N.nameC (S.vcopy v)).2.2 = 0
      · have hst : (N.nameC (S.vcopy v)).2.1 = (N.nameC (S.vcopy v)).1 := by
          obtain ⟨d, rfl⟩ := S.hRot.exists_tail_eq v
          revert h0
          show (N.nameC (S.tl d)).2.2 = 0 → (N.nameC (S.tl d)).2.1 = (N.nameC (S.tl d)).1
          cases S.tl d with
          | star v => intro; rfl
          | _ c => intro h; exact absurd h (by simp [Net.nameC])
        rw [ite_eq_left_of_eq_true _ _ (eq_true h0), ite_eq_left_of_eq_true _ _ (eq_true ⟨hst, h0⟩)]
        rfl
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h0),
        ite_eq_right_of_eq_false _ _ (eq_false (fun h => h0 h.2)), PadMap.order_empty]
    · rw [show S.name (Sum.inr x) = S.nameD x from rfl] at hreal ⊢
      have hk : ¬ (S.nameD x).2.2 < 5 := by have := S.nameD_kind x; omega
      unfold rawAt
      rw [ite_eq_left_of_eq_true _ _ (eq_true hreal)]
      dsimp only
      rw [ite_eq_right_of_eq_false _ _ (eq_false hk), S.levelNet_rotList_dart hN x]
      have ht := S.rTail_nameD x
      unfold rTail at ht
      have hp : ((S.nameD x).1, (S.nameD x).2.1, (S.nameD x).2.2) = S.nameD x := rfl
      rw [hp, ht]
      show [idEquiv (N.nameC (S.tl x)), idEquiv (S.nameD (S.hrev x))] = _
      rw [S.nameD_hrev, ← S.nameC_tl x]
  · have hreal : rawReal (N.rotList (hostOf z)) (S.dinfoAt (hostOf z)) (fun u => S.dinfoAt u (hostOf z))
        (hostOf z) ((idEquiv.symm z).2.1, (idEquiv.symm z).2.2) = false := by
      rw [Bool.eq_false_iff]
      intro h
      obtain ⟨y, hy⟩ := (S.rawReal_iff _ _ _).1 h
      exact hz ((S.isReal_iff hN z).2 ⟨y, hy⟩)
    unfold rawAt
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [hreal]; decide)),
      S.levelNet_rotList_pend hN hz]

end RData

end RotSystem

end SsspFlow
