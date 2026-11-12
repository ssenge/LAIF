import SsspFlow.ValueTab

/-!
# The value phases at the nodes

A node reads the records of a value call from its memory (`vItsL`), without knowing the network. Given the entries of
the memory, these records agree with `vItems` of `ValueTab`. A run of the value phases gives the tables of all value
calls (`values_of_run`). The corners of a leaf bag are few by the bound on the edges of a planar graph (`leaf_card`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal

namespace SsspFlow.Congest

open Cslib.Congest Cslib.Congest.Algorithm FourColor RotSystem RotSystem.RootedTree

variable {n : ℕ}

/-- The phase of a value call. -/
def phVal (H i : ℕ) : ℕ := 10 + 6 * (H + 1) + i

/-- A sector of a node as a number. -/
def secEnc (v : Fin n) : Option (Fin n × Bool) → ℕ
  | none => 0
  | some c => cL v c + 1

theorem secEnc_inj {v : Fin n} {o o' : Option (Fin n × Bool)} (h : secEnc v o = secEnc v o') : o = o' := by
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some c => simp [secEnc] at h
  | some c =>
    cases o' with
    | none => simp [secEnc] at h
    | some c' =>
      have h1 : cL v c = cL v c' := by simpa [secEnc] using h
      rw [cL_inj h1]

theorem secEnc_le (hn : 0 < n) (v : Fin n) (o : Option (Fin n × Bool)) : secEnc v o ≤ 2 * n * n := by
  cases o with
  | none => exact Nat.zero_le _
  | some c => exact codeRaw_lt v.2 c.1.2 c.2

section Readers

variable (P : ValP) (W : ℕ) (r : Fin n) (rl : List (Fin n)) (len : Fin n → ℕ) (v : Fin n) (m : Mem)
  (i : ℕ) (y : Fin n × Bool)

/-- The corners of a level from the top at a node, from the memory. -/
noncomputable def corV : Finset (Fin n × Bool) :=
  if i = 0 then (ownL rl).toFinset else corL W r rl v m (P.H + 1 - i)

/-- The name of the cycle of a corner, from the memory. -/
def cyV : ℕ := if i = 0 then Nat.pair 0 (min (cL v y) (cR v y)) else nameL v m (P.H + 1 - i) y

/-- The name of the sector of a corner, from the memory. -/
noncomputable def secV : ℕ := Nat.pair v (secEnc v (secOf (rotV rl) (corV P W r rl v m (i + 1)) y))

/-- The flag of a corner of the next level, from the memory. -/
noncomputable def flV : ℕ := if y ∈ corV P W r rl v m (i + 1) then 1 else 0

/-- The table of a value call for the bag of a dart, from the memory. -/
def tabV (κ : ℕ) : ℕ := m (phVal P.H i) (Nat.pair (nameL v m (P.H - i) y) κ)

/-- The label of a corner, from the memory. -/
noncomputable def labV : ℕ → List ℕ
  | 0 => [len y.1]
  | i + 1 => labPT P.bagF W (P.dec i) (tabV P v m i y) (minC v m (P.H - i) y) (cL v y)

/-- The pairs of a dart in a value call, from the memory. -/
noncomputable def vItsL : List (ℕ × ℕ) :=
  if y ∈ corV P W r rl v m i then
    fieldItems (cL v y) (cyV P v m i y) (secV P W r rl v m i y) (numPL r rl v m y) (flV P W r rl v m i y)
      (labV P W len v m y i)
  else []

end Readers

/-- The name of the sector of a corner of a level from the top. -/
noncomputable def Net.secN (N : Net (Fin n)) (Γ : ℕ → Finset (N.G.Dart × Bool)) (i : ℕ)
    (z : N.G.Dart × Bool) : ℕ :=
  Nat.pair z.1.fst (secEnc z.1.fst
    (secOf (rotV (N.rotList z.1.fst)) (N.cornersAt z.1.fst (Γ (i + 1))) (N.locN z)))

theorem Net.secN_lt (N : Net (Fin n)) (Γ : ℕ → Finset (N.G.Dart × Bool)) {W b : ℕ} (hW : 2 * n * n ≤ W)
    (hb : (W + 1) ^ 2 ≤ 2 ^ b) (i : ℕ) (z : N.G.Dart × Bool) : N.secN Γ i z < 2 ^ b := by
  have hn : 0 < n := z.1.fst.pos
  have h1 := secEnc_le hn z.1.fst
    (secOf (rotV (N.rotList z.1.fst)) (N.cornersAt z.1.fst (Γ (i + 1))) (N.locN z))
  have h2 : (z.1.fst : ℕ) < n := z.1.fst.2
  have h3 : n ≤ 2 * n * n := by nlinarith
  refine (Nat.pair_lt_max_add_one_sq _ _).trans_le (le_trans (Nat.pow_le_pow_left ?_ 2) hb)
  have : max (z.1.fst : ℕ) (secEnc z.1.fst
      (secOf (rotV (N.rotList z.1.fst)) (N.cornersAt z.1.fst (Γ (i + 1))) (N.locN z))) ≤ W :=
    max_le (by omega) (by omega)
  omega

/-- The entries of a value call. -/
def EV (N : Net (Fin n)) (L : LevelData (Fin n) N.toRot) (P : ValP) (g : N.G.Dart × Bool → ℕ)
    (sec : ℕ → N.G.Dart × Bool → ℕ) (m : Fin n → Mem) (i : ℕ) : Prop :=
  ∀ (z : N.G.Dart × Bool) (κ : ℕ),
    m z.1.fst (phVal P.H i) (Nat.pair (L.nm (P.H - i) z) κ) = L.vT P g sec i z κ

section Concrete

variable {N : Net (Fin n)} (hG : N.G.Connected) {r : Fin n} {d₀ : N.G.Dart} {W : ℕ} {id : N.G.Dart → ℕ}
  {m : Fin n → Mem} {P : ValP} {g : N.G.Dart × Bool → ℕ} {len : Fin n → Fin n → ℕ}

local notation "𝓛" => levelD N hG r d₀ W id
local notation "𝓣" => Net.treeN N hG r d₀

/-- Corners on one vertex of a split share a sector, and the name of the sector tells it. -/
theorem secN_iff (hG : N.G.Connected) (r : Fin n) (d₀ : N.G.Dart) {Γ : ℕ → Finset (N.G.Dart × Bool)} (i : ℕ)
    (p q : N.G.Dart × Bool) :
    N.secN Γ i p = N.secN Γ i q ↔
      (N.toRot.double.split (Γ (i + 1))).tail p = (N.toRot.double.split (Γ (i + 1))).tail q := by
  have ht : ∀ z, (N.treeN hG r d₀).vertM z = z.1.fst := fun _ => rfl
  constructor
  · intro e
    obtain ⟨e1, e2⟩ := Nat.pair_eq_pair.1 e
    have e4 : q.1.fst = p.1.fst := (Fin.ext e1).symm
    refine (N.sec_iff (N.treeN hG r d₀) ht (v := p.1.fst) rfl e4).2 ?_
    have e5 := e2
    rw [e4] at e5
    exact secEnc_inj e5
  · intro e
    have e1 : p.1.fst = q.1.fst := vertM_of_tail (t := N.treeN hG r d₀) e
    have e2 := (N.sec_iff (N.treeN hG r d₀) ht (v := p.1.fst) rfl e1.symm).1 e
    unfold Net.secN
    rw [← e1, e2]

variable (hC : ∀ v, ConstAt N hG r d₀ (m v) v) (hd₀ : d₀.fst = r) (hhd : d₀.snd = (N.rotList r).headD r)
  (hR : N.toRot.Planar) (hc : N.toRot.Connected)

include hC hd₀ hhd hR hc in
/-- **A node reads its corners at a level from the top from its memory.** -/
theorem corV_eq (hOK : (𝓛).OK) (hid : ∀ x : N.G.Dart, m x.fst 0 x.snd = id x)
    (hE : ∀ d, d ≤ P.H → EAll N (𝓛) m d) (i : ℕ) (v : Fin n) :
    corV P W r (N.rotList v) v (m v) i = N.cornersAt v ((𝓛).Γt P i) := by
  classical
  cases i with
  | zero =>
    unfold corV
    rw [if_pos rfl]
    ext y
    rw [List.mem_toFinset]
    constructor
    · intro hy
      obtain ⟨z, rfl, rfl⟩ := exists_dart_of_own hy
      exact (N.mem_cornersAt rfl).2 (Finset.mem_univ _)
    · intro hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨-, rfl⟩ := Finset.mem_filter.1 hz
      exact locN_mem_own z
  | succ i =>
    unfold corV
    rw [if_neg (Nat.succ_ne_zero i), LevelData.Γt_succ, show P.H + 1 - (i + 1) = P.H - i by omega]
    exact corL_eq hG hC hd₀ hhd hR hc hOK hid _ (fun d' hd' => hE d' (by omega)) v

theorem cyV_eq (hE : ∀ d, d ≤ P.H → EF N (𝓛) m d) {i : ℕ} (z : N.G.Dart × Bool) :
    cyV P z.1.fst (m z.1.fst) i (N.locN z) = (𝓛).cyId P i z := by
  unfold cyV LevelData.cyId
  by_cases hi : i = 0
  · rw [if_pos hi, if_pos hi]
    rfl
  · rw [if_neg hi, if_neg hi]
    exact nameL_eq (hE _ (by omega)) z

include hC hd₀ hhd hR hc in
theorem secV_eq (hOK : (𝓛).OK) (hid : ∀ x : N.G.Dart, m x.fst 0 x.snd = id x)
    (hE : ∀ d, d ≤ P.H → EAll N (𝓛) m d) (i : ℕ) (z : N.G.Dart × Bool) :
    secV P W r (N.rotList z.1.fst) z.1.fst (m z.1.fst) i (N.locN z) = N.secN ((𝓛).Γt P) i z := by
  unfold secV Net.secN
  rw [corV_eq hG hC hd₀ hhd hR hc hOK hid hE]

include hC hd₀ hhd hR hc in
theorem flV_eq (hOK : (𝓛).OK) (hid : ∀ x : N.G.Dart, m x.fst 0 x.snd = id x)
    (hE : ∀ d, d ≤ P.H → EAll N (𝓛) m d) (i : ℕ) (z : N.G.Dart × Bool) :
    flV P W r (N.rotList z.1.fst) z.1.fst (m z.1.fst) i (N.locN z) = (𝓛).flagOf P i z := by
  unfold flV LevelData.flagOf
  rw [corV_eq hG hC hd₀ hhd hR hc hOK hid hE]
  simp only [N.mem_cornersAt rfl]

theorem tabV_eq {sec : ℕ → N.G.Dart × Bool → ℕ} {i : ℕ} (hF : EF N (𝓛) m (P.H - i))
    (hV : EV N (𝓛) P g sec m i) (z : N.G.Dart × Bool) :
    tabV P z.1.fst (m z.1.fst) i (N.locN z) = (𝓛).vT P g sec i z := by
  funext κ
  show m z.1.fst (phVal P.H i) (Nat.pair (nameL z.1.fst (m z.1.fst) (P.H - i) (N.locN z)) κ) = _
  rw [nameL_eq hF z]
  exact hV z κ

include hC hd₀ hhd hR hc in
/-- **The records of a value call, from the memory.** -/
theorem vItsL_eq (hOK : (𝓛).OK) (hid : ∀ x : N.G.Dart, m x.fst 0 x.snd = id x)
    (hE : ∀ d, d ≤ P.H → EAll N (𝓛) m d) (hU : 1 ≤ P.U) (hlen : ∀ z : N.G.Dart × Bool, len z.1.fst z.1.snd = g z)
    {i : ℕ} (hprev : ∀ i', i = i' + 1 → EV N (𝓛) P g (N.secN ((𝓛).Γt P)) m i') (z : N.G.Dart × Bool) :
    vItsL P W r (N.rotList z.1.fst) (len z.1.fst) z.1.fst (m z.1.fst) i (N.locN z) =
      (𝓛).vItems P g (N.secN ((𝓛).Γt P)) i z := by
  classical
  unfold vItsL LevelData.vItems
  rw [corV_eq hG hC hd₀ hhd hR hc hOK hid hE]
  by_cases hz : z ∈ (𝓛).Γt P i
  · rw [if_pos ((N.mem_cornersAt rfl).2 hz), if_pos hz,
      cyV_eq hG (fun d hd => (hE d hd).f), secV_eq hG hC hd₀ hhd hR hc hOK hid hE,
      constAt_numP hG hC hd₀ hhd hR hc rfl, flV_eq hG hC hd₀ hhd hR hc hOK hid hE]
    have hlab : labV P W (len z.1.fst) z.1.fst (m z.1.fst) (N.locN z) i = (𝓛).labelOf P g i z := by
      cases i with
      | zero =>
        show [len z.1.fst z.1.snd] = [g z]
        rw [hlen]
      | succ i =>
        show labPT P.bagF W (P.dec i) (tabV P z.1.fst (m z.1.fst) i (N.locN z))
          (minC z.1.fst (m z.1.fst) (P.H - i) (N.locN z)) (cL z.1.fst (N.locN z)) = _
        rw [tabV_eq hG (hE _ (by omega)).f (hprev i rfl) z, minC_eq (hE _ (by omega)).f z,
          hOK.label_read hU (fun i p q _ _ => secN_iff hG r d₀ i p q) hz]
        rfl
    rw [hlab]
    rfl
  · rw [if_neg (fun h => hz ((N.mem_cornersAt rfl).1 h)), if_neg hz]

end Concrete

section Run

/-- What the value phases of a run compute. -/
structure ValueRun (N : Net (Fin n)) (P : ValP) (W : ℕ) (r : Fin n) (len : Fin n → Fin n → ℕ) (s k b : ℕ)
    (mem : ℕ → Fin n → Mem) : Prop where
  stable : ∀ {j k}, j < k → ∀ v, mem k v j = mem (j + 1) v j
  hVal : ∀ i, i ≤ P.H → AggDone N (fun v => nameL v (mem (phVal P.H i) v) (P.H - i))
    (fun v => vItsL P W r (N.rotList v) (len v) v (mem (phVal P.H i) v) i) s k b
    (fun v => mem (phVal P.H i + 1) v (phVal P.H i))

variable {N : Net (Fin n)} (hG : N.G.Connected) {r : Fin n} {d₀ : N.G.Dart} {W : ℕ} {id : N.G.Dart → ℕ}
  {P : ValP} {g : N.G.Dart × Bool → ℕ} {len : Fin n → Fin n → ℕ} {s k b h Jl C Cl cl B Wt : ℕ}
  {mem : ℕ → Fin n → Mem}

local notation "𝓛" => levelD N hG r d₀ W id
local notation "𝓣" => Net.treeN N hG r d₀

/-- **The value phases of a run give the tables of all value calls.** -/
theorem values_of_run (hOK : (𝓛).OK) (hV : LevelData.VOK (𝓛) P g C Cl cl B Wt h)
    (hrun : ValueRun N P W r len s k b mem)
    (hK : ∀ j, 10 ≤ j → ∀ v, ConstAt N hG r d₀ (mem j v) v)
    (hid : ∀ j, 1 ≤ j → ∀ x : N.G.Dart, mem j x.fst 0 x.snd = id x)
    (hE : ∀ j, phVal P.H 0 ≤ j → ∀ d, d ≤ P.H → EAll N (𝓛) (mem j) d)
    (hd₀ : d₀.fst = r) (hhd : d₀.snd = (N.rotList r).headD r) (hR : N.toRot.Planar) (hc : N.toRot.Connected)
    (hlen : ∀ z : N.G.Dart × Bool, len z.1.fst z.1.snd = g z)
    (hs : (2 * P.H + 2) * (2 * (h + (1 + P.H * (2 + 4 * h))) + 1) ≤ s)
    (hkk : (Jl + (1 + P.H * (2 + 4 * h))) * (5 + (P.Lb + 1)) ≤ k)
    (hleaf : ∀ z, (Finset.univ.filter fun p => (𝓛).nm P.H p = (𝓛).nm P.H z).card ≤ Jl)
    (hHW : P.H ≤ W) (hb1 : (W + 1) ^ 2 ≤ 2 ^ b) (hb2 : (W + 6 + P.Lb) ^ 2 ≤ 2 ^ b)
    (hb3 : P.Wb + Wt + 1 ≤ 2 ^ b) (hW2 : 2 * n * n ≤ W) :
    ∀ i, i ≤ P.H → ∀ j, phVal P.H i < j → EV N (𝓛) P g (N.secN ((𝓛).Γt P)) (mem j) i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi j hj z κ
    rw [hrun.stable hj z.1.fst]
    have hKj := hK (phVal P.H i) (by unfold phVal; omega)
    have hEj := hE (phVal P.H i) (by unfold phVal; omega)
    have hidj := hid (phVal P.H i) (by unfold phVal; omega)
    have hprev : ∀ i', i = i' + 1 →
        EV N (𝓛) P g (N.secN ((𝓛).Γt P)) (mem (phVal P.H i)) i' := by
      intro i' hi'
      exact ih i' (by omega) (by omega) _ (by unfold phVal; omega)
    refine level_call hG hOK hV.hdep (show P.H - i ≤ P.H by omega) hs
      (fun z => (hOK.nm_lt hHW (by omega) z).trans_le hb1)
      (fun z => nameL_eq (hEj _ (by omega)).f z)
      (fun z => vItsL_eq hG hKj hd₀ hhd hR hc hOK hidj hEj hV.hU hlen hprev z) (hrun.hVal i hi) ?_ ?_ z κ
    · intro z
      obtain ⟨K, h1, h2⟩ := hOK.exists_val_keys (P := P) (g := g) (sec := N.secN ((𝓛).Γt P))
        (i := i) (z := z) (Lm := P.Lb + 1) (J := Jl + (1 + P.H * (2 + 4 * h)))
        (fun z hz => hOK.label_len hV hi hz) (hOK.card_cornersIn hV hleaf hi z)
      exact ⟨K, h1.trans hkk, h2⟩
    · intro z p hp
      exact hOK.vItems_lt hV hi hHW hb2 hb3 (fun i z => N.secN_lt _ hW2 hb1 i z) hp

/-- **The darts of a leaf bag are few.** The vertices of a leaf bag are its hubs, and a planar graph has few edges. -/
theorem leaf_card (hOK : (𝓛).OK) {H : ℕ} (hdep : ∀ v, (𝓣).dep v ≤ h) (hsurj : ∀ v, ∃ d, (𝓣).vert d = v)
    (hH : ∀ v, ¬ (𝓣).NP ((𝓛).Γs H) v) (z : N.G.Dart × Bool) :
    (Finset.univ.filter fun p => (𝓛).nm H p = (𝓛).nm H z).card ≤ 16 * (1 + (H + 1) * (2 + 4 * h)) := by
  classical
  have hadj : ∀ a b, N.G.Adj a b → ∃ d : N.G.Dart, (𝓣).vert d = a ∧ (𝓣).vert (N.toRot.rev d) = b :=
    fun a b hab => ⟨⟨(a, b), hab⟩, rfl, rfl⟩
  set x := (𝓛).nm H z with hx
  have hhubc := Decomp.hub_card (hD := hOK.decomp) (hc := hOK.hc) (hinj := hOK.hinj) (hadj := hadj)
    (hsurj := hsurj) (hH := hH) hdep x
  have hhubeq := Decomp.hub_eq (hOK.decomp) hOK.hc hOK.hinj hadj hsurj hH x
  set S : Finset (Fin n) := Finset.univ.filter
    (· ∈ (hOK.decomp.hierarchy hOK.hc hOK.hinj hadj hsurj hH).hub x) with hS
  have hSc : S.card ≤ 1 + (H + 1) * (2 + 4 * h) := by
    have h1 : (S : Set (Fin n)) = (hOK.decomp.hierarchy hOK.hc hOK.hinj hadj hsurj hH).hub x := by
      ext a
      simp [hS]
    rw [← Set.ncard_coe_finset, h1]
    exact hhubc
  set A : Finset N.G.Dart := Finset.univ.filter fun d => d.fst ∈ S ∧ d.snd ∈ S with hA
  have hAr : N.toRot.RevClosed A := by
    intro d hd
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 hd
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h2, h1⟩
  have hcard := RotSystem.card_le_of_planar (R := N.toRot) (τ := fun d : N.G.Dart => d.fst)
    (fun d d' => (𝓣).vert_eq_iff d d') (fun d => (d.adj).ne')
    (fun d d' e1 e2 => SimpleGraph.Dart.ext _ _ (Prod.ext e1 e2)) hAr hOK.hR
  have him : (A.image fun d : N.G.Dart => d.fst).card ≤ S.card := by
    refine Finset.card_le_card fun a ha => ?_
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 ha
    exact (Finset.mem_filter.1 hd).2.1
  have hmemHub : ∀ p : N.G.Dart × Bool, (𝓛).nm H p = x → (𝓣).vertM p ∈ S := by
    intro p hp
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rw [hhubeq]
    refine Finset.mem_coe.2 (mem_bagHubs.2 ⟨p, ?_, ?_, rfl⟩)
    · unfold hubLevel
      have e1 : (Nat.unpair x).1 = H := bagName_fst _ _
      rw [e1, Nat.sub_self, topLevel_zero]
      exact Finset.mem_univ _
    · have e1 : (Nat.unpair x).1 = H := bagName_fst _ _
      show _ ∧ _
      rw [e1]
      exact ⟨le_rfl, hp⟩
  have hB : (Finset.univ.filter fun p => (𝓛).nm H p = x) ⊆ A ×ˢ (Finset.univ : Finset Bool) := by
    intro p hp
    have hp' := (Finset.mem_filter.1 hp).2
    refine Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hmemHub p hp', ?_⟩,
      Finset.mem_univ _⟩
    have h1 : (𝓛).nm H (N.toRot.double.rev p) = x := by
      rw [← hp']
      exact (LevelData.nm_congr (same_rev _ p)).symm
    exact hmemHub _ h1
  have h2 := Finset.card_le_card hB
  rw [Finset.card_product, Finset.card_univ, Fintype.card_bool] at h2
  omega

end Run

end SsspFlow.Congest
