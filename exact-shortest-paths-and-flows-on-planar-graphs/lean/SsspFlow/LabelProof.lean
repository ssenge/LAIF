import SsspFlow.Output

/-!
# The program of the nodes

`progL`: the program of a node, a function of the phase, its local input and its memory. The memory after the phases
holds what `labelsOK_of_mem` asks for (`labels_memL`), and the output of the machine is correct.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal

namespace SsspFlow.Congest

open Cslib.Congest Cslib.Congest.Algorithm FourColor RotSystem RotSystem.RootedTree

variable {n : ℕ}

/-- The inputs of the constant phases. -/
noncomputable def constIn (r : Fin n) (rl : List (Fin n)) (v : Fin n) (m : Mem) : ℕ → RelaxIn (Fin n)
  | 1 => passIn (if v = r then 0 else n) (fun x _ => x) (depF r v)
  | 2 => passIn 0 (fun _ _ => (parR rl v m : ℕ)) (fun _ => 0)
  | 3 => passIn 0 (fun x _ => x) (upF 0 r rl v m)
  | 4 => passIn 0 (fun x _ => x) (upF 1 r rl v m)
  | 5 => passIn 0 (downM 0 3 r rl v m) (downF r rl v m)
  | 6 => passIn 0 (downM 1 4 r rl v m) (downF r rl v m)
  | 7 => passIn 0 (fun _ w => revM (numFL 0 3 5 r rl v m) w) (fun _ => 0)
  | 8 => passIn 0 (fun _ w => revM (numFL 1 4 6 r rl v m) w) (fun _ => 0)
  | _ => passIn 0 (fun _ w => revM (numPL r rl v m) w) (fun _ => 0)

/-- The inputs of the phases of one level. -/
noncomputable def levelIn (W : ℕ) (r : Fin n) (rl : List (Fin n)) (v : Fin n) (m : Mem) (d : ℕ) :
    ℕ → AggIn (Fin n) ⊕ RelaxIn (Fin n) ⊕ List (Fin n)
  | 0 => .inr (.inl (floodIn W v rl (corL W r rl v m d)))
  | 1 => .inl (aggInOf rl (nameL v m d) (portItsL r rl v m (corL W r rl v m d)))
  | 2 => .inl (aggInOf rl (nameL v m d) (selAIts W r rl v m d (corL W r rl v m d)))
  | 3 => .inl (aggInOf rl (nameL v m d) (recAIts W r rl v m d (corL W r rl v m d)))
  | 4 => .inl (aggInOf rl (nameL v m d) (selYIts W r rl v m d))
  | _ => .inl (aggInOf rl (nameL v m d) (recYIts W r rl v m d))

/-- **The program of a node.** -/
noncomputable def progL (P : ValP) (W : ℕ) (r : Fin n) (k : ℕ) (v : Fin n) (loc : LocalIn (Fin n)) (m : Mem) :
    AggIn (Fin n) ⊕ RelaxIn (Fin n) ⊕ List (Fin n) :=
  if k = 0 then .inr (.inr loc.nbrs)
  else if k < 10 then .inr (.inl (constIn r loc.nbrs v m k))
  else if k < 10 + 6 * (P.H + 1) then levelIn W r loc.nbrs v m ((k - 10) / 6) ((k - 10) % 6)
  else .inl (aggInOf loc.nbrs (nameL v m (P.H - (k - (10 + 6 * (P.H + 1)))))
    (vItsL P W r loc.nbrs loc.lenOut v m (k - (10 + 6 * (P.H + 1)))))

section Prog

variable (P : ValP) (W : ℕ) (r : Fin n) (v : Fin n) (loc : LocalIn (Fin n)) (m : Mem)

theorem progL_zero : progL P W r 0 v loc m = .inr (.inr loc.nbrs) := by
  unfold progL
  rw [if_pos rfl]

theorem progL_const {k : ℕ} (h1 : 1 ≤ k) (h2 : k < 10) :
    progL P W r k v loc m = .inr (.inl (constIn r loc.nbrs v m k)) := by
  unfold progL
  rw [if_neg (by omega), if_pos h2]

theorem progL_level {k d i : ℕ} (hk : k = 10 + 6 * d + i) (hd : d ≤ P.H) (hi : i < 6) :
    progL P W r k v loc m = levelIn W r loc.nbrs v m d i := by
  unfold progL
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), show (k - 10) / 6 = d by omega,
    show (k - 10) % 6 = i by omega]

theorem progL_val (i : ℕ) : progL P W r (phVal P.H i) v loc m =
    .inl (aggInOf loc.nbrs (nameL v m (P.H - i)) (vItsL P W r loc.nbrs loc.lenOut v m i)) := by
  unfold progL phVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    show 10 + 6 * (P.H + 1) + i - (10 + 6 * (P.H + 1)) = i by omega]

end Prog

section Mach

variable {σa σf : Type} {Bm : ℕ} (Aa : Algorithm (Fin n) (AggIn (Fin n)) σa Bm)
  (Af : Algorithm (Fin n) (List (Fin n)) σf Bm) (outa : Fin n → σa → ℕ → ℕ → Option ℕ)
  (outf : Fin n → σf → Fin n → ℕ) (Ta Tr Tf T : ℕ) (P : ValP) (W : ℕ) (r : Fin n)

/-- The answers of an aggregation as a table. -/
def resAL (v : Fin n) (s : σa) (key : ℕ) : ℕ := encO (outa v s (Nat.unpair key).1 (Nat.unpair key).2)

/-- The face names at a node as a table. -/
def resFL (v : Fin n) (s : σf) (key : ℕ) : ℕ := if h : key < n then outf v s ⟨key, h⟩ else 0

variable (N : Net (Fin n)) (ℓ : Fin n → Fin n → ℕ)

/-- The memory of a node after `k` phases. -/
noncomputable abbrev memL (k : ℕ) (v : Fin n) : Mem :=
  memAt Aa Af Ta Tr Tf T (progL P W r) (resAL outa) (resFL outf) N.G (N.localIn ℓ) k v

/-- The names of the faces. -/
def idL (x : N.G.Dart) : ℕ := outf x.fst (Af.run N.G N.rotList Tf x.fst) x.snd

theorem memL_id (hTf : Tf ≤ T) {j : ℕ} (hj : 1 ≤ j) (x : N.G.Dart) :
    memL Aa Af outa outf Ta Tr Tf T P W r N ℓ j x.fst 0 x.snd = idL Af outf Tf N x := by
  have h1 : memL Aa Af outa outf Ta Tr Tf T P W r N ℓ 1 x.fst 0 =
      resFL outf x.fst (Af.run N.G N.rotList Tf x.fst) :=
    mem_face Aa Af Ta Tr Tf T _ _ _ N.G _ (k := 0) N.rotList (fun w => progL_zero P W r w _ _) hTf x.fst
  have h2 : memL Aa Af outa outf Ta Tr Tf T P W r N ℓ j x.fst 0 =
      memL Aa Af outa outf Ta Tr Tf T P W r N ℓ 1 x.fst 0 :=
    mem_stable Aa Af Ta Tr Tf T _ _ _ N.G _ (j := 0) (k := j) (by omega) x.fst
  rw [h2, h1]
  unfold resFL idL
  rw [dif_pos x.snd.2]

theorem memL_const (hTr : Tr ≤ T) {k : ℕ} (h1 : 1 ≤ k) (h2 : k < 10) (v : Fin n) :
    memL Aa Af outa outf Ta Tr Tf T P W r N ℓ (k + 1) v k = relaxSt Bm N.G
      (fun w => constIn r (N.rotList w) w (memL Aa Af outa outf Ta Tr Tf T P W r N ℓ k w) k) Tr v :=
  mem_relax Aa Af Ta Tr Tf T _ _ _ N.G _ _ (fun w => progL_const P W r w _ _ h1 h2) hTr v

theorem constRun_memL (hTr : Tr ≤ T) : ConstRun N Bm Tr r (memL Aa Af outa outf Ta Tr Tf T P W r N ℓ) where
  stable := fun h v => mem_stable Aa Af Ta Tr Tf T _ _ _ N.G _ h v
  hDep v := memL_const Aa Af outa outf Ta Tr Tf T P W r N ℓ hTr (k := 1) (by omega) (by omega) v
  hPar v := memL_const Aa Af outa outf Ta Tr Tf T P W r N ℓ hTr (k := 2) (by omega) (by omega) v
  hUpF v := memL_const Aa Af outa outf Ta Tr Tf T P W r N ℓ hTr (k := 3) (by omega) (by omega) v
  hUpU v := memL_const Aa Af outa outf Ta Tr Tf T P W r N ℓ hTr (k := 4) (by omega) (by omega) v
  hDownF v := memL_const Aa Af outa outf Ta Tr Tf T P W r N ℓ hTr (k := 5) (by omega) (by omega) v
  hDownU v := memL_const Aa Af outa outf Ta Tr Tf T P W r N ℓ hTr (k := 6) (by omega) (by omega) v
  hRevF v := memL_const Aa Af outa outf Ta Tr Tf T P W r N ℓ hTr (k := 7) (by omega) (by omega) v
  hRevU v := memL_const Aa Af outa outf Ta Tr Tf T P W r N ℓ hTr (k := 8) (by omega) (by omega) v
  hRevP v := memL_const Aa Af outa outf Ta Tr Tf T P W r N ℓ hTr (k := 9) (by omega) (by omega) v

variable {sA kA b : ℕ}

/-- What the aggregation primitive promises. -/
def AggSpec (N : Net (Fin n)) (Aa : Algorithm (Fin n) (AggIn (Fin n)) σa Bm)
    (outa : Fin n → σa → ℕ → ℕ → Option ℕ) (Ta sA kA b : ℕ) : Prop :=
  ∀ inp : Fin n → AggIn (Fin n), AggIn.Valid N inp sA 2 kA b → ∀ v, ∀ x ∈ (inp v).member, ∀ κ,
    AggIn.IsMin inp x κ (outa v (Aa.run N.G inp Ta v) x κ)

theorem aggDone_memL {k₀ : ℕ} {nm : Fin n → Fin n × Bool → ℕ} {its : Fin n → Fin n × Bool → List (ℕ × ℕ)}
    (hTa : Ta ≤ T) (hAa : AggSpec N Aa outa Ta sA kA b)
    (hprog : ∀ w, progL P W r k₀ w (N.localIn ℓ w) (memL Aa Af outa outf Ta Tr Tf T P W r N ℓ k₀ w) =
      .inl (inpOf N nm its w)) :
    AggDone N nm its sA kA b (fun v => memL Aa Af outa outf Ta Tr Tf T P W r N ℓ (k₀ + 1) v k₀) := by
  intro hV v x hx κ
  refine ⟨_, hAa _ hV v x hx κ, ?_⟩
  have e : memL Aa Af outa outf Ta Tr Tf T P W r N ℓ (k₀ + 1) v k₀ =
      resAL outa v (Aa.run N.G (inpOf N nm its) Ta v) :=
    mem_agg Aa Af Ta Tr Tf T _ _ _ N.G _ (inpOf N nm its) hprog hTa v
  show memL Aa Af outa outf Ta Tr Tf T P W r N ℓ (k₀ + 1) v k₀ (Nat.pair x κ) = _
  rw [e]
  show encO (outa v _ (Nat.unpair (Nat.pair x κ)).1 (Nat.unpair (Nat.pair x κ)).2) = _
  rw [Nat.unpair_pair]

theorem levelRun_memL (hTr : Tr ≤ T) (hTa : Ta ≤ T) (hAa : AggSpec N Aa outa Ta sA kA b) :
    LevelRun N Bm Tr W sA kA b r P.H (memL Aa Af outa outf Ta Tr Tf T P W r N ℓ) where
  stable := fun h v => mem_stable Aa Af Ta Tr Tf T _ _ _ N.G _ h v
  hFlood d hd v := mem_relax Aa Af Ta Tr Tf T _ _ _ N.G _ _
    (fun w => progL_level P W r w _ _ (i := 0) (by unfold phFlood; omega) hd (by omega)) hTr v
  hPorts d hd := aggDone_memL Aa Af outa outf Ta Tr Tf T P W r N ℓ hTa hAa
    (fun w => progL_level P W r w _ _ (i := 1) (by unfold phPorts; omega) hd (by omega))
  hSelA d hd := aggDone_memL Aa Af outa outf Ta Tr Tf T P W r N ℓ hTa hAa
    (fun w => progL_level P W r w _ _ (i := 2) (by unfold phSelA; omega) hd (by omega))
  hRecA d hd := aggDone_memL Aa Af outa outf Ta Tr Tf T P W r N ℓ hTa hAa
    (fun w => progL_level P W r w _ _ (i := 3) (by unfold phRecA; omega) hd (by omega))
  hSelY d hd := aggDone_memL Aa Af outa outf Ta Tr Tf T P W r N ℓ hTa hAa
    (fun w => progL_level P W r w _ _ (i := 4) (by unfold phSelY; omega) hd (by omega))
  hRecY d hd := aggDone_memL Aa Af outa outf Ta Tr Tf T P W r N ℓ hTa hAa
    (fun w => progL_level P W r w _ _ (i := 5) (by unfold phRecY; omega) hd (by omega))

theorem valueRun_memL (hTa : Ta ≤ T) (hAa : AggSpec N Aa outa Ta sA kA b) :
    ValueRun N P W r (fun v => (N.localIn ℓ v).lenOut) sA kA b (memL Aa Af outa outf Ta Tr Tf T P W r N ℓ) where
  stable := fun h v => mem_stable Aa Af Ta Tr Tf T _ _ _ N.G _ h v
  hVal i _ := aggDone_memL Aa Af outa outf Ta Tr Tf T P W r N ℓ hTa hAa (fun w => progL_val P W r w _ _ i)

theorem fidN_lt {id : N.G.Dart → ℕ} {f : ℕ} (hidb : ∀ d, id d < 2 ^ f) (hf : 2 * f ≤ b)
    (hb1 : (W + 2) * (W + 2) ≤ 2 ^ b) (hW : ∀ z, N.codeN z < W) (z : N.G.Dart × Bool) : N.fidN id z < 2 ^ b := by
  unfold Net.fidN
  by_cases hz : z.2 = true
  · rw [if_pos hz]
    refine (Nat.pair_lt_max_add_one_sq _ _).trans_le ?_
    have h1 : max 0 (id z.1) + 1 ≤ 2 ^ f := by
      have := hidb z.1
      simpa using this
    calc (max 0 (id z.1) + 1) ^ 2 ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = 2 ^ (2 * f) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hf
  · rw [if_neg hz]
    refine (Nat.pair_lt_max_add_one_sq _ _).trans_le ?_
    have h1 := hW (z.1, false)
    have h2 : W ≠ 0 := by omega
    have h3 : max 1 (min (N.codeN (z.1, false)) (N.codeN (z.1.symm, false))) + 1 ≤ W + 2 := by
      have := min_le_left (N.codeN (z.1, false)) (N.codeN (z.1.symm, false))
      omega
    calc _ ≤ (W + 2) ^ 2 := Nat.pow_le_pow_left h3 2
      _ = (W + 2) * (W + 2) := by ring
      _ ≤ 2 ^ b := hb1

/-- The numbers of a run. -/
structure NumOK (n : ℕ) (P : ValP) (W h sA kA b Bm Tr₀ Wt hh ss ww : ℕ) : Prop where
  hTrB : (2 * P.H + 2) * (2 * (2 * h + 1 + 2 * (1 + P.H * (2 + 4 * h))) + 1) ≤ Tr₀ + 1
  hTr2 : h + 1 ≤ Tr₀
  hs : (2 * P.H + 2) * (2 * (h + (1 + P.H * (2 + 4 * h))) + 1) ≤ sA
  hk1 : 5 * (1 + P.H * (2 + 4 * h)) + 4 ≤ kA
  hk2 : (16 * (1 + (P.H + 1) * (2 + 4 * h)) + (1 + P.H * (2 + 4 * h))) * (5 + (P.Lb + 1)) ≤ kA
  hW5 : 5 ≤ W
  hWn : 2 * n * n + 2 ≤ W
  hHW : P.H ≤ W
  hBm : (W + 1) ^ 2 ≤ 2 ^ Bm
  hb1 : (W + 2) * (W + 2) ≤ 2 ^ b
  hb2 : (W + 6 + P.Lb) ^ 2 ≤ 2 ^ b
  hb3 : P.Wb + Wt + 1 ≤ 2 ^ b
  hhh : P.H ≤ hh
  hspan : (2 * P.H + 2) * (2 * (h + (1 + P.H * (2 + 4 * h))) + 1) ≤ ss
  hcard : 1 + (P.H + 1) * (2 + 4 * h) ≤ ss
  hname : (W + 1) ^ 2 ≤ 2 ^ ww
  hval : 2 * (((2 * P.H + 2) * (2 * (h + (1 + P.H * (2 + 4 * h))) + 1)) * Wt) < 2 ^ ww

/-- **The memory of a node after all phases gives correct labels.** -/
theorem labels_memL {e h Tr₀ Wt C Cl cl B₀ f k₀ hh ss ww : ℕ}
    (hNum : NumOK n P W h sA kA b Bm Tr₀ Wt hh ss ww) (hRB : RealizationBox C)
    (hq : LabelQuery Cl cl P.U P.query) (hU : 1 ≤ P.U) (hs1 : 1 ≤ P.s) (hB : 1 ≤ B₀)
    (hks : C * (2 + P.H * (2 + 4 * h) + 1) ^ 6 ≤ P.s) (hBig : 2 * (P.U * (2 * n * n) * Wt) ≤ B₀)
    (hcn : cU P.U ^ (2 * P.H + 1) ≤ 2) (hLb : P.Lb = bagLen Cl cl P.U P.s B₀) (hWb : P.Wb = bagWord cl P.s B₀)
    (hce : cU P.U ^ (2 * P.H + 1) ≤ 1 + (e : ℝ≥0∞)⁻¹) (hH3 : P.H = 3 * k₀) (hk₀ : 2 * n < 2 ^ k₀)
    (hTr : Tr₀ + 1 ≤ T) (hTa : Ta ≤ T) (hTf : Tf ≤ T) (hAa : AggSpec N Aa outa Ta sA kA b)
    (hfaces : ∀ d d' : N.G.Dart, idL Af outf Tf N d = idL Af outf Tf N d' ↔
      N.toRot.faceOf d = N.toRot.faceOf d')
    (hidb : ∀ d, idL Af outf Tf N d < 2 ^ f) (hf : 2 * f ≤ b)
    (hG : N.G.Connected) (hne : ∀ v, ∃ u, N.G.Adj v u) (hR : N.toRot.Planar) (hc : N.toRot.Connected)
    (hdist : ∀ v, N.G.dist r v ≤ h) (hℓ : N.LensIn ℓ Wt) :
    LabelsOK N ℓ e hh ss ww (fun v => outL P W r (N.rotList v) v
      (memL Aa Af outa outf Ta (Tr₀ + 1) Tf T P W r N ℓ (phVal P.H P.H + 1) v)) := by
  classical
  have hd₀ : (N.dart0 hne r).1.fst = r := rfl
  have hhd : (N.dart0 hne r).1.snd = (N.rotList r).headD r := rfl
  have hWz : ∀ z, N.codeN z < W := fun z => (N.codeN_lt z).trans_le (by have := hNum.hWn; omega)
  have hOK : (levelD N hG r (N.dart0 hne r).1 W (idL Af outf Tf N)).OK :=
    { h₀ := hd₀
      h₁ := rfl
      hR := hR
      hc := hc
      hinj := N.codeN_inj
      hcW := hWz
      hW := N.card_le.trans (show 2 * n * n ≤ W by have := hNum.hWn; omega)
      hfid := N.fid_iff hfaces }
  have hdep : ∀ v, (N.treeN hG r (N.dart0 hne r).1).dep v ≤ h := hdist
  have hVk : LevelData.VOK (levelD N hG r (N.dart0 hne r).1 W (idL Af outf Tf N)) P (gOf N ℓ) C Cl cl B₀ Wt h :=
    { hC := hRB
      hq := hq
      hU := hU
      hg := fun z => (hℓ _ _ z.1.adj).1
      hWt := fun z => (hℓ _ _ z.1.adj).2
      hs := hs1
      hB := hB
      hks := hks
      hBig := le_trans (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right Wt (Nat.mul_le_mul_left P.U N.card_le))) hBig
      hcn := hcn
      hLb := hLb
      hWb := hWb
      hdep := hdep }
  have hCR := constRun_memL Aa Af outa outf Ta (Tr₀ + 1) Tf T P W r N ℓ hTr
  have hfit : ∀ x, x ≤ 2 * n * n + 2 → x < 2 ^ Bm := fun x hx => by
    have h1 := hNum.hWn
    have h2 := hNum.hBm
    have h3 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by omega) _
    omega
  have hpair : ∀ a b, a ≤ 2 * n * n + 2 → b ≤ 2 * n * n + 2 → Nat.pair a b < 2 ^ Bm := fun a b ha hb' => by
    refine (Nat.pair_lt_max_add_one_sq a b).trans_le (le_trans (Nat.pow_le_pow_left ?_ 2) hNum.hBm)
    have h1 := hNum.hWn
    have : max a b ≤ W := max_le (by omega) (by omega)
    omega
  have hd : ∀ v, N.G.dist r v + 1 ≤ Tr₀ := fun v => by
    have h1 := hdist v
    have h2 := hNum.hTr2
    omega
  have hK : ∀ j, 10 ≤ j → ∀ v, ConstAt N hG r (N.dart0 hne r).1
      (memL Aa Af outa outf Ta (Tr₀ + 1) Tf T P W r N ℓ j v) v :=
    fun j hj v => constAt_of_run hG hCR hd hfit hpair hd₀ hhd hR hc hj v
  have hid : ∀ j, 1 ≤ j → ∀ x : N.G.Dart,
      memL Aa Af outa outf Ta (Tr₀ + 1) Tf T P W r N ℓ j x.fst 0 x.snd = idL Af outf Tf N x :=
    fun j hj x => memL_id Aa Af outa outf Ta (Tr₀ + 1) Tf T P W r N ℓ hTf hj x
  have hLR := levelRun_memL Aa Af outa outf Ta (Tr₀ + 1) Tf T P W r N ℓ (sA := sA) (kA := kA) (b := b) hTr hTa hAa
  have hbf := fidN_lt (W := W) (b := b) N hidb hf hNum.hb1 hWz
  have hlevels := levels_of_run hG hOK hLR hK hid hd₀ hhd hR hc hdep hNum.hBm hNum.hTrB hNum.hs hNum.hk1 hNum.hb1
    hbf hNum.hHW hNum.hW5
  have hE : ∀ j, phVal P.H 0 ≤ j → ∀ d, d ≤ P.H →
      EAll N (levelD N hG r (N.dart0 hne r).1 W (idL Af outf Tf N))
        (memL Aa Af outa outf Ta (Tr₀ + 1) Tf T P W r N ℓ j) d :=
    fun j hj d hd' => hLR.transport (hlevels d hd') (by unfold phVal at hj; unfold phRecY; omega)
  have hH : ∀ v, ¬ (N.treeN hG r (N.dart0 hne r).1).NP
      ((levelD N hG r (N.dart0 hne r).1 W (idL Af outf Tf N)).Γs P.H) v := fun v => by
    rw [hH3]
    exact hOK.decomp.final (by rw [Fintype.card_fin]; exact hk₀) v
  have hleaf := fun z => leaf_card hG hOK hdep (hsurjN hG r (N.dart0 hne r).1 hne) hH z
  have hVR := valueRun_memL Aa Af outa outf Ta (Tr₀ + 1) Tf T P W r N ℓ (sA := sA) (kA := kA) (b := b) hTa hAa
  have hb1' : (W + 1) ^ 2 ≤ 2 ^ b := by
    refine le_trans ?_ hNum.hb1
    rw [pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hvals := values_of_run hG hOK hVk hVR hK hid hE hd₀ hhd hR hc (fun z => if_pos z.1.adj) hNum.hs hNum.hk2
    hleaf hNum.hHW hb1' hNum.hb2 hNum.hb3 (by have := hNum.hWn; omega)
  have hphi : phVal P.H 0 ≤ phVal P.H P.H + 1 := by unfold phVal; omega
  have hM : MemOK N hG r (N.dart0 hne r).1 W (idL Af outf Tf N) P (gOf N ℓ)
      (memL Aa Af outa outf Ta (Tr₀ + 1) Tf T P W r N ℓ (phVal P.H P.H + 1)) :=
    { hC := hK _ (by unfold phVal; omega)
      hid := hid _ (by unfold phVal; omega)
      hE := hE _ hphi
      hV := fun i hi => hvals i hi _ (by unfold phVal; omega) }
  exact labelsOK_of_mem hG hOK hVk hM hne hH hd₀ hhd hR hc hce hNum.hhh hNum.hspan hNum.hcard hNum.hHW hNum.hname
    hNum.hval

end Mach

section Final

variable {σa σf : Type} {Bm B' : ℕ} (Aa : Algorithm (Fin n) (AggIn (Fin n)) σa Bm)
  (Af : Algorithm (Fin n) (List (Fin n)) σf Bm) (outa : Fin n → σa → ℕ → ℕ → Option ℕ)
  (outf : Fin n → σf → Fin n → ℕ) (Ta Tr Tf T KP : ℕ) (P : ValP) (W : ℕ) (r : Fin n)

/-- **The algorithm of the nodes.** -/
noncomputable def finalAlg (hB : Bm ≤ B') :=
  (((mach Aa Af Ta Tr Tf T (progL P W r) (resAL outa) (resFL outf)).stopAt (KP * T)).premap
    fun _ (i : LocalIn (Fin n)) => ((i, 0, fun _ _ => 0) : LocalIn (Fin n) × ℕ × Mem)).widen hB

theorem run_finalAlg (hB : Bm ≤ B') (hT : 0 < T) (N : Net (Fin n)) (ℓ : Fin n → Fin n → ℕ) {t : ℕ} (ht : KP * T ≤ t)
    (v : Fin n) :
    let st := (finalAlg Aa Af outa outf Ta Tr Tf T KP P W r hB).run N.G (N.localIn ℓ) t v
    st.2.1.1 = N.localIn ℓ v ∧ st.2.1.2.2 = memL Aa Af outa outf Ta Tr Tf T P W r N ℓ KP v := by
  intro st
  have h1 : st = (KP * T, (mach Aa Af Ta Tr Tf T (progL P W r) (resAL outa) (resFL outf)).run N.G
      (fun v => (N.localIn ℓ v, 0, fun _ _ => 0)) (KP * T) v) := by
    show (finalAlg Aa Af outa outf Ta Tr Tf T KP P W r hB).run N.G (N.localIn ℓ) t v = _
    unfold finalAlg
    rw [run_widen, run_premap, run_stopAt, min_eq_right ht]
  have h := run_iter (bodyAlg Aa Af Ta Tr Tf) (T := T)
    (fun v (j : LocalIn (Fin n) × ℕ × Mem) => progL P W r j.2.1 v j.1 j.2.2)
    (fun v j s => (j.1, j.2.1 + 1, Function.update j.2.2 j.2.1 (resOf (resAL outa) (resFL outf) v s)))
    N.G (fun v => (N.localIn ℓ v, 0, fun _ _ => 0)) hT KP 0 hT
  rw [Nat.add_zero] at h
  have h2 : st.2.1 = machData Aa Af Ta Tr Tf T (progL P W r) (resAL outa) (resFL outf) N.G (N.localIn ℓ) KP v := by
    rw [h1]
    show ((mach Aa Af Ta Tr Tf T (progL P W r) (resAL outa) (resFL outf)).run N.G
      (fun v => (N.localIn ℓ v, 0, fun _ _ => 0)) (KP * T) v).1 = _
    unfold mach machData
    rw [h]
  rw [h2]
  exact ⟨data_fst Aa Af Ta Tr Tf T _ _ _ N.G _ KP v, rfl⟩

end Final

end SsspFlow.Congest
