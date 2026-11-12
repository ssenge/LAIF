import EqualSubsetSum.Accounting
import EqualSubsetSum.Windows

/-!
# The lemmas composed over the coin

For a fixed instance, the coin of the procedure is the labeling, the prime and the number of
iterations. `coin_mean` bounds below the mean over the coin of the probability that the search returns
a marked residue. It composes, for the actual lists, Lemma 2, Lemma 3 (`filter_lists`), Lemma 4
(`pairFound_of_good`), the marked fraction (`marked_fraction`) and a uniform number of iterations
(`grover_uniform`). The only quantum hypothesis it uses is the `GroverSuccess` formula.

Its hypothesis on the instance is the one of `filter_lists`: the values of the representations of `D`
are distinct on good labelings, and `⟨D, y⟩ = 0`. `coin_mean_minimal` gets this from minimality and
`2 z < n`. `coin_mean_empty` gets it from an empty label, where `K = 1`, at any `p` and without
minimality.

`coin_cost` puts the bound on the mean and the bound on the cost on the same family of instances,
with the same schedule and the same `q (3/32)`. It connects the two numerically. It does not say that
the amplified procedure is the search of `coin_mean`, since `Primitives` has no circuits: its fields
`amplify` and `amplifySucc` are constrained only by the hypotheses of `EqualSubsetSum.Model`.
-/

open Finset

namespace EqualSubsetSum

section Fixed

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {ν : Layout} {D y : ι → ℤ}

open scoped Classical in
/-- The fraction of residues of `Z_P` whose windows contain a pair with equal exact sum, for a
labeling and a prime. -/
noncomputable def markedFrac (T : ℕ)
    (ex : ∀ (L : ι → Label) (P : ℕ) (ρ : ℤ), Enum (binX L ν y P ρ))
    (ey : ∀ (L : ι → Label) (P : ℕ) (ρ : ℤ), Enum (binY L ν y P ρ))
    (L : ι → Label) (P : ℕ) : ℝ :=
  (#((Ico (0 : ℤ) (P : ℤ)).filter (PairFound T (ex L P) (ey L P))) : ℝ) / P

/-- The parameters of the coin for one instance. A fraction at least `q` of the labelings is good.
The primes have `PrimeHit`, the lists have size at most `U`, `T ≥ 1` with `64 U δ ≤ T`, `K δ ≤ b`,
`P ≤ 2 K s` for all primes, and `J² ≥ 2 (2 + 64 b) s`. -/
structure CoinHyp (G : Primitives) (ε Λ : ℕ → ℝ) (n : ℕ) (ν : Layout) (D y : ι → ℤ)
    (ΩL : Finset (ι → Label)) (q : ℝ) (Ps : Finset ℕ) (B : ℤ) (δ U : ℝ) (T : ℕ) (b s : ℝ) (J : ℕ) :
    Prop where
  grover : GroverSuccess G ε Λ
  q_nonneg : 0 ≤ q
  good : q ≤ prob ΩL (fun L => Good L ν D)
  primes_ne : Ps.Nonempty
  prime : ∀ P ∈ Ps, P.Prime
  hit : PrimeHit Ps B δ
  δ_nonneg : 0 ≤ δ
  bound : 4 * ∑ i, |y i| ≤ B
  listX_le : ∀ L : ι → Label, (#(listX L ν) : ℝ) ≤ U
  listY_le : ∀ L : ι → Label, (#(listY L ν) : ℝ) ≤ U
  T_pos : 1 ≤ T
  T_ge : 64 * U * δ ≤ T
  b_ge : ((ν .A 0).choose ν.f : ℝ) * δ ≤ b
  s_pos : 0 < s
  P_le : ∀ P ∈ Ps, (P : ℝ) ≤ 2 * (((ν .A 0).choose ν.f : ℝ) * s)
  J_ge : 2 * (2 + 64 * b) * s ≤ (J : ℝ) ^ 2
  J_le : (J : ℝ) ≤ Λ n
  err : ε n ≤ 1 / 4

/-- **The mean success over the coin.** Let `D` annihilate `y`, with distinct values of its
representations on good labelings. Under `CoinHyp`, the mean over the coin `(Π, P, j)` of the
probability that the search returns a marked residue is at least `q (3/4) (1/4 - ε n)`. -/
theorem coin_mean {G : Primitives} {ε Λ : ℕ → ℝ} {n : ℕ} {ΩL : Finset (ι → Label)} {q : ℝ}
    {Ps : Finset ℕ} {B : ℤ} {δ U : ℝ} {T : ℕ} {b s : ℝ} {J : ℕ} (hy : dot D y = 0)
    (hinj : ∀ L : ι → Label, Good L ν D →
      Set.InjOn (fun p : (ι → ℤ) × (ι → ℤ) => dot p.1 y) (reps L ν D))
    (h : CoinHyp G ε Λ n ν D y ΩL q Ps B δ U T b s J)
    (ex : ∀ (L : ι → Label) (P : ℕ) (ρ : ℤ), Enum (binX L ν y P ρ))
    (ey : ∀ (L : ι → Label) (P : ℕ) (ρ : ℤ), Enum (binY L ν y P ρ)) :
    q * ((3 / 4) * (1 / 4 - ε n)) ≤ mean (ΩL ×ˢ (Ps ×ˢ range J))
      (fun x => G.groverSucc n (markedFrac T ex ey x.1 x.2.1) x.2.2) := by
  classical
  have hKpos : (0 : ℝ) < ((ν .A 0).choose ν.f : ℝ) := by
    exact_mod_cast Nat.choose_pos ν.f_le
  have hb0 : 0 ≤ b := le_trans (mul_nonneg hKpos.le h.δ_nonneg) h.b_ge
  have hc : 0 < 2 + 64 * b := by linarith
  have hs := h.s_pos
  have hthr : 0 < 2 * (2 + 64 * b) * s := by positivity
  refine coin_success ΩL Ps (range J) (fun L => Good L ν D)
    (fun L P => GoodPrimeLists L ν D y (T : ℝ) b P)
    (fun L P j => G.groverSucc n (markedFrac T ex ey L P) j)
    h.q_nonneg (by linarith [h.err]) (fun _ _ _ _ _ _ => G.groverSucc_nonneg _ _ _) h.good ?_ ?_
  · intro L _ hL
    exact filter_lists hL hy (hinj L hL) Ps h.primes_ne h.hit h.δ_nonneg h.bound (h.listX_le L)
      (h.listY_le L) h.T_ge h.b_ge
  · intro L _ _ P hP hgood
    obtain ⟨R, hR, hρ⟩ := hgood
    have hPpos : 0 < P := (h.prime P hP).pos
    have hPr : (0 : ℝ) < P := by exact_mod_cast hPpos
    have hPz : (0 : ℤ) < (P : ℤ) := by exact_mod_cast hPpos
    have hRsub : R ⊆ (Ico (0 : ℤ) (P : ℤ)).filter (PairFound T (ex L P) (ey L P)) := by
      intro ρ hρR
      obtain ⟨p, -, hres, -⟩ := hρ ρ hρR
      refine mem_filter.mpr ⟨mem_Ico.mpr ⟨?_, ?_⟩,
        pairFound_of_good h.T_pos hy (ex L P) (ey L P) (hρ ρ hρR)⟩
      · rw [← hres]
        exact Int.emod_nonneg _ hPz.ne'
      · rw [← hres]
        exact Int.emod_lt_of_pos _ hPz
    have hcount : (#R : ℝ)
        ≤ #((Ico (0 : ℤ) (P : ℤ)).filter (PairFound T (ex L P) (ey L P))) := by
      exact_mod_cast card_le_card hRsub
    obtain ⟨hm1, hm2⟩ := marked_fraction hKpos hs hb0 hPr hR hcount (h.P_le P hP) rfl
    have hmarked : 1 / (2 * (2 + 64 * b) * s) ≤ markedFrac T ex ey L P := by
      have hm3 := hm2.trans hm1
      unfold markedFrac
      convert hm3
    have hφ0 : 0 < markedFrac T ex ey L P :=
      lt_of_lt_of_le (by positivity) hmarked
    have hφ1 : markedFrac T ex ey L P ≤ 1 := by
      unfold markedFrac
      apply div_le_one_of_le₀ _ hPr.le
      have h1 : #((Ico (0 : ℤ) (P : ℤ)).filter (PairFound T (ex L P) (ey L P))) ≤ P := by
        refine (card_filter_le _ _).trans ?_
        simp
      convert (by exact_mod_cast h1 :
        (#((Ico (0 : ℤ) (P : ℤ)).filter (PairFound T (ex L P) (ey L P))) : ℝ) ≤ P)
    have hJφ : 1 ≤ (J : ℝ) ^ 2 * markedFrac T ex ey L P := by
      have hJ0 : (0 : ℝ) ≤ (J : ℝ) ^ 2 := by positivity
      have h1 : (J : ℝ) ^ 2 * (1 / (2 * (2 + 64 * b) * s)) ≤
          (J : ℝ) ^ 2 * markedFrac T ex ey L P := mul_le_mul_of_nonneg_left hmarked hJ0
      have h2 : 1 ≤ (J : ℝ) ^ 2 * (1 / (2 * (2 + 64 * b) * s)) := by
        rw [mul_one_div, le_div_iff₀ hthr]
        linarith [h.J_ge]
      linarith
    exact grover_uniform h.grover n hφ0 hφ1 hJφ h.J_le

/-- **The mean success, label `A` in use.** For a solution of minimum support with fewer than half
zeros, that is `p < 1/2`. -/
theorem coin_mean_minimal {G : Primitives} {ε Λ : ℕ → ℝ} {n : ℕ} {ΩL : Finset (ι → Label)} {q : ℝ}
    {Ps : Finset ℕ} {B : ℤ} {δ U : ℝ} {T : ℕ} {b s : ℝ} {J : ℕ}
    (hmin : MinimalSolution D y) (hz : 2 * #({i | D i = 0} : Finset ι) < Fintype.card ι)
    (h : CoinHyp G ε Λ n ν D y ΩL q Ps B δ U T b s J)
    (ex : ∀ (L : ι → Label) (P : ℕ) (ρ : ℤ), Enum (binX L ν y P ρ))
    (ey : ∀ (L : ι → Label) (P : ℕ) (ρ : ℤ), Enum (binY L ν y P ρ)) :
    q * ((3 / 4) * (1 / 4 - ε n)) ≤ mean (ΩL ×ˢ (Ps ×ˢ range J))
      (fun x => G.groverSucc n (markedFrac T ex ey x.1 x.2.1) x.2.2) :=
  coin_mean hmin.dot_eq (fun _ hL => value_injOn hL hmin (card_free_lt_supp hz)) h ex ey

/-- **The mean success, empty label.** If `ν A 0 = 0` then `K = 1`, and neither minimality nor
`p < 1/2` is used: `D` only has to annihilate `y`. -/
theorem coin_mean_empty {G : Primitives} {ε Λ : ℕ → ℝ} {n : ℕ} {ΩL : Finset (ι → Label)} {q : ℝ}
    {Ps : Finset ℕ} {B : ℤ} {δ U : ℝ} {T : ℕ} {b s : ℝ} {J : ℕ}
    (hy : dot D y = 0) (h0 : ν .A 0 = 0)
    (h : CoinHyp G ε Λ n ν D y ΩL q Ps B δ U T b s J)
    (ex : ∀ (L : ι → Label) (P : ℕ) (ρ : ℤ), Enum (binX L ν y P ρ))
    (ey : ∀ (L : ι → Label) (P : ℕ) (ρ : ℤ), Enum (binY L ν y P ρ)) :
    q * ((3 / 4) * (1 / 4 - ε n)) ≤ mean (ΩL ×ˢ (Ps ×ˢ range J))
      (fun x => G.groverSucc n (markedFrac T ex ey x.1 x.2.1) x.2.2) :=
  coin_mean hy (fun _ hL => value_injOn_of_empty hL h0) h ex ey

end Fixed

/-- **The probability bound and the cost bound together.** For a family of instances with `CoinHyp`
at each `n`, the schedule `s = 2^{σ n}`, `P₀ = K s`, `T ≤ c (n + 1) U / P₀ + 1`,
`J ≤ √(c (n + 1) s) + 1`, and `ε n ≤ 1/8`, put `q' = q (3/32)`. Then `q'` is a lower bound on the mean
success over the coin, the amplification with parameter `q'` has total cost of exponent
`L = a / 2 + max (a₀ + σ, σ / 2 + (2/3)(u - a₀ - σ))`, and its success probability is at least `2/3`.

The theorem does not identify the procedure amplified in `totalCost` with the search of `coin_mean`,
which would need a circuit model. -/
theorem coin_cost {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] {G : Primitives}
    {π ε Λ : ℕ → ℝ} {ν : ℕ → Layout} {D y : ∀ n, ι n → ℤ} {ΩL : ∀ n, Finset (ι n → Label)}
    {q δ U b : ℕ → ℝ} {Ps : ℕ → Finset ℕ} {B : ℕ → ℤ} {T J : ℕ → ℕ} {a a₀ u σ c : ℝ}
    (hπ : IsPoly π) (hπ1 : ∀ n, 1 ≤ π n) (hTb : TableBuild G π Λ) (hUn : Unranking G π)
    (hCl : ClawWindows G π Λ) (hGr : GroverResidues G π Λ) (hAA : AmplitudeAmplification G π Λ)
    (hy : ∀ n, dot (D n) (y n) = 0)
    (hinj : ∀ n, ∀ L : ι n → Label, Good L (ν n) (D n) →
      Set.InjOn (fun p : (ι n → ℤ) × (ι n → ℤ) => dot p.1 (y n)) (reps L (ν n) (D n)))
    (hC : ∀ n : ℕ, CoinHyp G ε Λ n (ν n) (D n) (y n) (ΩL n) (q n) (Ps n) (B n) (δ n) (U n) (T n)
      (b n) ((2 : ℝ) ^ (σ * n)) (J n))
    (hε : ∀ n, ε n ≤ 1 / 8) (hq0 : ∀ n, 0 < q n) (hq1 : ∀ n, q n ≤ 1)
    (hσ : 0 ≤ σ) (hc : 0 ≤ c) (hTexp : 0 ≤ u - a₀ - σ)
    (hqe : SoftO (fun n => 1 / q n) a)
    (hKe : SoftO (fun n => (((ν n) .A 0).choose (ν n).f : ℝ)) a₀)
    (hKi : SoftO (fun n => 1 / (((ν n) .A 0).choose (ν n).f : ℝ)) (-a₀)) (hUe : SoftO U u)
    (hT : ∀ n : ℕ, (T n : ℝ) ≤ c * ((n : ℝ) + 1) * U n /
      (((ν n) .A 0).choose (ν n).f * (2 : ℝ) ^ (σ * n)) + 1)
    (hJ : ∀ n : ℕ, (J n : ℝ) ≤ √(c * ((n : ℝ) + 1) * (2 : ℝ) ^ (σ * n)) + 1) (hJ1 : ∀ n, 1 ≤ J n)
    (hPΛ : ∀ n : ℕ, 2 * (((ν n) .A 0).choose (ν n).f * (2 : ℝ) ^ (σ * n)) ≤ Λ n)
    (hTΛ : ∀ n, (T n : ℝ) ≤ Λ n) (hqΛ : ∀ n, 1 / (q n * (3 / 32)) ≤ Λ n)
    (ex : ∀ n (L : ι n → Label) (P : ℕ) (ρ : ℤ), Enum (binX L (ν n) (y n) P ρ))
    (ey : ∀ n (L : ι n → Label) (P : ℕ) (ρ : ℤ), Enum (binY L (ν n) (y n) P ρ)) :
    (∀ n, q n * (3 / 32) ≤ mean (ΩL n ×ˢ (Ps n ×ˢ range (J n)))
      (fun x => G.groverSucc n (markedFrac (T n) (ex n) (ey n) x.1 x.2.1) x.2.2)) ∧
    SoftO (fun n => totalCost G n (q n * (3 / 32))
        (2 * (((ν n) .A 0).choose (ν n).f * (2 : ℝ) ^ (σ * n))) (T n) (J n))
      (totalExp a u a₀ σ) ∧
    ∀ n c', 0 ≤ c' → (2 : ℝ) / 3 ≤ G.amplifySucc n (q n * (3 / 32)) c' := by
  have hq' : ∀ n, 0 < q n * (3 / 32) := fun n => mul_pos (hq0 n) (by norm_num)
  have hq'1 : ∀ n, q n * (3 / 32) ≤ 1 := fun n => by linarith [hq1 n, hq0 n]
  refine ⟨fun n => ?_, ?_, fun n c' hc' =>
    (hAA n _ c' (hq' n) (hq'1 n) (hqΛ n) hc').2⟩
  · have hm := coin_mean (hy n) (hinj n) (hC n) (ex n) (ey n)
    refine le_trans ?_ hm
    have h1 : (3 : ℝ) / 32 ≤ (3 / 4) * (1 / 4 - ε n) := by linarith [hε n]
    exact mul_le_mul_of_nonneg_left h1 (hq0 n).le
  · have hK1 : ∀ n, (1 : ℝ) ≤ (((ν n) .A 0).choose (ν n).f : ℝ) := fun n => by
      exact_mod_cast Nat.choose_pos (ν n).f_le
    have hU0 : ∀ n, 0 ≤ U n := fun n =>
      le_trans (by positivity) ((hC n).listX_le fun _ => .A)
    exact total_exponent hπ hπ1 hTb hUn hCl hGr hAA (K := fun n => (((ν n) .A 0).choose (ν n).f : ℝ))
      (T := fun n => (T n : ℝ)) (J := fun n => (J n : ℝ)) hK1 hU0 hσ hc hTexp hKe hKi hUe hT
      (fun n => by exact_mod_cast (hC n).T_pos) hJ (fun n => by exact_mod_cast hJ1 n) hq' hq'1
      (softO_inv_const (by norm_num) hq0 hqe) hPΛ hTΛ (fun n => (hC n).J_le) hqΛ

end EqualSubsetSum
