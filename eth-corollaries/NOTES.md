# Notes on the ETH claims and their corollaries

## Sources (both unrefereed, both Lean-formalized)
- **OpenAI**, "The Exponential Time Hypothesis is False" (17 Oct, rev. 25 Oct 2026). github.com/openai/math, family 378:
  `preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf`, Lean scope `lean/docs/378.md`.
- **Anthropic/Claude**, "A 2^{o(n)} Time Algorithm for 3-SAT", hexagon:2610.00577v1 (26 Oct 2026; pdf at hexagonmath.org/pdf/2610.00577v1).

## What is claimed
| | OpenAI | Anthropic |
|---|---|---|
| Problem | #k-SAT, every fixed k ≥ 2, deterministic, poly space | #k-SAT, one uniform machine for all k |
| Time (general) | (n+m)^{O_k(1)} · 2^{O_k(n loglog n/√log n)} | 2^{C·min{k² n loglog n/√log n, k m/√log m}}, C absolute |
| Time (m ≤ Dn) | 2^{O_{k,D}(n/√log n)} | 2^{O(k n/√log n)} |
| Lean proves | weaker exponent n(loglog n)²/√log n | both statements, TM2 model, std axioms only |
| Core tool | Boolean tensor-network contraction (Thm D.1): **s wires → 2^{O(s/√log s)}**; entries in (Z/2^P)[V]/(V^ℓ), ℓ,P ≤ Cs; node degree ≤ s^{0.9} | sum-product on clause graph; recursive merge/cut; edge "cost" decompositions via the **eight-square (octonion) identity** |
| Also | sparse F2 polynomial systems (Thm 2.2, ≤ polylog monomials each); local-function (Goldreich OWF) inversion; #PM / #IS / #q-col in 2^{o(v)}; E^NP ⊄ SIZE(c·n√log n) | Corollary 7 (counting; any number of edges): IS, Clique, VC, **Dominating Set** of size s in O(2^{δn}) |

Refuted: ETH, SETH, #ETH, Gap-ETH, NSETH (plus their randomized versions).
**Not** refuted: OV conjecture, the CNF-SAT hypothesis with poly(n) clauses of unbounded width, the k-Clique conjecture, the Set Cover conjecture, P≠NP.
Galactic: Anthropic reports no gain over 2^n until n > 10^10 (the n-bound) or n > 10^{10000} (m = 5n).

## Background

A refuted lower bound gives **no** algorithm by itself. A speedup for a problem needs a reduction *to* SAT or tensor
contraction with o(n·√log n / loglog n) variables or wires. A reduction with mild superlinear blowup, such as
n·(log n)^{0.49}, still yields 2^{o(n)}. Every problem in size-constrained SNP reduces this way (IPZ01, SERF-completeness).

What the claims give with known tools:
- **CNF-SAT of growing width and density.** Anthropic's uniform k² gives 2^{o(n)} for width k ≤ (log n)^{1/4−ε}. With the
  CIP06 width-reduction branching (leaves ≤ 2^{(n/w)·log(e(cw+1))}, c = m/n) this extends to clauses of any width when the
  density is mild (A1, A1′). Hitting Set and Set Splitting with that many sets reduce the same way.
- **Colorings with few colors.** ⌈log k⌉ bits per vertex give width 2⌈log k⌉ on n⌈log k⌉ variables, so 2^{o(n)} for
  k ≤ 2^{(log n)^{1/6−ε}} (A2, N5). The regime of large chromatic number stays at the 2^n of BHK.
- **Linear-kernel FPT problems in 2^{o(k)}·poly(n)**, e.g. Vertex Cover and Nonblocker (A3, A3′). This direction is
  equivalent to ¬ETH (Cai and Juedes).
- **Sparse partition functions and weighted #CSP**, via OpenAI's Thm D.1 with a generating variable V (ℓ ≤ Cs): the Ising
  density of states, integer-q Potts, the Tutte polynomial on the hyperbolas (x−1)(y−1) = q ∈ ℕ, the Max-Cut spectrum and
  exact discrete graphical-model inference on O(n)-edge graphs (A4, N3). These lie below the #ETH lower bounds of Dell et al.

Problems with global constraints (connectivity, orderings, permutations, large numbers, dense pairwise interaction) do not
reduce this way directly. Connectivity needs Cut & Count, which gives parities (A5a, N2, N7, N9), and for decisions an
isolation step. Isolation weights of size ~n² do not fit D.1, which allows only ℓ ≤ Cs, so the isolation used here is by
sparse parity checks (A5b, N2′).

Problems the claims do not reach directly:
- **Dense quadratic problems**: Max-Cut / Max-2-CSP (Williams 2^{ωn/3}, unchanged since 2004) and dense MQ over F2 (Dinur
  2^{0.694n}; relevant to UOV/MAYO). They have Θ(n²) pairwise wires, and Thm 2.2 handles only polylog-sparse equations.
- **Permanent / #PM in dense bipartite graphs.** Ryser's 2^n has only lower-order improvements (Bjö16). The natural
  encodings need v·log v bits, and at that size the √log savings are lost. The sparse case is OpenAI Cor 1.3.
- **CNF-SAT with poly(n) clauses in 2^{(1−ε)n}.** It would void the LMS18 treewidth-tightness bounds (IS 2^tw, DS 3^tw)
  and the bounds for unbounded Hitting Set and Set Splitting. It would not touch OVC.
- **Planar and geometric problems below 2^{O(√n)}**: planar IS / 3-Col / HC and Euclidean TSP in R². All the square-root
  lower bounds are ETH-based. This needs a *treewidth-sensitive* contraction, 2^{O(tw/√log tw)}; for general graphs the
  CNF-SAT hypothesis stands against it, for planar graphs it does not.
- **Subset Sum / Knapsack**: 2^{o(n)}, or T^{1−ε}·2^{o(n)} (the SETH-based ABHS19 bound no longer applies). The
  coefficients are huge, and D.1's measurements need bounded-coefficient linear forms.

Not affected (the barrier still stands): edit distance, LCS, Fréchet and other OV-based quadratic bounds (OVC); k-Clique in
n^{o(k)} (k-Clique conjecture); Set Cover in (2−ε)^n (Set Cover conjecture). No practical SAT speedups follow.

## Lean results (built on anthropics/formal-math@16a5ce4 `eth`, project `lean/`, std axioms only)
Check with `cd lean && lake build && lake env lean CheckAxioms.lean`.

### A2, colorings
`EthCor.colorings_uniform` (EthCor/ColorTM.lean): one TM counts the proper k-colorings of G for all 2 ≤ k ≤ n, input
`unary k ++ code G`, within c·2^{c·(2b)²·(nb)·r(nb)} steps, b = ⌈log₂k⌉, r(N) = lglg(N+4)/√lg(N+4).
`EthCor.colorings_subexp` (EthCor/ColorSubexp.lean): the same machine runs in 2^{εn} for every ε > 0 and 0 < θ < 1/6,
n ≥ n₀(θ, ε), lg k ≤ (lg n)^{1/6−θ}. Numbers: b ≤ 2(lg n)^{1/6−θ}, so (2b)²·nb ≤ 32·n·(lg n)^{1/2−3θ}, and
r(N) ≤ lg(N+4)^{a−1/2}/(a·ln 2) for any a > 0 (`rate_le_rpow`, a = θ); the exponent is O(n·(lg n)^{−2θ}) (`boundNK_le`).
Proof: binary color CNF (n·b+4 vars, width 2b) → Anthropic's compact-code machine, via `Wrap.everyMachineCanBeWrapped`.

### A1, any width, constant density
Width k = o((log n)^{1/4}/√loglog n) is already in Anthropic's remark after Thm D(b). The arbitrary-width part
(CIP06 branching + many machine calls) is what A1 and A1′ add.

`EthCor.CnfTM.cnf_counts` (EthCor/CnfTree.lean, CnfTM.lean): for every D and δ > 0, one TM counts the satisfying
assignments of any CNF φ on n variables with ≤ D·n clauses (any width, no repeated literal in a clause), input
`SatFree.enc φ`, within C·2^{δn} steps. Proof: literal (u,b) ↦ variable 2u / 2u+1 plus pair clauses, so every clause is
positive; Anthropic's Dominating-Set shortening tree (`stepD`) with a new invariant for M = D·n clauses (theirs needs
M ≤ n); their `SIZED` counter at the leaves; `walkSum`; `tm_of_stepped`. Mathematically this is CIP06 + ¬ETH (known
equivalence).

### A1′, growing density
`EthCor.GrowTM.cnf_grow` (EthCor/GrowTree.lean, GrowArith.lean, GrowTM.lean): ONE TM; for every δ > 0 there is n₀ such
that for every CNF φ on n ≥ n₀ variables with m ≤ n·2^{s} clauses, s = (lg n)^{1/4}/(lg lg n)² (any width, no repeated
literal), it outputs #SAT(φ) within ⌊2^{δn}⌋ steps. This density is above n·2^{(lg n)^{1/4−ε}} for every ε.
- Same tree, with the width read off the node (`stepW`); leaves counted by Anthropic's uniform compact-code machine
  (`MainTheoremCompact`), simulated as a stepped machine via `Wrap.sim`/`coding_exists` (space linear in time);
  `CountKSat.stHostW` for the final TM.
- Width w = 2^{⌊L/4⌋−⌊lg L⌋}+1 with ℓ = ⌊lg 2n⌋, L = ⌊lg ℓ⌋, q = ⌊lg L⌋ (`wN`), so (w−1)⁴·2^{4q} ≤ ℓ < 16(w−1)⁴·2^{4q}
  (`wN_bounds`, needs L ≥ 16), w²L² ≤ 16√ℓ and ℓ < 16(w−1)⁴L⁴ (`wN_facts`).
- Exponent ≤ 32C·N/L (`expN_le`); s ≤ 4(w−1)/(L−1) (`sN_le`); (2/w)lg(e·w·(D+2)) ≤ (2/w)(4 + 3√w + s) → 0 (`log_part`,
  `width_small`).
- Limit of the method: w = o((lg n)^{1/4}/√lglg n), i.e. density n·2^{o((lg n)^{1/4}/√lglg n)}. The stated density gives
  up a factor (lg lg n)^{3/2} for simpler arithmetic.

### A4, Max-SAT spectrum
`EthCor.Spectrum.maxsat_spectrum` (EthCor/Spectrum.lean): for every width r, density D, δ > 0, one TM, input
`unary t ++ SatFree.enc φ` (φ width ≤ r, ≤ D·n clauses, t ≤ m), outputs #{a : exactly t clauses true} in C·2^{δn}.
Proof: 2n+m variables (x_u on 2u, ¬x_u on 2u+1 via pairF, y_j ↔ C_j on 2n+j); satisfying assignments with n+t true
variables ↔ assignments with t satisfied clauses (`cntS_specF`, explicit bijection); Anthropic's `SIZED (r+2)`.
Covers the Max-Cut spectrum and the ±1 Ising density of states on O(n)-edge graphs (edge uv ↦ (u∨v),(¬u∨¬v);
#sat = |E| + cut); the graph-input forms go through N3 with q = 2 (`Special.maxcut_spectrum`, `Special.ising_spectrum`).

### A5a, ⊕Hamiltonian Cycle, bounded degree
`EthCor.HamTM.hc_parity_subexp` (EthCor/HamFormula.lean, HamTM.lean): for every Δ, one TM; for every ε > 0 there is n₀
such that for every graph G on n ≥ n₀ vertices with all degrees ≤ Δ, input `code G`, it outputs [#HC(G) is odd] within
⌊2^{εn}⌋ steps. #HC = `numHamCycles G` = #{H ≤ G spanning, connected, every degree 2}.
Proof (Cut & Count): CNF on m + n variables (edge bits x, side bits s; every vertex on exactly two chosen edges via
atMost2/atLeast2 clauses, chosen edges inside one side, s₀ false); #SAT = Σ over 2-factors x of #side maps (`cntN_hcF`);
the side maps number 2^{cc−1}, odd iff connected (`parity_sides`, flip s on a component missing 0); edge choices ↔ H ≤ G
(`card_hc`); so #SAT ≡ #HC mod 2 (`hc_parity`). Low bit of Anthropic's compact-code count, width Δ + 3 (`hc_parity_tm`,
bound c·2^{c(Δ+3)²·N·r(N)}, N = m + n ≤ (Δ+1)n, `boundH_le`).

### A5a′, ⊕HC, sparse, any degree
`EthCor.HamSTM.hc_parity_sparse` (EthCor/HamCounter.lean, HamSparseTM.lean): ONE TM; for every θ, ε > 0 there is n₀ such
that for every G on n ≥ n₀ vertices with |E(G)| ≤ n·(lg n)^{1/2−θ} it outputs [#HC(G) odd] within ⌊2^{εn}⌋ steps.
Corollary `hc_parity_bounded`: one TM for all Δ (A5a has one per Δ).
- Proof: `hcS` replaces atMost2/atLeast2 by a sequential counter. Bits m+n+4e+2b (+1) = "≥1 (≥2) of the edges at end b
  of e, up to e, chosen"; the start counter is the pair z = 5m+n, z+1 forced false. Steps: c = p ∨ x,
  c+1 = (p+1) ∨ (x ∧ p), ¬(p+1 ∧ x), final c_d+1 (`stepC`, `cntC`, `sat_cntC` by induction on the list). The bits are
  determined (`auxOK_iff` on the sorted incidence list, `aux_iff`), so cntN(5m+n+2, hcS) = cntN(m+n, hcF) (`cntN_hcS`,
  via Fin.appendEquiv and card_nbij'). Width 3 → `hcS_tm` with bound c·2^{9c·N·r(N)}, N = 5m+n+2; `boundS_le`
  (rate_le_rpow with a = θ/2) gives 2^{εn} for N ≤ 8n·(lg n)^{1/2−θ}. `length_edges_le_card`: the edge list injects
  into G.edgeFinset (Sym2).
- `hc_parity_little_o` (`lean/EthCor/HamLittleO.lean`): the machine of `hcS_tm`, for every g with g(n)·r(n) → 0,
  r(n) = `SatK.rN 1 (1/2) n` = lglg(n+4)/√lg(n+4), and every ε > 0: n₀ with 2^{εn} steps on graphs with |E| ≤ n·g(n).
- `rate_three`: n ≤ N, N + 4 ≤ (n+4)³ → r(N) ≤ 3·r(n) (lg(N+4) ≤ 3 lg(n+4), lg 3 ≤ 2, lglg(n+4) ≥ 1).
  `rate_tendsto` from `rate_le_rpow (1/4)`. `boundO_le`: c·2^{9c·N·r(N)} ≤ 2^{εn} for N ≤ 5n·g(n) + n + 2, via
  N·r(N) ≤ 18ηn + 6η, η = ε/(4(162c + 1)).
- Limit of the method: m = o(n·√lg n/lglg n).

### A5b (N1), deciding HC on sparse graphs with one-sided error
Why sparse checks: Cut & Count decides only with isolation. MVV weights (≤ 2m per edge) blow the variables up to ~m²,
and the cntS "exactly t true" trick only carries O(n) total weight. Dense Valiant–Vazirani XORs need ~n·m auxiliary
variables. CIKP08 sparse-hash isolation (k-sparse XORs, no new variables, success ≥ 2^{−εn}) fits, stated as
"∃ M on (G, seed): no HC ⇒ 0 for all seeds; HC ⇒ 1 for ≥ 2^{−εn} of the seeds". Deterministically, "¬ETH ⇒ HC in
2^{o(n)}" is not known (HC is not known to be SERF-reducible to SAT).

**Isolation for arbitrary sets.** The proof of [CIKP08] Lemma 3 (ECCC TR06-062 / JCSS 74(3)) uses only that S ⊆ {0,1}^M
is nonempty: Step I (k′-sparse hyperplanes, semi-isolated solutions, Hamming-ball count) and Step II (fix the coordinates
where the two furthest surviving solutions differ) never use that S is the solution set of a k-CNF; the k-CNF only makes
the output a k′-CNF. So it isolates an element of ANY nonempty S with probability 2^{−O(h(ε))M}, using O(M) XORs of
width k′ = O(ε⁻¹ ln ε⁻¹).

Version for Lean (all probabilities = counts over a product Fintype Ω; parameters t, k, mm, r = ⌈M/t⌉):
- Row = (Fin k → Fin M) × (Fin k → Bool): indices J (with repetition), coefficients C; rv ρ x = Σ_l [C_l ∧ x(J_l)] ∈ ZMod 2.
  rv x + rv y = rv (x xor y). For |z| = w: #{ρ : rv ρ z = 0} = 2^{k−1}(M^k + (M−w)^k) (flip C at the first hit index:
  involution), so Pr ≤ q := (1 + (1 − r/M)^k)/2 when w ≥ r.
- ω = (m ∈ Fin (mm+1), rows : Fin mm → Row, B : Fin mm → Bool, U : Fin M → Fin t, V : Fin M → Bool).
  H(ω) = {x : rv(row_i) x = B_i for i < m, and x_j = V_j wherever U_j = 0}.
- Step I. x ∈ S′(rows) iff no y ∈ S with dist(x,y) ≥ r agrees with x on rows < m. Union bound: #{rows : x ∉ S′} ≤ |S| q^m
  |Row|^{mm}. Take m minimal with |S| q^m ≤ 1/2 (m ≥ 1, m ≤ mm = 3M+3 as q ≤ 3/4); then |S|2^{−m} ≥ (1+η)^{−mm}/4,
  η = (1 − r/M)^k ≤ e^{−kr/M}. Σ_{x∈S} #{(rows,B) : x ∈ S′, rows(x) = B} ≥ |S|·½·|Row|^{mm}·2^{mm−m}; for fixed (rows,B)
  the semi-isolated x with rows(x)=B lie in one ball of radius r−1, volume V ≤ (eM/(r−1))^{r−1} (Σ_{i≤R} C(M,i)(R/M)^R ≤
  (1+R/M)^M ≤ e^R). So #{(rows,B) : T := S ∩ {rows = B} has a semi-isolated point} ≥ |S|2^{−m}|Row|^{mm}2^{mm}/(2V);
  such T is nonempty with diameter < 2r.
- Step II. u, ū ∈ T furthest apart, C = diff(u, ū), |C| < 2r. If U_j = 0 for j ∈ C and V_j = u_j wherever U_j = 0,
  then S ∩ H(ω) = {u} (w ≠ u agreeing with u on C has dist(w, ū) = |C| + dist(w,u) > |C|). Per coordinate: j ∈ C:
  1 of 2t choices; j ∉ C: 2t−1 of 2t. Fraction ≥ (2t)^{−2r}(1 − 1/(2t))^M.
- Total: Pr[|S ∩ H(ω)| = 1] ≥ 1/(mm+1) · e^{−η·mm}/(8V) · (2t)^{−2r}(1−1/(2t))^M = 2^{−(O(lg t / t) + O(e^{−k/t}))M}.
  With k = t², width t², this is 2^{−δM} for t = t(δ).
- Use: S = Hamiltonian cycles of G as edge sets (M = m edges). Cut & Count with the extra edge clauses: #SAT ≡ |S ∩ H(ω)|
  (mod 2). An XOR row is a CNF on the same variables: one clause per violating σ ∈ {0,1}^k (inconsistent σ give
  tautologies). Width max(3, t²), N = 5m + n + 2 variables. No HC ⇒ output 0 for every ω; HC ⇒ output 1 for ≥ 2^{−δm}
  of the ω. For m ≤ D·n: one-sided-error HC decision in 2^{δn}·2^{o(n)} for every δ.

**The isolation lemma in Lean**: `lean/EthCor/Isolation.lean` (pure counting) and `lean/EthCor/IsoBound.lean`
(parameters). Main theorems:
- `Iso.iso_count`: exact counting form, for every nonempty S and all r, mm, t;
- `Iso.iso_real`: explicit bound with r = ⌊M/a⌋+1, k = ab, mm = 3M+3;
- `Iso.isolation`: ∀ δ > 0, ∃ k t M₀, ∀ M ≥ M₀, ∀ S ≠ ∅: |Ω| ≤ 2^{δM}·#{ω : |S ∩ H ω| = 1}.

**Checks as clauses**: `lean/EthCor/HamIso.lean`. A row's support is {j : Σ_{l : J l = j} C l odd}, of size ≤ k, so the
row is 2^{|T|−1} clauses of width |T| on the edge variables. The reduction uses Tseitin chains instead of these 2^{k−1}
clauses per check: width stays 3 and the variable count is 5m+n+2+(3m+3)k, linear for fixed k. The fixings become unit
clauses. Main results: `HamI.iso_parity` (#SAT(hcI) ≡ |hcSet G ∩ H ω| mod 2) and `HamI.iso_decide` (the
one-sided-error statement, for every δ).

**The machine**: `lean/EthCor/HamIsoTM.lean`. Input `code G ++ seedBits`. The graph reader only looks at the first n²
matrix bits. The machine reads k, so one machine works for all δ.
- `seedCode ω` = unary W followed by `seedNums ω` in W-bit blocks 1^v 0^{W−v}, with W = M + k + mm + 1. The numbers are:
  the header k, m₁, mm, M; for each check, (j_l, c_l) for l < k, then the right-hand side; for each coordinate, "is
  fixed" as 0/1, then the bit.
- `decode_seedCode` reads k, m₁, mm, M, `rowsOf ω` and `fixesOf ω` back. `edges_append`: the edge list ignores whatever
  follows the matrix.
- `hcI_tm`: one machine, for every n ≥ 4, k ≥ 1, mm ≥ 1 and seed. It outputs the parity of #SAT(hcI) within
  c·2^{9c·N·r(N)}, where N = NI. The input stays within 1000·(N+2)³ because W ≤ 3(N+2).
- `ham_randomized`: ∀ D δ ε, ∃ k t n₀. For m ≤ D·n, out(ω) runs within 2^{εn} steps, is 0 for every seed when G has no
  Hamiltonian cycle, and |Seed| ≤ 2^{δn}·#{ω : out ω} when G has one. It uses iso_decide with δ/(D+1) and boundS_le with
  θ = 1/4; N ≤ A·n with A = 9Dk + 9k + 9D + 9, and A ≤ (lg n)^{1/4} for n ≥ 2^{A⁴}.

### numHamCycles and Mathlib
`lean/EthCor/HamMathlib.lean`.
- `numHamCycles_pos_iff` (n ≠ 1): 0 < numHamCycles G ⟺ G.IsHamiltonian (Mathlib). The ⇒ direction uses
  `IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp`: a connected 2-regular H is one cycle through all
  vertices (`exists_cycle_of_two`), then map it into G by `Hom.ofLE`. The ⇐ direction takes `p.toSubgraph.spanningCoe`
  (`two_of_cycle`).
- `numHamCycles_eq`: numHamCycles G = #{edge sets of walks p with p.IsHamiltonianCycle}, by `card_bij` with
  H ↦ H.edgeFinset (injective by `edgeFinset_inj`).
- `ham_randomized_mathlib`: A5b with ¬G.IsHamiltonian / G.IsHamiltonian in place of the count (n₀ + 2 so that n ≠ 1).

### Amplification
`lean/EthCor/Amplify.lean`.
- `amplify`: |Ω|·p ≤ #{out = 1} → #{w : Fin R → Ω | ∀ i, out (w i) = 0} ≤ |Ω|^R·e^{−pR} (piFinset,
  #{out = 0} ≤ (1 − p)|Ω| ≤ e^{−p}|Ω|). `amplify_sq`: R ≥ 2^{2δx} → ≤ |Ω|^R·e^{−2^{δx}}.
- `ham_amplified`, `conn_amplified`: the machines of A5b and N2′ with these bounds for R-tuples of seeds. The amplified
  algorithm is R runs of the same machine; no single TM looping over the seeds is built (A5b's machine is Anthropic's
  TM2 counter inside `Wrap.everyMachineCanBeWrapped`, which has no loop combinator).

### N2, parity of connected solutions
`lean/EthCor/ConnFormula.lean` and `ConnTM.lean`. The formula is `connF n E ψ` on 3n variables (x_v, s_v, s̄_v): ψ, plus
s̄ = ¬s, plus s_v → x_v, plus s_u = s_v on the edges inside X (width 4).
- `cnt_stepA`, `cnt_stepB` (with any vertex property P): cntS(3n, n+ℓ) = Σ_{X ⊨ ψ, P X, |X| = ℓ} sig(X), where
  sig(X) = 2^{cc(G[X])}.
- `sig_parity`: sig(X) is even, and sig(X)/2 is odd ⟺ G[X] is connected. This is `parity_root` (the flip argument with
  root r ∈ X) together with `card_sides_two`.
- `conn_parity`: cntS/2 ≡ numConnF (mod 2) for ℓ ≥ 1.
- Machines: SIZED (r+4) with target n+ℓ, then postC keeps bit 1. `conn_parity_tm` (input code G ++ unary ℓ ++
  SatFree.enc φ, width ≤ r, ≤ (n+2)^D clauses) runs in C·2^{δn}, and so does `cvc_parity_tm` (input code G ++ unary ℓ,
  φ = the edges). Any density, since there are 3n variables.

### N2′, Steiner tree and connected vertex cover with one-sided error
`lean/EthCor/ConnIso.lean` and `ConnIsoTM.lean`. Isolation on the n vertex bits; each Tseitin chain bit gets a complement
bit, so the count of true variables stays fixed.
- The formula is `ciF` = connF ++ [z = 3n false] ++ isoF(z, 3n+1, k, …) ++ compF(3n+1, mm·k), where compF makes bit
  3n+1+A+i the complement of chain bit 3n+1+i. It has 3n+1+2·mm·k variables and target n+ℓ+mm·k.
- Steps: `stepC` (complements), `stepD` (chains, via `sat_isoF_iff` with N₀ = 3n+1), `stepE` (z), then `conn_parity_P`
  with P = H ω. This gives `ci_parity`, and with Iso.isolation on the connected solutions also `ci_decide`.
- The input is `codeCI G ℓ ω φ` = code G ++ unary ℓ ++ unary |seedCode ω| ++ seedCode ω ++ enc φ. readFree ignores
  trailing bits, but the seed must come before φ, hence the length prefix.
- `conn_randomized`: ∀ r D δ ε, ∃ k t n₀ M C. The machine runs within C·2^{εn}; the bit is 0 for every seed when no
  solution exists, and |Seed| ≤ 2^{δn}·#{ω : out ω} when one does. SIZED(r+4) with δ' = ε/(2(12k+4)) works because
  N ≤ (12k+4)n.

### N3, Potts and Tutte
`lean/EthCor/Potts.lean` and `PottsTM.lean`.
- Definitions: `mono G σ` (monochromatic edges), `pottsSpec G q j`, `comps A` (components of (Fin n, A)), `fk`, `tutte`
  (rank-generating form with integer exponents, in a field).
- `card_const`: colorings constant on the components of A = q^{k(A)} (via ConnectedComponent.lift).
  `potts_fk`: Σ_j N_j (1+v)^j = Σ_{A ⊆ E} q^{k(A)} v^{|A|} in any commutative ring (prod_add).
  `tutte_hyperbola`: (x−1)^{k(E)} (y−1)^n T(G;x,y) = Σ_j N_j y^j when (x−1)(y−1) = q, x, y ≠ 1.
- Formula `pottsF n q E` on nq + m variables, width q + 3; `cnt_pottsF`: cntS(nq+m, n+j) = colorings with j
  monochromatic list edges; `mE_eq` matches list edges with G.edgeFinset (also gives |E(G)| ≤ length of the edge list,
  `card_le_length`).
- `potts_spectrum q D hq hδ`: input code G ++ unary j, output bits of N_j, C·2^{δn}, |E| ≤ D·n. `tutte_tm` packages it
  with `tutte_hyperbola`. q must be constant (SIZED has fixed width).

### A3, Vertex Cover
`lean/EthCor/VcTree.lean` and `VcTM.lean`.
- Node (k, E). `stepV d`: if k > 0 and some endpoint v has ≥ d distinct neighbours (`nbs`, deduped filterMap), branch
  into (k−1, E∖v) and (k−|N(v)|, E∖N[v]); if |N(v)| > k the second child is (0, E). `good_step`: Good x ↔ Good l ∨
  Good h (no nodup or loop assumptions needed).
- Tree bound via Anthropic's `length_leaves_le` with Inv: p = a + b, t = d·b, a + t ≤ k + d, x.1 ≠ 0 → x.1 + a + t ≤ k.
  Leaves ≤ Σ_{j ≤ (k+d)/d} C(k+d, j) ≤ 2^{ε(k+d)} (`sum_choose_le_two_rpow` with k=1, L=1, τ=d).
- Leaf: |V| ≤ k·d for a good leaf (`card_V_le`), else dead formula [[]] on 0 variables. `leafV` renames V by idxOf,
  s = min(k, |V|); `cnt_leafV_pos`: 0 < cntS ↔ Good.
- `tm_fpt`: host with time ⌊C·(sz+2)^C·2^{δ·par}⌋ from `stHostW` (states poly in n, steps c·2^{δ·par}).
- `vc_fpt`: ∀ ε > 0, one machine on code G ++ unary k (k ≤ n) decides VC ≤ k within C(n+2)^C 2^{εk}. d from
  `exists_width 1` at ε/4; SIZED width 2 at δ = ε/(4d).

### N5, homomorphisms G → H
`lean/EthCor/HomFormula.lean` and `HomTM.lean`. H is a relation on Fin h given in the input (generalizes A2).
- `hmat H` (h² entries, row by row), `numHom G H` = #{f : Fin n → Fin h | ∀ u v, G.Adj u v → H (f u) (f v)}.
- `homB h n mH m`: the invalid-code clauses, tautologies and padding of `colB`; the edge clauses are
  forbid(u, a) ++ forbid(v, c) for every edge (u, v) of G and every (a, c) with H(a, c) = false.
  `cntN_homB`: cntN (n·nb h + 4) = numHom (reuses `colOf`, `asgB`, `sat_forbid` from A2).
- `numHom_simple`: numHom with H.Adj = Nat.card (G →g H); `numColorings_eq`: numColorings G k = numHom G (≠).
- `hom_uniform`: input unary h ++ hmat H ++ code G, bound boundNK c (2 nb h) (n nb h), 2 ≤ h ≤ n (≤ n²h² + O(nh)
  clauses, so polynomial parts of degree 7 instead of 6). `hom_subexp`: 2^{εn} for lg h ≤ (lg n)^{1/6−θ}, via
  `boundNK_le`. `hom_subexp_graph`: same with Mathlib's G →g H.
- Generic helpers `allOccur_gen`, `two_le_length_gen`, `isKCNF_gen` (any formula with a list of facts).

### A3′, Nonblocker
`lean/EthCor/Nonblocker.lean` and `NonblockerTM.lean`.
- `ore`: no isolated vertices → ∃ dominating D, 2|D| ≤ n (minimum D; `compl_dominating`: univ \ D dominates, else
  D.erase v would).
- `niL n m` (vertices with a neighbour, by List.any on the matrix), `emb`, `core G = G.comap emb`,
  `matrix_core : matrix (core G) = subM n (matrix G) (niL ..)` (via `List.map_getElem_finRange`).
- `nb_iff`: ∃ D dom, |D| + k ≤ n ↔ same for core G and n′ (isolated vertices ⊆ every D; `card_iso_add`:
  #isolated + n′ = n). `nb_answer`: ↔ 2k ≤ n′ ∨ (k ≤ n′ ∧ 0 < numDominatingSets (core G) (n′ − k)).
- Machine `nbM = mapOut (mapIn preN DOMcount) postN`: preN writes codeWith ⊥₀ 0 (count 1), codeWith ⊥₁ 0 (count 0) or
  codeWith (core G) (n′−k); DOMcount from `stDominatingCounted (ε/2)`; time c·2^{(ε/2)N′} with N′ ≤ 2k in every case.
  `nb_fpt` via `VcTM.tm_fpt` with A = e = c + 2.
- Lean note: the generic lemmas `dec2_polyT`, `declt_polyT` over opaque f, g avoid a fun_prop timeout on
  `decide (2 * kX x ≤ (jX x).length)` (whnf of the defs).

### N6, the 0/1 permanent
`lean/EthCor/Perm.lean` and `PermTM.lean`.
- `ents n mA` = (pairs n).filter adjB (the ones, row by row; nodup), `clash` (same row or column), `permF E` =
  [(a,false),(b,false)] for a < b < |E| with clash E[a] E[b] (width 2, ≤ m² clauses).
- `cntS_permF`: cntS m n (permF E) = #{σ : Perm (Fin n) | ∀ i, A (σ i) i} by card_bij with
  `asg σ t = decide (row t = σ (col t))`; surjectivity via `surj_on_of_inj_on_of_card_le` (the column map is injective on
  the chosen entries and there are n of them) and Equiv.ofBijective of j ↦ row (t_j). `permanent_eq`: Mathlib's
  permanent of the 0/1 ℕ-matrix = that card (prod_boole). `length_ents`: m = #{(i,j) | A i j}.
- `perm_fpt`: input unary n ++ hmat A; `leafP` gives SIZED (m vars, s = n, permF) or the dead formula ([], 0, [[]]) if
  m < n (then the permanent is 0, `cntS_zero_of_lt`). Time C(n+2)^C 2^{εm}.
- [10] Thm 1.3 (arXiv 1206.1775): under #ETH, Perm^{0,1} not in exp(o(m/log n)), Perm^{-1,0,1} not in exp(o(m)). So N6
  is the matching upper bound up to the log, given the claimed refutation.

### N6′, the {−1, 0, 1} permanent
`lean/EthCor/SignedPerm.lean` and `SignedPermTM.lean`.
- `chainF m g b` = [z false] ++ xorC (m+1+k) (m+k) (g k) ++ compC (m+1+k) (m+1+r+k) ++ [p_{r−1} = b], z = x_m;
  `sF E g b = permF E ++ chainF |E| g b` on m + 1 + 2r variables, width 3. `negs n mS E`: indices t < |E| with S at E[t].
- `chain_det` (chain bits determined by the choice), `chainVal_eq` (p_k = parity of the first k + 1 −1 entries),
  `card_true_split`; `cnt_sF` generic in E, g; `cnt_sperm`: cntS (m+1+2r) (n+r) (sF ..) = numPar A Sg b via `card_asg`
  with Q = parity. `permanent_signed`: Mathlib's ℤ-permanent = numPar false − numPar true (each σ contributes
  (−1)^{#(−1 entries)}).
- `sperm_fpt`: input b :: (unary n ++ hmat A ++ hmat Sg); `leafS`; SIZED_counts 3 at ε/3, N ≤ 3m + 1, so
  T ≤ c·2^{ε/3}·2^{εm}; dead formula if m < n (numPar = 0 since the σ along A are cntS m n permF = 0).
- Lean note: `leafS_polyT` is split into `nS_unary`, `ES_polyT`, `gS_polyT`, `sFS_polyT`, `leafS_then_polyT`, with
  `nS_unary.poly` in context before `fun_prop`, so that fun_prop does not unfold `nS`.
- [10] Thm 1.3(i): under #ETH no exp(o(m)) for {−1, 0, 1}; N6′ is the matching upper bound.

### Special cases
`lean/EthCor/Special.lean`.
- `numHom_hInd`: hom(G, hInd) = #{S | G.IsIndepSet S} (hInd false only at (1,1)); `indep_subexp` from `hom_subexp` at
  h = 2, θ = 1/12 (lg 2 = 1 ≤ (lg n)^{1/12} for n ≥ 2).
- `cutSize`, `ind S`, `diag_iff_not_cut`, `cut_add_mono` (cut + mono = m); `pottsSpec_two`: N_j for q = 2
  = #{S | cut S + j = m}; `maxcut_spectrum` from `potts_spectrum 2 D`. `spin`, `spinProd` (Sym2.lift), `isingSum`;
  `isingSum_eq`: Σ s_u s_v = 2·mono − m; `ising_spectrum`.
- `pottsSpec_zero`: N₀ = Anthropic's `numColorings` = Nat.card (G.Coloring (Fin q)); `chromatic_tutte` (x = 1−q, y = 0
  in ℚ), `flow_tutte` (x = 0, y = 1−q). Flow polynomial = ±T(0, 1−q) is Tutte's theorem, cited, not formalized.
- Lean notes: `tutte` clashes with `SimpleGraph.tutte` (write `Potts.tutte`, and ascribe ℚ to the arguments);
  `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`, `Sym2.map_pair_eq` → `Sym2.map_mk`.

### Python reference implementations and agreement with Lean
`python/ethcor/`, one module per result, all front ends clause for clause as in Lean, counters replaced by an exact DPLL
weight-enumerator counter; tests against brute force (`cd python && python3 -m pytest -q`). Not mirrored: the compact
code `encK` handed to the Main Theorem's machine (Python passes the formula itself).

`lean/Dump.lean` reads `name arg bits` lines and prints the Lean front end's output as JSON;
`python/tests/test_lean_agreement.py` sends random words in one `lake env lean --run Dump.lean` call and compares clause
for clause.

### Related work
- Tulsyan, github.com/xennygrimmato/eth-hamiltonicity (repo created 27 Oct 22:13 UTC): Lean
  `EthFollowup.ExactHC.theorem1` (exact #HC, |E| ≤ Dn, C·2^{δn}) and `theorem2` (one TM, C·2^{C(m+n)/√lg(n+2)}), via
  Anthropic's network machinery + matrix-tree identity. Supersedes A5a, A5a′, A5b. Both build on Anthropic rev 16a5ce4
  (Lean v4.33.1) and `#print axioms` of `theorem1` and `theorem2` gives [propext, Classical.choice, Quot.sound].
  `hamCycles G` = 2-regular spanning edge sets of G that are connected, the same as our `numHamCycles`.
- The same repository also has, in Lean: sparse TSP `EthFollowup.ExactHC.theoremTSP`, `theoremTSP_decode` (|E| ≤ Dn,
  weights ≤ W, 2^{δn}·poly(W)); exact #HC in 2^{O(n log d̄/√log n)} for average degree d̄ = 2^{o(√lg n)} (`theorem3`,
  `theorem3_maxdeg`), beyond the A5a′ range; HC decision, search and Hamiltonian paths at the TM level; exact directed HC
  and ATSP; exact quantum circuit amplitudes (`amplitude_TM*`).
- Stated there as conjectures or claims, not in Lean: a sketch of deterministic Steiner tree, FVS, connected VC /
  connected DS (decision and minimum only) and k-leaf out-branchings on |E| ≤ Dn with bounded degree or hubs, conditional
  on Anthropic's paper lemmas and checked numerically on ≤ 7 vertices (exact counts of CVC/CDS are listed as open there);
  exact induced-forest counts (exact min FVS and #min FVS) for |E| = O(n) via a "2−deg mass" determinant identity,
  checked numerically; connected OCT; a Tutte-plane note (the engine reaches the integer hyperbolas and y = 1 on sparse
  graphs; an n log n cut-rank barrier elsewhere, informal). N2, N2′, N7, N7′ hold on any density.
- Informal notes there: dense-permanent barriers (Θ(n log n) shared bits), k-dependence of #k-SAT (Theorem S),
  crossover estimates (Anthropic's Lean algorithm beats 2^n from n ≈ 2^{552 000}). These point the same way as the
  Cut & Count barrier below.
- Other repositories that pin anthropics/formal-math: cert-machine (certifies the ETH bridge), glitnir-notebooks (ETH
  walkthrough), apsp-bound, ImprovedExponents. To our knowledge none of them has corollaries of this kind.
- OpenAI Cor. 1.3 (#indep. sets, #q-colorings fixed q, #perfect matchings in 2^{o(v+e)}: covers N6); Anthropic Cor. 7
  (sized counts of indep. sets, cliques, VCs, dominating sets; fixed-k colorings).
- Decision forms known: A1 (CIP06; Calabro thesis Lemma 10.12), A4 maximum (JLSU14 Thm 8), A3 (IPZ01 Thm 5 + kernel),
  A3′ (Ganian–de Haan–Kanj–Szeider MFCS 2016).
- New to our knowledge: A1′, A2 growing k, N5, A4 spectrum, N3, N6′, N2, N2′, N7, N7′, N7″, N8, N8′, N8″, N9, N9′.
  Connectivity was open in this direction (IPZ01: HC only SNP-hard; Ganian et al.: FVS → 3-SAT open).

### N7, N7′, connected dominating set on graphs of any density
`lean/EthCor/CdsTree.lean`, `CdsTM.lean`, `CdsIsoTM.lean`. To our knowledge no 2^{o(n)} algorithm for CDS on dense graphs
was known; Tulsyan's repository lists dominating set (dense) as not covered and CDS only for sparse graphs. Under ETH, CDS
has no 2^{o(n)} algorithm on intersection graphs of convex objects (de Berg, Kisfaludi-Bak, arXiv:2601.08425).
- The point: N2 needs φ of bounded width r, but the n domination clauses N[v] have unbounded width.
- `CdsTree.rootN N s n m F`: root with N variables, target s, the n clauses `nbhd n m` open, and any closed F.
  `InvC N s W R P`: Anthropic's `Inv` with the open variables bounded by R = n (not by N = 3n) and closed width W = w + 4.
  `shortensN`: depth 2n, ≤ 2^{εn} leaves via `sum_choose_le_two_rpow` with k = L = 2, leaves of width ≤ w + 4 with
  ≤ |F| + 3n clauses, the count identity `cntS N s (domF ++ F) = Σ leaves`, and a stack bound.
- `CdsTM.cds_parity_tm`: walkSum (stepD w) from `rootC` = rootN (3n) (n+ℓ) n (mH x) (sideF ++ edgeCC), `SIZED (w+4)` at
  δ/12 on 3n variables, `postC`. `hcf`: domF ++ sideF ++ edgeCC = connF n E domF, then `conn_parity`. `numCDS` via
  Anthropic's `Sets.sat_domF`.
- `CdsITM.cds_randomized`: root `rootR` with closed `formD` = ciF for ψ = []; `ci_decide` with ψ = domF. `cds_amplified`
  via `Amplify.amplify`, `amplify_sq`.
- Python `ethcor/cds.py`, `tests/test_cds.py`; Dump.lean `cds`, `cdr` (leaves of stepD from rootC, rootR).
- Corollary (classical): for connected G with n ≥ 3, γ_c(G) = n − maxleaf(G) (Caro, West, Yuster 2000), and supersets of
  a CDS are CDS, so N7′ also decides Max Leaf Spanning Tree. Formalized as N7″.

### N7″, Max Leaf Spanning Tree and minimum CDS
`lean/EthCor/LeafTree.lean`, `MaxLeafTM.lean`.
- `Leaf.IsCDS G X` (Finset, `G.induce X` connected), `Leaf.leaves T` = degree-1 vertices.
- `cds_of_tree`: n ≥ 3, T ≤ G tree ⇒ the non-leaves are a CDS (`two_le_degree`: inner vertices of a path have degree
  ≥ 2; `induce_connected_of_patches` with the tree paths).
- `tree_of_cds`: n ≥ 2, X a CDS ⇒ ∃ tree T ≤ G with Xᶜ ⊆ leaves T. H = G[X] edges plus one edge v–f(v) for every v ∉ X
  (`fromRel`); H is connected; take `Connected.exists_isTree_le`; every v ∉ X has H-degree 1.
- `cds_grow`, `cds_le_iff`: a CDS with |X| < ℓ ≤ n gets a vertex outside with a neighbour in X
  (`induce_union_connected`, `induce_pair_connected_of_adj`).
- `leaf_iff`: n ≥ 3, 1 ≤ L < n: (∃ tree T ≤ G with ≥ L leaves) ↔ ∃ CDS of size n − L.
- `MaxLeafTM.numCDS_pos_iff` (numCDS over Bool vectors ↔ Finset CDS), `mincds_randomized`, `maxleaf_randomized`
  (n₀ := max n₀ 3, ℓ = n − L): direct from `cds_randomized`.
- No connectivity test needed: a disconnected G has neither a spanning tree nor a CDS.
- Python `cds.maxleaf_randomized`, `mincds_randomized`; `tests/test_maxleaf.py` (leaf_iff and cds_le_iff against all
  spanning trees on ≤ 7 vertices, one-sided error).

### N8, N8′, positive CNF of any width on graphs of any density
`lean/EthCor/PosConnTM.lean`, generalized tree in `CdsTree.lean`.
- `CdsTree.InvP N s W M R P`: open clauses ≤ M (= D·n), their variables ≤ R (= n), separately (as `CnfTree.Inv2`).
  `invP_root` for any open O (Nodup, vars < R, |O| ≤ M). `shortensN` goes through InvP with M = R = n.
  `shortensP D w`: depth (D+1)·n, ≤ 2^{εn} leaves via `sum_choose_le_two_rpow` with k = 2, L = D + 2, leaves of width
  ≤ W with ≤ |F| + (2D+1)·n clauses, count identity, stack bound.
- `PosTM.opens ψ` = variables of each clause, dedup; `cntS_opens` (positive clause ≡ clause of its vars).
  `rootP x = ((rootC x).1, (opens (fC x), (rootC x).2.2))`, `rootQ` likewise from `rootR`/`fR`, so PolyT comes from
  `rootC_polyT`/`rootR_polyT` projections. Input `code G ++ unary ℓ ++ SatFree.enc φ` (parity) and `codeCI G ℓ ω φ`
  (randomized); clause length ≤ n needed for the input-length bound.
- `pos_parity_tm D`, `pos_randomized D`: copies of cds_parity_tm / cds_randomized with depth (D+1)·n and node bound S·X²
  (S = 2D+9, resp. 24k+16+2D+1). Special cases: Group Steiner tree (≤ D·n groups), connected hitting set, connected
  total domination (open neighbourhoods; isolated vertex = empty clause, count 0). Red-blue domination is outside this
  form: X ⊆ red needs negative unit clauses.
- Python `cds.opens`, `rootP`, `rootQ`, `pos_parity`, `pos_randomized`; `tests/test_pos.py`; Dump `pos`, `posr`.

### N8″, minimum Steiner tree / connected vertex cover / Group Steiner tree
`lean/EthCor/MinConnTM.lean`.
- `MinTM.conn_grow`: G connected, G[X] connected, |X| ≤ ℓ ≤ n ⇒ ∃ Y ⊇ X, G[Y] connected, |Y| = ℓ (boundary dart of a
  walk from X to a vertex outside, Mathlib `Walk.exists_boundary_dart`).
- `Meets φ X`, `numConn_pos_iff` (positive φ), `min_iff` (connected G): ≤ ℓ ↔ 0 < numConn G φ ℓ.
- `min_conn_randomized r D` from `conn_randomized`, `min_pos_randomized D` from `pos_randomized`; G.Connected is a
  hypothesis (disconnected G: run per component). Python: `test_pos.test_min_iff` (brute force).

### N9, N9′, feedback vertex set on sparse graphs
`lean/EthCor/ForestFormula.lean`, `ForestTM.lean`, `ForestIsoTM.lean`.
- Key identity `Forest.sides_edges` (any finite W with a linear order): S(H)·2^{e(H)} = 2^{|W|+j} with j = 0 ↔
  H.IsAcyclic, S(H) = #{s : W → Bool constant on edges}, e(H) = #{(a,b) : a < b, adj}. Induction on e: delete an edge uv;
  if u, v are not reachable in H − uv, S(H − uv) = 2·S(H) (`card_sides_eq`, flip the side of everything reachable from
  v) and acyclicity is kept (`isAcyclic_add_edge_iff_of_not_reachable`); else S is unchanged (`sides_reach`) and j grows
  by 1 (`isAcyclic_sup_fromEdgeSet_iff`). No components or cyclomatic numbers needed.
- Formula `fvsF n E ψ = connF n E ψ ++ ebF n E ++ compF 3n m` on 3n + 2m vars: b_i = 3n + i with b_i → x_u, b_i → x_v
  (`ebF`), b̄_i = 3n + m + i. Count with target n + s + m: Σ_{|x| = s, x ⊨ ψ, P x} sig(x)·2^{e(x)} (`fvs_count`: `stepF`
  drops the complements, `stepG` splits off the edge bits as a sum over b, then `cnt_stepA`/`cnt_stepB` with property
  `EdgeIn E b ∧ P`, swap sums, `card_edgeIn` = 2^{e(x)} via `Fintype.piFinset`). `card_inE` links the edge-list count to
  edges of G[x] (`edges_nodup`). `fvs_parity`: count / 2^s mod 2 = #induced forests of size s mod 2.
- Machine: bit s, not bit 1, so the post step needs s: `Stepped.bind (mapIn preF SIZED) (ofFun postF)` with
  `postF (x, N) = [N / 2^{lC x} % 2 = 1]` (PolyT via `PolyT.pow_unary` with `lC` unary). Size bound through
  `bind_runs`/`ofFun_runs`; count < 2^{N+1} so size(count) ≤ N + 2. SIZED_4 on ≤ (2D+3)·n vars.
- Isolation: `isoAdd N₀ F ω` and `isoC`/`isoD`/`isoE`/`iso_count` for ANY formula F on N₀ variables (ConnIso's steps
  are tied to connF). `fi_parity`, `fi_decide`. Input `codeFI G s ω = code G ++ unary s ++ seedL ω`; reuses ConnITM's
  `sdR`, `aR` (nothing after the seed: `List.take_length`). Variables ≤ (2D + 12k + 4)·n for n ≥ 1.
- `numFVS_eq` (complement bijection), `fvs_iff` (induced forests are closed under subsets:
  `IsAcyclic.embedding (induceHomOfLE)`), `fvs_parity_tm`, `fvs_randomized` with input s = n − k. N9′ decides "at most
  k", which gives the minimum feedback vertex set.
- Python `forest.py`, `tests/test_forest.py` (incl. j = cyclomatic number); Dump `for`, `fi`.
- N9′ reduces to sized counting and is randomized, so the question of Ganian et al. (does FVS reduce to 3-CNF-SAT
  preserving subexponentiality?) stays open.

### N10, odd cycle transversal, deterministic, any density
`lean/EthCor/OctTM.lean`.
- Formula `octF n E = sideF n ++ edgeOC n E` on 3n vars: x_v kept, s_v color (0 if not kept), s̄_v = ¬s_v; per edge
  ¬x_u ∨ ¬x_v ∨ s_u ∨ s_v and ¬x_u ∨ ¬x_v ∨ ¬s_u ∨ ¬s_v (width 4). Only positivity is needed, no counting identity:
  `oct_pos` (0 < cntS (3n) (n + s) ↔ ∃ x, |x| = s ∧ (G.induce {x}).IsBipartite), by splitting w = Fin.append y g and
  building the coloring from `Coloring.mk`; `oct_iff` via `exists_subset_card_eq` and
  `Colorable.of_hom (induceHomOfLE _).toHom`. Machine = `cvcM` shape with `postO N = [decide (0 < N)]`; `oct_tm` rewrites
  with `decide_eq_decide`.
- Novelty: known. IPZ01 Thm 5: size-constrained SNP allows "possibly size-constrained" second-order quantifiers, and
  OCT = ∃X (|X| ≤ k) ∃C ∀u,v: E(u,v) → X(u) ∨ X(v) ∨ C(u) ≠ C(v). Not in Anthropic Cor. 7 (IS, clique, VC, DS, k-col).
  Tulsyan's repository has connected OCT, as a sketch. Label: known, formalized.

### Barrier for Cut & Count
`lean/EthCor/Barrier.lean` (imports Mathlib only). It concerns deterministic versions of N2′/N7′/N9′, FVS on dense graphs
and exact connected counts.
- Cut & Count with q colors, weights x shared by all vertices: X contributes ∏_C p_{|C|}(x) (rooted:
  x_a^{|C_r|} ∏_{C≠C_r} p_{|C|}). Sympy check (q ≤ 4, ℓ ≤ 7): the connected term p_ℓ resp. x_a^ℓ lies in the ℚ-span of
  the disconnected patterns exactly when ℓ > q, rooted and unrooted alike.
- Lean: `esymm_mem` (Newton, Mathlib `mul_esymm_eq_sum`, strong induction), `pow_eq` (Vieta,
  `Multiset.prod_X_sub_X_eq_sum_esymm` evaluated at X a), `psum_eq`, `psum_mem`, `pow_mem`, `barrier`, `barrier_rooted`
  (any ℚ-linear map to any ℚ-module). Spans of `Prods q k m` / `RProds q a k` as multisets of degrees. The colorings →
  power sums step is checked numerically (`tests/test_barrier.py`), not formalized.
- Tight: q = ℓ with ℓ-th roots of unity gives ℓ·#connected, but lg ℓ bits per vertex; within the counters'
  n·o(√lg n/lglg n) budget only ℓ = 2^{o(√lg n/lglg n)}, where n^ℓ = 2^{o(n)} brute force works.
- Not covered: vertex-dependent weights, restrictions that vary between terms (isolation), other encodings (Tulsyan's
  matrix-tree on sparse graphs). Integer form: clearing denominators gives two pattern multisets, one with D > 0
  connected sets and one with none, with equal polynomials; for q = 2, D must be even, consistent with Cut & Count giving
  the parity.
- FVS on dense graphs: a vertex-coloring count depends only on component sizes, so it cannot tell an induced path from an
  induced cycle; N9 needs its edge bits.

### N11, logical operators and distance of a CSS code, deterministic, exact
`lean/EthCor/CodeFormula.lean`, `lean/EthCor/CodeTM.lean`.
- Code semantics over ZMod 2: `vecR r j = (r.count j : ZMod 2)` (a qubit listed twice cancels), `InKer H x`,
  `rowSp H = span {vecR r}`, `numLog H₁ H₂ s = #{x : |x| = s, InKer H₁ x, vecB x ∉ rowSp H₂}`.
- `logical_iff`: vecB x ∉ rowSp H₂ ↔ ∃ y, InKer H₂ y ∧ ⟨x, y⟩ = 1, from
  `Submodule.exists_dual_map_eq_bot_of_notMem` and `LinearMap.pi_apply_eq_sum_univ`.
- `half`: if ⟨x, y₀⟩ = 1 with y₀ ∈ ker H₂, then y ↦ y ⊕ y₀ is an involution of ker H₂ that flips ⟨x, y⟩,
  so 2·#{y ∈ ker H₂ : ⟨x, y⟩ = 1} = |ker H₂|.
- Formula `cssF w n ψ e` on 5n + 2 variables (x, y, chain c₀..c_n, complements of y and c): `rowF` forbids the
  odd patterns of each check (the patterns of `pats w` of the check's length), `chainF` gives c₀ = 0, c_{i+1} = c_i ⊕ x_i y_i,
  c_n = e with `xorC` (8 clauses of width 4), `compF`. `shaped_cssF : Shaped (w + 4) (5n + 2)`,
  `length_cssF ≤ |ψ|·2^{w+1} + 12n + 4`.
- `cnt_cssF`, `card_pairs`, `pairs_true`, `pairs_false`, `numLog_eq`:
  2·cntS (s + 2n + 1) (cssF … true) / cntS (2n + 1) (cssF … false) = numLog H₁ H₂ s.
- Machine `codeM`: K = SIZED_{w+4}(preQ false), N = SIZED_{w+4}(preQ true), output `Nat.bits (2N/K)`. Input
  `unary s ++ SatFree.enc (codeCNF H₁ H₂)`, H₁ as positive and H₂ as negative literals, so the reader of A1
  is reused. Input length ≤ (2D(w+1)+3)(n+2)²; `css_counts` with SIZED at δ/14.
- Python `codes.py` with `brute_num_log` (Gaussian elimination on bitmasks), `tests/test_codes.py`: random
  codes; Steane [[7,1,3]] (7 logical operators of weight 3 per type), [[4,2,2]] (distance 2, 6 of weight 2),
  Shor [[9,1,3]] (distance 3 for both types, degenerate). Dump `css0`, `css1`.
- General stabilizer codes: the same with the symplectic product and one support bit per qubit.
