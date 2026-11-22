# Single-layer quantum models with the fixed observable Z ⊗ I

2026-11-22

## Problem

Let x = (x_1, …, x_N) ∈ [0, 2π)^N carry the uniform probability measure, and let L² be the space of real-valued square-integrable functions on it. A register of R = R_1 + … + R_N qubits is split into blocks, and block v of R_v qubits encodes x_v by single-qubit rotations about the z axis:

S(x) = ⊗_v ⊗_{r ≤ R_v} e^{−i x_v Z/2}.

The single-layer model of [1, eq. (9)] is

f(x) = ⟨0| W₁* S(x)* W₂* M W₂ S(x) W₁ |0⟩,

with arbitrary unitaries W₁, W₂ and an observable M. Such models approximate every function in L² when M may depend on the target [2], but then M has no norm bound. In [1, Section 1] it is asked whether the usual fixed observable M = Z ⊗ I ⊗ … ⊗ I can approximate every square-integrable function with arbitrary precision. More generally, it asks whether there is a sequence of observables (M_k) such that, for every target g and every ε > 0, there is an index K with this property: for all k ≥ K, unitaries W₁, W₂ exist with ‖g − f‖₂ < ε.

Write F_R for the set of all such models with M = Z ⊗ I and block sizes R = (R_1, …, R_N).

| | fixed observable Z ⊗ I |
|---|---|
| Previous result | approximation of all of L² with target-dependent observables [2]; the fixed-observable case is open [1] |
| Theorem 1 | the L² closure of the models is exactly {g : \|g\| ≤ 1 almost everywhere}; the uniform closure is exactly the continuous g with \|g\| ≤ 1 |
| Theorem 2 | for every g with \|g\| ≤ 1, a model equals the arithmetic mean of the partial frequency sums of g of orders 0 to R_v |
| Theorem 3 | the observables c_k Z ⊗ I with c_k → ∞ approximate every g ∈ L² |
| Theorem 4 | every trigonometric polynomial of degree D with sup \|g\| ≤ 1 − η is a model exactly, on R qubits once R + 1 ≥ D + D√(2D)/η |

So the first form of the question has a negative answer: a function that exceeds 1 in absolute value on a set of positive measure stays at a fixed positive distance from every model. The second form has a positive answer with rescaled copies of Z ⊗ I.

## Results

For g ∈ L² write ĝ(k) = ∫ g(x) e^{−ik·x} dx for k ∈ ℤ^N. For n = (n_1, …, n_N) let

A_n g(x) = Σ_{|k_v| < n_v} ∏_v (1 − |k_v|/n_v) ĝ(k) e^{ik·x}.

In one variable, A_n g is the arithmetic mean of the partial frequency sums of g of orders 0, 1, …, n − 1. In several variables it is the product of these means, one per coordinate. As min_v n_v → ∞, A_n g → g in L² for every g ∈ L², and uniformly for every continuous g.

**Theorem 1 (closure).** Every model f ∈ F_R is a real trigonometric polynomial of degree at most R_v in x_v with |f| ≤ 1. For every g ∈ L² and every model f,

‖g − f‖₂ ≥ ‖(|g| − 1)₊‖₂.

The L² closure of the union of all F_R is exactly {g ∈ L² : |g| ≤ 1 almost everywhere}. In the uniform norm, the closure is exactly the set of continuous 2π-periodic functions g with |g| ≤ 1.

**Theorem 2 (construction).** Let g be real and integrable with |g| ≤ 1 almost everywhere, and let R_v ≥ 3 for every v. With n_v = R_v + 1, there are unitaries W₁, W₂ such that the model with M = Z ⊗ I equals A_n g exactly.

**Theorem 3 (rescaled fixed observable).** Use R_v = k qubits in every block and the observable M_k = c_k Z ⊗ I, where c_k → ∞. For every g ∈ L² and every ε > 0 there is a K such that for all k ≥ K, unitaries W₁, W₂ exist with ‖g − f‖₂ < ε.

**Theorem 4 (exact representation).** Let N = 1, and let g be a real trigonometric polynomial of degree D with sup |g| ≤ 1 − η, where 0 < η ≤ 1. If R ≥ 3 and R + 1 ≥ D + D√(2D)/η, then g is a model in F_R exactly.

## Proofs

**Theorem 2.** In block v, choose for each n ∈ {0, …, R_v} one computational basis vector e^{(v)}_n with exactly n ones. For a tuple t = (t_1, …, t_N) with 0 ≤ t_v ≤ R_v, let ε_t = ⊗_v e^{(v)}_{t_v}. Each qubit in state 1 picks up the phase e^{i x_v} relative to state 0, so S(x) ε_t = e^{iφ(x)} e^{it·x} ε_t, with a phase φ(x) that does not depend on t. Let L = ∏_v n_v and ψ = L^{−1/2} Σ_t ε_t, and let W₁ be any unitary with W₁|0⟩ = ψ.

Let h = (1 + g)/2, so 0 ≤ h ≤ 1, and let G_{t,t'} = ĥ(t' − t). This matrix is constant along its diagonals and self-adjoint. For every vector c,

Σ_{t,t'} c̄_t c_{t'} G_{t,t'} = ∫ h(x) |Σ_t c_t e^{−it·x}|² dx ∈ [0, ‖c‖²],

so 0 ≤ G ≤ I. Choose L further basis vectors η_t outside {ε_t}. On span{ε_t} ⊕ span{η_t}, the block matrix

P₀ = [[G, B], [B, I − G]],  B = (G(I − G))^{1/2},

is an orthogonal projector of rank L, the dilation of G. Add 2^{R−1} − L further basis vectors to its range. This is possible because R_v + 1 ≤ 2^{R_v − 1} for R_v ≥ 3, so L ≤ 2^{R−N} ≤ 2^{R−1}. Then 2L + (2^{R−1} − L) ≤ 2^R basis vectors are used. The result is a projector P of rank 2^{R−1}, so 2P − I has the spectrum of Z ⊗ I, and some unitary W₂ has W₂*(Z ⊗ I)W₂ = 2P − I.

Since S(x)ψ lies in span{ε_t}, where P acts as G,

f(x) = 2⟨S(x)ψ, P S(x)ψ⟩ − 1 = (2/L) Σ_{t,t'} ĥ(t' − t) e^{i(t'−t)·x} − 1.

The number of pairs with t' − t = k is ∏_v (n_v − |k_v|), so f = 2 A_n h − 1 = A_n g.

**Convergence of A_n.** In L², the multipliers ∏_v (1 − |k_v|/n_v) lie in [0, 1] and tend to 1 for each k, so ‖A_n g − g‖₂² = Σ_k (1 − multiplier)² |ĝ(k)|² → 0 by dominated convergence. In one variable, A_n g is the convolution of g with the nonnegative kernel K_n(u) = (1/n) |Σ_{j<n} e^{iju}|², which has mean 1 and mass concentrating at u = 0. The same holds for the product kernel in several variables, so A_n g → g uniformly for continuous g.

**Theorem 1.** Every model is a real trigonometric polynomial of the stated degree, and |f| ≤ ‖Z ⊗ I‖ = 1. Pointwise |g − f| ≥ (|g| − 1)₊, which gives the distance bound. An L² limit of functions bounded by 1 is bounded by 1 almost everywhere, since a subsequence converges almost everywhere. Conversely, for |g| ≤ 1, Theorem 2 gives models A_n g → g. A uniform limit of models is continuous and bounded by 1, and for continuous g with |g| ≤ 1 the models A_n g converge to g uniformly.

**Theorem 3.** Let g_k be g truncated to [−c_k, c_k]. Theorem 2 applied to g_k/c_k gives a model with c_k Z ⊗ I equal to c_k A_n(g_k/c_k) = A_n g_k, with n_v = k + 1. The multipliers lie in [0, 1], so A_n does not increase L² norms, and

‖g − A_n g_k‖₂ ≤ ‖g − A_n g‖₂ + ‖g − g_k‖₂.

Both terms tend to 0 as k → ∞, the first by the convergence of A_n and the second because c_k → ∞.

**Theorem 4.** Let h = (1 + g)/2 ∈ [η/2, 1 − η/2] and n = R + 1 > D. Replace G in the proof of Theorem 2 by the constant-diagonal matrix with entries T(k) = ĥ(k) n/(n − |k|) for |k| ≤ D and 0 otherwise. The model then equals 2 Σ_k ((n − |k|)/n) T(k) e^{ikx} − 1 = 2h − 1 = g. The matrix is the section of the symbol h̃(x) = Σ_{|k| ≤ D} T(k) e^{ikx}, so 0 ≤ G ≤ I holds when 0 ≤ h̃ ≤ 1. Now

|h̃ − h| ≤ Σ_{0<|k|≤D} |ĥ(k)| |k|/(n − |k|) ≤ (D/(n − D)) (1/2) Σ_{k≠0} |ĝ(k)| ≤ (D/(n − D)) √(2D)/2.

The last step bounds a sum of 2D terms by √(2D) times the root of the sum of their squares, together with ‖g‖₂ ≤ 1. So |h̃ − h| ≤ η/2 once n − D ≥ D√(2D)/η.

## Remarks

- Theorems 1 to 3 hold for every number of variables N, with one block of at least 3 qubits per variable. The construction uses one basis vector per tuple of numbers of ones. The remaining basis vectors only complete the dilation.
- With a single qubit and repeated data loading, models with the fixed observable Z are universal for suitably bounded targets [3, 4]. Approximation rates for periodic functions with a rescaled single-qubit amplitude are given in [5], and a model with the fixed observable |0⟩⟨0|, a rescaling and a square root of the output is given in [6]. These architectures differ from the single-layer model above.
- For continuous g, Theorem 2 gives the uniform error of the arithmetic mean of partial sums. For every non-constant g the L² error is at least of order 1/R, since the coefficient of a frequency k ≠ 0 is reduced by the factor 1 − |k|/(R + 1). Theorem 4 shows that faster rates are possible for trigonometric polynomials with a margin.

## Check

`sim/check.py`, output in `sim/out.txt`. The script builds W₁ and W₂ explicitly, evaluates the model as in [1, eq. (9)] with the observable Z ⊗ I, and asserts:

- **Theorem 2:** the model equals A_n g to within 10⁻⁹ at 60 random points. The targets are a square wave, a smooth function and a step function in one variable (R = 3, 5, 7), and two functions in two variables (blocks of 3 + 3 and 3 + 4 qubits).
- **Theorem 4:** exact representation to within 10⁻⁹ for random trigonometric polynomials of degree 1, 2 and 3 with margins 0.5, 0.4 and 0.9, on the number of qubits given by the theorem (3, 11 and 11).
- **Theorem 3:** with the observable 6 Z ⊗ I, the L² error for a target with values up to 5 decreases with R.

## Scope

- The encoding generators are single-qubit Z rotations, the standard example of [1]. Other generators change the frequency sets, and they are not treated here.
- Theorem 4 is stated for one variable.
- Lean: not formalized.

## References

1. P. Holzer, I. Turkalj. Spectral invariance and maximality properties of the frequency spectrum of quantum neural networks. arXiv:2402.14515.
2. M. Schuld, R. Sweke, J. J. Meyer. The effect of data encoding on the expressive power of variational quantum machine learning models. Phys. Rev. A 103, 032430 (2021). arXiv:2008.08605.
3. A. Pérez-Salinas, D. López-Núñez, A. García-Sáez, P. Forn-Díaz, J. I. Latorre. One qubit as a universal approximant. Phys. Rev. A 104, 012405 (2021). arXiv:2102.04032.
4. Z. Yu, H. Yao, M. Li, X. Wang. Power and limitations of single-qubit native quantum neural networks. NeurIPS 2022. arXiv:2205.07848.
5. A. Neufeld, P. Schmocker, V. K. Tran. Approximation rates of quantum neural networks for periodic functions via Jackson's inequality. arXiv:2511.16149.
6. J. Tang, J. Zhang, X. Sun. SAQNN: Spectral adaptive quantum neural network as a universal approximator. arXiv:2602.09718.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
