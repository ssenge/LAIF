# Optimal approximation rates of fixed-encoding quantum neural networks

Written 5 Nov 2026.

## Setting

**Function classes.** For β = s + r with s ∈ N₀ and r ∈ (0, 1], the Hölder ball B^β_d is the set of f: [0, 1]^d → R with ‖D^α f‖_∞ ≤ 1 for |α| ≤ s and |D^α f(x) − D^α f(y)| ≤ |x − y|^r for |α| = s. For an integer k, the ball C^k_d is the set of f with ‖D^α f‖_∞ ≤ 1 for all |α| ≤ k.

**Fixed-encoding models.** A model with T trainable parameters θ ∈ R^T acts on a finite-dimensional system. It applies a sequence of operations of two kinds:

- *Fixed operations:* arbitrary quantum channels that may depend on the input x in any way but not on θ. This covers every data encoding, any number of qubits, measurements in the middle of the circuit, and noise.
- *Trainable gates:* e^{−iθ_i G} for some i, with G Hermitian and with spectrum in ½Z ∩ [−g/2, g/2]. Pauli rotations and controlled Pauli rotations have g = 1, and phase gates diag(1, e^{iθ}) have g = 2.

Let U be the total number of trainable gates, so each parameter may be reused. The output f(x; θ) is the expectation of a fixed observable, or the real part of an amplitude ⟨0|W(x; θ)|0⟩. It may be multiplied by a trainable scale λ > 0.

The architecture, that is the sequence of operations, is fixed; only θ and λ depend on the target function. So the data enters only through gates without trainable frequencies. The circuits of [2] are of this form, and so are those of [1] once its localization circuit, which does not depend on the target, is held fixed.

## Results

**Theorem 1 (capacity).** For every x₁, …, x_m with m ≥ 2T, the number of vectors (1[f(x_j; θ) ≥ 0])_j over all θ is at most 2(2em·2gU/(2T))^{2T}. Hence the sign class {x ↦ 1[f(x; θ) ≥ 0]} has VC dimension at most 4T log₂(8egU) + 2. The same holds with thresholds, so this also bounds the pseudo-dimension of {f(·; θ)}.

**Theorem 2 (lower bound).** Let ψ be a fixed smooth bump on R^d with support in (−1/2, 1/2)^d and ψ(0) = 1. Let C_ψ be the largest of the sup norms of D^αψ for |α| ≤ s and of the r-Hölder seminorms of D^αψ for |α| = s, over R^d (for C^k_d, the largest sup norm of D^αψ for |α| ≤ k). If a fixed-encoding model approximates every f ∈ B^β_d within ε in sup norm on [0, 1]^d, and ε ≤ 2^{−β−1}/C_ψ, then

4T log₂(8egU) + 2 ≥ 2^{−d} (2C_ψ ε)^{−d/β}.

The same holds for C^k_d with β = k.

**Previous proof for β = 1.** For 1-bounded, 1-Lipschitz functions, [10] shows that circuits of fixed structure need Ω̃(ε^{−d}) gates (Theorem 7 of [10]). Theorem 2 extends this to every β and to C^k, counts trainable parameters with reuse and generators of half-integer spectrum, and Theorem 3 shows it is tight for every β.

**Theorem 3 (upper bound).** For all d, β there is C = C_{d,β} such that for every N ≥ 1 there is one fixed-encoding circuit with

- n = (4N + 1)^d frequencies, q = ⌈log₂ n⌉ + 1 qubits,
- T ≤ 3n trainable angles, each used once (so U = T), with g = 2,

such that for every f ∈ B^β_d some θ and λ ≤ C n^{1/2} give sup_{x∈[0,1]^d} |f(x) − λ f(x; θ)| ≤ C N^{−β}.

**Corollary 4 (rate).** Fix a > 0 and g ≥ 1. Among fixed-encoding models with U ≤ (1/ε)^a trainable gates, the least number of trainable parameters that approximates all of B^β_d within ε in sup norm is between c ε^{−d/β}/log(1/ε) and C ε^{−d/β} for ε ≤ ε₀. Here c depends on d, β, ψ, g and a, and C on d and β. Depth, width, data encoding and reuse of parameters change this only by the logarithmic factor.

**Comparison with ReLU networks.** For f ∈ C^k_d, deep ReLU networks of width O(N ln N) and depth O(L ln L) reach sup-norm error O(N^{−2k/d} L^{−2k/d}) [3]. With N fixed and L growing, that is O(ε^{−d/(2k)} log(1/ε)) weights. By Theorem 2 with β = k, a fixed-encoding model needs at least c ε^{−d/k}/log(gU) parameters, whatever the fixed-encoding circuit, which is about the square of that count. [1] compares the two model classes at a fixed ε as d grows, with the constants of the respective constructions; its Theorem 4 holds in sup norm outside a small region, and in L² on the whole cube. Corollary 4 concerns the other limit, fixed d and ε → 0, in sup norm on the whole cube.

**Periodic functions.** For 2π-periodic f with ‖f‖_∞ ≤ 1 and ‖∂_j^k f‖_∞ ≤ 1 for each j, [2] reaches sup-norm error ε with O(ε^{−(d+1)/k}) parameters for d ≥ 2, and with O(ε^{−1/k}) for d = 1. The construction of Theorem 3 needs no extension step for this class and gives O(ε^{−d/k}), and Theorem 2 applies to it as well, since the bumps of its proof, rescaled to [0, 2π]^d and extended periodically, lie in this class up to a constant factor. So for this class the rate is ε^{−d/k} up to a logarithmic factor.

## Proof of Theorem 1

Fix x. Write c_i = cos(θ_i/2) and s_i = sin(θ_i/2). As G has spectrum in ½Z ∩ [−g/2, g/2], e^{−iθ_i G} = Σ_j e^{−iθ_i j/2} P_j over its eigenprojections, and e^{−iθ j/2} = (c − is)^j for j ≥ 0 and (c + is)^{|j|} for j < 0. So each trainable gate has entries that are polynomials of degree at most g in (c_i, s_i). The fixed channels are linear and do not depend on θ, so an amplitude is a polynomial of degree at most gU in the 2T variables (c, s), and an expectation, in which each gate appears with its adjoint, one of degree at most 2gU. A scale λ > 0 does not change signs.

By the sign-pattern bound for polynomials (Theorem 8.3 of [4]), m polynomials of degree at most D in n ≤ m real variables take at most 2(2emD/n)^n vectors of signs (1[p_j ≥ 0])_j. Here n = 2T and D = 2gU, and restricting (c_i, s_i) to the circle can only lower the count. If m ≥ 2T points are shattered, then 2^m ≤ 2(2egUm/T)^{2T}, so m ≤ 1 + 2T log₂(2egU/T) + 2T log₂m. Now log₂ y ≤ y for y > 0 gives log₂m ≤ log₂(4T) + m/(4T), hence m ≤ 1 + 2T log₂(8egU) + m/2, and m ≤ 2 + 4T log₂(8egU). For m < 2T there is nothing to prove. Thresholds r_j only replace p_j by p_j − r_j. ∎

Bounds of this type for quantum circuit learning are known in other forms [5, 6]. The point here is that the count depends only on T, g and U, and not on the qubits, the depth of the fixed part or the encoding.

## Proof of Theorem 2

The argument is the standard one that links approximation and VC dimension, as in [7]. Let n be an integer with n^{−β} > 2C_ψ ε, and z_j for j ∈ {0, …, n − 1}^d the centres of the cells of the grid of side 1/n. For p ∈ {±1}^{n^d} let

f_p(x) = h Σ_j p_j ψ(n(x − z_j)), h = n^{−β}/(2C_ψ).

The terms have disjoint supports inside their cells. For |α| ≤ s, ‖D^α f_p‖_∞ ≤ h n^{|α|} C_ψ ≤ 1/2. For |α| = s and x, y in one cell, |D^α f_p(x) − D^α f_p(y)| ≤ h n^{β} C_ψ |x − y|^r = |x − y|^r/2. For x, y in different cells, D^α f_p vanishes at the points x′, y′ where the segment from x to y leaves the cell of x and enters the cell of y, so the difference is at most |x − x′|^r/2 + |y′ − y|^r/2 ≤ |x − y|^r. So f_p ∈ B^β_d, and for C^k_d only the first bound is needed.

As f_p(z_j) = p_j h and h > ε, any u with ‖u − f_p‖_∞ ≤ ε has sign p_j at z_j. So the sign class shatters the n^d grid points, and n^d ≤ 4T log₂(8egU) + 2 by Theorem 1. The largest admissible n is at least (2C_ψ ε)^{−1/β}/2 when ε ≤ 2^{−β−1}/C_ψ, which gives the claim. ∎

## Proof of Theorem 3

**Periodic extension.** There is a bounded linear extension operator E from Hölder functions on [0, 1]^d to Hölder functions on R^d of the same order, for every β > 0 (Theorem 4 in Section 2.3 of Chapter VI of [8]). Let χ be smooth, equal to 1 on [0, 1]^d and supported in [−1/2, 3/2]^d, and let F̃ be the 3-periodic sum of the translates of χ·Ef by 3Z^d, which are at distance at least 1 from each other. Then G(y) = F̃(3y/(2π)) is 2π-periodic in each coordinate, equals f(3y/(2π)) for y ∈ [0, 2π/3]^d, and has Hölder norm of order β at most a constant C₁ = C₁(d, β). For the periodic class above this step is not needed.

**Polynomial.** Let V_N be the de la Vallée-Poussin mean in one variable. It reproduces trigonometric polynomials of degree at most N, has norm at most 3, and has degree at most 2N − 1, so ‖g − V_N g‖_∞ ≤ 4E_N(g), where E_N is the error of best approximation. The one-dimensional estimate of [9] gives E_N(g) ≤ C_β N^{−β} for g of Hölder norm at most 1 of order β, and for g with ‖g^{(k)}‖_∞ ≤ 1 when β = k. Apply V_N in each coordinate in turn. Writing the error as a telescoping sum, each term is at most 3^{d−1} times a one-dimensional error, so P = V_N^{(1)} ⋯ V_N^{(d)} G satisfies ‖G − P‖_∞ ≤ 4d 3^{d−1} C_β C₁ N^{−β}. P is real, with coefficients c_k for k ∈ K = {−2N, …, 2N}^d, and c_{−k} is the complex conjugate of c_k.

**Circuit.** Let n = |K|, q₀ = ⌈log₂ n⌉, and index K by an index register of q₀ qubits. Put λ = Σ_k |c_k| and c_k = |c_k|e^{iφ_k}. The circuit is:

1. Prepare V|0⟩ = Σ_k (|c_k|/λ)^{1/2} |k⟩ with a binary tree of uniformly controlled RY rotations, which takes 2^{q₀} − 1 < 2n trainable angles, each used once.
2. Put an ancilla in |+⟩. Controlled by the ancilla, apply the trainable phases Σ_k e^{iφ_k}|k⟩⟨k|, that is n controlled phase gates, and the fixed data diagonal D(y) = Σ_k e^{ik·y}|k⟩⟨k| with y = 2πx/3.
3. Measure X on the ancilla.

The expectation is Re Σ_k (|c_k|/λ) e^{i(k·y + φ_k)} = P(y)/λ. So λ f(x; θ) = P(2πx/3), and on [0, 1]^d the error is |f(x) − P(2πx/3)| = |G(y) − P(y)| ≤ C N^{−β}. Finally λ ≤ n^{1/2}(Σ_k |c_k|²)^{1/2} = n^{1/2}‖P‖_{L²} ≤ n^{1/2}‖P‖_∞ ≤ n^{1/2}(C₁ + C N^{−β}), with L² taken with respect to normalized measure. ∎

The diagonal D(y) is a fixed unitary: it uses the data only through the fixed frequencies k, with no trainable parameter.

## Scope

- The lower bounds are for fixed-encoding models. Trainable frequencies escape them: the class sin(wx) with trainable w has infinite VC dimension. So do trainable classical layers after the circuit, beyond a positive scale. The lower bound on T of Theorem 2 weakens by a factor log U, which reflects that a parameter reused U times can produce frequencies up to U.
- Nested circuits, which feed a measured and rounded output of a trainable circuit into a later encoding, are not fixed-encoding models and are not covered. With one parameter θ, nesting that maps x_j to cos(π2^j cos θ) already realizes every sign pattern on any number of points.
- The counts are of trainable parameters for exact expectations. Estimating an expectation to accuracy ε/λ by sampling takes about λ²/ε² repetitions, which Theorem 3 does not optimize.
- The upper bound is for sup norm on [0, 1]^d. Theorem 2 is stated for sup norm.

## Simulation

`sim/lcu_check.py` needs Python 3 with NumPy. It builds the circuit of Theorem 3 as matrices for random real trigonometric polynomials with d = 1, N ∈ {1, 3}, and d = 2, N = 1, with the tree of rotations and the controlled phases, and checks that ⟨X⟩ equals P(y)/λ at 200 random points to 10⁻¹⁰. It then checks that N^β times the sup error of the tensor de la Vallée-Poussin mean stays bounded for test functions of order β ∈ {0.5, 1.5, 2.5} with d = 1, and β = 1.5 with d = 2.

## References

1. Z. Yu, Q. Chen, Y. Jiao, Y. Li, X. Lu, X. Wang, J. Z. Yang. Non-asymptotic Approximation Error Bounds of Parameterized Quantum Circuits. NeurIPS 2024. arXiv:2310.07528.
2. A. Neufeld, P. Schmocker, V. K. Tran. Approximation rates of quantum neural networks for periodic functions via Jackson's inequality. arXiv:2511.16149.
3. J. Lu, Z. Shen, H. Yang, S. Zhang. Deep network approximation for smooth functions. SIAM Journal on Mathematical Analysis 53 (2021), 5465-5506. arXiv:2001.03040.
4. M. Anthony, P. L. Bartlett. Neural Network Learning: Theoretical Foundations. Cambridge University Press, 1999.
5. C.-C. Chen, M. Sogabe, K. Shiba, K. Sakamoto, T. Sogabe. General Vapnik-Chervonenkis dimension bounds for quantum circuit learning. Journal of Physics: Complexity 3 (2022), 045007.
6. M. C. Caro, I. Datta. Pseudo-dimension of quantum circuits. Quantum Machine Intelligence 2 (2020), 14. arXiv:2002.01490.
7. D. Yarotsky. Error bounds for approximations with deep ReLU networks. Neural Networks 94 (2017), 103-114. arXiv:1610.01145.
8. E. M. Stein. Singular Integrals and Differentiability Properties of Functions. Princeton University Press, 1970, Chapter VI.
9. R. A. DeVore, G. G. Lorentz. Constructive Approximation. Springer, 1993, Chapter 7.
10. H. Zhao, L. Lewis, I. Kannan, Y. Quek, H.-Y. Huang, M. C. Caro. Learning quantum states and unitaries of bounded gate complexity. arXiv:2310.19882.
