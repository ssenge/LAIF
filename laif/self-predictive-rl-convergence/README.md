# Where linear self-predictive learning converges: the sign pattern of the predictor decides

Written 21 Nov 2026.

Self-predictive representation learning in reinforcement learning trains a representation Φ so that a latent predictor maps the representation of a state to the representation of the next state, with a stop-gradient on the target. In [1] its learning dynamics with a linear representation and a symmetric transition matrix were reduced to an ordinary differential equation. They showed that a trace objective never decreases along it and that this objective is maximized by the top-k eigenvectors of the transition matrix, sorted by absolute value. Which critical point the dynamics reaches was left open there and in [2]. For the related setting of real diagonalizable matrices with positive eigenvalues, [3] showed by linearization that invariant subspaces other than the top-k are unstable, with a remark on the order of the stable points when some eigenvalues are negative. The results below are the global version for symmetric matrices. The sign pattern of the latent predictor is fixed at the start, and it decides the limit.

**Setting.** T ∈ ℝ^{n×n} is symmetric (the transition matrix P^π of [1]) and Φ(t) ∈ ℝ^{n×k} with Φ(0)ᵀΦ(0) = I. The latent predictor is Q = ΦᵀTΦ, which is symmetric, and the dynamics is equation (5) of [1],

    Φ̇ = (I − ΦΦᵀ) T Φ Q,

which holds under the assumptions of [1]: an optimal predictor at every time, a semi-gradient update of Φ, a uniform first-state distribution and an orthonormal initialization. Along it ΦᵀΦ = I for all t [1]. Write f(Φ) = tr(Q²), the trace objective of [1], and let p be the number of positive eigenvalues of Q(0).

## Results

**Theorem 1 (the sign pattern is conserved).** For every solution, G = (TΦ)ᵀ(I − ΦΦᵀ)(TΦ) is positive semidefinite and

    Q̇ = QG + GQ.

For t ≥ s there is a matrix W with smallest singular value at least 1 and Q(t) = W Q(s) Wᵀ. Hence the rank of Q and the numbers of its positive and negative eigenvalues are constant in time, and every eigenvalue of Q, ordered by size, keeps its sign and does not decrease in absolute value: |λᵢ(Q(t))| ≥ |λᵢ(Q(s))|. This holds for every initialization and for every multiplicity of the eigenvalues of T.

**Theorem 2 (the limit is an invariant subspace with the same sign pattern).** Φ(t) converges as t → ∞. If Q(0) is nonsingular, the limit Φ∞ spans a T-invariant subspace on which T has exactly p positive and k − p negative eigenvalues. In particular, from a nonsingular Q(0) the dynamics never converges to a critical point whose span is not T-invariant, such as a point with ΦᵀTΦ singular, and never to a subspace that contains an eigenvector of T with eigenvalue 0.

**Theorem 3 (which invariant subspace).** Let S be a T-invariant subspace of dimension k with nonsingular T restricted to S, spanned by eigenvectors uᵢ of T with eigenvalues μᵢ, and let vⱼ be eigenvectors orthogonal to S with eigenvalues λⱼ. The second variation of f at S in the direction that turns uᵢ towards vⱼ is 2μᵢ(λⱼ − μᵢ). So S is a local maximum of f exactly when it is spanned by eigenvectors for the p largest positive and the k − p smallest negative eigenvalues of T (with ties, any choice of eigenvectors for the equal eigenvalues), where p is the number of positive μᵢ. Every other such S has a direction of increase, so it is a saddle point. For almost every Φ(0) on the Stiefel manifold, the limit of Theorem 2 is a local maximum of this form. A lower-dimensional set of starts converges to saddle invariant subspaces; for example a start that already spans an invariant subspace stays there.

**Corollary 4 (when the global maximum is reached).** Let q be the number of positive eigenvalues among the k eigenvalues of T of largest absolute value. For almost every start with nonsingular Q(0), the dynamics converges to a global maximizer of f exactly when p = q. If T is positive semidefinite, then p = k for every start with nonsingular Q(0), and almost every start reaches the global maximum. If T has eigenvalues of both signs, almost every start with nonsingular Q(0) and p ≠ q converges to a local maximum of f that is not global; the starts with nonsingular Q(0) and p ≠ q form an open set, which is nonempty for example when k = 1.

**Example.** For the matrix T = [[0.1, 0.9], [0.9, 0.1]] of equation (6) in [1] with k = 1 (eigenvalues 1 and −0.8), Q = q is a scalar, and by Theorem 1 the sign of q is fixed and |q| does not decrease. A start near the eigenvector for −0.8 therefore converges to that eigenvector, a local maximum of f = q² with value 0.64, and not to the top eigenvector or to the four points with q = 0. This hints at a possible difference from the limit stated for Fig. 3 of [1]; the conclusion there that such starts miss the top eigenvector holds.

## Proofs

**Theorem 1.** With ΦᵀΦ = I, differentiating Q = ΦᵀTΦ gives Q̇ = Φ̇ᵀTΦ + ΦᵀTΦ̇ = QΦᵀT(I − ΦΦᵀ)TΦ + ΦᵀT(I − ΦΦᵀ)TΦQ = QG + GQ, using T = Tᵀ and Q = Qᵀ. G is positive semidefinite since I − ΦΦᵀ is an orthogonal projection. Let W solve Ẇ = G(t)W with W(s) = I. Then W Q(s) Wᵀ solves the same linear equation X' = GX + XG as Q with the same value at s, so Q(t) = W Q(s) Wᵀ. Moreover (WᵀW)' = 2WᵀGW is positive semidefinite, so WᵀW ⪰ I and every singular value of W is at least 1. Sylvester's law of inertia gives the constant numbers of positive, negative and zero eigenvalues. Ostrowski's theorem [4] gives λᵢ(WQWᵀ) = θᵢλᵢ(Q) with θᵢ between the smallest and the largest squared singular value of W, so θᵢ ≥ 1.

**Theorem 2.** The Euclidean gradient of f/4 is TΦQ, and its projection onto the tangent space of the Stiefel manifold with the embedded metric is TΦQ − Φ sym(ΦᵀTΦQ) = TΦQ − ΦQ² = (I − ΦΦᵀ)TΦQ. So the dynamics is the Riemannian gradient flow of the analytic function f/4 on a compact analytic manifold, and it converges to a single critical point by the Łojasiewicz gradient inequality [5]. By Theorem 1 and continuity, Q∞ = Φ∞ᵀTΦ∞ has the same numbers of positive and negative eigenvalues as Q(0) and is nonsingular. At a critical point (I − ΦΦᵀ)TΦQ = 0, so (I − ΦΦᵀ)TΦ = 0, that is TΦ∞ = Φ∞Q∞: the span of Φ∞ is invariant, and T restricted to it is similar to Q∞.

**Theorem 3.** In an eigenbasis, perturb the basis of S as Φ = (U + VΔ)(I + ΔᵀΔ)^{−1/2}, with U = [u₁ … u_k], V the eigenvectors orthogonal to S and Δ small. Then Q = M + ΔᵀΛΔ − (MΔᵀΔ + ΔᵀΔM)/2 + O(‖Δ‖³) with M = diag(μᵢ) and Λ = diag(λⱼ), so f = tr M² + 2 Σᵢⱼ μᵢ(λⱼ − μᵢ)Δⱼᵢ² + O(‖Δ‖³). The quadratic form is diagonal with the coefficients 2μᵢ(λⱼ − μᵢ). It is negative for all pairs exactly when every λⱼ outside S lies below every positive μᵢ and above every negative μᵢ, which is the stated form; it vanishes only for ties λⱼ = μᵢ, along which f is constant. Any other S has a coefficient that is positive, hence a direction of increase. The statement for almost every start follows from the stable manifold theorem in the form of [6], applied to the time-one map of the flow, a diffeomorphism whose Jacobian has an eigenvalue above 1 at every such saddle point (also when the saddle points are not isolated); by Theorem 1 only critical points with nonsingular Q can be limits, so no other critical points need to be excluded.

**Corollary 4.** The global maximizers of f are the spans of k eigenvectors of largest |λ| [1]; by Theorems 2 and 3 the limit has p positive eigenvalues, and among the local maxima of Theorem 3 it is global exactly when p = q. The set of starts with p ≠ q is open, since the inertia of Q(0) is locally constant on nonsingular Q(0).

## Scope and status

| Result | Scope | Status | Posted |
|---|---|---|---|
| Theorem 1 | Symmetric T, every solution of equation (5) of [1], any initialization with Φ(0)ᵀΦ(0) = I, any multiplicities | Claim; uses Sylvester's law of inertia and Ostrowski's theorem [4]; checked numerically | 2026-11-21 |
| Theorem 2 | Symmetric T, Q(0) nonsingular | Claim; uses the Łojasiewicz convergence theorem [5]; checked numerically | 2026-11-21 |
| Theorem 3 | Symmetric T, nonsingular T restricted to S; the limit for almost every start; starts on a lower-dimensional set may end at saddle invariant subspaces | Claim; uses the stable manifold theorem [6]; checked numerically | 2026-11-21 |
| Corollary 4 | As Theorems 2 and 3 | Claim | 2026-11-21 |

Not covered: non-symmetric transition matrices, the action-conditional objective of [2] (a sum of trace objectives over actions), finite step sizes and predictors that are not optimal at every time.

## Simulations

[`sim/`](sim/) holds Python scripts with asserts (NumPy):

- `inertia_check.py`: equation (5) integrated by the classical Runge-Kutta method with step 0.02 for 30000 steps, with no re-orthonormalization, for n = 10 and k = 3: 30 random symmetric T and 10 matrices with repeated eigenvalues (0.9 twice, −0.6 three times, and a zero eigenvalue). In all 40 runs the numbers of positive and negative eigenvalues of Q are constant, every ordered |eigenvalue| of Q is non-decreasing (largest decrease 2.7 · 10⁻¹⁵), ΦᵀΦ = I holds to 6.1 · 10⁻¹⁵, and the limit is the subspace of Theorem 3 (projector distance below 10⁻⁴ for distinct eigenvalues, eigenvalues of Q∞ for repeated ones). The global maximum is reached in 21 of the 40 runs.
- `fig3_example.py`: the example above, from starts 0.05, 0.2 and 0.5 radians away from the eigenvector for −0.8: convergence to that eigenvector, with f non-decreasing.

## References

1. Y. Tang, Z. D. Guo, P. H. Richemond, B. Á. Pires, Y. Chandak, R. Munos, M. Rowland, M. G. Azar, C. Le Lan, C. Lyle, A. György, S. Thakoor, W. Dabney, B. Piot, D. Calandriello, M. Valko. Understanding self-predictive learning for reinforcement learning. ICML 2023. arXiv:2212.03319.
2. K. Khetarpal, Z. D. Guo, B. Á. Pires, Y. Tang, C. Lyle, M. Rowland, N. Heess, D. Borsa, A. Guez, W. Dabney. A unifying framework for action-conditional self-predictive reinforcement learning. arXiv:2406.02035, 2024.
3. C. Voelcker, T. Kastner, I. Gilitschenski, A.-m. Farahmand. When does self-prediction help? Understanding auxiliary tasks in reinforcement learning. RLC 2024. arXiv:2406.17718.
4. A. M. Ostrowski. A quantitative formulation of Sylvester's law of inertia. Proceedings of the National Academy of Sciences 45, 1959.
5. S. Łojasiewicz. Sur les trajectoires du gradient d'une fonction analytique. Seminari di Geometria, Bologna, 1984.
6. J. D. Lee, I. Panageas, G. Piliouras, M. Simchowitz, M. I. Jordan, B. Recht. First-order methods almost always avoid strict saddle points. Mathematical Programming 176, 2019. arXiv:1710.07406.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check the proofs, to write the simulation scripts, and to draft the text.
