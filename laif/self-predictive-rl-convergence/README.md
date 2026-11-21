# Where linear self-predictive learning converges: the sign pattern of the predictor decides

Written 21 Nov 2026.

Self-predictive representation learning in reinforcement learning trains a representation Φ so that a latent predictor maps the representation of a state to the representation of the next state, with a stop-gradient on the target. In [1] its learning dynamics with a linear representation and a symmetric transition matrix were reduced to an ordinary differential equation. They showed that a trace objective never decreases along it and that this objective is maximized by the top-k eigenvectors of the transition matrix, sorted by absolute value. Which critical point the dynamics reaches was left open there and in [2]. For the related setting of real diagonalizable matrices with positive eigenvalues, [3] showed by linearization that invariant subspaces other than the top-k are unstable, with the same coefficients μᵢ(λⱼ − μᵢ) as in Theorem 3 below and a remark on the order of the stable points when some eigenvalues are negative. The results below are the global version for symmetric matrices. The sign pattern of the latent predictor is fixed at the start, and it decides the limit.

**Setting.** T ∈ ℝ^{n×n} is symmetric (the transition matrix P^π of [1]) and Φ(t) ∈ ℝ^{n×k} with Φ(0)ᵀΦ(0) = I. The latent predictor is Q = ΦᵀTΦ, which is symmetric, and the dynamics is equation (5) of [1],

    Φ̇ = (I − ΦΦᵀ) T Φ Q,

which holds under the assumptions of [1]: an optimal predictor at every time, a semi-gradient update of Φ, a uniform first-state distribution and an orthonormal initialization. Along it ΦᵀΦ = I for all t [1]. Write f(Φ) = tr(Q²), the trace objective of [1], and let p be the number of positive eigenvalues of Q(0).

## Results

**Theorem 1 (the sign pattern is conserved).** For every solution, G = (TΦ)ᵀ(I − ΦΦᵀ)(TΦ) is positive semidefinite and

    Q̇ = QG + GQ.

For t ≥ s there is a matrix W with smallest singular value at least 1 and Q(t) = W Q(s) Wᵀ. Hence the rank of Q and the numbers of its positive and negative eigenvalues are constant in time, and every eigenvalue of Q, ordered by size, keeps its sign and does not decrease in absolute value: |λᵢ(Q(t))| ≥ |λᵢ(Q(s))|. This holds for every initialization and for every multiplicity of the eigenvalues of T.

**Theorem 2 (the limit is an invariant subspace with the same sign pattern).** Φ(t) converges as t → ∞. If Q(0) is nonsingular, the limit Φ∞ spans a T-invariant subspace on which T has exactly p positive and k − p negative eigenvalues. In particular, from a nonsingular Q(0) the dynamics never converges to a critical point whose span is not T-invariant (such as the points with ΦᵀTΦ = 0 in the example below), and never to a critical point with ΦᵀTΦ singular, for example an invariant subspace that contains an eigenvector of T with eigenvalue 0.

**Theorem 3 (which invariant subspace).** Let S be a k-dimensional T-invariant subspace on which T is nonsingular with p positive and k − p negative eigenvalues, spanned by eigenvectors uᵢ of T with eigenvalues μᵢ, and let vⱼ be eigenvectors of T orthogonal to S with eigenvalues λⱼ.
(i) If the eigenvalues of T on S are the p largest positive and the k − p smallest negative eigenvalues of T, counted with multiplicity, then S maximizes f among all Φ whose predictor has at most p positive and at most k − p negative eigenvalues; in particular S is a local maximum of f. This includes ties and zero eigenvalues of T.
(ii) Otherwise S is not a local maximum: turning uᵢ by the angle s towards vⱼ changes f by 2μᵢ(λⱼ − μᵢ)s² + O(s⁴), which is positive for some pair.
(iii) If rank T ≥ k, then Q(0) is nonsingular for almost every Φ(0) on the Stiefel manifold, and for almost every Φ(0) the limit of Theorem 2 is a subspace of the form (i). A set of starts of measure zero converges to subspaces of the form (ii); for example a start that already spans such a subspace stays there.

**Corollary 4 (when the global maximum is reached).** Assume rank T ≥ k, and that the k-th largest absolute value of an eigenvalue of T is larger than the (k + 1)-th or is attained only by eigenvalues of one sign, so that the number q of positive eigenvalues among k eigenvalues of T of largest absolute value is well defined. For almost every start, the dynamics converges to a global maximizer of f exactly when p = q. If T is positive semidefinite, then p = k for every start with nonsingular Q(0), and almost every start reaches the global maximum. If T has eigenvalues of both signs, almost every start with p ≠ q converges to a local maximum of f that is not global; the starts with nonsingular Q(0) and p ≠ q form an open set, which is nonempty for example when k = 1.

**Example.** For the matrix T = [[0.1, 0.9], [0.9, 0.1]] of equation (6) in [1] with k = 1 (eigenvalues 1 and −0.8), Q = q is a scalar, and by Theorem 1 the sign of q is fixed and |q| does not decrease. Every start with q(0) < 0, in particular every start near the eigenvector for −0.8, therefore converges to that eigenvector (the only invariant subspace with a negative eigenvalue), a local maximum of f = q² with value 0.64, and not to the top eigenvector or to the four points with q = 0. This hints at a possible difference from the limit stated for Fig. 3 of [1]; the conclusion there that such starts miss the top eigenvector holds.

## Proofs

**Theorem 1.** With ΦᵀΦ = I, differentiating Q = ΦᵀTΦ gives Q̇ = Φ̇ᵀTΦ + ΦᵀTΦ̇ = QΦᵀT(I − ΦΦᵀ)TΦ + ΦᵀT(I − ΦΦᵀ)TΦQ = QG + GQ, using T = Tᵀ and Q = Qᵀ. G is positive semidefinite since I − ΦΦᵀ is an orthogonal projection. Let W solve Ẇ = G(t)W with W(s) = I. Then W Q(s) Wᵀ solves the same linear equation X' = GX + XG as Q with the same value at s, so Q(t) = W Q(s) Wᵀ. Moreover (WᵀW)' = 2WᵀGW is positive semidefinite, so WᵀW ⪰ I and every singular value of W is at least 1. Sylvester's law of inertia gives the constant numbers of positive, negative and zero eigenvalues. Ostrowski's theorem [4] gives λᵢ(WQWᵀ) = θᵢλᵢ(Q) with θᵢ between the smallest and the largest squared singular value of W, so θᵢ ≥ 1.

**Theorem 2.** The Euclidean gradient of f/4 is TΦQ, and its projection onto the tangent space of the Stiefel manifold with the embedded metric is TΦQ − Φ sym(ΦᵀTΦQ) = TΦQ − ΦQ² = (I − ΦΦᵀ)TΦQ. So the dynamics is the Riemannian gradient flow of the analytic function f/4 on a compact analytic manifold, and it converges to a single critical point by the Łojasiewicz gradient inequality [5], which is local and so applies in charts of the manifold. By the lower bound of Theorem 1, |λᵢ(Q(t))| ≥ |λᵢ(Q(0))| > 0 with constant signs for all t, so Q∞ = Φ∞ᵀTΦ∞ is nonsingular and has the same numbers of positive and negative eigenvalues as Q(0). At a critical point (I − ΦΦᵀ)TΦQ = 0, so (I − ΦΦᵀ)TΦ = 0, that is TΦ∞ = Φ∞Q∞: the span of Φ∞ is invariant, and T restricted to it is similar to Q∞.

**Theorem 3.** (i) For Φ with ΦᵀΦ = I, Cauchy's interlacing theorem gives λᵢ↓(Q) ≤ λᵢ↓(T) and λᵢ↑(Q) ≥ λᵢ↑(T) for i ≤ k, for the eigenvalues sorted downwards and upwards. If Q has at most p positive and at most k − p negative eigenvalues, the square of each positive eigenvalue of Q is therefore at most the square of the corresponding one among the p largest positive eigenvalues of T, and likewise for the negative ones, so f(Φ) is at most the sum F of the squares of the p largest positive and the k − p smallest negative eigenvalues of T. Subspaces of the form (i) attain F. Near S the predictor stays nonsingular with the same signs, so S is a local maximum.
(ii) In an eigenbasis, turning uᵢ by the angle s towards vⱼ keeps the predictor diagonal, since T maps the other basis vectors of S into S and vⱼ to a multiple of itself, with the entry μᵢcos²s + λⱼsin²s in place of μᵢ. So f changes by (μᵢ + (λⱼ − μᵢ)sin²s)² − μᵢ² = 2μᵢ(λⱼ − μᵢ)s² + O(s⁴). If S is not of the form (i), some positive μᵢ has an eigenvalue λⱼ > μᵢ outside S or some negative μᵢ has an eigenvalue λⱼ < μᵢ outside S, and the change is positive. More generally, Φ = (U + VΔ)(I + ΔᵀΔ)^{−1/2} with U = [u₁ … u_k] and V the eigenvectors orthogonal to S gives f = tr M² + 2 Σᵢⱼ μᵢ(λⱼ − μᵢ)Δⱼᵢ² + O(‖Δ‖⁴) with M = diag(μᵢ), so the Hessian of f at S has a positive eigenvalue.
(iii) If rank T ≥ k, det(ΦᵀTΦ) is an analytic function on the Stiefel manifold that does not vanish identically on any connected component (it is nonzero at k orthonormal eigenvectors with nonzero eigenvalues, and for k = n it equals det T), so Q(0) is singular only on a set of measure zero. The time-one map of the flow is a diffeomorphism of the Stiefel manifold, its fixed points are the critical points (f increases strictly along every solution that is not constant), and at a critical point its derivative is the exponential of the Hessian of f/4, which has an eigenvalue above 1 at every subspace of the form (ii). By the stable manifold theorem for maps with non-isolated fixed points in the form of [6], applied in charts, the starts that converge to subspaces of the form (ii) form a set of measure zero. By Theorem 2, the limits of starts with nonsingular Q(0) are invariant subspaces of the forms (i) and (ii).

**Corollary 4.** The global maximizers of f are the spans of k eigenvectors of largest |λ| [1]. Under the assumption on the k-th largest absolute value, every global maximizer has q positive eigenvalues on its span, and the value F of (i) for p ≠ q is smaller than the maximum, since some eigenvalue among the k of largest absolute value is replaced by one of smaller absolute value. With Theorem 3 (iii) this gives the first statement. The set of starts with nonsingular Q(0) and p ≠ q is open, since the signs of the eigenvalues of a nonsingular Q(0) are locally constant.

## Scope and status

| Result | Scope | Status | Posted |
|---|---|---|---|
| Theorem 1 | Symmetric T, every solution of equation (5) of [1], any initialization with Φ(0)ᵀΦ(0) = I, any multiplicities | Claim; uses Sylvester's law of inertia and Ostrowski's theorem [4]; checked numerically | 2026-11-21 |
| Theorem 2 | Symmetric T, Q(0) nonsingular | Claim; uses the Łojasiewicz gradient inequality [5]; checked numerically | 2026-11-21 |
| Theorem 3 | Symmetric T, nonsingular T restricted to S; (iii) for rank T ≥ k and almost every start, while a set of starts of measure zero may end at subspaces of the form (ii) | Claim; uses Cauchy's interlacing theorem and the stable manifold theorem [6]; checked numerically | 2026-11-21 |
| Corollary 4 | rank T ≥ k, and the k-th largest absolute eigenvalue larger than the (k + 1)-th or attained by eigenvalues of one sign; almost every start | Claim | 2026-11-21 |

Not covered: non-symmetric transition matrices, the action-conditional objective of [2] (a sum of trace objectives over actions), finite step sizes and predictors that are not optimal at every time.

## Simulations

[`sim/`](sim/) holds Python scripts with asserts (NumPy):

- `inertia_check.py`: equation (5) integrated by the classical Runge-Kutta method with step 0.02 for 30000 steps, with no re-orthonormalization, for n = 10 and k = 3: 30 random symmetric T and 10 matrices with repeated eigenvalues (0.9 twice, −0.6 three times, and a zero eigenvalue). In all 40 runs the numbers of positive and negative eigenvalues of Q are constant, every ordered |eigenvalue| of Q is non-decreasing (largest decrease 2.7 · 10⁻¹⁵), ΦᵀΦ = I holds to 6.1 · 10⁻¹⁵, and the limit is the subspace of Theorem 3 (projector distance below 10⁻⁴ for distinct eigenvalues, eigenvalues of Q∞ for repeated ones). The global maximum is reached in 21 of the 40 runs.
- `maximum_check.py`: Theorem 3 (i) and (ii): the bound f(Φ) ≤ F from interlacing in 8000 random cases (n from 3 to 8, half of them with tied and zero eigenvalues; largest excess 1.7 · 10⁻¹⁶), equality at the subspaces of the form (i), and the coefficient 2μᵢ(λⱼ − μᵢ) of s² by finite differences.
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
