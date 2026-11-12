# Random-basis measurements of pure states: three bases lose all information at some state, four keep a positive fraction

Written 11 Nov 2026.

## Problem

A measurement that picks one of K orthonormal bases at random, measures in it and records the basis label is a standard state-independent readout for sensing. For a pure state ψ of a d-level system and a direction u ⊥ ψ, write I(u) for the information of the measurement (the variance of the score) and J(u) = 4‖u‖² for the quantum limit. Reference [1] measures a measurement M by its retained fraction

c(M) = inf over ψ and u of I(u)/J(u),

with the information evaluated at the state itself (outcomes of probability zero are left out) [1, Eq. (2), App. A].

[1, Theorem 6] shows that for K ≥ 5 independent uniformly random bases, mixed with equal weights, there is a constant c_K > 0, free of d, with c(M) ≥ c_K with probability at least 1 − 2^{−d} in all large dimensions, and that c(M) > 0 almost surely when K(d − 1) > 4d. It also shows that at least three bases are necessary. In its outlook, [1, Sec. VIII] writes: "Three random bases are necessary and five suffice in large dimensions, and whether three or four suffice is open."

## Result

- **Theorem 1 (four bases).** For K ≥ 4 independent uniformly random bases, any positive weights and every d ≥ 2, c(M) > 0 almost surely. The condition K(d − 1) > 4d of [1] never holds for K = 4, and for K = 5 it needs d ≥ 6.
- **Theorem 2 (three bases, every choice).** For d = 3 and every d ≥ 5, every measurement that mixes three orthonormal bases, with any weights, has c(M) = 0. The proof uses a classical non-immersion theorem for complex projective space [3, 4]; for d = 3 and for a family of dimensions including d = 5, 9, 10, 17 to 21 we also give self-contained proofs. More generally, a measurement with N outcomes has c(M) = 0 when N − 1 ≤ 4(d − 1) − 2α(d − 1) + ε, with α the number of binary ones and ε ∈ {−1, 0, 1} given below.
- **Proposition 3 (three bases, d = 4).** For each d from 3 to 12, and so in particular for d = 4, the one dimension d ≥ 3 not covered by Theorem 2, three uniformly random bases have c(M) = 0 with positive probability (computer-assisted proof in exact rational arithmetic). Numerically, every one of 70 sampled triples with d between 3 and 12 has c(M) = 0, at a state where every outcome has positive probability.

So three bases do not suffice: in every dimension d ≥ 3 other than 4 no choice of three bases keeps any information in the worst case, and in d = 4 random triples fail with positive probability. No guarantee of the form of [1, Theorem 6] holds for K = 3. (In d = 2 three bases can work: the eigenbases of X, Y and Z keep 1/3 [1].) Four random bases keep a positive fraction in every dimension, almost surely. Whether that fraction can be bounded below independently of d, as for K ≥ 5, is not settled here.

## The key identity

Let q_s(ψ) = |⟨s|ψ⟩|² be the outcome probabilities, up to the weights. They define a smooth map Φ from the complex projective space CP^{d−1} of pure states to R^N, whose image lies in an affine subspace of dimension N − 1 (dimension K(d − 1) for K bases). Its differential at ψ in the direction u is dq_s(u) = 2 Re⟨ψ|s⟩⟨s|u⟩.

**Lemma 0.** I(u) = 0 if and only if dΦ_ψ(u) = 0, and c(M) > 0 if and only if Φ is an immersion (its differential is injective at every state).

*Proof.* I(u) = Σ_{s: q_s > 0} w_s (dq_s(u))²/q_s, a sum of nonnegative terms. For an outcome with q_s = 0, dq_s(u) = 0 anyway. So I(u) = 0 exactly when dq_s(u) = 0 for all s. Each term is continuous where q_s > 0. Near a state where q_s = 0 the term is nonnegative, and at that state it is left out, so I is lower semicontinuous on the compact set Ω = {(ψ, u): ‖ψ‖ = ‖u‖ = 1, ⟨ψ|u⟩ = 0}. Hence the infimum of I/J over Ω is attained, and it is positive exactly when I never vanishes. ∎

## Proof of Theorem 1

Fix K bases U_1, …, U_K (the columns are the basis vectors) and let Z be the set of (U_1, …, U_K, ψ, u) with (ψ, u) ∈ Ω and I(u) = 0 at ψ. Since the condition is invariant under (ψ, u) ↦ e^{iα}(ψ, u), we may restrict to the slice Ω′ ⊂ Ω where the first nonzero coordinate of ψ is real and positive, of real dimension 4d − 5. Z is a semialgebraic set (polynomial equations, with "q_s = 0 or dq_s(u) = 0" for each outcome).

*Fibres.* For fixed (ψ, u), the condition on each basis U is the same, and by unitary invariance (replace U, ψ, u by WU, Wψ, Wu) the set S(ψ, u) of blind bases is a translate of S(e_1, e_2). In S(e_1, e_2) the condition reads: for every x, either U_{1x} = 0 or Re(U_{1x} conj U_{2x}) = 0. It involves only the first two rows (r_1, r_2) of U, an orthonormal pair, and U ↦ (r_1, r_2) is a submersion onto the space of orthonormal pairs (dimension 4d − 4).
- Fix the set D of the m coordinates where r_1 vanishes (m ≤ d − 1). Such r_1 form a set of dimension 2(d − m) − 1.
- Given r_1, r_2 lies in the complement of r_1 (real dimension 2d − 2), and must satisfy the d − m conditions Re(r_{1x} conj r_{2x}) = 0, x ∉ D. These functionals act on different coordinates and are independent. Their sum is the real part of Σ_x r_{1x} conj r_{2x}, which vanishes on the complement, and the imaginary part of that sum is independent of them. So on the complement they have rank d − m − 1.

So the pairs with dark set D have dimension (2d − 2m − 1) + (d + m − 2) = 3d − m − 3 ≤ 3d − 3, a codimension of at least d − 1 in the space of pairs. Hence S(e_1, e_2) has codimension at least d − 1 in U(d).

*Count.* The dimension of Z is at most the dimension of the base plus that of the largest fibre:

dim Z ≤ (4d − 5) + K(d² − d + 1),

which is less than dim U(d)^K = Kd² exactly when K(d − 1) > 4d − 5, that is, for K ≥ 4 and every d ≥ 2. The projection of Z to U(d)^K is semialgebraic of smaller dimension, so it has measure zero for the invariant measure. Outside it, no (ψ, u) has I(u) = 0, and Lemma 0 gives c(M) > 0. ∎

For K = 3 the same count gives (4d − 5) − 3(d − 1) = d − 2, so for d ≥ 3 the zeros are expected to form a set of dimension d − 2, and they do in every sampled case (Proposition 3).

## Proof of Theorem 2

By Lemma 0, c(M) > 0 would make Φ an immersion of the closed manifold CP^n, of real dimension 2n, into an affine space of dimension 3n (for K bases the probabilities lie in an affine subspace of dimension K(d − 1); for a general measurement, of dimension at most N − 1). An immersion in R^m gives one in every larger R^{m′}, so it suffices that CP^n does not immerse in R^{3n}.

*d ≥ 5 (n ≥ 4).* CP^n does not immerse in R^{4n−2α(n)+ε(n)}, with α(n) the number of ones in the binary expansion of n, ε(n) = 0 if n is even and α(n) ≡ 1 (mod 4), ε(n) = 1 if n is even and α(n) ≡ 2, 3 (mod 4), and ε(n) = −1 otherwise [3, Theorem 1.3], [4]. Since ε(n) ≥ −1, it suffices that 3n ≤ 4n − 2α(n) − 1, that is, n ≥ 2α(n) + 1. For 4 ≤ n ≤ 8 this holds since α(n) ≤ 3 and α(7) = 3. For 2^r ≤ n < 2^{r+1} with r ≥ 3 and n ≥ 9, α(n) ≤ r + 1 and 2r + 3 ≤ max(9, 2^r) ≤ n.

*d = 3 (n = 2).* Here ε(2) = 0 and 4n − 2α(n) = 6 = 3n, so the same theorem applies. A direct proof: an immersion of CP² in R⁶ would have an oriented normal bundle ν of rank 2, since CP² is simply connected. The total rational class of CP² is (1 + x²)³ [2, Example 15.6], so p₁(ν) = −p₁(CP²) = −3x². For an oriented plane bundle p₁(ν) = e(ν)² [2, Corollary 15.8], and e(ν) = m x with m an integer, so m² = −3, which is impossible.

For a general measurement with N outcomes the same argument gives c(M) = 0 whenever N − 1 ≤ 4n − 2α(n) + ε(n). For example, when d − 1 ≥ 2 is a power of two, every measurement with at most 4d − 5 outcomes has c(M) = 0.

*An elementary version.* For many n the mod 2 classes alone suffice. The normal bundle of an immersion in R^{2n+k} has rank k, so the mod 2 dual classes w̄ = w(T)^{−1} vanish above degree k [2, Sec. 4]. For CP^n, w(T) = (1 + x)^{n+1} with x the generator of H²(CP^n; Z/2) [2, Theorem 14.10], and w̄ = Σ_{i ≤ n} C(n + i, i) x^i mod 2. C(n + i, i) is odd exactly when n and i share no binary digit, so for n = 2^r + m (0 ≤ m < 2^r) the top term has i(n) = 2^r − 1 − m, and CP^n does not immerse in R^{2n+2i(n)−1}. This excludes R^{3n} when 3m < 2^r − 2, for example for d = 5, 9, 10, 17 to 21 and 33 to 42. ∎

The argument uses no randomness: in these dimensions every three bases, including three mutually unbiased bases, have a state and direction that they do not see at all. In d = 4 topology cannot decide, since CP³ embeds in R⁹; Proposition 3 covers it. The analogous topological argument for distinguishing all pure states, with embeddings in place of immersions, is in [5, 6].

## Proof of Proposition 3

For each d, three bases are built as U = (1 − iH)(1 + iH)^{−1} from rational self-adjoint H, so they are exactly unitary with entries in Q(i). A zero (ψ, u) of the system

Re⟨ψ|b⟩⟨b|u⟩ = 0 for every basis vector b,  Im⟨ψ|u⟩ = 0,  ‖ψ‖ = ‖u‖ = 1,  Im ψ_1 = 0

is found in floating point. The last outcome of the second and third basis is dropped, since its equation follows from the others. Fixing d − 2 coordinates gives a square system of 4d quadratic equations. In exact rational arithmetic the check computes, at the floating-point point x_0, β = ‖J(x_0)^{−1}‖, η = ‖J(x_0)^{−1}F(x_0)‖ and a bound L on how fast the Jacobian J changes, all in the maximum norm. Since h = βLη < ½, the system has a root within 2η of x_0 at which J is invertible [7]. Every outcome probability at x_0 exceeds the change that this distance can cause, so the root is a state where every outcome is possible.

At the root, the Jacobian in (ψ, u) of the 3d + 2 kept equations is onto. By the implicit function theorem the zero persists, at a state where every outcome is possible, for all triples of bases near the given one, and the dropped equations still follow for every triple of unitary bases. So c(M) = 0 on an open set of triples, which has positive probability. ∎

The values of h are between 1.6 · 10⁻¹⁴ and 7 · 10⁻¹², and the smallest outcome probabilities at the roots between 5 · 10⁻⁵ and 10⁻² (`sim/out.txt`).

## Check

`sim/check.py` (about one minute) checks:
1. the rank d − m − 1 in the fibre count of Theorem 1, for d = 2 to 8 and every m;
2. zeros at states where every outcome is possible, for 10 random triples each at d = 3, 4, 5, 6, 8, 10, 12;
3. the exact certificates of Proposition 3 for d = 3 to 12 (`sim/cert3.py`);
4. that four random bases give no zero (5 instances each at d = 3 to 6), as Theorem 1 says;
5. the inequality n ≥ 2α(n) + 1 for 4 ≤ n < 10⁵ and 3n ≤ 4n − 2α(n) + ε(n) at n = 2 (Theorem 2), the top degree i(n) of the mod 2 dual class for n < 200, and a zero for three mutually unbiased bases in d = 5.

The output is in `sim/out.txt`.

## References

1. W. Li, J. Liu. The exact information cost of randomized measurements in quantum metrology. arXiv:2611.00599 (2026).
2. J. W. Milnor, J. D. Stasheff. Characteristic Classes. Princeton University Press (1974).
3. D. M. Davis. Some new immersion results for complex projective space. arXiv:math/0602472 (2006).
4. B. J. Sanderson, R. L. E. Schwarzenberger. Non-immersion theorems for differentiable manifolds. Proc. Cambridge Philos. Soc. 59, 312-322 (1963).
5. T. Heinosaari, L. Mazzarella, M. M. Wolf. Quantum tomography under prior information. Commun. Math. Phys. 318, 355-374 (2013), arXiv:1109.5478.
6. C. Carmeli, T. Heinosaari, J. Schultz, A. Toigo. How many orthonormal bases are needed to distinguish all pure quantum states? Eur. Phys. J. D 69, 179 (2015), arXiv:1504.01590.
7. J. M. Ortega, W. C. Rheinboldt. Iterative Solution of Nonlinear Equations in Several Variables. Academic Press (1970), Sec. 12.6.
