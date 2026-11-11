# Random-basis measurements of pure states: three bases lose all information at some state, four keep a positive fraction

Written 11 Nov 2026.

## Problem

A measurement that picks one of K orthonormal bases at random, measures in it and records the basis label is a standard state-independent readout for sensing. For a pure state ψ of a d-level system and a direction u ⊥ ψ, write I(u) for the information of the measurement (the variance of the score) and J(u) = 4‖u‖² for the quantum limit. Reference [1] measures a measurement M by its retained fraction

c(M) = inf over ψ and u of I(u)/J(u),

with the information evaluated at the state itself (outcomes of probability zero are left out) [1, Eq. (2), App. A].

[1, Theorem 6] shows that for K ≥ 5 independent uniformly random bases there is a constant c_K > 0, free of d, with c(M) ≥ c_K with probability at least 1 − 2^{−d} in all large dimensions, and that c(M) > 0 almost surely when K(d − 1) > 4d. It also shows that at least three bases are necessary. In its outlook, [1, Sec. VIII] writes: "Three random bases are necessary and five suffice in large dimensions, and whether three or four suffice is open."

## Result

- **Theorem 1 (four bases).** For K ≥ 4 independent uniformly random bases, any positive weights and every d ≥ 2, c(M) > 0 almost surely. The condition K(d − 1) > 4d of [1] never holds for K = 4, and for K = 5 it needs d ≥ 6.
- **Theorem 2 (three bases, every choice).** Write n = d − 1 = 2^r + m with 0 ≤ m < 2^r. If r ≥ 2 and 3m < 2^r − 2, then every measurement that mixes three orthonormal bases, with any weights, has c(M) = 0. This covers d = 5, 9, 10, 17 to 21, 33 to 42, 65 to 85, and in general about a third of each range 2^r < d ≤ 2^{r+1}. More generally, every measurement with N outcomes has c(M) = 0 when N − 1 < 2n + 2(2^r − 1 − m); for d − 1 a power of two this means N ≤ 4d − 6.
- **Proposition 3 (three bases, small d).** For each d from 3 to 12, three uniformly random bases have c(M) = 0 with positive probability (computer-assisted proof in exact rational arithmetic). Numerically, every one of 70 sampled triples with d between 3 and 12 has c(M) = 0, at a state where every outcome has positive probability.

So three bases do not suffice: in infinitely many dimensions no choice of three bases keeps any information in the worst case, so no guarantee of the form of [1, Theorem 6] holds for K = 3. Four random bases keep a positive fraction in every dimension, almost surely. Whether that fraction can be bounded below independently of d, as for K ≥ 5, is not settled here.

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

By Lemma 0, c(M) > 0 would make Φ an immersion of the closed manifold CP^n, of real dimension 2n, into R^{N−1}, with N − 1 = 3n for three bases. If a closed manifold immerses in R^{2n+k}, its normal bundle has rank k, and the mod 2 characteristic classes of the normal bundle, the dual classes w̄ = w(T)^{−1}, vanish above degree k [2]. For CP^n the total mod 2 class of the tangent bundle is (1 + x)^{n+1}, with x the generator of H²(CP^n; Z/2) and x^{n+1} = 0 [2]. So

w̄ = (1 + x)^{−(n+1)} = Σ_{i ≤ n} C(n + i, i) x^i  (mod 2).

C(n + i, i) is odd exactly when adding n and i in binary has no carries, that is, when i and n share no binary digit. For n = 2^r + m the largest such i ≤ n is i(n) = 2^r − 1 − m, so w̄ ≠ 0 in degree 2i(n), and CP^n does not immerse in R^{2n+2i(n)−1}. For three bases this excludes an immersion when 3n < 2n + 2i(n), that is, when 2(2^r − 1 − m) > 2^r + m, or 3m < 2^r − 2. For a general measurement it excludes N − 1 < 2n + 2i(n). ∎

The argument uses no randomness: in these dimensions every three bases, including three mutually unbiased bases, have a state and direction that they do not see at all. The analogous topological argument for distinguishing all pure states, with embeddings in place of immersions, is in [3, 4].

## Proof of Proposition 3

For each d, three bases are built as U = (1 − iH)(1 + iH)^{−1} from rational self-adjoint H, so they are exactly unitary with entries in Q(i). A zero (ψ, u) of the system

Re⟨ψ|b⟩⟨b|u⟩ = 0 for every basis vector b,  Im⟨ψ|u⟩ = 0,  ‖ψ‖ = ‖u‖ = 1,  Im ψ_1 = 0

is found in floating point. The last outcome of the second and third basis is dropped, since its equation follows from the others. Fixing d − 2 coordinates gives a square system of 4d quadratic equations. In exact rational arithmetic the check computes, at the floating-point point x_0, β = ‖J(x_0)^{−1}‖, η = ‖J(x_0)^{−1}F(x_0)‖ and a bound L on how fast the Jacobian J changes, all in the maximum norm. Since h = βLη < ½, the system has a root within 2η of x_0 at which J is invertible [5]. Every outcome probability at x_0 exceeds the change that this distance can cause, so the root is a state where every outcome is possible.

At the root, the Jacobian of the full system in (ψ, u) is onto. By the implicit function theorem the zero persists, at a state where every outcome is possible, for all triples of bases near the given one, and the dropped equations still follow for every triple of unitary bases. So c(M) = 0 on an open set of triples, which has positive probability. ∎

The values of h are between 2 · 10⁻¹⁴ and 7 · 10⁻¹², and the smallest outcome probabilities at the roots between 5 · 10⁻⁵ and 10⁻² (`sim/out.txt`).

## Check

`sim/check.py` (about one minute) checks:
1. the rank d − m − 1 in the fibre count of Theorem 1, for d = 2 to 8 and every m;
2. zeros at states where every outcome is possible, for 10 random triples each at d = 3, 4, 5, 6, 8, 10, 12;
3. the exact certificates of Proposition 3 for d = 3 to 12 (`sim/cert3.py`);
4. that four random bases give no zero (5 instances each at d = 3 to 6), as Theorem 1 says;
5. the top degree i(n) of the dual class for n < 200, the list of dimensions of Theorem 2, and a zero for three mutually unbiased bases in d = 5.

The output is in `sim/out.txt`.

## References

1. W. Li, J. Liu. The exact information cost of randomized measurements in quantum metrology. arXiv:2611.00599 (2026).
2. J. W. Milnor, J. D. Stasheff. Characteristic Classes. Princeton University Press (1974), Sec. 4 and Theorem 14.10.
3. T. Heinosaari, L. Mazzarella, M. M. Wolf. Quantum tomography under prior information. Commun. Math. Phys. 318, 355-374 (2013), arXiv:1109.5478.
4. C. Carmeli, T. Heinosaari, J. Schultz, A. Toigo. How many orthonormal bases are needed to distinguish all pure quantum states? Eur. Phys. J. D 69, 179 (2015), arXiv:1504.01590.
5. J. M. Ortega, W. C. Rheinboldt. Iterative Solution of Nonlinear Equations in Several Variables. Academic Press (1970), Sec. 12.6.
