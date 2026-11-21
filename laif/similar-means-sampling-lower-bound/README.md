# Testing similar means in the quantum sampling model: a lower bound close to √m

Written 21 Nov 2026.

**Setting.** As in [1]: D = (D_1, …, D_m) is a collection of distributions on {0, …, n}. It has γ-similar means if all means E[D_i] lie in one interval of length γn, and it is ε-far from this property if (1/m) Σ_i ‖D_i − D_i*‖_1 > ε for every collection D* with γ-similar means. In the quantum sampling model the algorithm gets a unitary O_B, with its inverse and controlled versions, such that

O_B |0⟩|0⟩|0⟩ = Σ_{i=1}^{m} (1/√m) |i⟩ Σ_{j=0}^{n} √(D_i(j)) |j⟩|φ_{i,j}⟩

with ⟨φ_{i,j}|φ_{i,l}⟩ = δ_{jl}. The task is to tell γ-similar means from ε-far with probability at least 2/3.

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Testing γ-similar means against ε-far, quantum sampling model, lower bound | Ω(m^{1/3} + m^{1/4}/ε) [1]; upper bound Õ(√m/ε) [1] | Ω(r m^{1/2−1/(2r)}) for every r ≥ 2 for which a moment-matching pair (μ_0, μ_1) of order r with parameters (γ, ε_1) exists and every ε < ε_1, for all large enough m | Claim; checked by script |
| Cor 2 | The same, explicit | as above | Ω(r m^{1/2−1/(2r)}) for every even r ≥ 4 when γ ≤ cos(π/r) and ε < 4γ/r³; so the exponent of m is 1/2 − O((ε/γ)^{1/3}) | Claim; checked by script |

In [1] the dependence on m in the sampling model is named as not yet fully understood. Corollary 2 gives m^{3/8} for r = 4, already above m^{1/3}, and the exponent of m tends to 1/2 as ε/γ tends to 0. So the upper bound Õ(√m/ε) of [1] has the right exponent of m up to O((ε/γ)^{1/3}). The argument follows the moment-matching method of [2], adapted to collections in which every distribution carries the same weight 1/m.

A **moment-matching pair of order r with parameters (γ, ε_1)** is a pair of distributions μ_0, μ_1 on [0, 1] with finite rational support such that E_{μ_0}[p^j] = E_{μ_1}[p^j] for j = 1, …, r − 1, μ_0 is supported in an interval J_0 of length γ, and E_{μ_1}[dist(p, J)] ≥ ε_1 for every interval J of length γ.

## The hard instances

Every distribution is a coin on {0, n}: D_i(n) = p_i and D_i(0) = 1 − p_i. Take m even, R = F = m/2, a centre c ∈ J_0, and an integer M ≥ m such that every support point of μ_0 and μ_1 times M is an integer. Let N = mM. For b ∈ {0, 1}, the instance Π_b is drawn as follows. R **random rows** get biases p_1, …, p_R drawn independently from μ_b, and F **filler rows** get bias c. Every row is a set of M positions in [N], of which pM carry the bit 1 and the rest the bit 0. The positions and the names in [m] of the rows are assigned uniformly at random, which gives a function f: [N] → [m] × {0, 1}.

*Simulation.* From the oracle of f, O_B is one query: prepare the uniform superposition over x ∈ [N], write f(x) = (i, b), and put |i⟩ in the first register and |bn⟩ in the second, with |x⟩ as the junk. Each row has exactly M positions, so each i has amplitude 1/√m, and D_i(n) = p_i. The inverse and the controlled versions also cost one query each. So a T-query algorithm in the sampling model gives a T-query algorithm with oracle access to f.

*Promise.* Under Π_0 every bias lies in J_0, so the collection has γ-similar means. Under Π_1, take any D* with γ-similar means, with all means in nJ for an interval J of length γ. For coins, ‖D_i − D_i*‖_1 ≥ 2|E[D_i] − E[D_i*]|/n ≥ 2 dist(p_i, J), so (1/m) Σ_i ‖D_i − D_i*‖_1 ≥ (1/R) Σ_{random rows} dist(p_i, J). The support of μ_1 is finite, so with probability tending to 1 as m → ∞ the empirical frequencies of the R random biases are within ε_1 − ε of μ_1 in ℓ1 distance, and then this average is above ε for every J at once.

## Theorem 1, the proof

Fix a T-query algorithm. By [3] its acceptance probability is a polynomial of degree at most 2T in the indicators [f(x) = ℓ]. Average it over the uniform positions and names. For distinct x_1, …, x_s and labels ℓ_1, …, ℓ_s using u distinct names, the probability that f(x_t) = ℓ_t for all t is the sum, over ordered u-tuples of distinct rows ρ_1, …, ρ_u, of Π_v (k_{ρ_v})_{a_v} (k′_{ρ_v})_{b_v} / ((N)_s (m)_u). Here k_ρ and k′_ρ are the numbers of positions of row ρ with bit 1 and bit 0, a_v and b_v count the labels (v, 1) and (v, 0), and (x)_a is the falling factorial. This formula holds for every function whose rows hold N positions in total and number at most m.

**Lemma 1.** Fix the biases w of all rows but one random row. There is a polynomial G(t, p) of degree at most 2T in t with these properties. (i) G(1, p) is the averaged acceptance probability q_w(p) when that row has bias p. (ii) G(t, p) ∈ [0, 1] for every integer 0 ≤ t ≤ F + 1 and every p ∈ {0, 1/(tM), …, 1} (every p for t = 0). (iii) Writing G(t, p) = Σ_d h_d(p) t^d, each h_d is a polynomial in p of degree at most d.

*Proof.* Let G(t, p) be the averaged acceptance probability for the function in which that row has tM positions, ptM of them with bit 1, and the number of filler rows is F + 1 − t instead of F. The total number of positions is still N, and there are at most m rows of positive size, so (ii) holds and (i) is the case t = 1. In the formula above, the sum over tuples of distinct rows splits by which entries are the special row, filler rows or the other rows. The special row contributes (ptM)_a ((1 − p)tM)_b, a polynomial in t in which every power of p comes with at least the same power of t. The filler rows contribute falling factorials in F + 1 − t, which do not involve p. This gives the degree bound in t and (iii). ∎

**Lemma 2.** If 8T² ≤ M and 8T² ≤ F + 1, then |h_d(p)| ≤ 4 (8T²/(F + 1))^d / (d! (2d − 1)!!) for all p ∈ [0, 1] and d ≥ 1.

*Proof.* A polynomial g of degree D with |g| ≤ 1 on K + 1 equally spaced points of an interval satisfies |g| ≤ 1/(1 − D²/K) on the interval. This follows from the Markov inequality |g′| ≤ (2/length) D² max|g|, since every point is within half a grid step of the grid. For t ≥ 1, apply this to G(t, ·) on [0, 1] with K = tM ≥ 2(2T)². So |G(t, p)| ≤ 2 for all real p ∈ [0, 1] and integer t. Then apply it to G(·, p) on [0, F + 1] with K = F + 1 ≥ 2(2T)², so |G(t, p)| ≤ 4 there. The inequality of V. A. Markov for the d-th derivative on an interval of length L gives |∂_t^d G(0, p)| ≤ 4 (2/L)^d D^{2d}/(2d − 1)!!, and h_d(p) = ∂_t^d G(0, p)/d!. ∎

*Hybrid.* Let H_j be the averaged acceptance probability when the first j random rows draw their bias from μ_1 and the others from μ_0. Then H_{j+1} − H_j = E_w[Σ_p (μ_1(p) − μ_0(p)) q_w(p)]. Let Q(p) = Σ_{d<r} h_d(p). By Lemma 1 (iii) it has degree at most r − 1 in p, so its expectations under μ_0 and μ_1 agree. Hence |H_{j+1} − H_j| ≤ 2 max_p |q_w(p) − Q(p)| ≤ 2 Σ_{d≥r} |h_d(p)|, using Lemma 1 (i). Put x = 16T²/m ≥ 8T²/(F + 1). If x ≤ 1/2, Lemma 2 gives Σ_{d≥r} |h_d| ≤ 8x^r/(r! (2r − 1)!!). Summing over the R = m/2 random rows,

|Pr_{Π_0}[accept] − Pr_{Π_1}[accept]| ≤ 8m x^r / (r! (2r − 1)!!).

A tester accepts with probability at least 2/3 under Π_0. Under Π_1 it accepts with probability at most 1/3 plus the probability that the instance is not ε-far, so for large m the difference is at least 1/6. Either x > 1/2, which means T > √(m/32), or x^r ≥ r!(2r − 1)!!/(48m), which means

T ≥ (√m/4) · (r! (2r − 1)!!/(48m))^{1/(2r)} = Ω(r m^{1/2 − 1/(2r)}).

The conditions of Lemma 2 hold since M ≥ m and F + 1 > m/2. ∎

## Corollary 2, the moment-matching pairs

Let r be even, s ≤ 1/2 and c = 1/2, and take the r + 1 nodes y_k = c + s cos(kπ/r). The weights w_k = 1/Π_{j≠k}(y_k − y_j) alternate in sign and annihilate every polynomial of degree below r. So the normalized positive part μ_1 (even k, including both outer nodes y_0 and y_r) and the normalized negative part μ_0 (odd k) match the moments of orders 1 to r − 1. These are the Chebyshev-Lobatto weights, and each outer node carries mass 1/r in μ_1. μ_0 is supported in J_0 = [c − s cos(π/r), c + s cos(π/r)], of length γ = 2s cos(π/r). Every interval J of length γ satisfies dist(y_0, J) + dist(y_r, J) ≥ 2s − γ, so

E_{μ_1}[dist(p, J)] ≥ (2s − γ)/r ≥ (γ/r)(1 − cos(π/r)) ≥ 4γ/r³ for r ≥ 4.

Rounding the nodes to rationals with a large common denominator keeps exact moment matching, since the weights are recomputed from the rounded nodes, and changes the masses and γ only slightly. So for every ε < 4γ/r³ there is a pair with ε_1 > ε, and Theorem 1 applies. For a given ratio ε/γ, the largest even r with 4γ/r³ > ε gives the exponent 1/2 − O((ε/γ)^{1/3}).

## Scripts

`sim/check_pairs.py` builds the pairs of Corollary 2 for r ∈ {4, 6, 8, 12, 16, 24} and two values of s, in exact rational arithmetic. It checks equal total mass and equal moments of orders 1 to r − 1, that μ_0 lies in an interval of length γ, and computes ε_1 exactly as a minimum over intervals of length γ. It also checks the two polynomial inequalities of Lemma 2 on 300 random polynomials.

```
python sim/check_pairs.py
 r      gamma       eps_1     outer mass   eps_1*r^3/gamma
 4  0.705692  7.308e-02  0.50000     6.627
 6  0.864294  2.228e-02  0.33333     5.569
 8  0.922032  9.496e-03  0.25000     5.273
12  0.963994  2.834e-03  0.16667     5.080
16  0.978824  1.199e-03  0.12500     5.015
24  0.989462  3.558e-04  0.08333     4.970
 4  0.141422  1.464e-02  0.50000     6.627
 6  0.173206  4.466e-03  0.33334     5.569
 8  0.184776  1.903e-03  0.25000     5.273
12  0.193186  5.679e-04  0.16669     5.080
16  0.196158  2.402e-04  0.12503     5.015
24  0.198288  7.130e-05  0.08330     4.971
moment-matching pairs checked (exact rational arithmetic)
grid and Markov inequalities checked on 300 random polynomials
```

**Not formalized:** all of the folder.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check scripts, and to draft the text.

## References

1. C. Gao, Y. Xu, S. Zheng, L. Li. Quantum speedups for testing similar means. arXiv:2608.00741, 2026.
2. C. Kayal, F. Magniez, S. Sen, D. Szabó. Quantum query lower bounds from classical moment matching. arXiv:2611.05117, 2026.
3. R. Beals, H. Buhrman, R. Cleve, M. Mosca, R. de Wolf. Quantum lower bounds by polynomials. Journal of the ACM 48, 2001.
