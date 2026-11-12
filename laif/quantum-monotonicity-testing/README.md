# Quantum testing of monotone distributions with n^{1/3} uses of the code

2026-11-12

## Problem

A distribution p on [n] = {1, …, n} is monotone if p_1 ≥ p_2 ≥ … ≥ p_n. A tester must accept every monotone p and reject every p whose total variation distance to all monotone distributions exceeds ε, each with probability at least 2/3. Access is through "the code" for p [3]: a unitary that prepares a purification of p, together with its inverse, and cost counts their uses.

Previous best bounds: classically O(√n/ε² + log(n)/ε⁴) samples, which is Θ(√n/ε²) for ε > n^{−1/4}(log n)^{1/2} [1, Theorem 3 and Corollary 1]; see also [2]. To our knowledge no quantum bound has been stated. For uniformity testing, a special case, the code gives O(n^{1/3}/ε^{4/3}) for ε ≥ n^{−1/2} [3, Theorem 1.1], and Ω(n^{1/3}) and Ω(1/ε) are necessary [3].

## Results

**Theorem 1.** For 2/√n ≤ ε ≤ 1 there is a quantum tester for monotonicity on [n] that uses the code

O( n^{1/3}/ε^{4/3} + K polylog(K)/ε² )   times, with K = O(log(n)/ε²),

that is Õ(n^{1/3}/ε^{4/3} + log(n)/ε⁴), where Õ hides factors polylogarithmic in log(n)/ε. This is at most the classical O(√n/ε² + log(n)/ε⁴) of [1] in every regime up to these factors, and the first term dominates for ε ≥ n^{−1/8} log^{3/8}(n). The tester is computationally efficient.

**Theorem 2.** Every quantum tester for monotonicity with ε ≤ 0.4 uses the code Ω(n^{1/3}) times for even n ≥ 4000, and Ω(1/ε) times for every n ≥ 2.

So the dependence on n is n^{1/3} for constant ε, against √n for samples [1].

## Algorithm

Let m = ⌈200/ε²⌉ + 1 and partition [n] into consecutive buckets B_0, B_1, …, B_{K−1} with lengths ℓ_j:

- m singletons, the elements 1, …, m;
- then, for k = 2, …, m − 1, ⌈m/k⌉ buckets of length k;
- then one bucket of length m, and after each bucket of length ℓ ≥ m one of length ⌈(1 + 1/m)ℓ⌉, until [n] is covered, with the last bucket cut at n.

This gives K ≤ m(ln n + 3) = O(log(n)/ε²) buckets; if m ≥ n, all buckets are singletons. Let w_j = p(B_j).

1. *Learn.* Let η = ε²/(300K). Estimate all K bucket masses at once to additive error η with the algorithm for multiple expectation values of [4, Theorem 37], which gives z_j, and set the upper estimate ŵ_j = z_j + η.
2. *Hypothesis.* Form the shifted flattening ŝ. A singleton keeps its value, ŝ_i = ŵ_j for B_j = {i}. Every element of a bucket B_j of length at least 2 gets the average of the previous bucket, ŝ_i = ŵ_{j−1}/ℓ_{j−1}. Let Z = Σ_i ŝ_i and q = ŝ/Z.
3. *Check the hypothesis.* Compute the total variation distance from q to the monotone distributions by a linear program over the K bucket values. A monotone distribution that is closest to a bucket-constant q can be taken bucket-constant, since averaging over the buckets keeps it monotone and does not increase the distance. If this distance exceeds ε/4, reject.
4. *Test.* Apply the kernel F_q below to the code for p′ = (p + u_n)/2. Then run the uniformity tester of [3, Theorem 4.1] on [6n] with θ = ε²/17 and B = 2, and output its answer.

*The kernel F_q.* Let q′ = (q + u_n)/2 and c_i = ⌊6n q′_i⌋ ≥ 3. Give each i a private set S_i of c_i elements of [6n], and let R be the remaining r = 6n − Σ c_i elements. F_q maps i to a uniform element of S_i with probability c_i/(6n q′_i), and otherwise to a uniform element of R. Adding this classical post-processing to the code gives the code for F_q(p′), as in [3, Appendix A]. It satisfies:

- F_q(q′) is uniform on [6n].
- d_TV(F_q(p′), u_{6n}) ≥ (2/3) d_TV(p′, q′) = d_TV(p, q)/3, because the mass on the private sets alone gives (1/2) Σ_i |p′_i − q′_i| c_i/(6n q′_i), and c_i/(6n q′_i) ≥ 2/3.
- Every value of F_q(p′) is at most max_i (p′_i/q′_i)/(6n).
- χ²(F_q(p′) ‖ u_{6n}) ≤ χ²(p′ ‖ q′) ≤ χ²(p ‖ q)/2, by data processing and joint convexity.

## Proofs

**Lemma 3 (shifted flattening).** Let p be monotone, w_j = p(B_j), and s the shifted flattening built from the exact masses w. Then p_i ≤ s_i for every i, and Σ_i s_i ≤ 1 + 4/(m − 1). If upper estimates ŵ_j ≥ w_j have total excess Δ = Σ_j (ŵ_j − w_j), then p ≤ ŝ, Z ≤ 1 + 4/(m − 1) + 3Δ, χ²(p ‖ q) ≤ Z − 1 and p_i/q_i ≤ Z.

*Proof.* For a singleton, s_i = p_i. For i in a bucket B_j of length at least 2, every element of B_{j−1} lies before i, so w_{j−1}/ℓ_{j−1} ≥ p_i.

For the total, Σ_i s_i − 1 = Σ_{j ≥ m} (ℓ_j/ℓ_{j−1} − 1) w_{j−1} + w_{m−1} − w_{K−1}, where w_{m−1} = p_m is the last singleton. This holds because Σ_{j≥m} ℓ_j w_{j−1}/ℓ_{j−1} = Σ_{j≥m} w_{j−1} + Σ_{j≥m}(ℓ_j/ℓ_{j−1} − 1) w_{j−1}. The ratio exceeds 1 only where the length grows:

- *From k to k + 1 for k ≤ m − 1.* The cost is w_{j−1}/k ≤ p_{x_k}, where x_k is the first element of the last bucket of length k (x_1 = m). The interval (x_{k−1}, x_k] holds k⌈m/k⌉ − 1 ≥ m − 1 elements, each at least p_{x_k}.
- *In the geometric part.* ℓ_{j+1}/ℓ_j − 1 ≤ 1/m + 1/ℓ_j ≤ 2/m, which costs at most 2/m in total.

With a = p_1 + … + p_m, the last singleton and the first transition together cost 2p_m ≤ 2a/m, and the other transitions cost Σ_{k≥2} p_{x_k} ≤ (1 − a)/(m − 1). Since 2/m ≥ 1/(m − 1), the total is at most 2/m + 2/m ≤ 4/(m − 1).

With upper estimates, each excess ŵ_j − w_j enters Z once with weight 1 and once with weight ℓ_{j+1}/ℓ_j ≤ 2, which gives the bound on Z. Since p_i ≤ ŝ_i, Σ_i p_i²/ŝ_i ≤ Σ_i p_i = 1. Hence χ²(p ‖ q) = Z Σ_i p_i²/ŝ_i − 1 ≤ Z − 1, and p_i/q_i = Z p_i/ŝ_i ≤ Z. ∎

**Lemma 4 (upper estimates).** Apply [4, Theorem 37] to the state ρ = Σ_j w_j |j⟩⟨j| on the bucket register, whose purification is prepared by one use of the code followed by the classical map from an element to its bucket, with E_j = |j⟩⟨j|, ε_j = η and failure probability 0.03. Since the E_j are orthogonal projectors, ‖Σ_j E_j²/η²‖ = 1/η², so σ = (2 ln(67K))^{1/2}/η and the algorithm makes O(K polylog(K)/ε²) uses of the code and its inverse. With probability at least 0.97, |z_j − w_j| ≤ η for all j, hence ŵ_j ≥ w_j and Δ = Σ_j (ŵ_j − w_j) ≤ 2Kη = ε²/150. ∎

*Proof of Theorem 1.*

*Completeness.* Let p be monotone. On the event of Lemma 4, Lemma 3 gives Z ≤ 1 + ε²/50 + ε²/50 and χ²(p ‖ q) ≤ 0.04ε². So d_TV(p, q) ≤ (1/2)(χ²)^{1/2} ≤ 0.1ε, and step 3 passes, since p is monotone. The kernel gives χ²(F_q(p′) ‖ u_{6n}) ≤ 0.02ε² ≤ 0.99θ. Moreover p′_i/q′_i ≤ max(1, p_i/q_i) ≤ Z ≤ 2, so every value of F_q(p′) is at most 2/(6n). Since θ = ε²/17 ≥ 1/(6n) for ε ≥ 2/√n, [3, Theorem 4.1] accepts with probability at least 0.99.

*Soundness.* Let p be ε-far from monotone. If step 3 does not reject, q is ε/4-close to a monotone distribution, so d_TV(p, q) ≥ 3ε/4. This needs nothing from step 1. Then d_TV(F_q(p′), u_{6n}) ≥ ε/4, and the distance d_H² = Σ_i (√a_i − √b_i)² used in [3] is at least d_TV² ≥ ε²/16 > θ. So [3, Theorem 4.1] rejects with probability at least 0.99.

*Cost.* Step 1 uses O(K polylog(K)/ε²) codes, and step 4 uses O((6n)^{1/3}/θ^{2/3}) = O(n^{1/3}/ε^{4/3}). ∎

*Proof of Theorem 2.*

*The bound Ω(n^{1/3}).* Distinguishing a one-to-one f: [n] → [n] from a two-to-one f takes Ω(n^{1/3}) quantum queries [5, 6]. Given f, pick a uniformly random permutation π of [n] and let p be the law of π(f(x)) for uniform x. One use of the code for p costs one query to f. If f is one-to-one, p is uniform, hence monotone. If f is two-to-one, p is uniform on a uniformly random set T of n/2 elements.

Such a p is more than 0.4-far from monotone with probability at least 0.99 for n ≥ 4000. For a monotone g and positions z < t with z ∉ T and t ∈ T, |p_z − g_z| + |p_t − g_t| ≥ g_z + 2/n − g_t ≥ 2/n. A greedy matching of such pairs has n/2 − max_k(T_k − (k − T_k))⁺ pairs, where T_k = |T ∩ [k]|. So d_TV(p, monotone) ≥ 1/2 − max_k(2T_k − k)⁺/n. By the tail bound for sampling without replacement, P(2T_k − k ≥ 0.09n) ≤ exp(−0.004n) for each k, and n exp(−0.004n) < 0.01 for n ≥ 4000.

A tester with ε = 0.4 and success probability 2/3 therefore solves the collision problem with probability at least 0.65.

*The bound Ω(1/ε).* On [2], the distribution (1/2 − ε, 1/2 + ε) is ε-far from monotone and (1/2 + ε, 1/2 − ε) is monotone. Distinguishing the two needs Ω(1/ε) uses of the code (see [3]). ∎

## Check

`sim/check.py` asserts the following:

- For partitions with n up to 10⁶ and m ∈ {5, 20, 100}, and for five families of monotone distributions (sorted exponentials, power laws, steps with sharp drops, uniform prefixes, point masses with tails), the bucket count is at most m(ln n + 3), p ≤ s, and Σ s − 1 ≤ 4/(m − 1). The largest observed value is 1.81/(m − 1).
- With random upper estimates, the bounds on Z, χ² and p/q hold.
- On random instances with n ≤ 40, F_q(q′) is uniform, and the TV, maximum-value and χ² properties of F_q hold.
- The matching bound lies below the exact linear-program distance to monotonicity for random half sets with n ≤ 120. At n = 4000 the matching bound is never below 0.4 in 1000 samples.
- The linear program over bucket values equals the full one for bucket-constant q.

Output is in `sim/out.txt`.

## Scope

- Written proofs with numerical checks. The uniformity tester [3, Theorem 4.1] (with its constant B = 2), the estimation of multiple expectation values [4, Theorem 37] (which uses controlled versions of the code) and the collision lower bound [5, 6] are used as stated.
- The learning term log(n)/ε⁴ matches the classical one of [1] up to polylogarithmic factors; the gain is in the term that depends on n.
- Only non-increasing distributions on [n] are treated, and the range ε ≥ 2/√n.

## References

[1] J. Acharya, C. Daskalakis, G. Kamath. Optimal testing for properties of distributions. NeurIPS 2015. arXiv:1507.05952.

[2] C. L. Canonne, I. Diakonikolas, T. Gouleakis, R. Rubinfeld. Testing shape restrictions of discrete distributions. arXiv:1507.03558.

[3] C. L. Canonne, R. Kothari, R. O'Donnell. Uniformity testing when you have the source code. arXiv:2411.04972.

[4] J. van Apeldoorn, A. Cornelissen, A. Gilyén, G. Nannicini. Quantum tomography using state-preparation unitaries. arXiv:2207.08800.

[5] S. Aaronson, Y. Shi. Quantum lower bounds for the collision and the element distinctness problems. Journal of the ACM 51(4) (2004).

[6] A. Ambainis. Polynomial degree and lower bounds in quantum complexity: collision and element distinctness with small range. Theory of Computing 1 (2005).

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
