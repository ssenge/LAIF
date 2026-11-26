# Quantum lower bounds for local search via vertex congestion

Written 25 Nov 2026, Theorem 4 added 26 Nov 2026.

**Setting.** As in [1]: G = (V, E) is a connected undirected graph with n vertices, and f : V → ℝ is given by an oracle that answers |v, a⟩ ↦ |v, a ⊕ f(v)⟩. The task is to find a local minimum, a vertex v with f(v) ≤ f(u) for every neighbour u, with success probability at least 2/3 for every f. An all-pairs path system P = {P^{u,w}} assigns a simple path from u to w to every ordered pair (u, w), with P^{u,u} = (u). Its vertex congestion is the largest number of paths of P that contain a vertex; g denotes the least vertex congestion over all such systems. Every vertex lies on the n paths that start at it, so g ≥ n, and g ≤ n².

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Quantum query complexity of local search on G, for g ≤ n^{2−δ} with a constant δ > 0 | Ω(n^{3/4}/√g) [1, Theorem 1] | Ω_δ(n^{2/3}/g^{1/3}) | Claim |
| Cor 2 | The same on Δ-regular β-expanders with constant Δ and β | Ω(n^{1/4}/√(log n)) [1, Corollary 2]; upper bound O(n^{1/3}) [5, Theorem 3.2] | Ω((n/log n)^{1/3}), which matches the upper bound up to the factor (log n)^{1/3} | Claim |
| Cor 3 | The same on vertex-transitive graphs of diameter d ≤ n^{1−δ}/4 and degree Δ | Ω(n^{1/4}/√d), implied by [1, Theorem 1] with the path system below; Ω(n^{1/4}/√(d log n)) [6]; upper bound O(n^{1/3} Δ^{1/6}) [5, Theorem 3.2] | Ω_δ((n/d)^{1/3}) | Claim |
| Thm 4 | The same on connected d-regular Ramanujan graphs, d ≥ 3, of girth g ≥ (2/3 + ε) log_{d−1} n with a constant ε > 0, among them the bipartite graphs X^{p,q} of [9] | Ω(n^{1/4}/√(log n)) [1, Corollary 2]; Ω((n/log n)^{1/3}) by Cor 2; upper bound O(n^{1/3} d^{1/6}) [5, Theorem 3.2] | Ω_{d,ε}(n^{1/3}), so Θ(n^{1/3}) for constant d | Claim |

**Comparison.** n^{2/3}/g^{1/3} ≥ n^{3/4}/g^{1/2} holds exactly when g ≥ n^{1/2}, so for every graph, since g ≥ n. The bound of [1, Theorem 1] is above a constant only for g < n^{3/2}, and there Theorem 1 applies with δ = 1/2, so its constant does not depend on the graph in that range. Cor 2 follows from Theorem 1 with g = O(n log n) for constant-degree expanders [2, Corollary D.1]. Cor 3 follows from Theorem 1 with a path system of congestion at most 2n(D̄ + 1) ≤ 4nd, where D̄ is the mean distance (below). Theorem 1 of [1] with the same path system gives Ω(n^{1/4}/√d), which Cor 3 exceeds by the factor n^{1/12} d^{1/6}; the bound of [6] is lower by a further factor √(log n). The bound of [6] holds for every vertex-transitive graph but exceeds a constant only for d < n^{1/2}, and there Cor 3 applies with δ = 1/4 for n large enough. The congestion of a path system is, up to the paths that end at a vertex, its vertex-forwarding index; see [7] for known bounds. For vertex-transitive graphs of polylogarithmic diameter and degree, such as many Cayley graphs, Cor 3 matches the upper bound up to polylogarithmic factors. On the hypercube and on grids of dimension at least 6, the bound Θ(N^{1/3}) up to logarithmic factors is known from [3]; the lower bound technique of [8] applies to every graph that contains a product graph, which covers graphs containing such grids, among them tori of dimension at least 6, where it is stronger than Cor 3.

## Theorem 1, the proof

**Inputs.** Fix a path system P of congestion g. For L ≥ 1 the inputs are the staircases of [2]: sequences x = (x_1, …, x_{L+1}) with x_1 = 1 and x_2, …, x_{L+1} ∈ V, and the function f_x(v) = −i n − j if v lies on the walk P^{x_1,x_2} ∘ ⋯ ∘ P^{x_L,x_{L+1}}, where i is the largest index with v ∈ P^{x_i,x_{i+1}} and v is the j-th vertex of that path, and f_x(v) = dist(v, 1) otherwise. The only local minimum of f_x is x_{L+1} [2, Lemmas 6 and 7]. So it suffices to bound the queries needed to output F(x) = x_{L+1}.

**The adversary matrix.** Write x ∧ y = k if x and y agree in x_1, …, x_k and differ in x_{k+1}. Let tail_x(k) be the set of vertices of P^{x_k,x_{k+1}} ∘ ⋯ ∘ P^{x_L,x_{L+1}}, with the first occurrence of x_k removed. If x ∧ y = k, then f_x(v) ≠ f_y(v) only for v ∈ tail_x(k) ∪ tail_y(k). Put Γ[x, y] = 1/((n − 1) n^{L−k}) when x ∧ y = k and F(x) ≠ F(y), and Γ_v[x, y] = Γ[x, y] when moreover f_x(v) ≠ f_y(v). By the positive adversary bound [4], the query complexity is at least a constant times ‖Γ_G‖/max_v ‖Γ_{G,v}‖ for the restriction to any set G of inputs.

**The weights.** Let c_u(v) be the number of w with v ∈ P^{u,w}, and c(v) = Σ_u c_u(v) ≤ g. For a continuation x' of a fixed prefix ending in x_k = u, the probability that v ∈ tail_{x'}(k) is at most

q_k(u, v) = c_u(v)/(n − 1) + (L − k) c(v)/(n(n − 1)),

since the first new segment has one fixed end and each later one has two independent uniform ends. With α_k = √q_k(x_k, v), give a pair at level k the weights U = Γ α_k, V = Γ/α_k if v lies only on the tail of x, the weights U = Γ/α_k, V = Γ α_k if v lies only on the tail of y, and U = V = Γ if v lies on both. Then Γ_v[x, y]² ≤ U[x, y] V[x, y], and the bound of a matrix norm by weighted row and column sums gives ‖Γ_v‖² ≤ max_x Σ_y U · max_y Σ_x V. Each of the three kinds of pairs contributes at most α_k at level k to a row or a column sum (the second kind by q_k/α_k = α_k, the third by min(1, q_k) ≤ α_k), so

‖Γ_{G,v}‖ ≤ 3 max_{z ∈ G} Σ_k α_k(z_k, v) ≤ 3 (Φ_max + L^{3/2} √(g/(n(n − 1)))), where Φ(z, v) = Σ_k √(c_{z_k}(v)/(n − 1)).

**The good inputs.** For a uniform random input z and a fixed v, the terms of Φ(z, v) with k ≥ 2 are independent, at most 1.1 (for n ≥ 6), and by concavity of the square root have mean at most √(c(v)/(n(n − 1))) each. Their sum has mean μ ≤ L√(2g)/n, and the multiplicative tail bound for sums of independent bounded variables gives Pr[sum ≥ t] ≤ (eμ/t)^{t/1.1}. Let G be the set of inputs with Φ(z, v) ≤ t + 1.1 for every v. With L = ⌊(n²/g)^{1/3}⌋ and g ≤ n^{2−δ}, μ ≤ √2 n^{−δ/6} and L^{3/2}√(2g)/n ≤ √2, and for t > 6.6/δ the union bound over the n vertices gives Pr[z ∉ G] ≤ 1/4 for n large enough. Then ‖Γ_G‖ ≥ 1ᵀ Γ_G 1/|G| ≥ L (1 − 2 · 1/4 − 1/n) ≥ L/3, since both inputs of a pair at level k are uniform. Hence the query complexity is at least a constant times L/(t + 4), which is Ω_δ(n^{2/3}/g^{1/3}). ∎

The weight α_k depends on the milestone x_k that the two inputs share, through c_{x_k}(v). Vertices near the shared milestone get a large weight, and the rest a weight of order √(L g)/n.

## Cor 3, the path system

Let G be vertex-transitive, and let D̄ be the mean of dist(u, w) over all ordered pairs (u, w), including u = w. For every pair u ≠ w choose P^{u,w} uniformly among the shortest paths from u to w, independently. An automorphism σ maps the shortest paths from u to w bijectively onto those from σu to σw, so Pr[v ∈ P^{u,w}] = Pr[σv ∈ P^{σu,σw}], and the expected number E c(v) of paths through v is the same for every v. Summing over v gives n · E c(v) = Σ_{u,w} (dist(u, w) + 1) = n²(D̄ + 1), so E c(v) = n(D̄ + 1) ≥ n. Each c(v) is a sum of independent indicators, and the multiplicative tail bound gives Pr[c(v) ≥ 2n(D̄ + 1)] ≤ e^{−n/3}. For n ≥ 9 the union bound over the n vertices leaves a path system with g ≤ 2n(D̄ + 1) ≤ 4nd. If d ≤ n^{1−δ}/4, then g ≤ n^{2−δ}, and Theorem 1 gives Ω_δ(n^{2/3}/(nd)^{1/3}) = Ω_δ((n/d)^{1/3}). ∎

## Theorem 4, the tight bound on Ramanujan graphs of large girth

**Statement.** Let G be a connected d-regular graph with n vertices, d ≥ 3, whose adjacency eigenvalues other than ±d lie in [−2√(d−1), 2√(d−1)], and whose girth g satisfies g ≥ (2/3 + ε) log_{d−1} n for a constant ε > 0. Then the quantum query complexity of local search on G is Ω_{d,ε}(n^{1/3}). With the upper bound O(n^{1/3} d^{1/6}) of [5, Theorem 3.2] this gives Θ(n^{1/3}) for constant d. The bipartite graphs X^{p,q} of [9] (p ≠ q primes congruent to 1 mod 4 with Legendre symbol (p/q) = −1) are (p + 1)-regular Ramanujan graphs with n = q(q² − 1) vertices and girth at least 4 log_p q − log_p 4 [9]. Since n < q³, this is at least (4/3) log_p n − log_p 4, so they satisfy the hypothesis with ε = 1/2 for q large enough. The proof gives more generally Ω(min(n^{1/3}, (d−1)^{g/2}/(log n)^C)) on Ramanujan graphs of girth g, for a constant C.

**Inputs.** The staircases are non-backtracking walks with unit steps: all sequences z = (z_1, …, z_{T+1}) with z_1 = 1, z_{k+1} a neighbour of z_k, and z_{k+1} ≠ z_{k−1} for k ≥ 2. There are d(d−1)^{T−1} of them, all used with equal weight. Put f_z(v) = −max{t : z_t = v} if v lies on the walk and f_z(v) = dist(v, 1) otherwise. The endpoint z_{T+1} is the only local minimum: it is the global minimum; an on-walk vertex with last index i ≤ T has the neighbour z_{i+1}, whose last index is larger; an off-walk vertex u ≠ 1 has a neighbour closer to 1, which either lies on the walk (value below 0) or has a smaller distance. If x ∧ y = k (the walks agree in z_1, …, z_k and differ in z_{k+1}), then f_x and f_y differ only on tail_x(k) ∪ tail_y(k), where tail_x(k) = {x_{k+1}, …, x_{T+1}}.

**Adversary matrix and weights.** Put Γ[x, y] = 1/N_k when x ∧ y = k and x_{T+1} ≠ y_{T+1}, where N_k is the number of walks y with x ∧ y = k (the same for every x). Two walks of length m = T + 1 − k from z_k with different first steps end at the same vertex only if g ≤ 2m, and then with probability at most 2d/n + 4(m + 1)(d−1)^{−(m−2)/2} = o(1) by (W1) below. So every row sum of Γ lies between T(1 − o(1)) and T, and ‖Γ_Good‖ ≥ T/3 for every set Good containing at least 3/4 of the walks. Let q_k(z, v) be the probability that a uniformly random non-backtracking continuation of z_1, …, z_k visits v within T + 1 − k steps. The partners y of x at level k are the continuations with y_{k+1} ∉ {x_{k+1}, z_{k−1}}, so a fraction at most c_d q_k of them has v in its tail, with c_d = (d−1)/(d−2) (c_d = d/(d−1) at k = 1). The weights of Theorem 1 with α_k = √(c_d q_k) on the shared prefix give ‖Γ_{Good,v}‖ ≤ 3√c_d max_{z∈Good} Φ(z, v), where Φ(z, v) = Σ_{k=1}^{T} √q_k(z, v). Hence the query complexity is at least a constant times T / max_{z∈Good, v} Φ(z, v). This step uses no property of G beyond d ≥ 3.

**Walk counts.** Let A_t(x, y) be the number of non-backtracking walks of length t from x to y. Then A_1 = A, A_2 = A² − dI, A_{t+1} = A A_t − (d−1) A_{t−1}, and A_t = (d−1)^{t/2}(U_t(X) − U_{t−2}(X)/(d−1)) with X = A/(2√(d−1)) and U_t the Chebyshev polynomials of the second kind [9]. Since |U_t| ≤ t + 1 on [−1, 1], the Ramanujan condition gives ‖A_t‖ ≤ 2(t + 1)(d−1)^{t/2} on the eigenvectors other than those of ±d, and these two contribute at most 2d(d−1)^{t−1}/n to each entry. So

(W1) A_t(x, y) ≤ 2d(d−1)^{t−1}/n + 2(t + 1)(d−1)^{t/2},  (W2) Σ_{y∈S} A_t(x, y) ≤ 2d(d−1)^{t−1}|S|/n + 2(t + 1)(d−1)^{t/2}√|S|.

A non-backtracking walk on the directed edge e = (u, w) that takes t further uniform steps is at y with probability p_t(e, y) ≤ (d−1)^{−t} A_{t+1}(u, y) ≤ 2d/n + 4(t + 2)(d−1)^{−(t−1)/2}. By the girth, two different non-backtracking walks from the same directed edge with lengths a and b and the same end give a cycle of length at most a + b.

**Splitting q.** Fix ρ = ⌈5 log_{d−1} log n⌉, s = 2ρ and L = ⌈3 log_{d−1} n⌉, so g > 2s for n large. By the union bound over times, q(e, v) ≤ Σ_{t=1}^{T} p_t(e, v). For t < s there is at most one non-backtracking walk from e to v; let ℓ(e, v) be its length (∞ if there is none). Then √q_k ≤ a_k + b_k + c_k with a_k = (d−1)^{−ℓ/2} if ℓ < ρ, b_k = (d−1)^{−ℓ/2} if ρ ≤ ℓ < s (each 0 otherwise), ℓ = ℓ(e_k, v), e_k = (z_{k−1}, z_k), and c_k the square root of Σ_{s≤t≤T} p_t(e_k, v).

**The near part.** If the walk follows the short walk from e_k to v, then ℓ drops by 1. If it leaves it, then ℓ(e_{k+1}, v) ≥ s, since otherwise two walks from z_k with different first steps, both shorter than s + 1, would end at v and close a cycle shorter than g. So the times with ℓ < ρ form runs along which ℓ decreases by 1, and each run contributes at most Σ_{j≥0} (d−1)^{−j/2} = C_d (C_3 < 3.42). Two runs for the same v give a closed walk from the point where the first run is left, along z to the start z_{k'} of the second run, then to v and back, with no backtracking at its two joints; it contains a cycle, so the two times differ by at least g − 2ρ while dist(z_k, z_{k'}) < 2ρ. By (W2) with S the ball of radius 2ρ, the probability that such a pair of times exists is at most T Σ_{t≥g−2ρ} (2d|S|/n + 4(t + 2)(d−1)^{−(t−1)/2}√|S|), which is (log n)^{O(1)}(T²/n + T(d−1)^{−g/2}) = o(1) for T ≤ n^{1/3} and g ≥ (2/3 + ε) log_{d−1} n. Outside this event, Σ_k a_k ≤ C_d for every v.

**The middle and late parts.** Here b_k ≤ (d−1)^{−ρ/2} ≤ (log n)^{−5/2}, and c_k ≤ (2dT/n + O(s(d−1)^{−s/2}))^{1/2} ≤ (log n)^{−2.4} for n large. Under the uniform law π on directed edges, E_π b ≤ Σ_{ℓ<s} (d−1)^{ℓ/2}/n = (log n)^{O(1)}/n, since at most d(d−1)^ℓ of the nd directed edges have a walk of length ℓ to v, and E_π c ≤ √(T/n) by concavity, since π is stationary and its head is uniform. By the bound on p_L for directed edges, the law of e_{k+L} given e_1, …, e_k is at most 6π. Split the times into their L residue classes modulo L. Along one class the conditional means of the terms sum to at most 6T√(T/n)/L = 6/L for c (at T = n^{1/3}) and to (log n)^{O(1)} n^{−2/3} for b. The multiplicative Chernoff bound for nonnegative terms at most β with conditional means summing to at most μ, Pr[S ≥ a] ≤ (eμ/a)^{a/β}, with a = 30/L for c and a = 1/L for b, gives failure probability exp(−Ω((log n)^{1.4})) per class and vertex. The first L terms add at most L((log n)^{−5/2} + (log n)^{−2.4}) = o(1). By the union bound over the L classes and the n vertices, with probability 1 − o(1) we have Σ_k (b_k + c_k) ≤ 32 for every v.

**Conclusion.** Let Good be the walks outside both events. Then Φ(z, v) ≤ 1 + C_d + 32 for every z ∈ Good and every v (the term k = 1 is at most 1), and with T = ⌊n^{1/3}⌋ the query complexity is Ω(T) = Ω(n^{1/3}). ∎

The walks are non-backtracking because a simple random walk stays near a vertex for about log T steps; for simple random walks the corresponding sum grows with n (`sim/phi_nb.py`).

## Scripts

`sim/check_adv.py` builds Γ and every Γ_v exactly for random 3- and 4-regular graphs with breadth-first path systems (n ≤ 12, L ≤ 3, up to 512 inputs). It asserts that x_{L+1} is the only local minimum of every f_x, that f_x and f_y differ only on the two tails, the bound q_k for every prefix and vertex, and ‖Γ_v‖ ≤ 3 max_z Σ_k α_k(z_k, v) for every v. `sim/scaling.py` computes c_u(v) as subtree sizes of breadth-first trees on random 3-regular graphs with n ≤ 4000, and evaluates g/(n ln n), the worst Φ over sampled staircases, and the explicit bound B of the proof. At these sizes L ≤ 6 and B < 1, so the scripts check the inequalities and the growth of g and Φ, not the asymptotic advantage. `sim/transitive.py` computes, for hypercubes, tori, circulants and a cycle, the exact probability that a vertex lies on a uniform shortest path, asserts that E c(v) = n(D̄ + 1) at every vertex, draws one random shortest-path system and asserts g ≤ 2n(D̄ + 1) ≤ 4nd; the Petersen graph is included as a vertex-transitive graph that is not a Cayley graph, and the cycle lies outside the range of Cor 3. On a path graph, which is not vertex-transitive, the first assert fails, as it should. Output in `sim/out.txt`:

```
python sim/check_adv.py
n=8 deg=3 L=3: inputs 512, ||G|| = 2.750, max_v ||G_v|| = 1.718, ratio 1.601, g = 22
...
all asserts passed
python sim/scaling.py
n=  4000 g/(n ln n)=1.575 L=  6 Phi_max=2.148 tail=0.840 B=0.669 B/n^(1/3)=0.0422
```

`sim/check_nb_counts.py` computes A_t by brute force on four Ramanujan graphs (Petersen, Heawood, K_{4,4} and the Tutte 8-cage) and asserts the recurrence, the Chebyshev form and (W1) up to t = 8, with a mutation (the spectral term dropped) that fails. `sim/phi_nb.py` evaluates max_v Φ for sampled non-backtracking staircases on random 3-regular graphs at T = n^{1/3}; these graphs have short cycles and lie outside the class of Theorem 4, so the script shows the size of Φ, not the girth condition. Output in `sim/out_phi_nb.txt`:

```
d=3 n=  1000 T= 10  NB max_v Phi: mean 2.49 max 3.23  floor T^1.5/sqrt(n)=1.00  SRW mean 5.77
d=3 n= 64000 T= 40  NB max_v Phi: mean 2.97 max 3.25  floor T^1.5/sqrt(n)=1.00
```

**Not formalized:** the proofs of Theorems 1 and 4 and Cor 3 are written out above and checked numerically on the small cases listed; there is no Lean proof. The adversary bound of [4], the staircase lemmas of [2], the walk-count identity of [9] and the multiplicative Chernoff bound for martingales are used as stated there.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check scripts, and to draft the text.

## References

1. S. Brânzei, N. J. Recker. A note on quantum lower bounds for local search via congestion and expansion. arXiv:2412.13345, 2024.
2. S. Brânzei, D. Choo, N. J. Recker. The sharp power law of local search on expanders. arXiv:2305.08269, 2023.
3. S. Zhang. (Almost) tight bounds for randomized and quantum local search on hypercubes and grids. arXiv:quant-ph/0504085, 2005.
4. P. Høyer, T. Lee, R. Špalek. Negative weights make adversaries stronger. STOC 2007. arXiv:quant-ph/0611054.
5. S. Aaronson. Lower bounds for local search by quantum arguments. arXiv:quant-ph/0307149, 2003.
6. H. Dinh, A. Russell. Quantum and randomized lower bounds for local search on vertex-transitive graphs. arXiv:0806.3437, 2008.
7. J.-M. Xu, M. Xu. The forwarding indices of graphs, a survey. arXiv:1204.2604, 2012.
8. S. Zhang. New upper and lower bounds for randomized and quantum local search. arXiv:quant-ph/0603034, 2006.
9. A. Lubotzky, R. Phillips, P. Sarnak. Ramanujan graphs. Combinatorica 8(3), 1988.
