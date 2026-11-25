# Quantum lower bounds for local search via vertex congestion

Written 25 Nov 2026.

**Setting.** As in [1]: G = (V, E) is a connected undirected graph with n vertices, and f : V → ℝ is given by an oracle that answers |v, a⟩ ↦ |v, a ⊕ f(v)⟩. The task is to find a local minimum, a vertex v with f(v) ≤ f(u) for every neighbour u, with success probability at least 2/3 for every f. An all-pairs path system P = {P^{u,w}} assigns a simple path from u to w to every ordered pair (u, w), with P^{u,u} = (u). Its vertex congestion is the largest number of paths of P that contain a vertex; g denotes the least vertex congestion over all such systems. Every vertex lies on the n paths that start at it, so g ≥ n, and g ≤ n².

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Quantum query complexity of local search on G, for g ≤ n^{2−δ} with a constant δ > 0 | Ω(n^{3/4}/√g) [1, Theorem 1] | Ω_δ(n^{2/3}/g^{1/3}) | Claim |
| Cor 2 | The same on Δ-regular β-expanders with constant Δ and β | Ω(n^{1/4}/√(log n)) [1, Corollary 2]; upper bound O(n^{1/3}) [5, Theorem 3.2] | Ω((n/log n)^{1/3}), which matches the upper bound up to the factor (log n)^{1/3} | Claim |

**Comparison.** n^{2/3}/g^{1/3} ≥ n^{3/4}/g^{1/2} holds exactly when g ≥ n^{1/2}, so for every graph, since g ≥ n. The bound of [1, Theorem 1] is above a constant only for g < n^{3/2}, and there Theorem 1 applies with δ = 1/2, so its constant does not depend on the graph in that range. Cor 2 follows from Theorem 1 with g = O(n log n) for constant-degree expanders [2, Corollary D.1]. On the hypercube and on grids of dimension at least 6, the bound Θ(N^{1/3}) up to logarithmic factors is known from [3]; that argument uses the product structure of those graphs.

## Theorem 1, the proof

**Inputs.** Fix a path system P of congestion g. For L ≥ 1 the inputs are the staircases of [2]: sequences x = (x_1, …, x_{L+1}) with x_1 = 1 and x_2, …, x_{L+1} ∈ V, and the function f_x(v) = −i n − j if v lies on the walk P^{x_1,x_2} ∘ ⋯ ∘ P^{x_L,x_{L+1}}, where i is the largest index with v ∈ P^{x_i,x_{i+1}} and v is the j-th vertex of that path, and f_x(v) = dist(v, 1) otherwise. The only local minimum of f_x is x_{L+1} [2, Lemmas 6 and 7]. So it suffices to bound the queries needed to output F(x) = x_{L+1}.

**The adversary matrix.** Write x ∧ y = k if x and y agree in x_1, …, x_k and differ in x_{k+1}. Let tail_x(k) be the set of vertices of P^{x_k,x_{k+1}} ∘ ⋯ ∘ P^{x_L,x_{L+1}}, with the first occurrence of x_k removed. If x ∧ y = k, then f_x(v) ≠ f_y(v) only for v ∈ tail_x(k) ∪ tail_y(k). Put Γ[x, y] = 1/((n − 1) n^{L−k}) when x ∧ y = k and F(x) ≠ F(y), and Γ_v[x, y] = Γ[x, y] when moreover f_x(v) ≠ f_y(v). By the positive adversary bound [4], the query complexity is at least a constant times ‖Γ_G‖/max_v ‖Γ_{G,v}‖ for the restriction to any set G of inputs.

**The weights.** Let c_u(v) be the number of w with v ∈ P^{u,w}, and c(v) = Σ_u c_u(v) ≤ g. For a continuation x' of a fixed prefix ending in x_k = u, the probability that v ∈ tail_{x'}(k) is at most

q_k(u, v) = c_u(v)/(n − 1) + (L − k) c(v)/(n(n − 1)),

since the first new segment has one fixed end and each later one has two independent uniform ends. With α_k = √q_k(x_k, v), give a pair at level k the weights U = Γ α_k, V = Γ/α_k if v lies only on the tail of x, the weights U = Γ/α_k, V = Γ α_k if v lies only on the tail of y, and U = V = Γ if v lies on both. Then Γ_v[x, y]² ≤ U[x, y] V[x, y], and the bound of a matrix norm by weighted row and column sums gives ‖Γ_v‖² ≤ max_x Σ_y U · max_y Σ_x V. Each of the three kinds of pairs contributes at most α_k at level k to a row or a column sum (the second kind by q_k/α_k = α_k, the third by min(1, q_k) ≤ α_k), so

‖Γ_{G,v}‖ ≤ 3 max_{z ∈ G} Σ_k α_k(z_k, v) ≤ 3 (Φ_max + L^{3/2} √(g/(n(n − 1)))), where Φ(z, v) = Σ_k √(c_{z_k}(v)/(n − 1)).

**The good inputs.** For a uniform random input z and a fixed v, the terms of Φ(z, v) with k ≥ 2 are independent, at most 1.1 (for n ≥ 6), and by concavity of the square root have mean at most √(c(v)/(n(n − 1))) each. Their sum has mean μ ≤ L√(2g)/n, and the multiplicative tail bound for sums of independent bounded variables gives Pr[sum ≥ t] ≤ (eμ/t)^{t/1.1}. Let G be the set of inputs with Φ(z, v) ≤ t + 1.1 for every v. With L = ⌊(n²/g)^{1/3}⌋ and g ≤ n^{2−δ}, μ ≤ √2 n^{−δ/6} and L^{3/2}√(2g)/n ≤ √2, and for t > 6.6/δ the union bound over the n vertices gives Pr[z ∉ G] ≤ 1/4 for n large enough. Then ‖Γ_G‖ ≥ 1ᵀ Γ_G 1/|G| ≥ L (1 − 2 · 1/4 − 1/n) ≥ L/3, since both inputs of a pair at level k are uniform. Hence the query complexity is at least a constant times L/(t + 4), which is Ω_δ(n^{2/3}/g^{1/3}). ∎

The weight α_k depends on the milestone x_k that the two inputs share, through c_{x_k}(v). Vertices near the shared milestone get a large weight, and the rest a weight of order √(L g)/n.

## Scripts

`sim/check_adv.py` builds Γ and every Γ_v exactly for random 3- and 4-regular graphs with breadth-first path systems (n ≤ 12, L ≤ 3, up to 512 inputs). It asserts that x_{L+1} is the only local minimum of every f_x, that f_x and f_y differ only on the two tails, the bound q_k for every prefix and vertex, and ‖Γ_v‖ ≤ 3 max_z Σ_k α_k(z_k, v) for every v. `sim/scaling.py` computes c_u(v) as subtree sizes of breadth-first trees on random 3-regular graphs with n ≤ 4000, and evaluates g/(n ln n), the worst Φ over sampled staircases, and the explicit bound B of the proof. At these sizes L ≤ 6 and B < 1, so the scripts check the inequalities and the growth of g and Φ, not the asymptotic advantage. Output in `sim/out.txt`:

```
python sim/check_adv.py
n=8 deg=3 L=3: inputs 512, ||G|| = 2.750, max_v ||G_v|| = 1.718, ratio 1.601, g = 22
...
all asserts passed
python sim/scaling.py
n=  4000 g/(n ln n)=1.575 L=  6 Phi_max=2.148 tail=0.840 B=0.669 B/n^(1/3)=0.0422
```

**Not formalized:** the proof of Theorem 1 is written out above and checked numerically on the small cases listed; there is no Lean proof. The adversary bound of [4] and the staircase lemmas of [2] are used as stated there.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check scripts, and to draft the text.

## References

1. S. Brânzei, N. J. Recker. A note on quantum lower bounds for local search via congestion and expansion. arXiv:2412.13345, 2024.
2. S. Brânzei, D. Choo, N. J. Recker. The sharp power law of local search on expanders. arXiv:2305.08269, 2023.
3. S. Zhang. (Almost) tight bounds for randomized and quantum local search on hypercubes and grids. arXiv:quant-ph/0504085, 2005.
4. P. Høyer, T. Lee, R. Špalek. Negative weights make adversaries stronger. STOC 2007. arXiv:quant-ph/0611054.
5. S. Aaronson. Lower bounds for local search by quantum arguments. arXiv:quant-ph/0307149, 2003.
