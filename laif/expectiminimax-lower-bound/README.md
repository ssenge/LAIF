# Expectiminimax trees: a lower bound for quantum estimation of the value

Written 21 Nov 2026.

**Setting.** As in [1]: a complete tree of depth D = 2m in which every node has deg ≥ 2 children. The steps alternate between chance and deterministic, and the last step above the leaves is deterministic, so the root is a chance node. A chance node takes the mean of its children, and a deterministic node takes the maximum or the minimum. Leaf values lie in [0, 1], and a query returns one leaf value. Q_ε(T) is the number of queries needed to output an estimate of the root value with root mean square error at most ε.

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Q_ε(T), lower bound | Ω(max{deg^{m/2}, 1/ε}), and Ω(deg^{(m − m₂)/2}/ε) with m₂ = ⌈log_deg(1/(4ε))⌉ when m₂ ≤ m − 1 [1] | Ω(deg^{m/2}/(2^a ε)) for every m ≥ 1 and deg^{−m}/4 ≤ ε ≤ 1/8, with a = ⌈log_deg(1/(4ε))⌉ ≤ m | Claim; checked by script |

In particular Q_ε(T) = Ω(deg^{m/2}/ε) for every m ≥ 1 and 1/(4 deg) ≤ ε ≤ 1/8 (where a = 1), and for every ε with deg^{−m}/4 ≤ ε ≤ 1/8 when the depth is constant. Compared with [1]: for a = m, in particular for m = 1, the bound of [1] does not apply, and Theorem 1 is new in this range. Where the bound of [1] applies (a ≤ m − 1), the ratio of Theorem 1 to it is (√deg/2)^a up to constants, so Theorem 1 is larger for deg > 4, of the same order for deg = 4, and for deg ≤ 4 and a ≥ 2 the bound of [1] is the larger one. The upper bound of [1] is O(K^D · deg^{m/2}/ε · D^{4D} · log^{4D}(deg/ε)) for leaf values in [0, 1]. So for constant depth, the product deg^{m/2}/ε is the quantum query complexity up to polylogarithmic factors, and for general depth up to the factors of both bounds that depend on D (K^D D^{4D} log^{4D}(deg/ε) and 2^a ≤ 2^m). The range ε ≥ deg^{−m}/4 is where the root value of a tree with Boolean leaves can carry a gap of order ε.

## The hard instance

Leaves take values in {0, 1}. Every maximum node computes OR of its children, and every minimum node AND. Every chance layer j gets two integers t_j ≥ 0 and Δ_j ≥ 1 with t_j + Δ_j ≤ deg, and the promise that at every chance node of the layer exactly t_j or exactly t_j + Δ_j children are high. A layer with t_j = 0 and Δ_j = deg has all children equal.

**Lemma 1.** On every promise input, all nodes of one layer take one of two values ℓ < h, and the root takes one of two values whose difference is g = Π_j Δ_j/deg.

*Proof.* By induction from the leaves, where ℓ = 0 and h = 1. If every child takes a value in {ℓ, h}, then the maximum and the minimum take a value in {ℓ, h}, namely h exactly when OR (or AND) of the children's high bits is 1. A chance node with exactly k high children takes ℓ + (h − ℓ)k/deg, so with k ∈ {t_j, t_j + Δ_j} it takes one of two values whose difference is (h − ℓ)Δ_j/deg. ∎

So the root is high exactly when F(x) = 1, where F = f_0 ∘ f_1^{deg} ∘ ⋯ ∘ f_{D−1}^{deg^{D−1}} is a composition of partial Boolean functions: OR_deg, AND_deg, and the exact-weight function EW_{deg,t,Δ}, which maps inputs of Hamming weight t to 0 and of weight t + Δ to 1.

## Theorem 1, the proof

An estimate R with E[(R − V)²] ≤ ε² of the root value V satisfies |R − V| < 2ε except with probability at most 1/4. If g ≥ 4ε, comparing R with the midpoint of the two root values computes F with error at most 1/4, so Q_ε(T) ≥ Q(F) = Ω(Adv±(F)), since the general adversary bound characterizes bounded-error query complexity for every function with finite domain [3, Thm. 1.1].

The composition lemma for partial functions [2, Lemma 6] gives Adv±(f ∘ g^n) ≥ Adv±(f) · Adv±(g) for a partial Boolean f on {0, 1}^n and a partial Boolean g. Applied once per layer, Adv±(F) ≥ Π_d Adv±(f_d). The general adversary bound is at least the positive-weight adversary bound [5], which we use for the layer functions [4]. For OR_deg and AND_deg it is √deg, so the m deterministic layers give deg^{m/2}. For EW_{N,t,Δ}, relate every input of weight t to every input of weight t + Δ that contains it. An input of weight t has C(N − t, Δ) related inputs, of which C(N − t − 1, Δ − 1) differ from it in a given position, and an input of weight t + Δ has C(t + Δ, Δ) related inputs, of which C(t + Δ − 1, Δ − 1) differ in a given position. So Adv±(EW_{N,t,Δ}) ≥ √((N − t)(t + Δ))/Δ. With t = ⌊(N − Δ)/2⌋ we have N − t ≥ (N + Δ)/2 and t + Δ ≥ (N + Δ − 1)/2, so Adv±(EW_{N,t,Δ}) ≥ (N + Δ − 1)/(2Δ) ≥ N/(2Δ) for every 1 ≤ Δ ≤ N. A layer with all children equal is EW_{deg,0,deg} and contributes at least 1.

Let a ≥ 1 be the least integer with deg^{−a} ≤ 4ε; a ≤ m since ε ≥ deg^{−m}/4. Make a chance layers active, one with Δ = ⌈4ε deg^a⌉ ≤ deg and the others with Δ = 1, and give the remaining chance layers all children equal. Since deg^{−(a−1)} > 4ε, the root gap g = ⌈4ε deg^a⌉/deg^a lies between 4ε and 4ε + deg^{−a} ≤ 8ε. Altogether

Adv±(F) ≥ deg^{m/2} · 2^{−a} · deg^a/Π_j Δ_j = deg^{m/2}/(2^a g) ≥ deg^{m/2}/(2^a · 8ε). ∎

For 1/(4 deg) ≤ ε ≤ 1/8 one active layer suffices (a = 1), which gives Ω(deg^{m/2}/ε), also for m = 1. In the composed instance of [1] the deterministic layers inside each block of chance layers are set to identical children; here the exact-weight promise keeps every node two-valued, so all deterministic layers stay active.

## Scripts

`sim/check_lb.py` builds the instance for five layouts with deg ∈ {2, 3, 4} and depth up to 6, samples 200 promise inputs each, and checks that the tree value equals the predicted high or low root value with gap Π_j Δ_j/deg. It then solves the semidefinite programme of the general adversary bound for small cases and checks that Adv±(EW_{N,t,Δ}) ≥ √((N − t)(t + Δ))/Δ for all N ≤ 5, and that Adv±(EW ∘ OR) and Adv±(EW ∘ AND) agree with the product of the two bounds up to the solver tolerance, with the exact-weight function as a partial outer function (the case deg = 3 takes about ten minutes).

```
python sim/check_lb.py
tree values checked on 5 layouts
exact-weight adversary bound checked for N <= 5
deg=2 EW(t=0,D=1) o or: Adv(f)=1.4142 Adv(g)=1.4142 product=2.0000 Adv(fog)=2.0000
deg=2 EW(t=1,D=1) o and: Adv(f)=1.4142 Adv(g)=1.4142 product=2.0000 Adv(fog)=2.0000
deg=2 EW(t=0,D=2) o or: Adv(f)=1.0000 Adv(g)=1.4142 product=1.4142 Adv(fog)=1.4142
deg=3 EW(t=1,D=1) o or: Adv(f)=2.0000 Adv(g)=1.7321 product=3.4641 Adv(fog)=3.4641
composition lower bound checked
```

**Not formalized:** all of the folder.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check scripts, and to draft the text.

## References

1. M. Raat, M. Incerti-Medici, J. R. Wootton, E. van Nieuwenburg, D. Bultrini. How fast can a parent estimate the value of their children? A quantum algorithm for stochastic games. arXiv:2609.35511, 2026.
2. S. Kimmel. Quantum adversary (upper) bound. Chicago Journal of Theoretical Computer Science, 2013. arXiv:1101.0797.
3. T. Lee, R. Mittal, B. W. Reichardt, R. Špalek, M. Szegedy. Quantum query complexity of state conversion. FOCS 2011. arXiv:1011.3020.
4. A. Ambainis. Quantum lower bounds by quantum arguments. Journal of Computer and System Sciences 64, 2002. arXiv:quant-ph/0002066.
5. P. Høyer, T. Lee, R. Špalek. Negative weights make adversaries stronger. STOC 2007. arXiv:quant-ph/0611054.
