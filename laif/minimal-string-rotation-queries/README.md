# Finding the minimal string rotation with quantum queries

Written 12 Nov 2026.

**Setting.** A string s ∈ Σ^n over an ordered alphabet is given by queries: a query returns one character s_j. For 1 ≤ ℓ ≤ n, the *minimal length-ℓ substring* task asks for the least start e ∈ [0, n − ℓ] such that s[e, e + ℓ) is lexicographically least among all substrings of length ℓ. The minimal rotation of x ∈ Σ^n is the least start of a minimal length-n substring of x x[0, n − 1), and the minimal suffix, the maximal suffix and the maximal rotation reduce to the same task [1, Propositions 4.2 to 4.5]; [2, Theorem 5]. The same algorithm gives the longest Lyndon substring (Section 3).

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Find the least start of a minimal length-ℓ substring, for every ℓ | n^{1/2+o(1)} [1, Theorem 4.1], and √n · 2^{O(√log n)} by the proof of [3, Theorem 3.3], both for n/2 ≤ ℓ ≤ n; Õ(√n) for the decision version "does the minimal rotation start at i?" [2, Theorem 5] | O(√n (1 + log ℓ) log^{3/2} n (log log n)^{3/2}) | Claim; checked by script |
| Cor 2 | Find the minimal rotation, the minimal suffix, the maximal suffix, the maximal rotation | √n · 2^{O(√log n)} [3] | Õ(√n), so Θ̃(√n) with the lower bound Ω(√n) [6]; [1, Remark 4.7] | Claim |
| Thm 3 | Find a longest Lyndon substring | n^{1/2+o(1)} [1, Theorem 4.9] | Õ(√n), so Θ̃(√n) with the lower bound Ω(√n) [1, Remark 4.17] | Claim; checked by script |

The algorithm doubles the length of the minimal substring it knows. Each doubling step is one minimum finding over blocks of starts, and an exclusion rule leaves at most two candidates per block.

## 1. The exclusion rule

For L ≤ ℓ let u_L be the least substring of length L that starts in [0, N), N = n − ℓ + 1, and I_L ⊆ [0, N) the set of its starts. The prefix of length L of a minimal substring of length L' ≥ L is minimal, so I_{L'} ⊆ I_L. For a start e and a length L', write key_{L'}(e) = (s[e, e + L'), e), ordered lexicographically and then by e. The least start of a minimal length-L' substring is the start with the least key.

**Lemma 1.** Let L < L' ≤ ℓ and let G be a set of g ≤ max(1, ⌊L/2⌋) consecutive starts. Then I_L ∩ G is an arithmetic progression, and the least key_{L'} over I_L ∩ G is attained at its first or its last element.

*Proof.* If |I_L ∩ G| ≤ 1 there is nothing to show, so let g ≥ 2 and L ≥ 4. Two starts e < e' of u_L in G have distance d = e' − e < g ≤ L/2, so d is a period of u_L. Let p be the least period of u_L. Then p ≤ d and p + d ≤ L, so gcd(p, d) is a period by the periodicity lemma [4], and p divides d. So I_L ∩ G ⊆ a + pℤ for its first element a, and for its last element e' = a + kp the occurrences at a and e' overlap in L − kp > L/2 ≥ p positions, so s has period p on [a, e' + L). Then every a + jp with 0 ≤ j ≤ k is a start of u_L, and I_L ∩ G = {a, a + p, …, a + kp}.

Let r be the least position r ≥ a + kp + L with r = n or s_r ≠ s_{r−p}. Then s has period p on [a, r). Take e = a + jp with j < k and compare s[e, e + L') with s[e + p, e + p + L'). Their letters agree at every offset i with e + p + i < r. If e + p + L' ≤ r, the two strings are equal and the key of e is smaller. Otherwise r < e + p + L' ≤ n, and the strings first differ at the offset i = r − p − e, where they have the letters s_{r−p} and s_r. This comparison is the same for every j, and the condition e + p + L' > r holds for all j from some j₀ on. So the keys along the progression first increase by index only, with equal strings, and then all strictly increase (if s_{r−p} < s_r) or all strictly decrease (if s_{r−p} > s_r). In both cases the least key is at a or at a + kp. ∎

**Lemma 2.** Let the starts [0, N) be cut into blocks of g = max(1, ⌊L/2⌋) consecutive starts, and in each block G with I_L ∩ G ≠ ∅ let e_G be the element of {min(I_L ∩ G), max(I_L ∩ G)} with the least key_{L'}. Then the e_G with the least key_{L'} is the least start of a minimal length-L' substring.

*Proof.* Let e* be the least start of a minimal length-L' substring. Then e* ∈ I_{L'} ⊆ I_L, and e* has the least key_{L'} among all starts, in particular in its block G. By Lemma 1, e* is the first or the last element of I_L ∩ G, so e_G = e*, and no e_{G'} has a smaller key. ∎

## 2. The algorithm

**Theorem 1.** The least start of a minimal length-ℓ substring of s ∈ Σ^n can be found with O(√n (1 + log ℓ) log^{3/2} n (log log n)^{3/2}) quantum queries and bounded error.

*Proof.* Set L₀ = 1 and L_{i+1} = min(2L_i, ℓ), so that L_t = ℓ for t = ⌈log₂ ℓ⌉. Keep a start c_i of u_{L_i}. Find c₀ as the least start of a least letter in s[0, N), by minimum finding with O(√n) queries [5]. Level i computes c_{i+1}, the least start of a minimal length-L_{i+1} substring, by Lemma 2 with L = L_i, L' = L_{i+1} and u_L = s[c_i, c_i + L):

1. *Comparator.* Given two blocks G and H, compute the first and the last occurrence of the pattern s[c_i, c_i + L) in the text s[min G, max G + L) and in s[min H, max H + L), of length at most g + L − 1 ≤ 3L/2. This takes O(√(L log³ L log log L)) queries [3, Lemma 2.3], based on [6]. Then compare the keys of the at most four extremes by searches for the first difference, with O(√L) queries each [3, Lemma 2.2]. Blocks are ordered by the key of e_G and then by their index, and a block without an occurrence has the key ∞, so the order is a strict total order. Amplify the error to a small constant.
2. *Minimum.* Find the block G with the least e_G by minimum finding with a bounded-error comparator, with O(√(N/g + 1)) comparisons [6, Lemma 3.4] [3, Lemma 2.1], and set c_{i+1} = e_G.

A level takes O(√(n/L + 1) · √(L log³ L log log L)) = O(√(n log³ n log log n)) queries. With the error of each level reduced to 1/(3t) by O(log t) = O(log log n) repetitions with a majority vote on the output, all t levels succeed with probability 2/3, and the total is O(√n (1 + log ℓ) log^{3/2} n (log log n)^{3/2}). By Lemma 2, c_t is the answer. ∎

**Corollary 2.** The minimal rotation, the minimal suffix, the maximal suffix and the maximal rotation of a string of length n can be found with Õ(√n) quantum queries.

*Proof.* The minimal rotation of x is the least start of a minimal length-n substring of x x[0, n − 1), where every query costs one query to x. The other problems reduce to the minimal rotation or to a minimal length-ℓ substring of a string formed from x and padding letters, with one query to x per query, as in [1, Propositions 4.2 to 4.5]: the maximal rotation by reversing the order of the letters [1, Proposition 4.2], the minimal suffix as the least start of a minimal length-n substring of x followed by n − 1 letters below Σ [1, Proposition 4.5], and the maximal suffix as the minimal suffix of the string with the reversed order of letters followed by one letter above Σ [1, Proposition 4.4]. ∎

The lower bound Ω(√n) for the minimal rotation is given in [6], and the reductions carry it to the minimal and maximal suffix [1, Remark 4.7].

## 3. The longest Lyndon substring

A *Lyndon word* is a nonempty string that is smaller than each of its proper rotations. In the *Longest Lyndon Substring* problem the task is to find a longest substring of s that is a Lyndon word. Suffixes are compared lexicographically, with a proper prefix smaller than the longer string.

Two subroutines follow from Theorem 1.

- *Least suffix in a range of starts.* For a string u and r < |u|, the least suffix of u among the starts [0, r] is the least start of a minimal length-|u| substring of u followed by r copies of one letter below Σ, as in [1, Proposition 4.5]. The padded substrings are pairwise distinct, so there are no ties. By Theorem 1 the start is found with Õ(√|u|) queries.
- *Longest Lyndon prefix.* For a start i of u, let NSS(i) be the least j > i with u[j, |u|) < u[i, |u|), or |u| if there is none. The longest Lyndon prefix of u[i, |u|) has length NSS(i) − i [7, Lemma 15]. The predicate "some suffix with a start in (i, t] is smaller than u[i, |u|)" is monotone in t. One test is one least suffix of u[i + 1, |u|) among the starts [0, t − i − 1], followed by one comparison of two suffixes, a search for the first difference with O(√|u|) queries [3, Lemma 2.2]. So binary search over t finds NSS(i) with O(log |u|) tests, each with error reduced to 1/(10 log |u|), and Õ(√|u|) queries in total.

**Theorem 3.** A longest Lyndon substring of s ∈ Σ^n can be found with Õ(√n) quantum queries and bounded error.

*Proof.* Let e = ⌈εd⌉ with ε = 0.1. As in the proof of [1, Theorem 4.10], cut the lengths into the classes [d, (1 + ε)d), d = (1 + ε)^k, and cover s for each class with the O(n/(εd)) windows of length d + 2e that start at the multiples of e. A Lyndon substring s* with length in [d, (1 + ε)d) then lies in the window whose start j satisfies j ≤ start(s*) < j + e, at an offset of at most e − 1 ≤ εd.

Let u be a window. Let i be the start of the least suffix of u among the starts [0, e − 1], found with the first subroutine, and return the length NSS(i) − i of the longest Lyndon prefix of u[i, |u|), found with the second. This takes Õ(√d) queries, and O(log n) repetitions with a majority vote reduce its error to 1/n². When the subroutines succeed, the returned length is the length of a Lyndon substring of s. Let s* be a longest Lyndon substring of s, with length in the class of d, and let u be the window that holds it at an offset of at most εd. Then s* is a Lyndon factor of u [1, Proposition 4.12], its start is i [1, Lemma 4.13], and the longest Lyndon prefix of u[i, |u|) has length at least |s*|. For each class, maximum finding over its windows takes O(√(n/d)) window evaluations [5]; [6, Lemma 3.4], so Õ(√(n/d) · √d) = Õ(√n) queries, and a loop over the O(log n) classes returns |s*| and locates s*. With the error per window at most 1/n², all evaluations succeed with probability 1 − o(1), and the total is Õ(√n). ∎

The algorithm uses no subroutine other than the doubling algorithm of Theorem 1 and searches for a first difference. In [1], the length of s* is found by a binary search for the longest prefix of the window that is a prefix of a Lyndon word, with the test of [1, Lemma 4.16]. Such a prefix has the form x^k x', where x is a Lyndon word and x' a proper prefix of x, and the proof of the test (arXiv:2110.09696v2) uses that the minimal rotation of x^k x' is x' x^k. For x = ababb and x' = aba the string x x' = ababbaba is a prefix of the Lyndon word ababbabac, but its minimal rotation is aababbab and not x' x = abaababb. This hints at a possible gap in that step. The step can be completed by taking |x| as the least period of the prefix, which [1] already computes with exact string matching. The step through NSS(i) above avoids both, and with the subroutines of [1] in place of Theorem 1 it also gives the bound n^{1/2+o(1)} of [1, Theorem 4.9].

## Scripts

`sim/check_doubling.py` runs the doubling algorithm with exact subroutines, asserts in every block that the occurrences of u_L form an arithmetic progression and that the least key is at an extreme (Lemma 1), and compares the result with brute force (Lemma 2 and Theorem 1). It covers 30 000 strings of length up to 40 over 2 to 4 letters, periodic strings with changes, Fibonacci prefixes and random strings, each for the minimal rotation and for a random ℓ, and then all binary strings of length up to 12 and all ternary strings of length up to 7, for every ℓ and for the reductions of the minimal and the maximal suffix in Corollary 2. It runs in a few seconds with Python 3 and no extra packages.

`sim/check_lyndon.py` runs the algorithm of Theorem 3 with the doubling algorithm as its only subroutine for least suffixes, over the classes and windows of the reduction. It asserts that every returned length belongs to a Lyndon substring and that the result equals brute force, on 3000 random and nearly periodic strings of length up to 30 over 2 and 3 letters, on all binary strings of length up to 11 and on all ternary strings of length up to 7. On the 3000 strings it also asserts that NSS(i) − i is the length of the longest Lyndon prefix of s[i, n) for every start i, and it checks the example ababbaba. The subroutines are exact, so the script does not test error reduction. It runs in under a minute with Python 3 and no extra packages.

## Lean

`lean/KnownPattern/Rotation.lean` of [known-pattern-matching-queries](../known-pattern-matching-queries/), with only the standard axioms:

- `window_lt_of_diff` and `window_eq_of_agree`: windows in lexicographic order are compared at their first difference.
- `step_along_run`: two starts at distance p inside a run of period p have equal windows, or windows that first differ at the end r of the run, between the letters s_{r−p} and s_r.
- `min_at_ends`: a sequence that increases up to an index and decreases after it has its least value at an end.
- `exclusion_rule`: the least key over the progression a, a + p, …, a + kp inside a run of period p is at a or at a + kp (the second part of Lemma 1).

`lean/KnownPattern/Lyndon.lean`: `rotation_example` shows that ababb is a Lyndon word, that ababbaba is a prefix of the Lyndon word ababbabac, and that its rotation aababbab is smaller than abaababb (Section 3).

**Not formalized:** the first part of Lemma 1 (that the starts in a block form a full progression of the least period, which follows from `windows_period` of `lean/KnownPattern/Basic.lean`), Lemma 2, the subroutines [3, 5, 6], the reductions of Corollary 2, Theorem 3 with the results [1, 7] it uses, and the query counts.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check scripts and the Lean files, and to draft the text.

## References

1. S. Akmal, C. Jin. Near-optimal quantum algorithms for string problems. SODA 2022. arXiv:2110.09696.
2. A. M. Childs, R. Kothari, M. Kovacs-Deak, A. Sundaram, D. Wang. Quantum divide and conquer. arXiv:2210.06419.
3. Q. Wang. A note on quantum divide and conquer for minimal string rotation. arXiv:2210.09149.
4. N. J. Fine, H. S. Wilf. Uniqueness theorems for periodic functions. Proc. Amer. Math. Soc. 16, 1965.
5. C. Dürr, P. Høyer. A quantum algorithm for finding the minimum. arXiv:quant-ph/9607014, 1996.
6. Q. Wang, M. Ying. Quantum algorithm for lexicographically minimal string rotation. arXiv:2012.09376.
7. F. Franek, A. S. M. Sohidull Islam, M. S. Rahman, W. F. Smyth. Algorithms to compute the Lyndon array. arXiv:1605.08935.
