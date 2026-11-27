# A factorial exponent bound for directed disjoint shortest paths

**Theorem.** For k fixed, exact directed vertex-disjoint shortest paths with k prescribed source–target pairs on an arbitrary n-vertex digraph with positive real arc weights can be decided deterministically, and paths returned on yes instances, in n^(O(k^5 k!)) time in the same unit-cost real arithmetic model as Cao, Qi and Wang. The more precise bound has a factor depending on k: F(k,p)n^(p+1)+O(kn(n+m)), where p is given below. This tightens their full-model exponent upper bound from 2^(O(2^k k log k)) to 2^(O(k log k)). It is an improved analysis of their sweep, not a different search procedure.

## 1. The decomposition used by the sweep analysis

Use the definitions and geometric partition in [Cao–Qi–Wang, arXiv:2611.34013v1, §§5–10](https://arxiv.org/html/2611.34013v1#S10). For each nonsortable node X, their proof of Theorem 10.2 chooses a minimum-radius nonsortable ball B and partitions X into shell blocks and then grid cells. The recursive children are the nonempty **cells**, not the shell blocks. Each child in the innermost block is sortable by minimality of the radius. Each child in an outer block is disjoint from B and separated from B on every shared nonempty chain, by Lemma 10.1 and the radius/diameter inequalities in §10. In particular no child is the whole nonsortable X. Sortable nodes are leaves.

Instead of bounding the packing number over all configurations, fix a root-to-leaf branch, and count just its nonsortable nodes. Write them in depth order as X_1 ⊇ … ⊇ X_L, with chosen balls B_1,…,B_L. For d<L, the child X_(d+1) is outer because it is nonsortable. Every later ball lies inside that one child. On each chain i meeting B_d, define the sign of i at d to be + if B_d comes before X_(d+1) on i, and − if it comes after. If the child has no point on i, or d=L, choose either sign: then no later ball on that branch can also meet i.

Consequently, whenever d<e and both B_d and B_e meet chain i, the order of those two sets on i is determined by the sign at d. Subsets preserve the strict setwise order; no contiguity of either ball or cell in the original chain is needed.

## 2. Charge the depth to a cycle and a sign

At each d, partition chain indices by the assigned signs (irrelevant empty chains may go in either class). Since B_d is nonsortable, [Lemma 7.1](https://arxiv.org/html/2611.34013v1#S7.Thmtheorem1) supplies a strictly cheaper cyclic permutation on a support of size m≥2 all of whose indices have the same sign. Its support uses only nonempty chains. Charge d to that cycle together with that sign.

Fix one charge label (σ,+), with |support σ|=m. For any two charged nodes d<e, B_d precedes B_e on **every** chain used by σ. For label (σ,−) the reverse holds, so reverse the depth order. In either case, m nodes of the same label would be m aligned sub-configurations all having the same strictly cheaper cycle. [Lemma 7.2](https://arxiv.org/html/2611.34013v1#S7.Thmtheorem2) excludes this. Hence each label is charged at most m−1 times. This reasoning even covers the last nonsortable node, whose arbitrary signs never affect a comparison to a later one.

There are binom(k,m)(m−1)! cyclic permutations of support size m. It follows that every branch has at most

    D(k) = 2 Σ_(m=2)^k binom(k,m)(m−1)!(m−1) < 6 k!

nonsortable nodes. The inequality uses (m−1)!(m−1) ≤ m! and Σ_(j≥0) 1/j! < 3. No bound on general packings and no monotone-subsequence extraction are used.

## 3. Transfer to width and runtime

Let h(X) be the maximum number of nonsortable nodes along a branch of the above finite decomposition of X, including X when it is nonsortable. A sortable leaf has width at most 4k by Lemma 6.6. For any nonsortable X, the two applications of Lemma 8.8 in the final paragraph of Theorem 10.2 add at most 64q_k + 2s_k ≤ c_k = 1000(k+1)^5 to the maximum width of a child cell. The interfaces and choice of witnesses are exactly those of §10; their bounds do not depend on the ranking parameter used in the induction. Induction from the leaves therefore gives

    width(X) ≤ 4k + c_k h(X) ≤ 4k + c_k D(k).

Set p = 4k + 6 c_k k! + 1. Lemma 5.7 gives a memory-p order for any solution. The algorithm need not know the solution, its decomposition, or this order: Theorem 4.1's sweep searches all states within the cap. Its soundness applies unchanged and its bound is F(k,p)n^(p+1)+O(kn(n+m)), with F depending only on k and p. This gives the claimed fixed-k exponent. In the original normalized simple-arc model m≤n²; an input with explicitly listed parallel arcs can first retain just the lightest per ordered pair, adding the cost of reading/normalizing the original input. The k=1 case is ordinary shortest path.

## Scope and verification

The result applies to general directed graphs, not just DAGs or planar graphs, and inherits the comparison/addition model for arbitrary positive real weights. It does not extend to nonpositive weights, give a polynomial-in-k exponent, or answer either open question in §11. It does not replace faster special-case algorithms such as the known k=2 bounds. A primary-source audit checked the precise version of the full-model baseline and the recursive geometry; it found no earlier improvement of this form in the sources checked. This is not a claim of priority. The Lean companion verifies the combinatorial branch counting step, not the imported geometric partition or the sweep algorithm.
