# Minimum complementary sub-quorum sum has logarithmic order

Let `m(n)` be the minimum over all simple n-vertex graphs G of the sum of the sub-quorum coloring numbers of G and its complement. For every n ≥ 2,
`floor(log₂ n) + 1 ≤ m(n) ≤ 80 ceil(log₂ n)`.
Thus m(n) has order Θ(log n). No exact formula or leading constant is claimed.

**Source:** Ma–Sahbi–Zhang, [Sub-quorum colorings of graphs, §9](https://arxiv.org/html/2609.25128v4#S9). The question appears immediately after Conjecture 9.2. That conjecture is about the *maximum* of the sum, not the minimum. The lower bound is the paper's Theorem 9.1, reproved here. The upper bound answers the question about order of growth.

## Proof

Let L = ceil(log₂ n) and t = 32L+1. We first find a graph such that both it and its complement have at least one quarter of the possible edges on every induced set of at least t vertices. For one t-set, there are m = 16Lt = 8r Boolean edge positions with r = 2Lt. A string with ≤2r ones weighs at least 2^(6r) when each zero contributes a factor of 2. The total weight is 3^(8r) ≤ 2^(13r), so the bad fraction is ≤2^(-r). The same holds for its complement. There are at most n^t candidates (even when counting labeled injections), so the total bad fraction is ≤2^(1-Lt) < 1. To extend from t to larger sets, a graph with strict density below one quarter has a maximum-degree vertex whose deletion preserves that deficiency, by comparing degree with average degree. Iterating would produce a bad t-set.

Consider any valid sub-quorum coloring of either graph. On its colored support of size s≥t every degree is at most 2M-1, where M is the largest color class. The reason is that a colored vertex has at most M−1 same-color open neighbors and at most M differently colored neighbors (the center counts for its own color). Summing degrees and using density yields 8M ≥ s+3. Deleting the entire class preserves validity: no surviving vertex loses an ally. Each such deletion leaves at most 7/8 of the support, so each eight steps at least halves it. After at most 8L steps the remaining support has at most 32L vertices and therefore at most 32L colors. Thus each coloring has at most 40L colors.

For the lower bound, a clique in either graph has all distinct colors in its complement. If a graph has no clique of size a+1 and its complement no clique of size b+1, then n<2^(a+b). This follows by splitting the remaining vertices at any vertex into neighbors and non-neighbors and inducting on a+b. Applying the statement to the two sub-quorum maxima proves the lower bound.

## Check

The final statement is `QuorumMinimum.minSum_order` in `Result.lean`. It uses `SimpleGraph (Fin n)` (relabeling covers all n-vertex simple graphs), the surjective partial maps of Definition 2.2 (using its equivalent local inequality in Lemma 2.3), the maxima of feasible color counts, and the infimum of the finite nonempty set of complementary sums. The package contains both directions of the integer bounds.

Run `./check.sh /path/to/mathlib4` with Lean 4.34.1 at Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612` and its build artifacts present. The script rebuilds all 13 proof modules to a fresh temporary directory, reports the final axioms, and runs separate Python controls over all labeled graphs on 2–5 vertices. The probability part is a finite count, not a floating-point estimate. Only the standard Lean axioms are used.

Priority check: the latest arXiv version found (v4, 10 Oct 2026) still asks this order question. Searches under the title, arXiv ID, author names, parameter name, and Ramsey/Nordhaus–Gaddum formulations found no prior solution in the sources checked, including the original quorum paper and later caterpillar paper. This is not a claim of absolute priority.

This standalone dossier restates the coding of the coloring constraint from the merged [maximum-side proof](../sub-quorum-nordhaus/README.md) so it can replay against its own Mathlib pin. A helper independently checked parts of the counting argument; the result and its statement are checked by Lean.
