# A single-exponential exponent bound for directed k-disjoint shortest paths

This strengthens the [cycle-label counting bound](PROOF.md) from a factorial exponent to an exponent at most 2^{O(k)}. It applies to the same exact deterministic sweep and arbitrary positive-real directed graph model, not a restricted graph class. The polynomial-in-k exponent questions remain open.

## 1. Aligned sequences

Use the abstract configurations and length function of [Cao–Qi–Wang](https://arxiv.org/html/2611.34013v1). In particular, L(x,y)=max_j(π_j(y)−π_j(x)) satisfies the triangle inequality. On chain i in native order it equals π_i(y)−π_i(x). The triangle inequality does not require lengths to be positive.

A *cycle event* consists of nonempty fragments of some chains and a cyclic permutation on their indices, with total cross length from the first vertex of each fragment to the last vertex of its image strictly less than the sum of native lengths. Chain fragments need not be contiguous. A sequence of events is *aligned* if, on every chain i, each event's fragment on i strictly precedes every later event's fragment on i whenever both are present. We may and do discard fragments on chains not switched by the cycle. Discarding these fragments changes neither a chosen cycle's deficit nor alignment.

## 2. Compress a batch to one half of the labels

Fix a split of all k labels into A,B of sizes a,b, and let M=binom(k,a). For any M consecutive events, extend each chosen cycle by identity to a permutation σ_t of all k labels. Let P_0=id, P_t=σ_t∘…∘σ_1. Among the M+1 preimages P_t^{-1}(A), two are equal, since there are only M subsets of size a. For prefixes i<j with equal preimages, the composition σ_j∘…∘σ_(i+1)=P_j∘P_i^{-1} preserves both A and B. Keep this nonempty interval of events.

For each chain i participating in the interval, define F_i as its very first fragment's first vertex, and E_i as its very last fragment's last vertex. Chains not occurring during the interval are fixed by every permutation; they need no vertices or route. Start one token i on each occurring chain. When an event transfers a token from its current chain p to chain σ_t(p), move it along the abstract cross segment from that event's first p vertex to its last σ_t(p) vertex. When an event does not move a chain's token, it does nothing to that token. Bridge the gap between any two consecutive occurrences of each chain by the native segment from its preceding last vertex to its next first vertex, carrying the unique token that is there. At the first occurrence, the token on that chain is still its original one. At the last, the token ending there stays there. Thus each token i follows a composable route from F_i to E_{P(i)} for the interval composition P. Every cross and every between-occurrence bridge is counted exactly once over all routes.

For comparison, the total native baseline is ∑_i L(F_i,E_i). Because each chain's fragments are aligned, this sum equals the sum of native segment lengths through all events plus the sum of the very same bridge lengths. Therefore the sum over all tokens of (their routed length minus their own baseline L(F_i,E_i)) is the sum of the event deficits, which is strictly negative.

Split this sum by token origins in A and B. One group, say A, has a strictly negative sum. The routing can leave A at intermediate times; only the endpoints must stay in A, which follows from P(A)=A. By triangle inequality every such token's routed length is at least L(F_i,E_{P(i)}). Thus P restricted to the occurring labels of A is a strictly cheaper permutation compared with the native baseline on those very labels. Its total deficit is the sum of its disjoint cycle deficits; fixed points have zero deficit. Pick one negative cycle, at least two labels. Make the compressed event by taking the union of original fragments in the interval on those labels, whose first and last vertices are exactly F_i and E_i. This gives one new valid cycle event supported wholly on A. The same argument applies if B is the negative group.

Compressing disjoint batches in their original order preserves alignment on all chains, since every selected vertex of the new event comes from its own batch.

## 3. Count the resulting events

Define T(0)=T(1)=0. For k≥2 let a=⌊k/2⌋, b=⌈k/2⌉ and define
```
T(k) + 1 = binom(k,a) (T(a) + T(b) + 1).
```
Every aligned sequence over k chain labels has length at most T(k), by induction. If it had T(k)+1 events, take T(a)+T(b)+1 complete batches of size binom(k,a). Each gives one output event supported in either A or B. Keep each group's compressed events in time order. At least one group receives more than its inductive maximum: contradiction.

In particular T(k)+1≤4^{k−1} for k≥1. For even k=2a≥2, the central binomial coefficient is at most 2^{k−1}: its fraction of 2^k is 1/2 at k=2 and decreases, by the successive ratio (2a+1)/(2a+2). The two smaller terms sum to at most 2·4^{a−1}, proving the bound. For odd k=2a+1≥3, the central coefficient is at most (2/5)·2^k: its fraction is 3/8 at k=3 and decreases, by the successive ratio (2a+3)/(2a+4). The two smaller terms sum to at most 4^{a−1}+4^a=5·4^{a−1}. Multiplication gives 4^{k−1} again. The initial k=1 case is immediate. The explicit recurrence can be much less than this estimate.

## 4. Transfer to the directed problem

Use the exact recursive cells and suffix separation in [the companion proof](PROOF.md), §1. At each nonsortable branch node choose a cheap cycle monochromatic in the side sign, and reduce the chosen ball to the cycle support. Select the plus-sign events in increasing depth, and minus-sign events in decreasing depth. Each is aligned even when the support varies: any two events sharing a chain were separated on the earlier-depth event's chosen side of the entire descendant. Thus the number of nonsortable nodes on a branch is at most 2T(k). The same §10 interface bounds yield width ≤4k+2c_k T(k), where c_k=1000(k+1)^5.

The exact deterministic sweep therefore uses p=4k+2c_k T(k)+1 memory and takes F(k,p)n^(p+1)+O(kn(n+m)) time with Cao–Qi–Wang's F(k,p) bound, i.e. n^{O(k^5·4^k)} in the same comparison/addition model, with a k-dependent prefactor. The application need not compute the unknown solution's decomposition or routes. The scope, reconstruction, and earlier special-case results are as in PROOF.md.

This is a paper result. The companion `DirectedAnchorPreimage.lean` verifies the prefix-pigeonhole step and the exact chronological subinterval product. The route compression, cycle selection, recurrence, geometry and original sweep are not formalized in Lean.
