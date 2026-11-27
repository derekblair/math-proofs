# Equality, sharper pair bounds, and antichain orders in the poset shuffle inequality

[PR #122](https://github.com/derekblair/math-proofs/pull/122) proves the directional shuffle bound. For incomparable \(x,y\) in a finite poset \(P\), let
\[
A=\{x\}\cup(U(x)\setminus U(y)),\qquad
B=\{y\}\cup(D(y)\setminus D(x)).
\]
Use strict upsets and downsets. The groups are disjoint, and there are no comparabilities \(a<_P b\) with \(a\in A,b\in B\). The bound is \(\Pr(y<_L x)\ge \binom{|A|+|B|}{|B|}^{-1}\). The results below use the same fiber decomposition, which fixes the outsiders' absolute positions and the two groups' internal orders. Each nonempty fiber has exactly one extension with all B before all A, hence exactly one extension with \(y<_L x\).

## Exactly when the directional bound is attained

Equality holds if and only if both conditions hold:
1. The induced subposet on \(A\cup B\) is the disjoint union, in the order sense, of the two induced posets on \(A\) and \(B\).
2. \(A\cup B\) is a module. Every outsider is below all its elements, above all its elements, or incomparable to all its elements.

For sufficiency, each outsider has the same relation to every filtered element, so its fixed position is valid for every shuffle of the two internally fixed group orders. There are no cross relations by the first condition. Every fiber therefore has the full binomial size.

For necessity, equality implies every fiber has full binomial size, because each fiber has one favorable member and size at most the binomial bound. In particular, the all-A-first shuffle must be feasible in every fiber. A cross comparison \(b<a\) would forbid this shuffle everywhere. The other cross direction is already impossible.

Now suppose an outsider \(z\) is below some member of \(A\), but fails to be below all of \(B\). There is an extension with exactly the strict nonsuccessors of \(z\) before \(z\), obtained by extending the ideal \(P\setminus(\{z\}\cup U(z))\), taking \(z\), and then extending its upset. In that extension every A-nonsuccessor of \(z\) is before it, and at least one B letter is also before it. The all-A-first shuffle would move an A-successor of \(z\) into the prefix before \(z\), a contradiction. Therefore any outsider below some A is below all of B.

Dually suppose \(z\) is above some member of \(B\), but fails to be above all of \(A\). Extend \(D(z)\), take \(z\), then extend the remainder. At least one B letter lies before \(z\) and some A letter lies after it. The all-A-first shuffle decreases the number of B letters in the prefix, pushing a B-predecessor of \(z\) after it. This is impossible. Thus any outsider above some B is above all of A.

The group definitions give two direction rules for outsiders. If \(z<b\) for some B, then \(z<y\) and \(z\notin B\) imply \(z<x\), so \(z\) is below all of A. If \(a<z\) for some A, then \(x<z\) and \(z\notin A\) imply \(y<z\), so \(z\) is above all of B. Combine these with the two conclusions just proved. Any relation below a member of the union forces \(z\) below both groups, and any relation above forces \(z\) above both. This is exactly the module condition. It uses the standard poset-module notion of an outside element having the same relation to the whole module. [Cooper and Kirkpatrick, modular decompositions](https://people.math.sc.edu/cooper/posetpatterns.pdf)

## An explicit stronger denominator from cross precedences

Let \(p=|A|\), \(q=|B|\). For each \(b<_P a\) with \(b\in B,a\in A\), compute
\[
\ell_b=1+|D(b)\cap B|,\qquad h_a=p-|U(a)\cap A|.
\]
The internal B position of \(b\) is at least \(\ell_b\), and the internal A position of \(a\) is at most \(h_a\). Thus every valid shuffle puts \(B_{\ell_b}\) before \(A_{h_a}\), whether or not the internal orders in its fiber are known.

Equivalently, in the first \(\ell_b+h_a-1\) filtered letters there are at least \(\ell_b\) B letters. Decode this as a lower bound on each corresponding grid diagonal in the usual binary path representation. Let \(C\) count shuffles satisfying all such implied prefix bounds. It is computable by the lattice-path recurrence with \((p+1)(q+1)\) states once the cross comparabilities have been read. Every fiber has at most \(C\) members, so
\[
\Pr(y<_L x)\ge 1/C.
\]
This bound also holds in any nonempty union of complete fibers. Whenever there is a cross relation it strictly improves the binomial denominator. If the two induced groups are chains and their union is a module, all cross positions are exactly the stated bounds and the bound is attained. This includes nontrivial proper corridors. The equality classification above concerns the original binomial bound, not every case of equality in the refined bound.

## A computable lower bound for the full specified order of an antichain

Let \(x_1,\ldots,x_k\) be distinct pairwise incomparable elements, with prescribed extension order \(x_1<\cdots<x_k\). Choose any binary parenthesization of that sequence into adjacent interval blocks. At an internal node split an interval into nonempty adjacent blocks \(I,J\), let \(u\) be the last anchor in \(I\), and let \(v\) be the first anchor in \(J\). Define
\[
\begin{aligned}
p_{I,J}&=|I|+\left|\Big(\bigcup_{i\in I}D_P(x_i)\Big)\setminus D_P(v)\right|,\\
q_{I,J}&=|J|+\left|\Big(\bigcup_{j\in J}U_P(x_j)\Big)\setminus U_P(u)\right|.
\end{aligned}
\]
The probability of the full specified order is at least the reciprocal of the product of \(\binom{p_{I,J}+q_{I,J}}{p_{I,J}}\) over the internal nodes. The minimum product over parenthesizations can be obtained by interval dynamic programming, with \(O(k^3)\) split candidates after precomputing the interval unions and with exact integer arithmetic for the products.

Process the internal nodes in any bottom-up order. The constraints enforced so far form internally ordered chains on disjoint blocks of anchors. Uniform conditioning on these constraints is exactly the uniform linear extension law of the poset enlarged by their transitive closure. Added edges cannot create a comparable pair of anchors across distinct blocks: a path between blocks would need an original comparison between distinct anchors connecting two different blocks, which cannot exist. More precisely, among the strict predecessors of the last left anchor \(u\), the new elements can only be the earlier left anchors and original predecessors of left anchors. The strict downset of the first right anchor \(v\) is unchanged. Likewise the strict upset of \(v\) gains only later right anchors and original successors of right anchors, while the strict upset of \(u\) stays unchanged. This follows by following any transitive-closure path and noting that an original subpath between two different anchors is impossible. Hence the blocker group sizes for joining \(u< v\) are exactly \(p_{I,J},q_{I,J}\). Apply #122 and multiply the conditional probabilities. The binomial products telescope to \(k!\) if all specified anchors have the same upsets and downsets. In that case the prescribed order has probability exactly \(1/k!\), by symmetry. This extension does not assert a balanced pair in every poset.

## Verification

A separate exact replay enumerated extensions of 5,230 naturally labeled posets through order six, checking 86,340 ordered incomparable pairs and 5,022,944 pair-extension incidences. It observed 13,380 equalities in the binomial bound, each matching the module criterion, and 7,017 strict denominator improvements from cross relations. A further 10,338 prescribed antichain orders were checked on sampled seven-element posets against independently enumerated extension frequencies. These are written proofs with finite replay. #122's underlying cardinality inequality is Lean-verified, but the new classification and applications here have not been put in Lean.

For a small example where the merge tree matters, take four incomparable anchors x₁,x₂,x₃,x₄ and two outsiders a,b with only a<x₂ and x₃<b. The balanced merge (x₁x₂)(x₃x₄) gives denominator 80. The two one-direction combs give 100, and the other two parenthesizations give 120. Literal enumeration gives four favorable extensions among 180, so this example demonstrates the optimization without claiming its best bound is always attained.
## Joint stochastic comparison

For a fixed skeleton (outsider slots and sorted A and B orders), a
shuffle is encoded by \(z_i\), the number of B letters before the
\(i\)-th A letter. These are nondecreasing integers in \([0,q]\).
Every cross precedence is a coordinate-wise lower bound. Outsider
positions may initially give both lower and upper bounds on
the number of B letters after a filtered prefix. Upper bounds are
redundant because the all-B-first shuffle is feasible and maximizes each
prefix B count. Fixing a prefix B lower bound is equivalently imposing
that some \(B_j\) precede some \(A_i\), so translates to a lower coordinate
bound on \(z_i\). Taking prefix maxima then gives one least staircase.
The allowed shuffles are thus a principal filter in the finite
distributive lattice of weakly increasing vectors \(z\).

This gives more than the endpoint probability inequality. The full
unlabeled shuffle weight \(w(z)\) is the number of skeletons admitting
\(z\), a sum of principal-filter indicators. Consequently it is
coordinatewise nondecreasing, even after restricting to any subset of
skeletons. Relative to the uniform free-shuffle law the density is
proportional to \(w\), so one application of the
[FKG inequality](https://math.bme.hu/~balint/oktatas/perkolacio/percolation_papers/fortuin_kasteleyn_ginibre.pdf)
shows that for every increasing event of the unlabeled word, its actual
probability is at least its uniform free-shuffle probability. Conditional
on a single skeleton, FKG also proves positive association for any two
increasing events, because the uniform measure on a principal filter
is log-supermodular.

Do not infer those stronger FKG hypotheses for the full mixed law.
The exact replay includes a nine-element example with unlabeled weights
115, 161 at two staircases and 69, 207 at their meet and join: their
products disprove log-supermodularity. It also includes an eight-element
example of strictly negative covariance of two same-direction
fixed-label events, whose joint and marginal counts are 126, 141 and
136 out of 152. The latter is about labels, not a counterexample to
global stochastic dominance or to unlabeled association.
See [Shepp](https://faculty.wharton.upenn.edu/wp-content/uploads/2012/04/Fkg-inequality-and-some-monotonicity-properties-of-partial-orders.pdf)
for related two-population order constraints; the current reduction
freezes outside slots in an arbitrary poset.

## Degree-capacity refinement of the universal denominator

Form the bipartite comparability graph with an edge from \(b\in B\) to
\(a\in A\) for each \(b<_P a\). Let \(d_1\le\cdots\le d_p\) be the
sorted A indegrees and \(e_1\ge\cdots\ge e_q\) the sorted B outdegrees.
At grid state \((i,j)\) all neighbors of the first \(i\) A vertices
are among the first \(j\) B vertices. Thus
\[
 j\ge d_i\ (i>0),\qquad i\le p-e_{j+1}\ (j<q),\qquad
 \sum_{a=1}^{i}d_a\le\sum_{b=1}^{j}\min(i,e_b).
\]
For the first inequality, the maximum indegree among \(i\) chosen
A vertices is at least \(d_i\). Among the \(q-j\) not-yet-placed B
vertices some has outdegree at least \(e_{j+1}\), proving the
second. For the third, count edges from the chosen A vertices:
their total is at least the sum of the smallest \(i\) indegrees,
while each chosen B vertex can account for at most its outdegree
and at most \(i\) edges. These restrictions hold without knowing the
actual per-fiber internal permutations and can be imposed together
with the individual cross-rank necessities above. Prefix sums of
the capped B degrees for each \(i\) require \(O(pq)\) arithmetic
operations after sorting; each state then tests the three constraints
in constant arithmetic time. This is an exact computable denominator
for the inequality, not an exact algorithm for all linear extensions.

For instance, use \(x<a_1,a_2\), \(b_1,b_2<y\) and the matching
cross comparisons \(b_1<a_1,\ b_2<a_2\), with no other strict relations.
The binomial denominator is 20, the individual-rank path count is 19,
and the degree-capacity count is 14. There are literally 4 favorable
extensions out of 48, so the true reciprocal denominator is 12.
In the full enumeration through six vertices, degree rules strictly
improved the individual-rank corridor in 1,070 ordered pairs and
never violated the asserted lower bound.

Run node equality-replay.js for the equality, denominator, prescribed
antichain order, and correlation checks. CorridorRefinements.lean
checks the monotonicity of principal-filter weights and the finite
edge-capacity inequality. It does not formalize the equality
characterization, stochastic dominance, or antichain order theorem.
