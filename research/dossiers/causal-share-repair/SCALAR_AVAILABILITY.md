# Exact sparse pair-mask topology for one Shamir repair

A model result about single-repair passive scalar confidentiality and helper availability, not causal full-transcript simulation, a KEM, a deployment, or a prescription to relax a deployed security policy. No real keys, users or transports were used.

## Interface and threat model

Let k=t+1≥2. A pool of n≥k potential helpers and a reserved distinct nonzero repair target a are distinct nonzero points over F_q. The polynomial has degree≤t, with uniform nonconstant coefficients and scalar secret f(0). Before masked messages or pads are generated, a common authenticated readiness declaration fixes exactly k available helpers H. The theorem is for separately fixed choices of committee, exposed helpers and optional read site, or for such choices sampled independently of the secret and private polynomial state. Readiness that itself depends on private state can change what the view reveals and is outside the theorem. The result must hold for **every** such committee, not just a graph-aware optimal choice. With n=k+f this permits up to f departures before commitment, if the rest are live. Availability after commitment or during transmission is not provided. Correctness assumes honest computation, a correct common membership choice, a reachable target, and delivery by committed helpers.

A public simple graph G on the potential pool specifies private bilateral pad relations. Use an independent uniform one-use field pad on each edge with both endpoints in the chosen committee, contributing it with opposite signs to the two weighted helper messages. Each bilateral pad is held only through ideal confidential authenticated provisioning in the abstract model, not retained across repairs. The recipient adds the weighted messages to get f(a) since all pads cancel. It holds no central pad seed. The observer sees all masked helper messages, hence the repaired share, and all actual helper evaluations and corresponding incident edge pads for a specified subset C of up to c committed helpers. This is a passive compartment exposure; it does not include other true shares, retired state, more than one repair, selective late dropout, active tampering or unapproved buffer and logging paths. Assuming upfront separate pairs are possible is an ideal model, not a claim of post-quantum private link setup. Cost is the count of provisioned pair relations, not wall time, total erasures, KEM calls or all-round entropy.

## Exact scalar secrecy criterion

Write the weighted true-input coordinate at helper x_i as v_i=λ_i(a)f(x_i), where λ_i is its Lagrange basis polynomial for H. Every λ_i(a) is nonzero, so v gives an invertible coordinate system for the full polynomial. The repaired share is Σ_i v_i. The scalar secret is Σ_i α_i v_i, where

    α_i = λ_i(0)/λ_i(a) = C·(a−x_i)/(−x_i),
    C = ∏_(h in H)(−h)/(a−h) ≠0.

These α_i are pairwise distinct: the expression is C·(1−a/x_i) and a,C,x_i are nonzero. This depends on using exactly k=t+1 weighted helper coordinates and on target a≠0.

**Theorem.** The complete observed view has identical law for every scalar secret iff there is at least one edge in G[H∖C].

If no such edge exists, every used pad is known to the observer from an exposed endpoint. After subtracting known pads the observed linear map determines all weighted coordinates and therefore the scalar. This is an algebraic impossibility in the stated model, not a finding on a system.

If an unexposed edge (u,v) exists, consider any desired secret change Δ. Change the two coordinates by opposite quantities r and −r, with r=Δ/(α_u−α_v). There is a unique corresponding polynomial change by weighted interpolation. It preserves each exposed helper coordinate, the repaired sum, and shifts the secret by exactly Δ. Shift that one hidden pad by the opposite amount to keep the visible masked messages unchanged. Other true inputs, all exposed pads, and other privately sampled masks are unchanged. This gives an invertible translation from uniform initial-and-pad inputs for one secret to those for the other. Hence the secret-conditioned views are exactly equal over every eligible field; there is no computational assumption or statistical error. The construction may leak other linear combinations of nonconstant share state. It does not imply secret privacy after additional time windows, repeated repairs, or a wider snapshot domain.

## Sharp provisioning cost and comparison with full simulation

Assume 0≤c≤k−2 and let h=k−c. Any h-set of the n helpers can be extended to a committee of k and made its entirely unexposed subset by marking the extras exposed. So the scalar policy works for all committees and up to c exposures iff each h-set spans an edge, equivalently the independence number α(G)<h. Conversely if α(G)<h, even a larger honest set contains an edge. If c≥k−1, the all-committee policy is impossible because at most one honest vertex may remain. With precommit departures, no extra graph condition enters the scalar theorem: the chosen available committee is already one of the universal k-sets.

Let d=h−1 and divide n=ud+r with 0≤r<d. By Turán’s theorem applied to the complement, the sharp minimum number of provisioned relations is

    r·binom(u+1,2)+(d−r)·binom(u,2).

A union of d balanced cliques attains it; the graph can be disconnected.

For comparison, require **full honest-input simulation**, meaning two complete weighted input vectors with equal repaired sum and equal exposed helper values induce the same traffic law, regardless of the scalar. Hidden edge pads uniformly span the incidence subspace of the honest graph. Its mass consists of all zero-sum vectors separately on each component: edge differences generate such vectors via paths from a component root, and every edge stays within a component. Hence full simulation holds iff the honest graph is connected. If it is disconnected, independent component sums are necessarily observable; scalar confidentiality alone can still survive. Full simulation for every h-set is equivalent to vertex connectivity at least n−h+1: removing n−h vertices must leave a connected graph, and if fewer removals left a disconnected graph one could keep an h-set straddling components. The minimum edge count for that connectivity is ceil(n(n−h+1)/2) by Harary’s theorem. These two optima solve different privacy objectives; the smaller graph is not a drop-in full-transcript replacement.

Example: n=12, k=8, c=2 (four precommit departures tolerated). Every possible set of six unexposed helpers must span an edge. Balanced clique sizes 3,3,2,2,2 give exactly nine relations. Full honest-input simulation for the same rule needs 42. Public target and required sites fit GF(17); the finite-field criterion itself is independent of the field once sites exist.

## Exact diagnostic for one extra, non-helper observed value

A narrower extension permits one extra authorized actual evaluation f(b), where b is distinct from 0, a, and all helpers. Let β_i=λ_i(b)/λ_i(a). On the hidden edge-incidence space the scalar remains private iff the restriction of α is not in the span of the restriction of β: the extra evaluation must be preserved by a secret-shifting translation. Each edge restriction of β is nonzero. A direct subtraction of the two Lagrange ratios shows that for an edge (u,v),

    (α_u−α_v)/(β_u−β_v)
      = C' · ((b−x_u)(b−x_v))/(x_u x_v),

where C'≠0 is the same for every edge. Consequently the extra-read scalar privacy condition holds exactly when those products take **at least two distinct values over the hidden honest edges**. A length-two honest path always suffices (adjacent edges share a nonzero factor and differ on two distinct sites). A disjoint matching may or may not suffice, depending on the field and site placement. Thus even ordinary supplementary read budgets cannot be imported into the one-edge theorem unchanged. This uses one extra authorized evaluation at a specified distinct non-helper point, not access to another complete repair.

## Verification and precedents

[Sparse secure aggregation](https://eprint.iacr.org/2020/704) already treats connectivity after participant drops/collusions, and [Zhao–Sun](https://arxiv.org/abs/2101.07750) study substantially stronger dropout/communication models; neither full simulation nor pair-mask cancellation is put forward as new. [Huang–Bruck](https://arxiv.org/abs/1706.00500) focuses on secure repair and bandwidth. The graph formulas alone are classical [Turán theory](https://www.renyi.hu/~p_erdos/1971-01.pdf) and [Harary's maximum connectivity theorem](https://pmc.ncbi.nlm.nih.gov/articles/PMC220921/). The narrow candidate is the exact single-scalar graph criterion for weighted Shamir repair, the resulting sharp resource separation, and the extra-one-read field-dependent threshold. Limited primary-source search found no exact same criterion; priority unestablished.

Synthetic controls checked 10,560 combinations of GF(11) helper sets, small graphs and exposed sets against direct ranks (both the single-scalar and extra-read conditions). Also checked all 32,768 labeled graphs on six vertices, confirming minimum scalar edge counts 15,6,3,2,1 for honest-set sizes 2,3,4,5,6. No real systems or live behavior were tested. The safety conditions only address this single repair with an ideal classical visibility model, not active recovery, cross-time leakage, or [ML-KEM](https://csrc.nist.gov/pubs/fips/203/final).

Lean 4.34.1 checks the Lagrange ratio injectivity argument, one-edge shift and two-edge/extra-read determinant shift. The full probability and extremal graph conclusions are written proofs, not end-to-end Lean formalizations. Exact AGY/Neon was unavailable locally; no substitute or unpublished sharing.
