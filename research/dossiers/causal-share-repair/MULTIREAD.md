# Sharp field-uniform topology for a visible repair plus fixed external reads

Ideal passive single-repair model. No KEM, endpoint or transport test, active dropouts, or multi-epoch privacy claim.

Let k=t+1 live helpers H interpolate degree-at-most-t shares with scalar secret f(0), with uniformly independent mask coefficients. All helper points, nonzero target a, and r extra public read points b_1,...,b_r are mutually distinct and nonzero. Committee eligibility, the chosen helper set, exposure set, and extra read sites are fixed independently of hidden state and coins, or the statements are interpreted separately for each such fixed choice. Commit the helper set before generating or observing messages. Some fixed selected helpers reveal their actual shares and incident masks. Remaining helpers are the honest vertex set; G is the induced honest graph of hidden, independent, one-use pairwise zero-sum pads. The complete masked weighted repair batch is visible; its sum f(a), the designated external evaluations f(b_j), and the exposed helper shares/pads are all in the observer's view. No other shares, retained history, late departure, or buffers are included. Protecting the scalar alone is weaker than simulating every input given these authorized values.

## Exact criterion for fixed field and embedding

Use helper coordinates v_i=λ_i(a) f(x_i), with nonzero Lagrange weights and invertible weighted interpolation. For each possible output z define its coefficient vector α(z)_i=λ_i(z)/λ_i(a). A hidden edge changes two honest coordinates oppositely, and its matching mask change preserves traffic and all exposed values. These edge differences span exactly the zero-sum vectors on each honest component. Conversely any true-input difference preserving traffic after adjusting hidden masks lies in this span. Invariance of uniform affine views therefore reduces to whether a unit-secret change can be achieved within that span while preserving the authorized reads. If not, a linear-functional identity expresses the scalar from the completed view.

Represent the restriction of each output functional by an edge row indexed by hidden edges, α(z)_u−α(z)_v. Set L(X)=∏_(x in H)(X−x). For z distinct from a and helper sites (including z=0), every entry factors as

    α(z)_u−α(z)_v =
      (L(z)/L(a)) · (a−z) · (x_u−x_v) / ((z−x_u)(z−x_v)).

All row and column prefactors are nonzero, so one may test only the simpler rows

    B(z)_(u,v) = 1 / ((z−x_u)(z−x_v)).

The scalar is perfectly private iff B(0) is **not** in span(B(b_1),...,B(b_r)). This works over the exact field, including matching and disconnected honest graphs, and can be checked by comparing the two finite row ranks. Interpret empty rows and zero read sets in the usual linear-algebra sense. The result is a design audit criterion, not reciprocal access to shares, an exploit or a protocol for changing the allowed view.

## Sharp topology that is uniform in fields and labels

Put d=r+1. For a fixed abstract honest graph, **every eligible field/site embedding gives perfect scalar privacy iff the graph has a connected component of size at least d+1**. In fact the necessity counterexample works with any fixed target a and any fixed distinct b_j over a base finite field, after allowing a finite extension and relabeling the helper sites.

**Sufficiency.** Suppose the scalar row were spanned by the read rows. Equivalently, for some scalars θ_j the function on helper sites

    R(X) = C_0·(a−X)/(−X) − Σ_j θ_j C_j·(a−X)/(b_j−X),
    C_z = L(z)/L(a),

is constant on each honest component. Here C_0 and every C_j are nonzero. Its denominator divides D(X)=X∏_j(X−b_j), and its numerator over D(X) has degree at most d. This numerator is nonzero at 0, since the first summand has nonzero residue there and every other summand is regular there. If R equals c on d+1 distinct component sites, its numerator minus cD is a nonzero polynomial of degree at most d with d+1 roots, a contradiction.

**Necessity, even after fixing a and b_j.** Suppose each honest component has at most d vertices. Work over the algebraic closure of the base finite field. Form D(X)=X∏_j(X−b_j), whose roots are simple, so D' is not the zero polynomial (even in small characteristic). Exclude the finitely many critical values D(x) with D'(x)=0, as well as 0 and D(a). Choose a distinct remaining value for each honest component. Each regular fiber D(X)=v has exactly d distinct roots in the algebraic closure; different fibers are disjoint, and no root is 0, a or any b_j. Label each honest component by distinct roots of its chosen fiber. These labels, all chosen fiber values and enough further unused labels for the exposed/helpers outside this subgraph lie in a common finite extension. Adding unused labels changes C_z but never makes them zero.

On each chosen component the rational function 1/D is constant, with a nonzero simple residue at every pole, especially 0. Partial fractions over the fixed simple poles give
    1/D(X)=Σ_(z in {0,b_1,...,b_r}) (1/D'(z))/(X−z).
Starting with the actual secret Lagrange ratio C_0·(a−X)/(−X), multiply 1/D by a nonzero scalar so its residue at 0 matches the secret ratio. At each b_j choose the coefficient of C_j·(a−X)/(b_j−X) to match any desired residual residue there, since C_j(a−b_j)≠0. The resulting secret-minus-reads rational function differs from the scaled 1/D by a global constant: their simple residues match, no other poles exist, and all summands are bounded at infinity. It is thus constant on components. The secret row lies in the read span on edges, contradicting privacy for this allowed assignment. This does not say all labelings on small or fixed fields fail when components are small; the exact rank test handles those cases.

**Explicit witness in many individual fields.** If d divides q−1 and there are at least s+1 distinct multiplicative cosets of μ_d for s honest components, take a=−1, b_j the nonzero elements of {ζ−1:ζ∈μ_d}, D(X)=(X+1)^d−1. For each component choose a different nonidentity coset u μ_d, and label its vertices by distinct points uζ−1. These are regular fibers, distinct from all forbidden points. Also require enough remaining nonzero values for the rest of the pool. This construction uses public theoretical instances, not real targets or external data.

## Universal provisioning consequences

With n potential helpers, every k-helper committee eligible and at most c exposed helpers, assume 0≤c≤k≤n and set h=k−c. A graph gives field-uniform scalar privacy across that model iff **every induced h-vertex subgraph has a connected component of order ≥r+2**. Indeed every h-subset is realizable as exactly the honest vertices of some committee, and the property is monotone under adding honest vertices. If h<r+2 the requirement is impossible, even for a complete graph. This is a bounded-component induced-subgraph condition, **not** the condition that every h-set contain an (r+2)-clique.

Some sharp special cases follow, counting preprovisioned relations rather than communication or latency:

- r=0: the criterion is the independence-number/Turán condition from the single-scalar model.
- h=r+2: every induced h-subgraph must be connected. This is vertex connectivity at least n−h+1, with sharp ceil(n(n−h+1)/2) relations by Harary's theorem.
- h=n: one connected component of size r+2 is needed, with minimum r+1 relations, attained by a tree on r+2 vertices and isolated remaining vertices.
- h=n−1 and r≥1: the sharp minimum is r+3 relations whenever n≥r+3. Write d=r+1≥2. A cycle of length d+2 plus isolates attains the property: deletion of a cycle vertex leaves a connected path on d+1, and deletion of an isolate leaves the whole cycle. With at most d+1 edges, no component exceeds d+2 vertices; one of size d+2 would exhaust the budget as a tree, and deleting a nonleaf splits it into components of at most d. Otherwise at most one component has size d+1 (two would require ≥2d>d+1 edges), and deleting one of its vertices suffices to defeat the property. The r=0 case can differ (two disjoint edges can tolerate one deletion on n≥4).
- The general minimum edge count for this bounded-component condition is not claimed. Extremal results for [every h-set containing a large clique](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v32i1p22/pdf/) do not apply automatically. Component-size graph immunity has independent prior context in [dismantling problems](https://www2.math.uu.se/~svantejs/papers/sj206.pdf); the novel candidate here is the equivalence between the field-uniform repair predicate and this existing type of invariant, not a new invariant.

Primary context: [Huang–Bruck secure repair](https://arxiv.org/abs/1706.00500), [sparse secure aggregation](https://eprint.iacr.org/2020/704), and [Harary's maximum connectivity theorem](https://pmc.ncbi.nlm.nih.gov/articles/PMC220921/) solve different general problems. Limited search did not locate this exact multi-read field-uniform characterization, but priority remains open. No protocol for post-commit disappearances or threshold ML-KEM; no claim that an authorized trajectory across time preserves secrecy.

## Verification

Pinned Lean 4.34.1 checked the normalized edge ratio, that a pole with nonzero numerator rules out a constant rational function, and the root-count bound for a constant fiber. Only standard axioms are present. The finite-field extension/partial-fraction and extremal graph arguments are proof text rather than fully formalized. Synthetic exact controls tested 3,072 five-vertex graph/field instances across extra-read counts one through three, including constructed bad embeddings, and confirmed the sharp single-deletion relation optima 4, 5 and 6 in all six-vertex cases for d=2,3,4. Exact Neon XHigh was unavailable here; no substitute, real data or remote changes.
