# The regular-hexagon analogue of Bevan–Homberger–Tenner Question 5.5

**Result.** For any fixed orientation of a regular hexagon, let the circumradius be $t>0$, and let $n(t)$ be the smallest order of a nondegenerate permuted packing of translates. The packing centres are $(i,p(i))$, $i=1,\ldots,n(t)$, where $p$ is a permutation. Then
$$
\lim_{t\to\infty}\frac{n(t)}{t^2}=\frac{3\sqrt3}{2},
\qquad
\lim_{t\to\infty}d(\Pi_t,[1,n(t)]^2)=1.
$$
The second limit holds for every choice of minimum packing, not merely for a constructed sequence. The setting is translational: all hexagons have the same fixed orientation. The one-centre case has a zero-area clipping square, so is excluded from the density problem and recorded separately in Lean. No upper bound of 1 is needed as a premise.

**Source.** D. Bevan, C. Homberger and B. E. Tenner, *Prolific permutations and permuted packings: downsets containing many large patterns*, Definition 3.2 and the question about regular hexagons immediately after [Question 5.5](https://arxiv.org/pdf/1608.06931v3#page=20). The paper defines density by summing the clipped area of each translate and dividing by the square's area. Searches for this particular asymptotic permuted-packing problem found no earlier solution; this is a bounded priority check, not a claim of exhaustive novelty.

## Proof

- Put $q(x,y)=\max(2|x|/\sqrt3, |x|/\sqrt3+|y|)$. Its sublevel set at $t$ is the hexagon with vertices $(0,\pm t)$ and $(\pm\sqrt3t/2,\pm t/2)$. Indeed, the vertical slices are given by $|x|\le\sqrt3t/2$ and $|y|\le t-|x|/\sqrt3$. Its area is $At^2$ for $A=3\sqrt3/2$, by integrating the vertical height. For fixed orientation precompose the gauge with the corresponding planar rotation. Two translates have disjoint interiors exactly when the gauge of their centre difference is at least $2t$. Below that threshold the midpoint is in both interiors; otherwise the triangle inequality precludes an intersection.
- The columns $(\sqrt3,0)$ and $(\sqrt3/2,3/2)$ form a basis of determinant $A$; every nonzero lattice vector has gauge at least 2. Apply the inverse rotation to get the ideal basis for the chosen orientation. Approximate each row of the scaled basis, at scale $R$, by a primitive integer pair within arbitrarily small fixed relative error. First approximate the row direction by a primitive integer vector $v$ after scaling. Extend $v$ by a fixed integer vector $w$ with determinant 1 using Bézout, and choose vectors $mv+w$ at the desired scale. They are primitive for all integer $m$.
- A two-row primitive integer matrix with positive determinant $N$ generates a lattice whose reduction modulo $N$ is the graph of a permutation. Each coordinate projection is onto by row primitivity. Lattice differences with first coordinate zero have second coordinate a multiple of $N$ by the determinant identity and primitivity of the first row. A lattice vector of first coordinate 1 thus generates a slope modulo $N$, and surjectivity of the second coordinate makes the slope invertible. Representatives give an $N$-point permutation, with all point differences in the lattice since $N\mathbb Z^2$ is in the lattice. The gauge separation is at least $2R(1-12\epsilon)$, and $N\le (A+14\epsilon)R^2$. Take $R=t/(1-12\epsilon)$ and send $\epsilon$ to zero after taking the upper limit. This yields $\limsup n(t)/t^2\le A$ and proves existence of minimum packings for all sufficiently large $t$.
- Conversely, comparing any two centres of an admissible $n\ge2$ packing gives $t\le4n$. Each hexagon lies within the board expanded by $4t$ in each direction. The interiors are disjoint and have the same area as the closed hexagons. Thus $nAt^2\le(n-1+8t)^2$, giving $n\ge At^2-272t$.
- At most $4\lceil4t\rceil$ centres are close enough to the sides to lose clipped area, because there is one centre in each row and column. Consequently the summed clipped area lies between $(n-16t-4)At^2$ and $nAt^2$, while the clipping square has area $(n-1)^2$. The normalized order limit gives the full density limit 1.

## Lean

Main theorem: `PermHex.regular_hexagon_limit` in `LiteralHex.lean`. It quantifies over any unit rotation pair, all eventually minimum packing selections, the box $[1,n]^2$, pairwise disjoint topological interiors, and the actual product Lebesgue areas of the clipped pieces. `PermHex.order_limit` is the accompanying sharp order asymptotic; `PermHex.eventually_paper_min_exists` rules out vacuity for large radii. `PermHex.singleton_degenerate` records the zero-area literal singleton.

Use Lean 4.34.1 and Mathlib v4.34.1 at `d13f23b723b8a846827a245b89c10fc7d3f11612`. Run:

```bash
./Verify.sh /path/to/mathlib4 /path/to/new-verification
```

The script starts from a clean source-only temporary directory, builds each module, limits the axiom footprint to `propext`, `Classical.choice`, and `Quot.sound`, and invokes `leanchecker -v` on each module.
