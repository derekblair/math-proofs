# Erdős–Gyárfás for finite odd-order metabelian Haar graphs

Every cubic Haar graph over a finite metabelian group of odd order contains
a simple cycle of length **4, 8, 16, or 32**. Here the graph has two copies of
the group, and `(left,g)` is adjacent to `(right,g p)` for each of three
distinct ports `p`. The result does not require the graph to be connected or
vertex-transitive, or the group to be nilpotent. It does **not** settle the
full Erdős–Gyárfás conjecture, all cubic graphs, or all odd-order Haar graphs.

The Lean theorem is [`HaarMetaFullOdd.arbitrary_three_ports`](HaarMetaFullOddEnd.lean).
Its cycle witness is an injective cyclic sequence of vertices, not merely a
closed walk. Metabelian means the derived subgroup is abelian. The file
also provides the normalized-port form `HaarMetaFullOdd.normalized`.

## Proof outline

1. Normalize the three ports to `1,x,y` and restrict to the subgroup generated
   by `x,y`. In the abelianization, the derived subgroup acts as an abelian
   deck group. Its odd order means multiplication by 2 is injective.
2. With no nonzero relation `a X + b Y = 0` for `|a|,|b| ≤ 3` between
   projected ports, a 4-by-4 nonwrapping honeycomb patch embeds. An exact
   abelian-cover certificate finds a 16- or 32-cycle.
3. Otherwise reorder and translate the three ports, and cancel factors of two
   in the projected group. The seven cases are collapse, arithmetic progression,
   three primitive cyclic strips, and two order-three torsion cylinders. Large
   quotients are handled by fixed-width embedded patches. Smaller cyclic and
   torus quotients have their own exact checks. Three residual certificates
   use translations that lift in the Haar graph; no claim is made there about
   arbitrary abelian covers without that equivariance.
4. In each certificate, a candidate closed walk lifts whenever its voltage is
   zero. At a repeated vertex the resulting voltage relation leads to a smaller
   proof state. The checks use exact integer linear combinations and injectivity
   of doubling. A terminal witness has no repeated vertices.

## Sharpness
 
[An explicit 2,758-vertex example](HaarSharpAffine.lean#L90) shows the bound
is sharp. Its group is the affine semidirect product of the additive field
F₁₉₇ by C₇, with the generator acting by multiplication by 36. Lean checks
an explicit simple 32-cycle and excludes simple cycles of lengths 4, 8,
and 16. This is not a minimum-size claim.

[The sharpness proof](HaarSharpOptimal.lean) constructs a cubic Haar graph of
this class with a 32-cycle and no 4-, 8-, or 16-cycle. The group is
`(F₃⁷ × F₃⁷) ⋊ C₇`, with circular shifts on its two lamp arrays.
Rather than enumerate its vertices, the proof compares two reduced half
paths from a common start. For cycles of length 4, 8, and 16, respectively,
there are only 6, 24, and 384 half paths to check. Lean verifies the
exclusions and an explicit 32-cycle independently of the upper bound.

## Prior work and scope

[Burkhart, *Odd-ordered Cayley graphs satisfy Erdős–Gyárfás*, Theorem 1.1](https://arxiv.org/html/2611.05060v1)
covers ordinary Cayley graphs. The theorem here is about two-orbit Haar
graphs. This distinction is substantive: [Qin and Zhou, Construction 1 and
Lemma 5.1](https://arxiv.org/pdf/1610.07307) give a semisymmetric family over
odd metacyclic groups. Those graphs are not vertex-transitive, so they are not
Cayley graphs. Burkhart's intersection-at-one-vertex figure-eight uses four
incident edges and cannot itself occur in a cubic graph. The abelian-lifting
idea is related, but the patch and torsion arguments are different. No
absolute literature priority is claimed.

## Reproduce

Use Lean 4.34.1 and a cache-populated Mathlib checkout at
`d13f23b723b8a846827a245b89c10fc7d3f11612`. This dossier is standalone; the
files it repeats from earlier dossiers are included to pin the exact inputs.
The repository's ordinary Lean Action check alone does not replay a standalone
dossier.

```sh
python3 verify.py /path/to/pinned/mathlib4 -j 4
python3 certificates/quotient_cases.py
python3 certificates/check_reduced.py
```

The last two commands are independent exact checks of the finite quotient
case split and selected voltage certificates. They supplement rather than
replace the Lean proof. The verifier checks file digests, builds all imported
dossier modules in a fresh output directory and audits the final exported
theorem axioms.
