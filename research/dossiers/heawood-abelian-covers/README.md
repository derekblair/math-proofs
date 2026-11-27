# Sharp dyadic-cycle bound for regular abelian Heawood covers

Every regular abelian cover of the Heawood graph contains a simple cycle of
length **8, 16, or 32**. The deck group may have elements of order two, may
be infinite, and need not act compatibly with any vertex-transitive action
on the base. A connected 3,346-vertex abelian cover has a 32-cycle but no
4-, 8-, or 16-cycle. This proves that the bound 32 is sharp, not that the
example is smallest. The full Erdős–Gyárfás conjecture remains open.

- [Regular-cover theorem](HeawoodCoverChart.lean):
  `HeawoodCoverChart.RegularAbelianCover.dyadic_cycle` formalizes the
  chart from a regular abelian covering action to the voltage model.
- [Upper theorem](HeawoodAbelian.lean):
  `HeawoodCert.every_regular_abelian_voltage` takes arbitrary antisymmetric
  edge voltages in an additive abelian group. Its conclusion supplies
  an injective cyclic sequence of length 8, 16, or 32 in the voltage graph.
- [Sharpness in the same graph model](HeawoodSharpUnified.lean):
  `HeawoodSharpUnified.sharp`. The additive deck group for this example
  is the field of 239 elements. The coordinate model is conjugate to the
  semidirect-product model with group order 1,673.

The base has ports 0, 1, and 3 between left and right copies of the
integers modulo 7, the cyclic Fano incidence model of the Heawood graph.
As usual, choose a lift of each base vertex. In a regular abelian cover,
translating that lift by a deck element identifies the fiber with the
deck group; uniqueness of the lifted edge gives a translation by its
edge voltage. Reversing an edge negates the voltage. This chart does not
assume the cover finite, Haar, or vertex-transitive.

The upper proof gauges a spanning tree to zero. It checks 31 closed base
walks using exact integer prefix sums. If the closing voltage is zero and
every same-base prefix difference is nonzero, the lifted walk is simple.
Short walks force a collection of nonzero linear forms; these forms
exclude all repeated vertices in the final 32-walk. The row for doubling
an 8-cycle is represented by its full 16-step walk. All closure and
collision checks use integer relations, not division by two.

For context, [Gebendorfer](https://doi.org/10.5281/zenodo.22666267) treats
cubic bipartite vertex-transitive graphs of girth six. The Heawood covers
here need not be vertex-transitive; see [Conder et al., §IV](https://www.math.auckland.ac.nz/~conder/preprints/semisymmetric.pdf).
[Kelley and Walker](https://math.unl.edu/faculty/Kelley/Kelley_Walker_ISIT08.pdf)
supply the voltage-neutral walk framework; the simplicity checks are
essential here. Deck groups of exponent dividing four are an immediate
overlap: one simple base 8-cycle already lifts in one, two, or four laps.
No absolute publication-priority claim is made.

Replay with Lean 4.34.1 and a cache-populated Mathlib checkout at
`d13f23b723b8a846827a245b89c10fc7d3f11612`:

```sh
python3 verify.py /path/to/pinned/mathlib4 -j 2
```

`generate.py` also independently checks the vector relations in Python
and emits the walk table in the Lean gauge. Run it in a temporary directory
to avoid replacing the staged sources.
