# A metabelian regular Heawood cover with girth 54 and least dyadic cycle 64

There is a finite connected regular cover of the Heawood graph with an
odd-order, nonabelian metabelian deck group, ordinary girth **54**, and
shortest power-of-two simple cycle length **64**. This shows that the
sharp abelian-cover upper bound of 32 does not extend to metabelian deck
groups. It does not prove a universal upper bound for metabelian covers
or the full Erdős–Gyárfás conjecture.

- [Main theorem](HeawoodDoubleConnectedSharp.lean):
  `HeawoodDoubleComponent.connected_sharp` holds for every connected
  component of the explicit double lift. The component is connected,
  projects onto Heawood with unique local edge lifts, and its stabilizer
  acts simply transitively on every fiber.
- [Simple 64-cycle](HeawoodLift64Witness.lean):
  `HeawoodLift64.cycle64`.
- [Generic girth tools](HomologyThree.lean) and [matching upper
  bound](HomologyThreeUpper.lean): the all-edge modulo-three lift of
  a finite graph of even ordinary girth triples that girth.

## Construction and certificate

Take two successive modulo-three homology voltage lifts of the
Heawood graph. Each orientation of an edge records a signed crossing
modulo three. The large full-lamp model can be disconnected; restricting
to any connected component gives a regular Heawood cover. The first
layer has girth 18 and the second has girth 54. A projected lifted
cycle has integral net flow divisible by three on every edge. If
the flow is nonzero, its support contains a directed cycle, each edge
charged at least three times. If zero, the classical abelian-girth
inequality applies. In the other direction, three laps around a
shortest base cycle lift to a simple cycle. These arguments are
checked in Lean.

The 64-cycle comes from three internally disjoint paths of lengths
4, 14, and 14 between the same two first-cover vertices. The lifted
walk uses each path once each way. A certificate checks closure and
distinguishes repeated projected vertices using two lamp coordinates.
The compact chord-coordinate model embeds into the all-edge model;
no Haar symmetry is assumed.

Over the original base, second-layer lamp translations and first-layer
translations form a semidirect product of two finite elementary abelian
3-groups. A connected-component stabilizer is metabelian and still acts
regularly on fibers. It is not abelian by the abelian Heawood-cover
theorem: there are no 8-, 16-, or 32-cycles.

The abelian-girth inequality is classical; see
[Friedman, Izsak and Silberman](https://arxiv.org/abs/1511.03678).
The two-layer homology method is also standard. The dossier's claims
are the explicit checked regular cover, its exact girth and dyadic
spectrum endpoint, and the full Lean replay. It makes no priority claim
for classical homology-cover results or a minimum graph size claim.

Replay with Lean 4.34.1 and cached Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`:

```sh
python3 verify.py /path/to/pinned/mathlib4 -j 2
python3 check_witness.py
```

The second command independently constructs and checks the explicit
64-cycle using integer arithmetic.
