# Graffiti.pc Conjecture 271: a proof in Lean

For any finite simple connected graph with at least two vertices, let
`D` be the largest graph distance between maximum-degree vertices.
If `s` is the total domination number, then `2D ≤ s²`. Equivalently,
`s ≥ ceil(sqrt(2D))`.

This is [Conjecture 271 in the November 6 *Written on the Wall II*
catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf#page=157).
The maximum is over pairs drawn from the maximum-degree set; adding
the diagonal does not affect the maximum when distinct pairs exist.
A singleton maximum-degree set gives zero. The connected one-vertex
graph has no total dominating set, so the statement applies to
nontrivial connected graphs.

The statement matching the catalogue is `Wow271.conjecture271` in
`Answer271.lean`. `Wow271.square_bound` proves the inequality for every
total dominating set, not just a minimum one.

## Proof

Let S be a total dominating set of size s, and let a,b be maximum-degree
vertices. If s=2, the open neighborhoods of the two vertices of S cover
the graph. Thus twice the maximum degree is at least the graph order.
If a,b were farther apart than two, their open neighborhoods would be
disjoint and omit a. This would make twice the maximum degree smaller
than the graph order, a contradiction.

If s=3, any two vertices of S are at distance at most two. Indeed, if
they are not adjacent, their required neighbors within S must both be
the third vertex. Every vertex of the graph has a neighbor in S, so
the graph's diameter is at most four. Hence 2D≤8<9=s².

If s≥4, the radius bound rad(G)≤s gives D≤2s and 2D≤4s≤s².
The Lean source proves the radius bound using a spanning tree that
retains S as a total dominating set. The radius bound itself was
already known; see DeLaViña, Liu, Pepper, Waller and West, *On some
conjectures of Graffiti.pc on total domination* (2007).

The four-cycle has s=2 and D=2, so equality is attained. The
four-vertex path has ordinary diameter three but D=1, a useful
control for not confusing D with the full graph diameter.

## Reproduce

Use Lean 4.34.1 with Mathlib v4.34.1,
commit d13f23b723b8a846827a245b89c10fc7d3f11612. Run
`./Verify.sh /path/to/mathlib`. The supplied verification logs record
a clean source rebuild and independent kernel replay of all seven
modules. Axioms: propext, Classical.choice, Quot.sound only.
`check271.py` provides independent exhaustive controls on all 27,475
connected labeled graphs on two through six vertices.
