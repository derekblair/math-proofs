# Sharp no-four collinearity representability thresholds and two-matchings criterion
See [the nine-point witness and the separate coordinatewise OV reduction](COLLINEARITY.md). The general span characterization and abstract OV gadget mechanisms are prior work; the new scope is the explicit geometric witnesses and special threshold characterization.

Here an exact additive representation of a colored ternary relation means
one per-point group label on each of the three parts, whose sum is zero
precisely on the collinear triples. The target group may be any additive
abelian group, chosen for the instance. The parts consist of distinct
points and are pairwise disjoint; assume no four points are collinear.
These are representability statements, not runtime lower bounds.

## Exact criterion with at most two points in one color

For a two-point part A, color an edge between B and C by the unique A
point collinear with it. If there were two edge colors on one pair or
two neighbors of one vertex for a fixed A point, the corresponding
line would contain four distinct points. Thus the two colors are
disjoint matchings and components alternate, comprising paths (including
singletons) or even cycles.

**Criterion.** An exact representation in some additive abelian group
exists if and only if there are no cycles, or all cycles have the same
half-length m and all path lengths, in edges, are at most 2m−2.

*Proof.* Translate the two A labels so the target for B+C is 0 at color
0 and t at color 1. If there is any edge then t cannot be zero, since
the other color is forbidden at that same pair. In each component,
choose oriented consecutive indices in the alternating sequence:
B_r next to C_r with color 0, C_r next to B_(r+1) with color 1.
For a path one can start with B_r or C_r depending on its first color
and direction (or equivalently take consecutive subindices on the
bi-infinite alternating sequence). For a cycle use these indices
cyclically from any B vertex and its color-0 neighbor.
The forced potentials in a component are B_r = b+r t and
C_s = −b−s t, so B_r+C_s=(r−s)t. A cycle of half-length k forces
k t=0 by return to B_0. Let m be the least positive integer with
m t=0, if any. Then m divides k and m≥2.

If a cycle k is longer than m, its alternating segment of 2m−1 edges
has two nonadjacent opposite-side endpoints. Start the segment at
a B vertex with color 0. Its endpoints satisfy B_0+C_(m−1)=t,
so color 1 is falsely accepted. This proves m=k for every cycle.
Similarly a path with at least 2m−1 edges contains such a segment.
If its endpoint in B has first edge of color 1, interchange the two
colors for this argument (replacing t by −t). Its endpoints are
not otherwise joined, so this would be a false positive.

For sufficiency, if there are no cycles choose infinite-order t=1
in Z. Otherwise choose t=1 in Z/m. Use local B_r=r t,C_s=−s t.
On a path with at most 2m−2 edges the difference d=r−s lies in
[2−m,m−1] (because the odd distance is 2(s−r)+1 if r≤s and
2(r−s)−1 otherwise). In this interval, residues 0 and 1 occur
only at 0 and 1. On a 2m-cycle use indices modulo m; differences
0 and 1 are exactly adjacent pairs of the appropriate color.
Finally augment the group by Z, give each component a unique integer
tag, put opposite tags on B and C, and give A tag zero. Distinct
components therefore never jointly produce zero. ∎

A singleton A supplies just one matching. Give each matched pair its
own integer label on one side and its negative on the other; choose
different fresh component tags for unmatched points. Thus a singleton
color always has an exact representation even over Z. An empty color
has vacuous constraints.

## Sharp consequences

1. Any disjoint three-color no-four instance with at most eight points
   is representable in some additive group, since some part has size at
   most two. For a two-point part this leaves at most six other vertices
   (the same reasoning works up to seven). At most one cycle fits.
   After a 4-cycle, at most three other vertices remain; any leftover path
   has at most two edges, as required. After a 6-cycle, at most one remains.
   The nine-point example in the preceding geometry lane is nonrepresentable;
   its exact five unordered collinear triples share no point-pair and hence
   it also has no four collinear. Therefore nine is the general threshold.
2. If requiring at least one color of size at most two, the threshold is
   ten. The above lower argument covers B+C≤7. The Lean module
   TenPointTwoColors exhibits a disjoint (2,4,4) instance with no four
   collinear whose graph is the union of a C4 and a three-edge path, and
   proves no additive representation over any abelian group.
3. For torsion-free targets, including real 3SUM labels, the threshold is
   six: at most five forces a singleton or empty color; TorsionSix gives
   six distinct integer points of color sizes (2,2,2), no four collinear,
   exactly representable in a target group if and only if it has nonzero
   two-torsion. Thus it is representable over Z/2 but not over R.

## Geometric realizability

Every finite pair of disjoint matchings is realizable by planar rational
points with no four collinear and only the intended collinear triples.
Assign an x-coordinate to each component of the first matching (a pair
or a singleton), and a y-coordinate to each component of the second.
Each B or C vertex is their intersection grid cell. No two such grid
vertices occupy the same cell because no edge belongs to both matchings.
Choose distinct positive integer x values at most R, and distinct y
values among powers of M with M>2R. There is no collinear triple of grid
vertices. If any two x or y coordinates coincide the corresponding axis
line has at most two vertices. Otherwise in the determinant expansion
along the y coordinates the largest-power term has coefficient of
absolute value at least one, and dominates both lower terms whose
coefficients have absolute value at most R−1.

Now apply the rational chart (x,y) ↦ (x/(1+x+y), y/(1+x+y)) and include
the two finite anchor points (0,1),(1,0). The first anchor detects equality
of original x, the second equality of original y. Neither anchor pair is
collinear with a charted grid vertex, and incidence of triples of charted
vertices is unchanged. The chart is injective on this positive grid
(recover x,y by dividing by 1−x'−y'). Thus the only collinearities are
the prescribed matching edges incident to their anchors, and no four
collinearities occur. Common denominator clearing gives integer
coordinates. In particular for each m≥2 the alternating 2m-cycle realizes
a 2+2m point example representable in a given target group exactly when
the group has an element of order m (no extra components need separating).

## Verification and provenance

Pinned Lean 4.34.1 passed the four files TwoColorMatchingLocal (modular
interval, path force, cycle torsion, component tags), TwoPencilChart
(projective determinant identities), TorsionSix and TenPointTwoColors
(both explicit full-geometry no-four and group-label conclusions).
The general decomposition, threshold proof, and exponential-grid
dominance argument are written proofs, not yet fully formalized.
Independent exhaustive_matching.py directly checked exact encodings of
all 10,620 labeled pairs of disjoint matchings with B+C≤7; it did not
assume a geometric embedding or just count components.

General quotient representability is known (arXiv:2610.17420 Lemma 20.3);
these are geometric/two-matching specializations and explicit threshold
witnesses. Focused search did not identify the exact geometric thresholds;
no absolute novelty or priority asserted.
