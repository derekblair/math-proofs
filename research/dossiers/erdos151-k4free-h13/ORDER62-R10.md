# Order ≥62, tight dG=12/rC=10/eC=16 row

## Verified actual-graph consequences
Any further ambient edge among the 12 ambient neighbors, beyond the
32 directed chart incidences in the ten core neighbors, would give
at least 34 ambient directed incidences. Then the exterior total
I≤98, the core degree bounds give L≤62, and the 17-edge saturation
pressure argument applies verbatim. Therefore the ambient link is
the full core chart plus two isolated ghost owners. In particular
both edges from w to these two ghosts are ambient-lone.

Since at e=16 we have I≤100, P=A+D≥35 and L≥58. The ten core owner
lone rows each have ≤4; the two ghost rows ≤11. Thus each ghost has
≥7 exterior lone neighbors and cannot have core degree≥8 under
ambient cap12. With the global minimum nonzero core degree 8, both
ghosts are inactive. No d12/r10/e16 positive source can occur in an
ambient graph with a spanning core.

Proof files: N62AmbientSaturated, N62TenAmbientRigidity and
N62GhostInactivity. All kernel checked, only standard axioms.
N62DoubleStar additionally proves an arbitrary pairwise-shared-lone
exchange bound: if Z is an outside set, each pair shares some lone
owner and all supports are inside P⊆S, then |Z|≤|P|. This prohibits
two duplicate double-support pairs sharing the same owner, and
prohibits a support triangle with one duplicate side.

## Exact local owner model and analytic reduction (not end-to-end)
Let A singletons, D double-lone columns, and A+D≥35, A+2D≤62.
Thus A≥8. In the SAT model impose original owner path, pair,
triangle exchanges and the new rule that doubled supports form a
matching. Exact SAT experiments leave only A=10, both ghosts
unmarked; this is an exploratory solver result, not an LRAT or
Lean certificate for the whole graph semantics.

For the branch with both ghosts unmarked, there is a paper proof.
Put k=10−A, and let t,c,u be double multiplicities between ghosts
and core, within core, and between the two ghosts respectively.
Then t+c+u≥25+k and t+2c≤30+k, hence t+2u≥20+k. The duplicate-star
constraint gives t≤20+k. If u=2, no common core double partner
(otherwise the pair of duplicate ghost columns and two common
partner columns are pairwise sharing a lone owner on three
owners). Neither ghost can have another duplicate, so t≤10.

If u=1, ghost/core duplicate similarly forbids a common support
for that core owner, hence each cross multiplicity ≤2 and f=20−t.
Then k+f≤2. For a marked core owner neighboring both ghosts, its
singleton is forced lone to the ghost/ghost double by owner
triangle exchange. No double joins two such marked common
partners, since owner pair forcing would create a lone triangle
on their two singletons and the ghost/ghost double. Every core
double is incident to an exceptional core vertex. There are at
most j≤k+f exceptions. Their residual total double capacity is
≤j+k+f (capacity 3+individual unmarked indicator minus actual cross
multiplicity). This is below the necessary c≥4+k+f, contradiction.

If u=0, equalities t=20+k and c=5 force all 20 distinct cross
pairs and one duplicate per unmarked core vertex, and each core
owner has core/core double-degree one. Any unmarked core vertex's
duplicated cross side then makes a support triangle with its core
matching neighbor, contradiction. Hence A10, D25, neither ghost
marked, full cross, and core/core doubles a perfect matching.
N62TenOwnerNumbers formalizes arithmetic once these incidence
inputs hold. Exact pivot script shows 8 of 40 intact e16 charts
cannot even accommodate this required matching on nonadjacent
pivot pairs with at least one exterior common neighbor.

This remaining B=0 owner pattern is in fact impossible using
private columns. Since A+D=35, I≤100 and 3|X|≥147, the exact local
demand I + |privateColumns| + (A+D)≥147 forces |privateColumns|=12
and I=100. All 24 private slots are used; each of the ten marked
core owners uses both via its singleton. A 2-neighbor, 0-lone
private B-column would have to charge both isolated ghosts,
impossible: its two owners need an ambient edge to block a
triangle. Thus exactly two 2-neighbor, 1-lone C-columns charge the
ghosts, one per ghost (each such column charges twice to its lone
endpoint). Exterior lone slots L≤62 are now exhausted: 10 from
singleton columns, 50 from doubles, 2 from C-columns. Each ghost
has 10 doubles plus one C-column and its original lone edge to w,
so all 12 ambient incidences are lone. Hence a C-column's other,
nonlone endpoint is a core owner s. The C-column, the double
column on the same pair (ghost,s), and s's singleton are pairwise
nonadjacent by shared lone incidences. All three are supported
on {ghost,s}, impossible by the exchange cap.

Important: the tempting inequality 3|X|≤I+2A+D is false without
excluding B/C columns. It is not used. The actual local demand
uses both private and special column counts as above.

For A=8 and a marked ghost, D=27 and L=62, so every lone slot
saturates and the ghost has exactly ten distinct double partners.
At least six partners are marked. At most 11 doubles meet its
unique nonpartner, so at least six doubles lie entirely among
its partners. Owner pair and triangle forcing give its singleton
leaf at least 1+6+6=13 distinct ambient neighbors, contradiction.
For A=9, the same pressure excludes a marked ghost D-degree10
(at least 7 marked partners and 26−10−11=5 internal doubles).
Other marked-ghost cases have not been closed analytically or
kernel-certified. The full e16 row is NOT yet excluded.

## Full paper exclusion of the tight row (actual private constraints)

This section supersedes the preceding status "other marked-ghost cases
have not been closed analytically." Lean currently verifies the
ambient rigidity, inactivity, generic exchange, and some arithmetic
only. The full following graph argument has not been kernel replayed.

Use a 12-owner set S with independent ghosts inside the ambient
link (indeed they have no edges to any owner). Let P=A+D, J be
the number of private columns of type A/B/C, and keep I,L as above.
We have P≥35, J≤12, L≤62, A+2D≤L, and I+J+P≥147 with I≤100.
Thus 8≤A≤12. A mark refers only to A-column, which uses both private
slots of its unique owner. Each B (2-neighbor, 0-lone) column charges
one private slot to each endpoint, and these endpoints have an
ambient edge. Each C (2-neighbor, 1-lone) column charges two slots
at its unique lone owner, and contributes one to L. This follows by
the blocked-small-support lemmas; only these minimum charges are
needed, and they become exact if J=12. B cannot charge a ghost.

Call a double count D-star degree d_D. Every marked owner has a
simple D-star (a duplicate pair and its singleton make illegal
3-for-2 exchange), cap 3 at core owners and cap 10 at ghosts,
since its singleton takes one exterior lone slot. Unmarked limits
are 4 and 11. A pair of duplicate sides sharing an endpoint, and
a D-triangle containing a duplicate, violate the pairwise-shared-
lone exchange. A triangle of marked owners is forbidden: their
three singleton columns would be pairwise joined by required lone
edges. For a marked owner g the singleton leaf must meet every
marked D-neighbor's singleton and every internal D-column among
its D-neighbors by lone edges. All these vertices and g itself are
distinct. In particular if a marked ghost has d_D=10 then its
singleton has degree at least
  1 + (A−2) + (D−10−11) = A+D−22 ≥13,
as only one owner is omitted by its simple 10-star and at most
eleven other doubles lie at that omitted owner.

A=8: D=27, L=62, P=35 and hence J=12. No C column can fit in
the exhausted lone slots. Each unmarked owner must then be charged
by B, so neither ghost is unmarked. Both marked ghosts hit
d_D=10 (all individual lone row caps saturate), impossible.

A=9: D=26, P=35 and J=12. Exactly three private non-A columns
must exhaust six slots at three unmarked owners. At most one is C
because A+2D=61. If none is C, the three B supports have weighted
degree two on three vertices; with no loops their three pair
multiplicities must each be one, giving an ambient triangle in
the owner link. Thus exactly one C and two B. The B columns have
the same pair support on adjacent unmarked core owners; neither
ghost can receive B, so at least one ghost is marked. Now L=62,
and all lone rows saturate. Each marked ghost has 1 singleton,
no C, and exactly ten doubles: contradiction.

A=10: D=25 or 26. At D=26 there are no C (lone slots exhausted)
and J≥11, so at least one B exists. Its endpoints exhaust both
unmarked owners and both are core. Both marked ghosts then have
D-degree ten.

For A=10,D=25, P=35 and J=12. Exactly two B/C columns exhaust
four free slots at two owners; one B and one C cannot do this.
If both C, each unmarked owner gets one C and L=62. A marked
ghost must hit D-degree ten. If both ghosts are unmarked, all
ten core owners marked, the prior B=0 argument derives full
cross doubles. Each ghost has 10 doubles, one C, and w, with all
twelve incidences lone. Therefore its C-column's second, nonlone
owner s is core. The C-column, D_{g,s}, and A_s give the 3-for-2
exchange just described above.

The last A=10,D=25 case has two B columns on the same adjacent
unmarked pair {u,v} of core owners. Both ghosts are marked. Let
t,c,z denote respectively cross-double count, core-pair double
count, ghost-pair double count. Core owner cap gives t+2c≤32,
and t+c+z=25. If z=1, t≥16; but marked common core owners would
make an all-marked D triangle, so at most two common core partners,
hence t≤12. Thus z=0 and t≥18. Set f=20−t≤2. No D joins u and v,
since uv is ambient. Those core doubles touching u or v account
for at most 4+f_unmarked using their degree cap4 and cross degrees
2−missing. For marked pairs, if neither endpoint has both ghost
crosses absent, a permitted D must join opposite single crosses,
and each such endpoint has capacity2; count at most f_marked.
If there is a marked owner with both absent, its D-degree≤3 and
at most f_marked−2 other missing occurrences contribute; count
at most f_marked+1. Thus total c≤4+f except possibly when f=2
and both misses are at one marked owner. In that exception u and
v have full cross. Take one ghost g; the two B columns on {u,v}
and D_{g,u},D_{g,v} are pairwise nonadjacent. The B columns are
nonadjacent by K4-freeness and uv ambient; the other pairs share
an incident-lone edge at u,v, or g. These four have support inside
three owners, contradiction. Outside the exception the needed
c=25−t=5+f is above 4+f.

A=11: D≥24; all D pairs simple as at most one owner unmarked.
If the sole unmarked owner is core, both ghosts marked and t+2c≤31.
A ghost-pair double would imply t≥15 but at most one common core
partner so t≤11. Without that double, t≥17 and f=20−t≤3.
At most one marked core owner misses both ghosts (call their
count z≤1). Core doubles among marked owners count ≤f_marked+z:
those touching a no-cross owner cost at most 3z, the others join
opposite single cross classes and count at most f_marked−2z.
Core doubles at the unmarked owner count ≤2+f_unmarked. Hence
c≤3+f, but c≥24−t=4+f.

If the sole unmarked owner is ghost q, let g be the marked ghost
and λ,μ the numbers of missing cross pairs at g,q. All ten core
owners marked, so t+2c≤30. A ghost-pair double implies t≥16,
f=λ+μ≤4. The singleton of g is forced lone to the ≥10−λ
marked neighbor singletons, and to q-to-core D columns for each
of ≥10−f common partners (these lie entirely among g's D-neighbors).
Including g itself gives degree ≥21−λ−f≥13, impossible. Without
ghost-pair double, t≥18 and f≤2. Core doubles must touch a core
owner missing g, by marked triangle prohibition. Summing such
owners' remaining degrees bounds c≤2λ+β≤2f, where β≤μ is the
number missing both. But c≥4+f>2f.

A=12: all owners marked; D≥23 and t+2c≤30. A ghost-pair double
implies t≥14 but no common core cross partner, giving t≤10.
Otherwise t≥16, f=20−t≤4. With z≤2 no-cross core owners, all
core doubles count ≤3z + f−2z = f+z≤f+2 by the same opposite-
single vs no-cross argument. Required c≥23−t=f+3, impossible.

Thus the fully audited incidence logic reduces dG=12/rC=10 at
n≥62 to eC≤15 on paper. This is not a proof of the order-62
Erdős151 case, because dG=12/rC=9 positive classes and others
may remain. Independent review and end-to-end Lean not yet done.

## Lean result and replay

The final graph theorem is `Erdos151N62.degreeTwelve_r10_at_least62_sharp`
in `N62DegreeTwelveTenSharp.lean`. It uses no Ramsey-theoretic premise,
SAT output, or newly introduced axiom. Replaying the modules from
`order62-r10-modules.txt` in order against the parent dossier uses
Lean 4.34.1 and Mathlib v4.34.1. The numerical chart screen is not needed
for this theorem and remains separate. Other positive local configurations
are not ruled out by this proof; order 62 is not solved.
