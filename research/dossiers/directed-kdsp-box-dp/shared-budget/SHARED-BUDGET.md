# Disjoint shortest paths parameterized by used interaction vertices

For each original label i, retain the vertices and arcs on some positive-
weight s_i–t_i shortest route. If a required pair is unreachable, reject;
a zero-length route retains its singleton vertex. The result is a DAG D_i.
Preprocessing uses addition/comparison of original input weights; the bit
bounds below describe subsequent processing on these DAGs. Let B be the vertices
belonging to at least two such DAGs, including any terminals. A vertex
outside B is private, so a tuple of paths is vertex-disjoint if and only
if their visits to B never repeat. The same holds after restricting and
trimming each D_i at a specific transition in the SCC sweep.

## Shared-visit quota b: deterministic exact YES and NO

Given a quota b, decide whether there is a disjoint tuple with at most b
total visits to B. If b=0, remove B and use independent reachability.
Otherwise replace b by min(b, |B|). Make a b-perfect hash family on B
with b colors; any set of size less than b extends to one of size b.
For a fixed coloring, process the DAGs in label order. Within a DAG use
topological path DP carrying a mask of colors used so far. Initialization
passes exactly the masks attained at the previous target to the current
source. Traversing a private vertex costs nothing. Traversing a shared
vertex requires a fresh color and adds it to the mask, including at
sources, singleton paths, and targets. The same rule holds at each
transition into a fresh vertex, so it applies to current label and earlier
labels equally. Never permit traversing past the current target.

A colorful concatenation is sound because any repeated actual shared
vertex has the same color. A disjoint solution with at most b shared
vertices is accepted for a coloring injective on its shared vertices.
This retains original labels and endpoints and works on arbitrarily
cyclic unions. The postprocessing is O(2^b L) word operations per coloring
for summed labelled DAG length L (including vertices and arcs);
path recovery uses predecessor pointers. Standard perfect hash families
give deterministic 2^{O(b)} poly(L,n) time, using [Naor–Schulman–Srinivasan
splitters](https://users.cms.caltech.edu/~schulman/Papers/splitters.pdf)
(or standard color coding constructions). No new derandomization claim.

A quota rejection is an exact NO **for the quota decision problem**.
It is not a NO for unbudgeted k-DSP. In the SCC sweep, use this local solver
at a chosen quota on each trimmed local support, retaining the original
labelled endpoints. The resulting n^{O(k)}·2^{O(b)} algorithm decides
whether some route has local shared-use count ≤b in every visited SCC.
A YES witness with b=O(k log n) yields n^{O(k)} time even if every candidate
SCC is large and has unbounded potential grouping. No such bound is
claimed for all instances or for NO instances of the unbudgeted problem.

## Exact deterministic 2^r rank sieve in polynomial space, r=|B|

For S⊆B let P_{i,S}(z) be the sum of z^{number of shared visits} over
paths using no vertices in B\S. Sequential DAG DPs compute
Q_S(z)=∏_i P_{i,S}(z) by passing the target coefficient vector from each
label to the next source. Truncate to degree b for an optional quota.
Then compute
  Σ_{S⊆B} (−1)^{r−|S|} Σ_{j≤b} [z^j]Q_S(z) · binom(|S|,r−j).
The binomial enumerates a dummy filler subset of S of size r−j.
Inclusion–exclusion kills every tuple-plus-filler whose union of visited
shared vertices and dummy vertices is smaller than B. Degree r then
forces all these sets to be pairwise disjoint, so the unique filler
for each good tuple is precisely its unused shared set. Therefore the
answer is the exact number of disjoint original route tuples under
quota b, on simple labelled DAGs after parallel-arc normalization; these are vertex-path tuples, not tuples
of distinct parallel-arc identities.

For a fixed S, the degree-vector DP takes O((b+1)L) integer additions,
and computing the binomial weighted combination is polynomial. The
numbers have polynomial bit length: each simple DAG has at most
2^{|V_i|} paths for fixed endpoints (a vertex subset determines the order
in its topological order), and each filler and inclusion–exclusion sum
adds at most another r bits. Total bit-time 2^r poly(L,n), polynomial
space, in place of the old 3^{|C|} local mask-partition fallback. It also
counts, instead of merely deciding. This is an application of standard
inclusion–exclusion, not an unconditional faster worst-case k-DSP
algorithm or a claim of priority.

## Scope of checks

`SharedBudget.lean` verifies two finite mathematical facts: fresh colors
on shared vertices imply global disjointness across original supports;
covering a set in exactly its cardinality number of visits means every
pair of visit sets is disjoint. The programming algorithm, hash-family
construction, and time bound are paper arguments. `check.py` compares
both algorithms against complete path-tuple enumeration, using complete
tiny color families and no accidental global topological-order premise.

## The two local parameters are incomparable

The companion `CYCLIC-TRIM-BARRIER.md` constructs a support SCC of
arbitrarily large order, with arbitrarily many compulsory potential
groups after every admitted shortest-support trim, yet a private-route
YES witness with zero local shared visits.

Conversely, take q≥2 original labels, each with private entry a_i and exit
b_i in a component. Supply q parallel internally disjoint tracks of L
vertices, all with unit forward edges. Every a_i can enter the first
vertex of any track and every track's last vertex can exit to every b_i,
also by unit edges. Make the whole support strongly connected with
one extra connector label having unit length-three alternatives
s_c→b_i→a_i→t_c, plus an independent private length-three route. Add
original outer terminal arcs s_i→a_i and b_i→t_i. Every own local
shortest path uses exactly one entire track: using a connector bridge
would require a second track and add L+2 to the cost. Every track vertex
belongs to all q original trimmed supports, and q disjoint tracks give
a solution, but its local shared quota is exactly qL, arbitrarily
large. The track arcs and their incident entry/exit edges share one
potential (levels 0 through L+1, with backwards connector edges having
negative increments), and the connector supplies another. Thus the
untrimmed SCC uses at most two groups and the admitted original-label
trim only one. This is an explicit tradeoff, not a lower bound on the
running time of every algorithm.
