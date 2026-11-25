# Optimal local node conversion is polynomial on trees

This resolves the tree/path complexity question in Section 6 of Jie Zhang,
Yuezhou Lv, and Zihe Wang, *Node Conversion Optimization in Multi-hop
Influence Networks*, AAMAS 2023, pp. 2205–2212:
https://www.ifaamas.org/Proceedings/aamas2023/pdfs/p2205.pdf

**Result.** For any finite tree, any input radius k, and arbitrary individual
thresholds, the optimum local decision from Algorithm 2 can be computed in
polynomial time using only the node's own k-hop view. The path claim follows
as a special case. This replaces the conjectured tree intractability with an
explicit polynomial implementation. It does not claim a polynomial
algorithm for general graphs.

## Argument

Start inside the node's actual view, an induced subtree, and compute distances
only in this input tree. Write B(u) for the closed radius-k ball there.
Every ball is geodesically convex, and so is every nonempty intersection
of balls. Its induced distances are therefore exactly the distances in
the input tree. Thus the paper's visualization at u inside S is
S intersect B(u), with the induced edges; we are not assuming this identity
on general graphs.

If a,b are diameter endpoints of any nonempty set C of centers, the
four-point inequality in a tree implies
  d(x,c) + d(a,b) <= max(d(x,a) + d(b,c), d(x,b) + d(a,c))
for every c in C. The two distances from a or b to c are at most d(a,b),
so d(x,c) <= max(d(x,a),d(x,b)). The intersection of the balls centered
at C is exactly B(a) intersect B(b). A singleton uses a=b.
Consequently there are at most n^2 scopes, where n is the number of
vertices in the input view. Empty pair intersections may harmlessly be
included in the table.

Enumerate all pairwise ball intersections and process distinct scopes
in order of increasing cardinality. For a scope S, first mark each u
whose child scope is a proper subset and whose threshold is met by the
previously computed value for that scope. For any candidate count i,
add those marked vertices to the vertices with equal child scopes
whose threshold is at most i. Store the largest i for which the sum is
at least i. The decision at any root in this scope is simply whether
its threshold is at most that stored count. Only proper child scopes
are recursively queried, so this table returns the identical decisions
as Algorithm 2.

An explicit deterministic bound is O(n^4) elementary operations after
reading and normalizing the input, on a RAM with O(log n)-bit words:
compute the n ball bit vectors by breadth-first searches; put O(n^2)
pair intersections into a binary trie of depth n and bucket them
by cardinality. For each scope, O(n) intersections and child-key
lookups take O(n^2) time, and testing all counts against the equal-view
thresholds also takes O(n^2). No hashing assumption is needed. The
unoptimized Lean list table is polynomial too. A radius at least n
can be capped at n, and thresholds greater than n represented by n+1,
so binary input does not invalidate polynomial bit complexity.

The existing safety and optimality theorem is Theorem 5.1 of the paper.
The new algorithm computes that protocol exactly on tree inputs. If
the competing protocols are required to be safe only on trees, the
paper's optimality proof still applies: its minimal-counterexample
network is just the rooted view itself, which in this setting is a
tree. This restriction of the original safety/optimality argument
and the operation-cost accounting are supplied here in prose; they
are not claimed as formalized Lean lower-level machine semantics.

## Verification

* TreeInfluenceMetric.lean: the four-point inequality on arbitrary finite
  Mathlib trees, proved by leaf deletion.
* TreeInfluenceScopes.lean: two-center compression, catalog bound, convex
  tree scopes, and equality with intrinsic visualization.
* TreeInfluenceDP.lean: the literal counting-phase equivalence,
  correctness of the materialized bottom-up table, and its squared
  size bound and decision equivalence on the actual entire local input.
  The main theorem is `TreeInfluence.optimalLocalTreeTable`.
* tree_influence_check.py: independent regression test, using induced
  breadth-first distances and the printed descending scan as reference.

Use Lean 4.27.0 and Mathlib v4.27.0 (commit
a3a10db0e9d66acbebf76c5e6a135066525ac900). Set MATHLIB_DIR to a checkout
with dependencies and cached oleans, then run `bash check.sh` and
`python tree_influence_check.py`. The printed theorem audits contain
only standard Lean axioms; no admitted proofs are required.
