# Exact n=16 and n=17 cases of Frankl's Intersection–Union Product Conjecture

With p=q=2, Lean verifies the following maximum cardinalities for the
original unrestricted families of subsets:

| Ground-set size | 16 | 17 |
| --- | ---: | ---: |
| Largest family | 8649 | 17298 |

For every pair of family members, including equal members, the intersection
has size at least 2 and the union has size at most n−2. Theorems
IU.IU17.exact16 and IU.IU17.exact17 appear in Finalize17.lean. This settles
exactly the specified finite cases and does not settle the full conjecture.
The result is distinct from the Lubell-weighted intersection–union problem.

After the base bundle's proved reduction to a graph of prefix profiles, a
proper auxiliary 17467-coloring is used only to count surviving neighbors.
Three rounds eliminate 21390, 4854 and 14 vertices outside the 17298-member
anchor. At a fixed size, maximal prefix profiles certify omitted colors
for all profiles below them, in a two-sublayer order that removes selected
maximal labels first. Only 46 maximal rows are needed (34/8/4). Exact
weight and rank threshold masks certify full vertex coverage. Exact
bitwise mask comparisons certify the omitted colors of the maximal rows,
with earlier layers removed. The final graph cap transports to the
original finite families. A free extra coordinate doubles any n=16
family, giving that upper bound from n=17. The disjoint-block constructions
give the lower bounds.

Primary sources: [Frankl–Wang, JCTA 217 (2026), 106100](https://doi.org/10.1016/j.jcta.2025.106100);
[Chang–Frankl–Wang, arXiv:2610.25049, Thm 1.3](https://arxiv.org/html/2610.25049v1).
Neither stated range covers these two values, and this archive makes no
claim of priority.

Set BASE_SOURCE_DIR to the unchanged n=9–13 source bundle, MATHLIB_DIR
to a built Mathlib checkout at d13f23b723b8a846827a245b89c10fc7d3f11612,
and optionally LEAN_BIN to Lean 4.34.1. Then run ./replay.sh. The script
validates both source manifests and compiles into a fresh output folder
in the listed order, without downloads. LEAN_MEM_MIB defaults to 3000.
The original final statements use only propext, Classical.choice,
and Quot.sound. audit_ext17.py independently checks the supplied
mathematical certificate under a direct deadline scheduler, not the
Lean implementation; Python plays no trusted role in the proof.
