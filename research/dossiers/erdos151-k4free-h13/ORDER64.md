# Erdős #151 for K₄-free graphs on exactly 64 vertices

[N64FullOrder.lean](N64FullOrder.lean#L11) proves the bound for every
triangle-free independence guarantee at order 64, so no assumption
about the exact value of H(64) is needed. The explicit Fin64 graph
in [New64Input.json](New64Input.json) gives H(64) ≤ 13 by a checked
Lean certificate. This replaces the additional survey-listed
R(3,14) ≥ 67 input for order 64 only. The formal argument still uses
Angeltveit's R(3,10) ≤ 41 and Hall's locally Petersen classification
as explicit premises, as in the order-63 and uniform H=13 arguments.
For orders 65–66 the earlier corollary still uses the survey premise.

The 64-vertex graph was generated independently from the known 63-vertex
circulant with steps 1, 12, 15, 18, 20, 22 by adding one apex and 36
edges, removing none. Its apex has the nine old vertices congruent
to 6 modulo 7 as neighbors. The other 27 added edges pair vertices
at distance 9, using the perfect matching in each of the nine residual
six-vertex paths after removing the apex neighbor from a distance-9
7-cycle. The graph has 414 edges, is triangle-free, and has independence
number exactly 13. This is not an improvement to the ordinary Ramsey
lower bound, which is already stronger in the literature.

To reproduce the finite proof, run `python gen_new64.py` from this
directory. Its output is an untrusted proof-plan generator; the Lean
kernel checks the proof plans. With Lean 4.34.1, Mathlib v4.34.1,
and the already replayed order-63/uniform dependencies in LEAN_PATH,
replay the modules in [order64-new-modules.txt](order64-new-modules.txt)
in order. The final theorem uses only standard Mathlib axioms.

An [independent audit](ORDER64-REVIEW.md) checked the graph and both
proof ingredients without relying on the generator's clique search.
