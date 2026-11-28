# Erdős–Gallai–Tuza clique transversals: the K4-free H(n)=11 case

If every triangle-free graph on n vertices has an independent set of size
11, every K4-free graph on n vertices has a vertex set of size at most
n−11 that meets every inclusion-maximal clique of size at least two.
In particular this proves the K4-free case of [Erdős Problem #151](https://www.erdosproblems.com/151)
when H(n)=11. The full conjecture is still open. The stated result
continues to give n−11 for H(n)>11, not the conjectured n−H(n).

**Formal statement:** [`erdos151_k4free_H11`](Erdos151K4FreeEleven.lean).
It quantifies over an arbitrary finite vertex type and puts no additional
restriction on triangle or lone-edge intersections. The theorem depends
only on Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
The graph argument is not an exhaustive search over graphs.

## Proof

See [the paper proof](PROOF.md). If a red/blue coloring avoids
monochromatic triangles, the spanning graph made from red edges and
lone edges is triangle-free and meets every maximal nontrivial clique
in an edge. Its independent set of size 11 has a transversal complement.
Otherwise assume that the original graph has no free set of size 11 and
extract a minimal Ramsey core. A free neighborhood forces ambient
degree at most 10. Charging blocked extensions of a neighborhood to
the vertices whose removal frees them then excludes every ambient
degree 10, 9, and 8 in the core. The core cannot have smaller degree.

The statement is Problem 1 in [Erdős–Gallai–Tuza, 1992](https://doi.org/10.1016/0012-365X(92)90681-5),
restricted as above. The proof includes independent Lean derivations
of the needed [Bikov minimum-degree theorem](https://arxiv.org/abs/1604.03716)
and a kernel check of the published [Exoo (3,11;46) graph](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v20i1p68),
which forces n≥47. Neither prerequisite is claimed as a new result.
The red-edge reduction is also known. The new argument is the
three-stage incidence proof, which accommodates lone edges and does
not assume earlier finite-order results. Related public work treats
earlier orders and [pure-triangular cases](https://github.com/edisonymy/erdos-lean-research/blob/main/research/erdos151/ALLOCATION_CHECKPOINT.md).
A focused search did not locate this unrestricted-in-lone-edges
H(n)=11 case; this is not a claim of literature priority.

## Replay

Use Lean 4.34.1 (commit `5045d0056413266e57c625dcd7c365b10e377c52`)
and built Mathlib v4.34.1 (commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`). With absolute paths:

```bash
LEAN_BIN=/path/to/lean MATHLIB_ROOT=/path/to/mathlib4 bash replay-unblocking.sh
```

The script copies and compiles only source in a temporary directory.
The Exoo certificate's generator is not trusted by the proof. Its search
is checked with Lean kernel reduction, not `native_decide`.
```bash
python degree_descent_controls.py
```
runs independent small-order checks, which are not premises of the theorem.
