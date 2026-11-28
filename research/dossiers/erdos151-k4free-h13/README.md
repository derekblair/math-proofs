# Erdős #151: K4-free H(n)=13 at order at least 64

The [Lean theorem](H13Final64.lean) proves that an n-vertex K4-free graph
with n≥64 and H(n)≥13 has a transversal of at most n−13 vertices meeting
every inclusion-maximal nontrivial clique. H(n) is the independent-set
size guaranteed for all triangle-free graphs on n vertices. For H(n)>13,
this does not give n−H(n). It does not prove the unrestricted conjecture
or cover n<64.

The Lean statement takes explicitly the published Ramsey bounds
[R(3,10)≤41 (Angeltveit)](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v32i4p30)
and [R(3,11)≤50 (Goedgebeur–Radziszowski)](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v20i1p30).
Their computational proofs are not replayed in Lean. No new custom axioms,
sorries or native_decide are used in the dossier.
[PROOF.md](PROOF.md) explains the three-hub deletion and graph assembly.

Replay in a fresh directory with Lean 4.34.1 (5045d0056413266e57c625dcd7c365b10e377c52)
and a built Mathlib v4.34.1 checkout (d13f23b723b8a846827a245b89c10fc7d3f11612):

```sh
LEAN_BIN=/absolute/path/to/lean MATHLIB_ROOT=/absolute/path/to/mathlib4 bash replay.sh
```

The source closure includes the pieces it needs from earlier H(n)=11
and H(n)=12 dossiers.
