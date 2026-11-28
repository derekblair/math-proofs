# Erdős #151: the K4-free H(n)=12 case

Let H(n) be the independence number guaranteed for all triangle-free
graphs of order n. Every K4-free graph on n vertices with H(n)=12
has a vertex set of size at most n−12 meeting every inclusion-maximal
clique of size at least two. More generally, H(n)≥12 suffices for this
same bound. For H(n)>12 this does not assert n−H(n). The unrestricted
[Erdős Problem #151](https://www.erdosproblems.com/151) remains open.

The paper proof uses the published theorem [R(3,10)≤41, Angeltveit,
2025](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v32i4p30).
The [Lean theorem](H12Final.lean) verifies the argument with that
precise input as an explicit hypothesis. It does not formalize
Angeltveit's computational proof, which reports about three CPU
years. The only Lean axioms are `propext`, `Classical.choice`, and
`Quot.sound`; no `sorry`, custom axiom, or `native_decide` is used.

[PROOF.md](PROOF.md) gives the mathematical argument and provenance.
The source bundle includes independent Lean checks of [Bikov's seven
marked links](https://arxiv.org/html/1604.03716v1#S8) and the published
[52-vertex witness](https://leapsinbounds.org/constants/ramsey-3-12/)
that gives R(3,12)≥53. Neither is a new Ramsey result. Prior public
work identifies a locally Wagner obstruction in a different
degree regime and verifies its colorability by an exhaustive
classification. The proof here gives a separate finite Hall argument
to discharge that step inside Lean.

## Replay

Use Lean 4.34.1 (commit `5045d0056413266e57c625dcd7c365b10e377c52`)
and Mathlib v4.34.1 (commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`).
The [external import list](lean-external-imports.txt) identifies
the libraries required by the 238-module source closure. In a
configured Mathlib checkout, install the corresponding build cache
or build these Mathlib targets before running:

```bash
LEAN_BIN=/absolute/path/to/lean MATHLIB_ROOT=/absolute/path/to/mathlib4 bash replay.sh
```

The replay builds this dossier from source in an empty temporary
directory. The certified finite checks do not rely on their generators.
