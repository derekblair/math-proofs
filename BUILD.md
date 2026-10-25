# Building the corrected sources

The Lean toolchain and Mathlib revision are pinned by `lean-toolchain` and
`lake-manifest.json`. With those dependencies already available:

```bash
lake exe cache get
lake build
```

The library root imports the finite witnesses, the nine-row Sidon census,
the graph extremality bridge, and all covering/CRT modules, so they are
included in the full build. The Sidon census uses kernel computation and
can take several minutes and substantial memory on its first build. Axiom dependencies can be inspected
in a scratch file importing `Mathproofs` with `#print axioms <declaration>`.

The October 23 corrections update `overview.tex` and the ES identity, ES
barrier, r47, and sieve-inverse manuscript sources. Their committed PDFs are
historical pre-correction artifacts. No TeX toolchain was available during
this correction, so no regenerated or visually validated PDF is supplied.

With an existing TeX installation that supplies the required packages:

```bash
latexmk -pdf -interaction=nonstopmode overview.tex
```

Use each affected paper's `BUILD.md` for its working directory and commands.
The r47 paper includes the previously missing `strip.inc`, reproduced by
`python3 verify_witness.py --write-strip` from its directory.
