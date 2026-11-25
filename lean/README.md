# Lean formalizations

This directory contains Lean formalizations of results in this repository.
They are organized in a single library grouped by mathematical discipline (`Mathproofs.NumberTheory`, `Mathproofs.Combinatorics`, `Mathproofs.Topology`, `Mathproofs.Dynamics`), so we recommend compiling small portions at a time when iterating.

See the [Comparator README](ComparatorChallenges/README.md) for more information about how to verify exported theorem statements against trusted challenge files, [`docs/`](docs/) for per-family formalization scope documents, and [`formalization.yaml`](formalization.yaml) for the machine-readable catalogue.

## Building the Lean library

The Lean toolchain (`leanprover/lean4:v4.34.1`) and Mathlib revision (`d13f23b723b8a846827a245b89c10fc7d3f11612`) are pinned by `lean-toolchain`, `lakefile.lean`, and `lake-manifest.json`. From `lean/`:

```sh
lake exe cache get
lake build
```

To build a single discipline library or individual module:

```sh
lake build Mathproofs.NumberTheory
lake build Mathproofs.Combinatorics
lake build Mathproofs.Topology
lake build Mathproofs.Dynamics
lake build Mathproofs.NumberTheory.ESIdentity
```

The library root imports the finite witnesses, the nine-row Sidon census, the graph extremality bridge, and all covering/CRT modules, so they are included in the full build. The Sidon census (`Mathproofs.Combinatorics.SidonSat184Census`) uses kernel computation and can take several minutes and substantial memory on its first build. Axiom dependencies can be inspected in a scratch file importing `Mathproofs` with `#print axioms <declaration>`, and environment integrity can be checked with `lake env leanchecker`.

## Building the LaTeX manuscripts

The October 23–24, 2026 corrections updated `../overview.tex` and the ES identity, ES barrier, `r47-sat184`, sieve-inverse, and absorption-forcing manuscript sources. Their committed PDFs remain historical pre-correction artifacts pending regeneration with an existing TeX installation.

With a XeLaTeX/LuaLaTeX installation providing `fontspec`, `unicode-math`, `fancyhdr`, `lastpage`, `ragged2e`, `needspace`, `booktabs`, and TeX Gyre Pagella fonts, rebuild the overview from the repository root:

```sh
latexmk -xelatex -interaction=nonstopmode overview.tex
```

Use each manuscript's `../preprints/<slug>/README.md` for its build commands and supersession or rebuild notes. The `r47-sat184` manuscript includes `build/strip.inc`, reproduced by `python3 verify_witness.py --write-strip` from `../preprints/r47-sat184-October-7-2026/build/`.

## Technical note: mmap

Compiling the entire library may fail if Linux's `vm.max_map_count` is too low.
One workaround is to build Lean with the CMake option `-DMMAP=OFF`; it may also be necessary to set the environment variable `GLIBC_TUNABLES` to `glibc.malloc.mmap_max=0:glibc.malloc.arena_max=1` when running Lean or Lake.
