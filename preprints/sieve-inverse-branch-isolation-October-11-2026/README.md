# [Sieve Inversion and Branch Isolation](paper.pdf)

Derek Blair · October 11, 2026 edition (source corrected October 23, 2026)

> **Historical PDF notice:** The committed [PDF](paper.pdf) predates the October 23, 2026 correction (which replaced the three former `native_decide` calls with pure kernel proofs and sharpened the unformalized scope limits) and must not be used as the current verification-status record. The corrected [LaTeX source](build/main.tex) governs pending PDF regeneration.

We report two connected structural results from the Erdős–Straus sieve program. First, sieve-inversion theory characterizes the exact six-class support `{1}_8 × {1, 4, 7}_9 × {1}_5 × {2, 6}_{11}` modulo 3960, proves its multiplicative inverse closure modulo 3960, explains its selectivity via the 44-CRT equivalence `s ≡ 1 (mod 24) ⇒ (s ≡ 7 (mod 11) ⇔ s ≡ 29 (mod 44))`, and proves exact projection equality at `q = 19`. Second, the branch-isolation lemmas for H-cliques prove `uBranch_isolation` and the u-side degree bound `uSide_degree_bound`.

## Lean formalization

Both modules (`ESRefinedSieveInverse`, `ESUBranchIsolation`) are `[PROVED]` in Lean 4.34.1 using pure kernel proofs and standard axioms only (zero `native_decide` certificate axioms). External sieve provenance and the `q = 23` extension remain unformalized. [Proof link](../../lean/Mathproofs/NumberTheory/ESRefinedSieveInverse.lean#L64-L65) · [Scope](../../lean/docs/015.md)

## Manuscript files

The corrected [LaTeX source](build/main.tex) and [bibliography](build/references.bib) are in the [build directory](build/). With an existing TeX Live installation providing `latexmk`, TikZ, pgfplots, and booktabs (inline bibliography in `main.tex`), rebuild the [PDF](paper.pdf) and inspect logs before replacing the historical PDF:

```sh
cd build
latexmk -pdf -halt-on-error -interaction=nonstopmode main.tex
cp main.pdf ../paper.pdf
```

To check the Lean modules from `lean/`: `lake build Mathproofs.NumberTheory.ESRefinedSieveInverse Mathproofs.NumberTheory.ESUBranchIsolation`.

## Citation

```bibtex
@misc{blair2026sieveinversion,
  author = {Derek Blair},
  title = {{Sieve Inversion and Branch Isolation}},
  howpublished = {math-proofs preprint
                  \href{https://github.com/derekblair/math-proofs/blob/master/preprints/sieve-inverse-branch-isolation-October-11-2026/paper.pdf}{math-proofs:sieve-inverse-branch-isolation}},
  year = {2026},
  month = oct,
  note = {Corrected source 2026-10-23 (former native_decide replaced by kernel proofs); PDF is historical. Lean formalizations in lean/Mathproofs/NumberTheory/{ESRefinedSieveInverse,ESUBranchIsolation}.lean.}
}
```
