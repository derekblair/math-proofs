# [Fiber-Compatibility and Composite Suppression in Erdős–Straus Covering Families](paper.pdf)

Derek Blair · October 11, 2026 edition

We report five formalized components studying residue-covering families attached to the Erdős–Straus equation `4/n = 1/x + 1/y + 1/z`: (1) the prime-power Fiber-Compatibility Theorem characterizing inverse closure via the forced Hensel digit involution `A_r`; (2) the composite-modulus lift to `m = nD` with `D ∣ n` alongside empirical correlation-hole obstructions; (3) composite suppression theory (`κ`, `Π`, demands-descend, capability transfer, no-lift, and T4–T8 tower-refinement operators); (4) the thinned-tiling catalogue and no-tiling theorems on fibers `{6, 11}`; and (5) branch-2 degeneracy and the 92-identity `s ≡ 73 (mod 264)` covering family together with the formal mod-8 refutation of the naive claim.

## Lean formalization

All five modules (`ESFiberCompat`, `ESFiberCompatComposite`, `ESFiberTiling`, `CompositeSuppression`, `ESBranchTwo`) are `[PROVED]` in Lean 4.34.1 with zero sorrys and standard axioms only. [Proof link](../../lean/Mathproofs/NumberTheory/ESFiberCompat.lean#L186-L188) · [Scope](../../lean/docs/007.md)

## Manuscript files

The [LaTeX source](build/main.tex) and [bibliography](build/references.bib) are in the [build directory](build/). All figures are native TikZ/pgfplots and all tables use booktabs (no external image assets; bibliography is inline in `main.tex`). From this manuscript directory, rebuild the [PDF](paper.pdf) with pdfLaTeX through `latexmk`.

```sh
cd build
latexmk -pdf -halt-on-error -interaction=nonstopmode main.tex
cp main.pdf ../paper.pdf
```

## Citation

```bibtex
@misc{blair2026fibercompat,
  author = {Derek Blair},
  title = {{Fiber-Compatibility and Composite Suppression in Erd\H{o}s--Straus Covering Families}},
  howpublished = {math-proofs preprint
                  \href{https://github.com/derekblair/math-proofs/blob/master/preprints/fiber-compatibility-composite-suppression-October-11-2026/paper.pdf}{math-proofs:fiber-compatibility-composite-suppression}},
  year = {2026},
  month = oct,
  note = {Lean formalizations in lean/Mathproofs/NumberTheory/{ESFiberCompat,ESFiberCompatComposite,ESFiberTiling,CompositeSuppression,ESBranchTwo}.lean.}
}
```
