# [Sigma Transfer and Fiber Overlap: Pareto Transitions of the March-Graph Spectrum and the Sidon Fiber-Overlap Bound](paper.pdf)

Derek Blair · October 11, 2026 edition

We study the `σ`-spectrum `S(σ)` and Pareto frontier `Π(σ)` of the march-graph program, formalizing the `σ`-transfer suite (Pareto down-set membership, T5 locality bar, T6 abstract-only independence models, and reflection-dual exclusion `A3_holds`) together with the Sidon fiber-overlap suite (distinct pair-sum fibers `s - A` and `s' - A` overlap in at most one point, autocorrelation `≤ 1`, and conditional top-interval sparsity). The earlier claimed sharp floor `|E| = 0 ⇒ |S| ≥ 7` is recorded as refuted by an exact six-hole witness.

## Lean formalization

Both modules (`SigmaTrans`, `FiberOverlap`) are `[PROVED]` in Lean 4.34.1 with zero sorrys and standard axioms only. [Proof link](../../lean/Mathproofs/NumberTheory/FiberOverlap.lean#L117-L119) · [Scope](../../lean/docs/011.md)

## Manuscript files

The [LaTeX source](build/main.tex) and [bibliography](build/references.bib) are in the [build directory](build/). All figures are native TikZ/pgfplots and all tables use booktabs (inline bibliography in `main.tex`). From this manuscript directory, rebuild the [PDF](paper.pdf) with pdfLaTeX through `latexmk`.

```sh
cd build
latexmk -pdf -halt-on-error -interaction=nonstopmode main.tex
cp main.pdf ../paper.pdf
```

## Citation

```bibtex
@misc{blair2026sigmatransferfiber,
  author = {Derek Blair},
  title = {{Sigma Transfer and Fiber Overlap: Pareto Transitions of the March-Graph Spectrum and the Sidon Fiber-Overlap Bound}},
  howpublished = {math-proofs preprint
                  \href{https://github.com/derekblair/math-proofs/blob/master/preprints/sigma-transfer-fiber-overlap-October-11-2026/paper.pdf}{math-proofs:sigma-transfer-fiber-overlap}},
  year = {2026},
  month = oct,
  note = {Lean formalizations in lean/Mathproofs/NumberTheory/{SigmaTrans,FiberOverlap}.lean.}
}
```
