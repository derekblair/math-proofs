# [Translation Marches, Hole-Twin Dips, and Dip-March Mechanics](paper.pdf)

Derek Blair · October 11, 2026 edition

We present the structural theory of translation marches of Sidon sets in the raw blocked-set framework `W(A) ⊆ ℤ`. Translating a saturated Sidon set `A ⊂ [1, N]` by `t` sweeps holes deterministically from the bottom (`t > 0`) or top (`t < 0`) of `[1, N]` as the shadow gaps of `W(A)` in a sliding window; the same conveyor governs unsaturated seeds with an additive hole bound, corrected saturated-chain bounds intersect shadow and feasibility ranges, clean shadow-gap windows force hole-twin pairs at chain dips, and the sliding-window recurrence classifies continuation, break, reset, and perfect steps with `φ`-duality.

## Lean formalization

All five modules (`TranslationMarch`, `CorrectedMarch`, `TranslationMarchUnsat`, `HoleTwinDip`, `DipMarch`) are `[PROVED]` in Lean 4.34.1 with zero sorrys and standard axioms only. [Proof link](../../lean/Mathproofs/NumberTheory/TranslationMarch.lean#L195-L202) · [Scope](../../lean/docs/009.md)

## Manuscript files

The [LaTeX source](build/main.tex) and [bibliography](build/references.bib) are in the [build directory](build/). All figures are native TikZ and all tables use booktabs (bibliography is inline in `main.tex`). From this manuscript directory, rebuild the [PDF](paper.pdf) with pdfLaTeX through `latexmk`.

```sh
cd build
latexmk -pdf -halt-on-error -interaction=nonstopmode main.tex
cp main.pdf ../paper.pdf
```

## Citation

```bibtex
@misc{blair2026translationmarchdip,
  author = {Derek Blair},
  title = {{Translation Marches, Hole-Twin Dips, and Dip-March Mechanics}},
  howpublished = {math-proofs preprint
                  \href{https://github.com/derekblair/math-proofs/blob/master/preprints/translation-march-dip-October-11-2026/paper.pdf}{math-proofs:translation-march-dip}},
  year = {2026},
  month = oct,
  note = {Lean formalizations in lean/Mathproofs/NumberTheory/{TranslationMarch,CorrectedMarch,TranslationMarchUnsat,HoleTwinDip,DipMarch}.lean.}
}
```
