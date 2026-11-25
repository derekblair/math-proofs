# [Hole Suppression and Absorption in Saturated Sidon Families](paper.pdf)

Derek Blair · October 11, 2026 edition

This preprint formalizes two connected developments: the hole-suppression theory characterizing hole-capability via non-singleton margins (`t2_iff`) and proving that saturated fibers cannot host holes (`t5_saturation`, `t5_double_saturation`), and the absorbed `13 ∣ h` regime proving the `R ∈ {1, 2, 3, 6}` exclusions (`t5prime_combined`) and the repaired self-bound `c ≤ 320` for absorbed quads with `13 ∤ R` and `R ∣ 30030` (`t4_self_bound`).

## Lean formalization

All three modules (`HoleSuppression`, `AbsorbedRegime`, `AbsorbedBound`) are `[PROVED]` in Lean 4.34.1 with zero sorrys and standard axioms only. [Proof link](../../lean/Mathproofs/NumberTheory/AbsorbedBound.lean#L158-L165) · [Scope](../../lean/docs/008.md)

## Manuscript files

The [LaTeX source](build/main.tex) and [bibliography](build/references.bib) are in the [build directory](build/). All figures are native TikZ/pgfplots and all tables use booktabs (self-contained, inline bibliography). From this manuscript directory, rebuild the [PDF](paper.pdf) with pdfLaTeX through `latexmk`.

```sh
cd build
latexmk -pdf -halt-on-error -interaction=nonstopmode main.tex
cp main.pdf ../paper.pdf
```

## Citation

```bibtex
@misc{blair2026holesuppressionabsorption,
  author = {Derek Blair},
  title = {{Hole Suppression and Absorption in Saturated {Sidon} Families}},
  howpublished = {math-proofs preprint
                  \href{https://github.com/derekblair/math-proofs/blob/master/preprints/hole-suppression-absorption-October-11-2026/paper.pdf}{math-proofs:hole-suppression-absorption}},
  year = {2026},
  month = oct,
  note = {Lean formalizations in lean/Mathproofs/NumberTheory/{HoleSuppression,AbsorbedRegime,AbsorbedBound}.lean.}
}
```
