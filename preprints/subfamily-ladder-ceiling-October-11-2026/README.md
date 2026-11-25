# [Sub-Family Dichotomy and Ladder Ceilings: Generalized Erdős–Straus Identities, Admission Pinning, and the March Ladder Bound](paper.pdf)

Derek Blair · October 11, 2026 edition

This paper reports the generalized Erdős–Straus sub-family identity `4/(M't + s) = 1/x + 1/(nAC) + 1/(BC)` for all `t ≥ 0` on `s ≡ -m + 4qeV₀ (mod 4qeA₀)`, its prime-valuation admission criterion, `A₀`-constancy, the repaired conditional same-modulus split/layered dichotomy (the unconditional form having been refuted by `q = 29, A = 10, r = 510510`), and the two-sided ladder-length ceiling for hole-twin march ladders.

## Lean formalization

`ESSubfamilyExtended.generalized_subfamily_identity` and `MarchLadderCeiling` (`theorem6`, `catalog_ceiling`) are `[PROVED]`; the additional extensions in `ESSubfamilyExtended` (`admission_criterion`, `a0_constancy`, `split_layered_repaired`) carry staged `[PROVED*]` status, all kernel-checked with zero sorrys and standard axioms only. [Proof link](../../lean/Mathproofs/NumberTheory/ESSubfamilyExtended.lean#L48-L67) · [Scope](../../lean/docs/010.md)

## Manuscript files

The [LaTeX source](build/main.tex) and [bibliography](build/references.bib) are in the [build directory](build/). All figures are native TikZ/pgfplots and all tables use booktabs (inline bibliography in `main.tex`). From this manuscript directory, rebuild the [PDF](paper.pdf) with pdfLaTeX through `latexmk`.

```sh
cd build
latexmk -pdf -halt-on-error -interaction=nonstopmode main.tex
cp main.pdf ../paper.pdf
```

## Citation

```bibtex
@misc{blair2026subfamilyladder,
  author = {Derek Blair},
  title = {{Sub-Family Dichotomy and Ladder Ceilings: Generalized Erd\H{o}s--Straus Identities, Admission Pinning, and the March Ladder Bound}},
  howpublished = {math-proofs preprint
                  \href{https://github.com/derekblair/math-proofs/blob/master/preprints/subfamily-ladder-ceiling-October-11-2026/paper.pdf}{math-proofs:subfamily-ladder-ceiling}},
  year = {2026},
  month = oct,
  note = {Lean formalizations in lean/Mathproofs/NumberTheory/{ESSubfamilyExtended,MarchLadderCeiling}.lean.}
}
```
