# [Binary submasks and the middle column of Rules 126 and 129](paper.pdf)

Derek Blair · October 28, 2026 edition

We characterize the middle column of elementary cellular automata Rules 126 and 129 from a single live seed cell under an exact complementation reduction. Through a closed-form binomial-parity description of Rule 126, Lucas's theorem modulo 2, and base-2 digit-spread characterization, we prove the middle-column identity `A267442(n) = A043545(n)` for all `n ≥ 1` (resolving R. J. Mathar's 2016 OEIS conjecture via the Fredholm–Rueppel sequence `A036987`; equality fails at `n = 0`). The broader row-support target, finite computational evidence for popcounts 1 through 18, and prior-art limitations are retained alongside the completed proof of the three pinned middle-column theorems.

## Lean formalization

Four modules under `lean/Mathproofs/Dynamics/` (`Rule129ClosedForm`, `Rule129Lucas`, `Rule129Digits`, `Rule129MiddleColumn`) prove `rule126_middle_column_iff`, `rule126_middle_column_eq_a036987`, and `a267442_eq_a043545` with zero sorrys and standard axioms only. *(Family number and `lean/docs/` scope-file assignment pending.)* [Proof link](../../lean/Mathproofs/Dynamics/Rule129MiddleColumn.lean#L150-L173) · [Comparator challenge](../../lean/ComparatorChallenges/Rule129MiddleColumn.lean)

## Manuscript files

The [LaTeX source](build/main.tex) and [bibliography](build/references.bib) are in the [build directory](build/). From this manuscript directory, rebuild the [PDF](paper.pdf) with pdfLaTeX through `latexmk` (inline bibliography in `main.tex`).

```sh
cd build
latexmk -pdf -halt-on-error -interaction=nonstopmode main.tex
cp main.pdf ../paper.pdf
```

To check the Lean library from `lean/`: `lake build Mathproofs.Dynamics`.

## Citation

```bibtex
@misc{blair2026rule129,
  author = {Derek Blair},
  title = {{Binary submasks and the middle column of Rules 126 and 129}},
  howpublished = {math-proofs preprint
                  \href{https://github.com/derekblair/math-proofs/blob/master/preprints/rule129/paper.pdf}{math-proofs:rule129}},
  year = {2026},
  month = oct,
  note = {Lean formalizations in lean/Mathproofs/Dynamics/Rule129{ClosedForm,Lucas,Digits,MiddleColumn}.lean.}
}
```
