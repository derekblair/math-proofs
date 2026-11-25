# [An Erdős–Straus Covering Identity for n ≡ 217 (mod 264)](paper.pdf)

Derek Blair · October 3, 2026 edition (source corrected October 23–24, 2026)

> **Historical PDF notice:** The committed [PDF](paper.pdf) predates the October 23–24, 2026 corrections and contains the retracted novelty claim. The corrected [LaTeX source](build/main.tex) governs pending PDF regeneration. The former novelty claim is withdrawn in light of Miguel Angel Lopez (2024), [arXiv:2206.10319v4](https://arxiv.org/html/2206.10319v4); no priority is claimed.

We give a Lean formalization of the Erdős–Straus covering identity `4/n = 1/((n+3)/4) + 1/(n(n+3)) + 1/(n(n+3)/11)` for every natural number `n ≡ 217 (mod 264)`, in which all three denominators are positive integers. The identity covers the prime 1009 and exactly one-eleventh of each of the six hard square residue classes modulo 840 (six exact subclasses modulo 9240). The manuscript documents its specialization of Lopez (2024).

## Lean formalization

`es_covering_217mod264` proves positive natural denominators, exact denominator equations, and the Egyptian-fraction identity; `es_identity_217mod264` retains the rational equality; `ESIdentityCRT` proves the six exact subclasses modulo 9240 and one-out-of-eleven residue counts using only standard Lean axioms. [Proof link](../../lean/Mathproofs/NumberTheory/ESIdentity.lean#L82-L85) · [Scope](../../lean/docs/001.md)

## Manuscript files

The [LaTeX source](build/main.tex) and [bibliography](build/references.bib) are in the [build directory](build/). From this manuscript directory, rebuild the [PDF](paper.pdf) with pdfLaTeX through `latexmk` (requires TikZ, pgfplots, and booktabs; references are inline in `main.tex`). No TeX toolchain was available during the October 23–24 or November 25 passes, so no regenerated PDF build is claimed for the corrected source.

```sh
cd build
latexmk -pdf -halt-on-error -interaction=nonstopmode main.tex
cp main.pdf ../paper.pdf
```

To check the Lean module from `lean/`: `lake build Mathproofs.NumberTheory.ESIdentity Mathproofs.NumberTheory.ESIdentityCRT`.

## Citation

```bibtex
@misc{blair2026erdosstrausidentity217mod264,
  author = {Derek Blair},
  title = {{An Erd\H{o}s--Straus Covering Identity for $n \equiv 217 \pmod{264}$}},
  howpublished = {math-proofs preprint
                  \href{https://github.com/derekblair/math-proofs/blob/master/preprints/erdos-straus-identity-217mod264-October-3-2026/paper.pdf}{math-proofs:erdos-straus-identity-217mod264}},
  year = {2026},
  month = oct,
  note = {Corrected 2026-10-24: novelty claim withdrawn; Lopez (2024), arXiv:2206.10319v4, is prior art. Lean 4 formalization in lean/Mathproofs/NumberTheory/ESIdentity.lean (es_covering_217mod264).}
}
```
