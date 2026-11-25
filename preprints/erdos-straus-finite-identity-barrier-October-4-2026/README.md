# [CRT Escape from Local Quadratic Obstructions on Square Classes Modulo 840](paper.pdf)

Derek Blair · October 4, 2026 edition (source corrected October 23, 2026)

> **Historical PDF notice:** The committed [PDF](paper.pdf) predates the October 23, 2026 correction and must not be used as the current verification-status record. The corrected [LaTeX source](build/main.tex) governs pending PDF regeneration.

We prove a scoped Chinese Remainder Theorem escape theorem: for a finite family of arithmetic progressions `Aᵢ t + Bᵢ` with `8 ∣ Aᵢ`, if every residue `Bᵢ` is either a nonsquare modulo some odd prime divisor of `Aᵢ` or fails `Bᵢ ≡ 1 (mod 8)`, then infinitely many primes in each of the six square classes `{1, 121, 169, 289, 361, 529} (mod 840)` avoid all the progressions. The Schinzel–Mordell implication from integer polynomial identities to these local obstructions remains an external mathematical input and is not formalized here.

## Lean formalization

`es_crt_escape` is proved via CRT and Mathlib's general Dirichlet theorem using standard Lean axioms only (the former inconsistent custom axioms and false rational-polynomial `es_barrier` statement were removed on October 23, 2026). [Proof link](../../lean/Mathproofs/NumberTheory/ESBarrier.lean#L82-L89) · [Scope](../../lean/docs/001.md)

## Manuscript files

The [LaTeX source](build/main.tex) and [bibliography](build/references.bib) are in the [build directory](build/). From this manuscript directory, rebuild the [PDF](paper.pdf) with pdfLaTeX through `latexmk` (requires TikZ, pgfplots, and booktabs; references are inline in `main.tex`). No TeX toolchain was available during the correction or restructure passes, so the corrected source has not been re-rendered.

```sh
cd build
latexmk -pdf -halt-on-error -interaction=nonstopmode main.tex
cp main.pdf ../paper.pdf
```

To check the Lean module from `lean/`: `lake build Mathproofs.NumberTheory.ESBarrier`.

## Citation

```bibtex
@misc{blair2026erdosstrausfiniteidentitybarrier,
  author = {Derek Blair},
  title = {{{CRT} Escape from Local Quadratic Obstructions on Square Classes Modulo $840$}},
  howpublished = {math-proofs preprint
                  \href{https://github.com/derekblair/math-proofs/blob/master/preprints/erdos-straus-finite-identity-barrier-October-4-2026/paper.pdf}{math-proofs:erdos-straus-finite-identity-barrier}},
  year = {2026},
  month = oct,
  note = {Corrected source, 23 October 2026. Lean 4 theorem es_crt_escape in lean/Mathproofs/NumberTheory/ESBarrier.lean; integer-polynomial obstruction implication remains unformalized.}
}
```
