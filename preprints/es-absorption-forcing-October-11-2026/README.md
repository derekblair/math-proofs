# [Absorption Order and Forcing Spectrum in Erdős–Straus Families](paper.pdf)

Derek Blair · October 11, 2026 edition (source remediated October 24, 2026)

> **SUPERSEDED PDF NOTICE:** The committed [PDF](paper.pdf) is a historical October 11, 2026 pre-remediation artifact. **Do not use it as a statement of the current formalization.** The corrected [LaTeX source](build/main.tex) and the current Lean statements in [`ESAbsorptionOrder.lean`](../../lean/Mathproofs/NumberTheory/ESAbsorptionOrder.lean) govern:
> - `absorp_datum_iff` requires `G.C.Nonempty`; `datum_eq_of_absorpLE` requires no nonemptiness premise.
> - For distinct `G ≼ H`, `rho_absorption_collapse` and `absorption_collapse_unique_core` require `H.C.Nonempty` (uniqueness is for cardinality-one cores, hence the minimum core).
> - `singleton_factorization` takes a finite ambient family `𝒢 ⊇ S`, with no singleton footprint `{c}` in `𝒢` for `c ∈ S0`.
>
> The former universal nonemptiness premise was vacuous because `Group` admits an empty footprint; the PDF predates both that repair and the ambient-family repair, and its blanket machine-checking wording does not certify external census counts. An October 24 rebuild attempt with Tectonic (`--only-cached --untrusted`) exited 1 because `tectonic-format-latex.tex` was absent from cached resources, and no LaTeX toolchain is installed on the restructure host.

We study the absorption partial order `G ≼ H` on Erdős–Straus union groups `G = (C, p)`, proving partial-order laws (A1), datum-equality characterization under `C_G ≠ ∅` (A2), dominance pruning (A3), disjoint and general superadditivity of redundancy rank `ρ` (R3′, R3″), the overlap-deficit bound (T), absorption collapse and unique minimum core under `C_H ≠ ∅` (R4′), and singleton factorization within a finite ambient family `𝒢 ⊇ S`. We also formalize the ES forcing-spectrum partition S2(a)′/S2(b–d)/S3/S4 and the checked components of the two-sided forcing decomposition (`theoremA_crt`, `theoremA_crt_box`, `theoremB_scaling`, `theoremC_filter`, partial `theoremD_card` lemmas).

## Lean formalization

All three modules (`ESAbsorptionOrder`, `ESForcingSpectrum`, `ESForcingDecomp`) are `[PROVED]` in Lean 4.34.1 with zero sorrys and standard axioms only; unformalized decomposition bridges and external census counts are explicitly separated in the scope document. [Proof link](../../lean/Mathproofs/NumberTheory/ESAbsorptionOrder.lean#L201-L202) · [Scope](../../lean/docs/014.md)

## Manuscript files

The corrected [LaTeX source](build/main.tex) and [bibliography](build/references.bib) are in the [build directory](build/). With an existing TeX installation supplying TikZ, pgfplots, and booktabs (inline bibliography in `main.tex`), rebuild the [PDF](paper.pdf) and verify layout before replacing the superseded PDF:

```sh
cd build
latexmk -pdf -halt-on-error -interaction=nonstopmode main.tex
cp main.pdf ../paper.pdf
```

## Citation

```bibtex
@misc{blair2026absorptionforcing,
  author = {Derek Blair},
  title = {{Absorption Order and Forcing Spectrum in Erd\H{o}s--Straus Families}},
  howpublished = {math-proofs preprint
                  \href{https://github.com/derekblair/math-proofs/blob/master/preprints/es-absorption-forcing-October-11-2026/paper.pdf}{math-proofs:es-absorption-forcing}},
  year = {2026},
  month = oct,
  note = {October 11 PDF superseded; corrected source (2026-10-24) in build/main.tex governs. Lean formalizations in lean/Mathproofs/NumberTheory/{ESAbsorptionOrder,ESForcingSpectrum,ESForcingDecomp}.lean.}
}
```
