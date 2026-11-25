# [Void Frames, Defect Calculus, and Defect Homomorphisms](paper.pdf)

Derek Blair · October 11, 2026 edition

We develop the algebra of void frames — complete lock frames whose edge pattern fires nowhere — proving that void frames are exactly the zero triple of the `(T, F, C)` union-forcing datum and the union-identity of the frame algebra (V1–V8), constructing the parameterized annotated void-frame monoid `N′_W` and its defect calculus (P1–P2, T1/T1′/T2), repairing D2(c) and proving maximal-family tiling (D3), and establishing defect-homomorphism rigidity (H1: every monoid homomorphism `N′_W → M` into an additive cancellative monoid is zero), non-additivity of literal products (C4), and exact mixed-family splitting witnesses (C1/C2).

## Lean formalization

Four modules (`VoidUnion`, `VoidLock`, `VoidMonoid`, `VoidDefectHom`) are `[PROVED]` and `VoidMonoidParam` is a build-clean staged `[PROVED*]` dependency, all kernel-checked in Lean 4.34.1 with zero sorrys and standard axioms only. [Proof link](../../lean/Mathproofs/NumberTheory/VoidDefectHom.lean#L64-L66) · [Scope](../../lean/docs/013.md)

## Manuscript files

The [LaTeX source](build/main.tex) and [bibliography](build/references.bib) are in the [build directory](build/). All figures are native TikZ/pgfplots and all tables use booktabs (inline bibliography in `main.tex`). From this manuscript directory, rebuild the [PDF](paper.pdf) with pdfLaTeX through `latexmk`.

```sh
cd build
latexmk -pdf -halt-on-error -interaction=nonstopmode main.tex
cp main.pdf ../paper.pdf
```

## Citation

```bibtex
@misc{blair2026voidframes,
  author = {Derek Blair},
  title = {{Void Frames, Defect Calculus, and Defect Homomorphisms}},
  howpublished = {math-proofs preprint
                  \href{https://github.com/derekblair/math-proofs/blob/master/preprints/void-frames-defect-October-11-2026/paper.pdf}{math-proofs:void-frames-defect}},
  year = {2026},
  month = oct,
  note = {Lean formalizations in lean/Mathproofs/NumberTheory/{VoidUnion,VoidLock,VoidMonoidParam,VoidMonoid,VoidDefectHom}.lean.}
}
```
