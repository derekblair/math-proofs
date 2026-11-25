# [A Saturated 9-Element Sidon Set in [1,184]: A Kernel-Checked Finite Witness](paper.pdf)

Derek Blair · October 7, 2026 edition (source corrected October 23, 2026)

> **Historical PDF notice:** The committed [PDF](paper.pdf) is a historical pre-correction artifact (including the withdrawn extension claim) and has not been regenerated. The corrected [LaTeX source](build/main.tex) governs pending PDF regeneration.

We exhibit `A⋆ = {16, 62, 66, 74, 88, 104, 117, 122, 123} ⊂ [1, 184]`, a 9-element Sidon set whose 45 pairwise sums block all 175 complementary positions in `[1, 184]`, so no element of `[1, 184]` can be adjoined. We also report the nine displayed one-hole 183-coverage sets, their saturated 10-element extensions, and two counterexamples refuting the 121/123-gate conjecture C28. Search exhaustiveness, minimality, and historical priority are not claimed.

## Lean formalization

`SidonSat184.r47_sat184` kernel-checks cardinality 9, containment in `[1, 184]`, the Sidon property, and saturation using standard Lean axioms only (no `native_decide`). `SidonSat184Census` additionally kernel-checks all nine displayed one-hole rows, their 183 blocked positions, saturated ten-element extensions, and both C28 counterexamples. [Proof link](../../lean/Mathproofs/Combinatorics/SidonSat184.lean#L64-L65) · [Scope](../../lean/docs/006.md)

## Manuscript files

The [LaTeX source](build/main.tex), [bibliography](build/references.bib), TikZ strip include ([`build/strip.inc`](build/strip.inc)), and supplementary Python check ([`build/verify_witness.py`](build/verify_witness.py)) are in the [build directory](build/). From this manuscript directory, regenerate the diagram and rebuild the [PDF](paper.pdf) with Python 3 and pdfLaTeX through `latexmk` (requires TikZ, pgfplots, and booktabs; the Lean proof does not trust the Python script).

```sh
cd build
python3 verify_witness.py --write-strip
latexmk -pdf -halt-on-error -interaction=nonstopmode main.tex
cp main.pdf ../paper.pdf
```

To check the Lean modules from `lean/`: `lake build Mathproofs.Combinatorics.SidonSat184 Mathproofs.Combinatorics.SidonSat184Census`.

## Citation

```bibtex
@misc{blair2026sat184,
  author = {Derek Blair},
  title = {{A Saturated $9$-Element Sidon Set in $[1,184]$: A Kernel-Checked Finite Witness}},
  howpublished = {math-proofs preprint
                  \href{https://github.com/derekblair/math-proofs/blob/master/preprints/r47-sat184-October-7-2026/paper.pdf}{math-proofs:r47-sat184}},
  year = {2026},
  month = oct,
  note = {Source corrected 2026-10-23; PDF is historical. Lean kernel proof in lean/Mathproofs/Combinatorics/SidonSat184.lean.}
}
```
