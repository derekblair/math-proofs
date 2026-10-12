# Build instructions

Paper: `fiber-compatibility-composite-suppression-October-11-2026`
("Fiber-Compatibility and Composite Suppression in Erdős–Straus Covering Families")

## Source

`build/fiber-compatibility-composite-suppression-October-11-2026.tex`

## Build

No external assets needed — all figures are native TikZ/pgfplots and all
tables are booktabs. No `\includegraphics`, no `\svg`, no image files.

```sh
cd build
pdflatex fiber-compatibility-composite-suppression-October-11-2026.tex
pdflatex fiber-compatibility-composite-suppression-October-11-2026.tex
```

Two `pdflatex` passes resolve cross-references (theorem/equation/table/
figure labels and hyperref anchors). Or equivalently:

```sh
latexmk -pdf fiber-compatibility-composite-suppression-October-11-2026.tex
```

## Requirements

- A LaTeX distribution with `amsmath`, `amssymb`, `amsthm`, `tikz`
  (+ `positioning` library), `pgfplots` (compat 1.18), `booktabs`,
  `geometry`, `hyperref`.
- No bibliography tooling required (references are an inline
  `thebibliography` environment); `CITATION.bib` is the per-directory
  BibTeX record for the preprint catalogue only.

## Status

- PDF compiled later by the coordinator (not built by the drafting agent).
- After compiling: check the log for overfull `\hbox` in Table 1
  (wide catalogue table), Figure 1 (TikZ digit rows), and the
  Formalization note (long unbreakable `\texttt` theorem names) —
  see the typography notes at the end of the `.tex` file.
- Structural checks to confirm: 7 sections in order
  (Abstract, Introduction, Methods, Results, Discussion, Conclusion,
  References); no banned commands; every figure/table referenced in
  the text.
