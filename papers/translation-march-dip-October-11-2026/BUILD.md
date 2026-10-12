# BUILD.md — papers/translation-march-dip-October-11-2026/

## Build instructions

The PDF is compiled later by the coordinator. To build locally:

```bash
cd build
pdflatex translation-march-dip-October-11-2026.tex
pdflatex translation-march-dip-October-11-2026.tex
```

Two `pdflatex` passes resolve all `\ref`/`\label` cross-references and the
hyperref anchors. No `bibtex` run is needed: the paper's references are
inlined in the `\begin{thebibliography}` environment in the `.tex`
source (the standalone `CITATION.bib` in the paper directory is the
repo's machine-readable BibTeX block, kept in sync by hand).

## External assets

None. All figures are native TikZ (the sliding shadow-window diagram,
Figure 1); all tables use booktabs. There are no `\includegraphics`,
`\svg`, or external image files — the build directory contains only the
`.tex` source, so a clean `pdflatex` install with the standard packages
(`amsmath`, `amssymb`, `amsthm`, `tikz`, `pgfplots`, `booktabs`,
`geometry`, `hyperref`) is sufficient.

## Known checks for the coordinator

- Zero errors expected; the structural checklist: 7 sections in order
  (Abstract, Introduction, Methods, Results, Discussion, Conclusion,
  References), Figure 1 and Table 1 each referenced before they appear,
  no banned commands (`grep -n 'includegraphics\|\\svg' *.tex` should be
  clean).
- The file ends with three substantive weaknesses (W1–W3) and three
  typography issues (T1–T3) as LaTeX comments, per the preprint protocol.
- Length target: roughly 8–14 pages equivalent (this draft: ~11 pages at
  11pt/a4paper).
