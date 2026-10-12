# Build instructions — hole-suppression-absorption-October-11-2026

## Sources
- `build/hole-suppression-absorption-October-11-2026.tex` — the full preprint
  (self-contained; no `\input` of external generated files).
- `CITATION.bib` — minimal BibTeX entry (note: `eprint` field is a
  `[PLACEHOLDER]` until the arXiv ID is assigned).
- `BUILD.md` — this file.

## Build
```sh
cd build
pdflatex hole-suppression-absorption-October-11-2026
pdflatex hole-suppression-absorption-October-11-2026
```
Two runs: the second resolves cross-references (`\ref`/`\label`) and the
hyperref bookmarks. A third run is only needed if warnings persist
("Rerun to get cross-references right").

## Requirements
- A standard TeX Live install (2022+) with these packages: `amsmath`,
  `amssymb`, `amsthm`, `tikz` (+ `positioning` library), `pgfplots`
  (compat 1.18), `booktabs`, `geometry`, `hyperref`.
- **No external assets**: all figures are native TikZ/`pgfplots` inline in
  the `.tex`; all tables are `booktabs`. No `\includegraphics`, no `.svg`,
  no image files needed.

## PDF
The PDF is compiled later by the coordinator (not built here). After the
double `pdflatex`, expected output:
`build/hole-suppression-absorption-October-11-2026.pdf` (~8–14 pages).
