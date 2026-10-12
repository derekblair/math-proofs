# BUILD — subfamily-ladder-ceiling-October-11-2026

## Source

- Main file: `build/subfamily-ladder-ceiling-October-11-2026.tex`
- Bibliography is inline (`thebibliography`); no BibTeX/Biber run is needed.
- All figures are native TikZ/pgfplots; all tables are booktabs. No
  external image files, no `\includegraphics`.

## Build steps

From this directory:

```sh
cd build
pdflatex subfamily-ladder-ceiling-October-11-2026.tex
pdflatex subfamily-ladder-ceiling-October-11-2026.tex
```

Run `pdflatex` twice so that cross-references (`\ref`, `\label`) and the
table of contents resolve. The output is
`build/subfamily-ladder-ceiling-October-11-2026.pdf`.

(Alternative: `latexmk -pdf subfamily-ladder-ceiling-October-11-2026.tex`.)

## Requirements

- A LaTeX toolchain with TikZ, pgfplots (compat 1.18), booktabs,
  amsmath/amssymb/amsthm, geometry, hyperref — e.g. a current TeX Live.
- No special fonts, packages, or network access are required.

## Expected result

A PDF of roughly 10–12 pages. Verify after compiling:
1. All `\ref` targets resolve (no `??` in the output).
2. The ladder-length bar chart figure and both tables (formalization
   inventory, R245 eight-shape census) render.
3. The three substantive weaknesses and three typography issues are present
   as trailing LaTeX comments (not in the PDF).
