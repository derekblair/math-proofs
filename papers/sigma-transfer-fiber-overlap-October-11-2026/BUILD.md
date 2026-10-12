# BUILD — sigma-transfer-fiber-overlap-October-11-2026

## Source

- Main file: `build/sigma-transfer-fiber-overlap-October-11-2026.tex`
- Bibliography is inline (`thebibliography`); no BibTeX/Biber run is needed.
- All figures are native TikZ/pgfplots (including the six-hole witness
  number line drawn from `r294_q20_verify.json` data); all tables are
  booktabs. No external image files, no `\includegraphics`.

## Build steps

From this directory:

```sh
cd build
pdflatex sigma-transfer-fiber-overlap-October-11-2026.tex
pdflatex sigma-transfer-fiber-overlap-October-11-2026.tex
```

Run `pdflatex` twice so that cross-references (`\ref`, `\label`) resolve.
The output is `build/sigma-transfer-fiber-overlap-October-11-2026.pdf`.

(Alternative: `latexmk -pdf sigma-transfer-fiber-overlap-October-11-2026.tex`.)

## Requirements

- A LaTeX toolchain with TikZ (positioning, shapes, arrows.meta),
  pgfplots (compat 1.18), booktabs, amsmath/amssymb/amsthm, geometry,
  hyperref — e.g. a current TeX Live.
- No special fonts, packages, or network access are required.

## Expected result

A PDF of roughly 10–12 pages. Verify after compiling:
1. All `\ref` targets resolve (no `??` in the output).
2. The three figures (T5 taxonomy schematic, frontier-size bar chart,
   six-hole witness number line) and both tables render.
3. The three substantive weaknesses and three typography issues are present
   as trailing LaTeX comments (not in the PDF).
