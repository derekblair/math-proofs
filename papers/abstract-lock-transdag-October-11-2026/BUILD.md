# BUILD — abstract-lock-transdag-October-11-2026

## Source

- Main file: `build/abstract-lock-transdag-October-11-2026.tex`
- Bibliography is inline (`thebibliography`); no BibTeX/Biber run is needed.
- All figures are native TikZ/pgfplots (lock-frame firing patterns, the
  Q-26 non-entailment model diagram); all tables are booktabs. No external
  image files, no `\includegraphics`.

## Build steps

From this directory:

```sh
cd build
pdflatex abstract-lock-transdag-October-11-2026.tex
pdflatex abstract-lock-transdag-October-11-2026.tex
```

Run `pdflatex` twice so that cross-references (`\ref`, `\label`) resolve.
The output is `build/abstract-lock-transdag-October-11-2026.pdf`.

(Alternative: `latexmk -pdf abstract-lock-transdag-October-11-2026.tex`.)

## Requirements

- A LaTeX toolchain with TikZ (positioning, shapes, arrows.meta),
  pgfplots (compat 1.18), booktabs, amsmath/amssymb/amsthm, geometry,
  hyperref — e.g. a current TeX Live.
- No special fonts, packages, or network access are required.

## Expected result

A PDF of roughly 10–12 pages. Verify after compiling:
1. All `\ref` targets resolve (no `??` in the output).
2. The two figures (lock-frame firing patterns, Q-26 non-entailment
   model diagram) and both tables (formalization inventory, 472-frame
   census) render.
3. The three substantive weaknesses and three typography issues are present
   as trailing LaTeX comments (not in the PDF).
