# Building this paper

The preprint compiles to PDF with `latexmk`. TeX Live 2023+ works; no
external image files or non-CTAN packages are needed (all figures/tables are
native TikZ/pgfplots/booktabs).

```bash
cd papers/void-frames-defect-October-11-2026/build
latexmk -pdf -interaction=nonstopmode void-frames-defect-October-11-2026.tex
```

The committed `.pdf` in this directory was built with the command above and
has zero errors and zero undefined references/citations.
