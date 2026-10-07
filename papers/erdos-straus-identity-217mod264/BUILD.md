# Building this paper

The preprint compiles to PDF with `latexmk`. TeX Live 2023+ works; no
external image files or non-CTAN packages are needed (all figures/tables are
native TikZ/pgfplots/booktabs).

```bash
cd papers/erdos-straus-identity-217mod264
latexmk -pdf -interaction=nonstopmode erdos-straus-identity-217mod264.tex
```

The committed `.pdf` in this directory was built with the command above and
has zero errors, zero undefined references/citations, and zero overfull /
underfull boxes.
