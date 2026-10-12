# Building this paper

The preprint compiles to PDF with `latexmk`. TeX Live 2023+ works; no
external image files or non-CTAN packages are needed (all figures/tables are
native TikZ/pgfplots/booktabs).

```bash
cd papers/sieve-inverse-branch-isolation-October-11-2026/build
latexmk -pdf -interaction=nonstopmode sieve-inverse-branch-isolation-October-11-2026.tex
```

The committed `.pdf` in this directory will be built with the command above
by the coordinator; the build is expected to have zero errors, zero
undefined references/citations, and zero overfull / underfull boxes.
