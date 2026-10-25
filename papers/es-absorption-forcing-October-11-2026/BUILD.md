# Building this paper

The corrected source is in `build/`. Both committed PDFs are historical
October 11 artifacts and are **SUPERSEDED**; see [SUPERSEDED.md](SUPERSEDED.md)
for the repaired theorem scope. They have not been regenerated from this
source.

With an existing TeX installation supplying TikZ, pgfplots, and booktabs,
the intended build is:

```bash
cd papers/es-absorption-forcing-October-11-2026/build
latexmk -pdf -interaction=nonstopmode es-absorption-forcing-October-11-2026.tex
```

After a successful build and rendered-layout check, copy the resulting PDF
to the paper directory so both tracked copies agree.

The 2026-10-24 rebuild attempt used the existing Tectonic executable with
`--only-cached --untrusted --keep-logs` and task-local cache/output
directories. It failed with exit 1 because `tectonic-format-latex.tex` was
unavailable. No TeX resources or packages were installed. The corrected
source has not received a successful PDF build or rendered-layout check.
