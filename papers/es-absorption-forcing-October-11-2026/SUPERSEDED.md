# SUPERSEDED: October 11 absorption PDF

`es-absorption-forcing-October-11-2026.pdf` and the identical copy in
`build/` are historical, pre-remediation artifacts. **Do not use either PDF
as a statement of the current formalization.** The PDF was not regenerated
in this hygiene pass.

The current source is
[`build/es-absorption-forcing-October-11-2026.tex`](build/es-absorption-forcing-October-11-2026.tex).
The controlling theorem statements are in
[`Mathproofs/ESAbsorptionOrder.lean`](../../Mathproofs/ESAbsorptionOrder.lean):

- `absorp_datum_iff` requires `G.C.Nonempty`; `datum_eq_of_absorpLE` needs
  no nonemptiness premise.
- For distinct `G ≼ H`, `rho_absorption_collapse` and
  `absorption_collapse_unique_core` require `H.C.Nonempty`. Uniqueness is
  for cardinality-one cores, hence the minimum core in this situation.
- `singleton_factorization` takes a finite ambient family `𝒢 ⊇ S`, with
  no singleton footprint `{c}` in `𝒢` for `c ∈ S0`.

The previous universal nonemptiness premise was impossible because the
unrestricted `Group` structure admits an empty footprint. The merged
remediation replaced it with the local hypotheses above. The PDF predates
that repair and the ambient-family repair; its blanket machine-checking
wording also does not certify the external census counts.

On 2026-10-24, the installed Tectonic executable was tried with
`--only-cached --untrusted --keep-logs` and task-local cache/output
directories. It exited 1: `failed to open input file
"tectonic-format-latex.tex"`. `latexmk`, `pdflatex`, `lualatex`, and
`xelatex` were unavailable. No TeX resources or packages were installed.
See [BUILD.md](BUILD.md) for regeneration instructions.
