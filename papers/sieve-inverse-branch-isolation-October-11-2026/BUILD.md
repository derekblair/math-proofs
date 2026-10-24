# Building this paper

The authoritative current manuscript is
`build/sieve-inverse-branch-isolation-October-11-2026.tex`. It includes the
2026-10-23 correction replacing the three native-computation proof calls with
kernel-checked proofs and preserving the unformalized scope limits.

**The committed PDF is historical, predates this correction, and must not be
used as the current verification-status record.** No TeX toolchain was available
in the correction environment, so the PDF has not been regenerated or checked.

With an existing TeX Live installation providing `latexmk`, TikZ, pgfplots, and
booktabs, build from the repository root:

```bash
cd papers/sieve-inverse-branch-isolation-October-11-2026/build
latexmk -pdf -interaction=nonstopmode sieve-inverse-branch-isolation-October-11-2026.tex
```

The command writes its PDF in `build/`. Inspect the log for errors, unresolved
references, and layout warnings before replacing the historical PDF in the
parent paper directory. No successful TeX build is claimed for this revision.

The corrected finite residue statements can be checked from the repository root:

```bash
lake build Mathproofs.ESRefinedSieveInverse
```

The source distinguishes the kernel-proved `q = 19` lift-set equality from the
unformalized `q = 23` and external-sieve claims.
