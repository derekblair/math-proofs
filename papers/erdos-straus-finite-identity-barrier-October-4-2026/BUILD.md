# Building this paper

The authoritative current manuscript is `erdos-straus-finite-identity-barrier-October-4-2026.tex`. Its 2026-10-23 correction
records the scoped CRT escape theorem with explicit local-obstruction hypotheses and the exact remaining scope limits.

**The committed PDF is historical and predates these corrections.** It must not
be used as the current verification-status record. No TeX toolchain was available
in the correction environment, so this revision has not been compiled to PDF or
checked for layout and reference warnings. No toolchain was installed.

With an existing TeX installation providing `latexmk`, TikZ, pgfplots, and
booktabs, regenerate it from the repository root:

```bash
cd papers/erdos-straus-finite-identity-barrier-October-4-2026
latexmk -pdf -interaction=nonstopmode erdos-straus-finite-identity-barrier-October-4-2026.tex
```

This command replaces the historical PDF in place. Inspect the build log and PDF
before treating it as the current rendered manuscript. No successful TeX build
is claimed for this revision.

The Lean module can be checked from the repository root:

```bash
lake build Mathproofs.ESBarrier
```
