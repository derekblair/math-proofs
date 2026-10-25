# Building this paper

The `.tex` source contains the 2026-10-23 corrections. The committed PDF is
a historical pre-correction artifact, including the false extension claim;
it has not been regenerated. No TeX toolchain was available for this repair,
so no rendered-PDF validation is claimed.

From the repository root, build the Lean finite witness:

```bash
lake build Mathproofs.SidonSat184
```

With Python 3 and an existing TeX Live installation providing `latexmk`,
TikZ, pgfplots, and booktabs, regenerate the diagram and PDF:

```bash
cd papers/r47-sat184-October-7-2026
python3 verify_witness.py --write-strip
latexmk -pdf -interaction=nonstopmode r47-sat184-October-7-2026.tex
```

The Python checker verifies the main witness, blocking multiplicities, and
all nine displayed one-hole extensions. `strip.inc` is committed and can be
reproduced with the command above. The Lean theorem does not trust Python
output. The historical large shell enumeration is not reproduced here.
