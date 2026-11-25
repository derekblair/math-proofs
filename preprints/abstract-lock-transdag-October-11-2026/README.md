# [Abstract Locks and Transition DAGs: Repaired Consecutive-Firing Laws, the Dual-Ascent Barrier, and Ascent-Depth Bounds](paper.pdf)

Derek Blair · October 11, 2026 edition

We report two order-theoretic theories from the march-graph program. Abstract lock theory axiomatizes lock frames `L = (W, c⋆, τ, λ, ε)` and proves the repaired consecutive-firing laws together with the explicit sharpness counterexample `W = {0, 2}` refuting the original unconditional T3(iii) clause. Transition DAG theory proves the axiom-free dual-ascent barrier (`no_dual_target_demote`, `no_dual_source_promote`), reflection-cardinality preservation (`dual_preserves_s_card`), and finite-DAG ascent-depth bounds (`ascentDepth_*`), while recording the original stronger D7 barrier as `[OPEN]`.

## Lean formalization

Both modules (`AbstractLock`, `TransDAG`) are `[PROVED]` in Lean 4.34.1 with zero sorrys and standard axioms only (the dual-ascent barrier theorems are axiom-free). [Proof link](../../lean/Mathproofs/NumberTheory/TransDAG.lean#L78-L93) · [Scope](../../lean/docs/012.md)

## Manuscript files

The [LaTeX source](build/main.tex) and [bibliography](build/references.bib) are in the [build directory](build/). All figures are native TikZ/pgfplots and all tables use booktabs (inline bibliography in `main.tex`). From this manuscript directory, rebuild the [PDF](paper.pdf) with pdfLaTeX through `latexmk`.

```sh
cd build
latexmk -pdf -halt-on-error -interaction=nonstopmode main.tex
cp main.pdf ../paper.pdf
```

## Citation

```bibtex
@misc{blair2026abstractlocktransdag,
  author = {Derek Blair},
  title = {{Abstract Locks and Transition DAGs: Repaired Consecutive-Firing Laws, the Dual-Ascent Barrier, and Ascent-Depth Bounds}},
  howpublished = {math-proofs preprint
                  \href{https://github.com/derekblair/math-proofs/blob/master/preprints/abstract-lock-transdag-October-11-2026/paper.pdf}{math-proofs:abstract-lock-transdag}},
  year = {2026},
  month = oct,
  note = {Lean formalizations in lean/Mathproofs/NumberTheory/{AbstractLock,TransDAG}.lean.}
}
```
