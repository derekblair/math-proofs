# Status

Last updated: 2026-10-28 (UTC).

## Task completed

Delivered the self-contained Rule 129 / Rule 126 preprint requested in `BRIEF.md`, with an explicit pending-proof status, exact supplied evidence bounds, references, and delivery notes. All task files are in this directory; no installs, Lean invocations, or GitHub writes were performed. This completion is for the writing task, not the mathematical proof.

## Progress

- Read `BRIEF.md`, both supplied reports, and applicable local instructions.
- Extracted the lower-part submask statement, Mersenne exception, and all 18 thresholds.
- Identified an input limitation: the consolidation report gives the largest converse range (`p = 18`, `2 <= n <= 512000`) but does not reproduce per-tier analytic-row or simulation ranges. Missing bounds are explicitly disclosed.
- Mathematical audit confirms the exact same-seed reduction: Rule 129 is the pointwise complement of Rule 126 for every positive generation; generation zero is exceptional.
- Reference audit found necessary corrections to the brief: `A267442(n) = A043545(n)` is a published OEIS conjecture for `n > 0`, not a new identity assertion, and the sequences differ at `n = 0`. `A071051` already records the row-count formula. The draft discloses this prior art and qualifies its novelty language.
- Confirmed and used the installed `pdflatex` (pdfTeX / TeX Live 2025).
- Drafted `paper.tex`: target theorem, exact same-seed reduction, positive-index OEIS identity, binomial/Lucas roadmap, all-tier evidence table, threshold checks, and bibliography.
- Completed independent source audits in `math-audit.md`, `evidence-audit.md`, and `references-audit.md`; public source snapshots are retained locally.
- Disclosed the required footnote's pin-status tension: the brief says "proof pinned", while both reports still list pin freezing as pending.
- Integrated all three independent reviews. Corrected the support-tranche marker attribution and displayed the algebraic equivalence to the existing A127872 formula, further limiting the novelty claim.
- Completed `PAPER-NOTES.md`, including all source omissions, deviations needed for accuracy, pin-status qualifications, proof obligations, theorem-numbering considerations, and compile details.
- Compiled `paper.pdf`: **9 pages**, using the installed `pdflatex`; final build has **no errors or warnings**, unresolved citations/references, or overfull/underfull boxes.
- Checked all 18 numerical table rows, labels/citation keys, first-page status footnote, and proof-status vocabulary. Visually reviewed all nine pages. Results are recorded in `verification.txt`.

## Deliverables

- `paper.tex` — self-contained article source.
- `paper.pdf` — compiled preliminary preprint.
- `PAPER-NOTES.md` — delivery notes and unresolved source/proof questions.
- `math-audit.md`, `evidence-audit.md`, `references-audit.md` — independent reviews.
- `compile-final.log`, `verification.txt`, `paper.txt`, and `preview-*.png` — verification artifacts.

## Future proof-project work (outside this writing task)

- Establish the dynamical recurrence-to-binomial equality and complete the Lean development.
- Supply/audit the frozen pin and formal theorem identifiers.
- Retrieve original tranche logs to fill omitted per-tier bounds.
- Complete wider literature review before asserting mathematical novelty.

No writing-task action or user confirmation remains pending.
