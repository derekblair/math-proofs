# Math Proofs

This repository contains Lean 4.34.1 and Mathlib v4.34.1 formalizations together with accompanying mathematical manuscripts where available. **The exact exported statements determine what is proved.**

Some larger research claims still require bridges, external computational sweeps, or mathematical inputs that are not formalized; these scope limits are stated explicitly in the per-family scope documents under [`lean/docs/`](lean/docs/) and in [`lean/formalization.yaml`](lean/formalization.yaml). Nothing in this collection is claimed on the basis of a `sorry`.

Status labels used across the collection:

- **`[PROVED]`** — the named Lean statement is kernel-checked using only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
- **`[CONDITIONAL]`** — a larger interpretation whose remaining mathematical inputs are explicit theorem arguments.
- **`[PROVED*]`** — staged publication status; never silently asserts end-to-end verification of a larger unassembled claim.
- **`[COMPUTED]`** — external computation not certified by the Lean kernel.

## Navigating the collection

The catalogued collection covers **15 result families** across **12 dated preprints** (plus 4 families with preprints in preparation), alongside `preprints/rule129/` and 22 additional OEIS/Seam B and Seam C preprints under [`preprints/`](preprints/) (35 manuscript folders total). A family groups a principal result with companion arguments, consequences, or alternative proofs.

- Start with the [overview PDF](overview.pdf) ([LaTeX source](overview.tex)) for descriptions of the families.
- Use the [manuscript map](CONTENTS.md) to find individual papers, abstracts, and their supporting Lean modules.
- The [`preprints/`](preprints/) directory contains PDFs, LaTeX sources (`build/main.tex`), bibliographies (`build/references.bib`), and manuscript-specific citation and build instructions.
- The [Lean library](lean/README.md), [per-family scope documents](lean/docs/), and [formalization catalogue](lean/formalization.yaml) describe the available formal proofs, their associated papers, and verification configurations. See the [Comparator instructions](lean/ComparatorChallenges/README.md) for statement-identity checking instructions. All 15 catalogued result families (100%) have Lean formalizations (13 families with `[PROVED]` flagship theorems and 2 `[CONDITIONAL]` classification/assembly families).
- Updates and disclosed corrections are described in the [history](history.md).
- Working research dossiers and audit reports live in [`research/`](research/).

### Highlights and explicitly scoped kernels

- **Complete finite and arithmetic results:**
  - `es_covering_217mod264` in [ESIdentity.lean](lean/Mathproofs/NumberTheory/ESIdentity.lean) proves positive natural denominators for `4/n = 1/x + 1/y + 1/z` whenever `n ≡ 217 (mod 264)` (with rational equality `es_identity_217mod264`); [ESIdentityCRT.lean](lean/Mathproofs/NumberTheory/ESIdentityCRT.lean) proves the six covered subclasses modulo 9240 and exact `1/11` residue count per parent class. The former novelty claim is withdrawn in light of Miguel Angel Lopez (2024), [arXiv:2206.10319v4](https://arxiv.org/html/2206.10319v4); no priority is claimed.
  - `SidonSat184.r47_sat184` in [SidonSat184.lean](lean/Mathproofs/Combinatorics/SidonSat184.lean) kernel-checks that `{16, 62, 66, 74, 88, 104, 117, 122, 123}` is a 9-element saturated Sidon subset of `[1, 184]`; [SidonSat184Census.lean](lean/Mathproofs/Combinatorics/SidonSat184Census.lean) kernel-checks the nine displayed one-hole rows, coverage counts, saturated 10-element extensions, and both C28 gate counterexamples.
  - The refined-sieve residue theorems in [ESRefinedSieveInverse.lean](lean/Mathproofs/NumberTheory/ESRefinedSieveInverse.lean) use pure kernel proofs (former `native_decide` certificate axioms were removed).
- **Explicitly scoped kernels:**
  - `es_crt_escape` ([ESBarrier.lean](lean/Mathproofs/NumberTheory/ESBarrier.lean)) proves infinitely many escaping primes from explicit local quadratic obstructions via Mathlib's Dirichlet theorem; the Schinzel–Mordell implication from integer polynomial identities remains unformalized.
  - [ESAbsorptionOrder.lean](lean/Mathproofs/NumberTheory/ESAbsorptionOrder.lean) proves datum equivalence under `G.C.Nonempty`, absorption collapse and unique minimum core under `H.C.Nonempty`, and singleton factorization within a finite ambient family `𝒢 ⊇ S`.
  - The Collatz gap-factor modules ([CollatzGapFactor.lean](lean/Mathproofs/NumberTheory/CollatzGapFactor.lean) and companions) prove analytic/continued-fraction identities and conditional odd-block argmin assemblies; specialization to `log₂ 3` and Collatz dynamics remains outside these statements.
  - [ESQRCoreCount.lean](lean/Mathproofs/NumberTheory/ESQRCoreCount.lean), [ESCovering.lean](lean/Mathproofs/NumberTheory/ESCovering.lean), [ESDescentCovering.lean](lean/Mathproofs/NumberTheory/ESDescentCovering.lean), [ESQadicBoundary.lean](lean/Mathproofs/NumberTheory/ESQadicBoundary.lean), and [Girth5Extremal.lean](lean/Mathproofs/Combinatorics/Girth5Extremal.lean) carry explicit scope boundaries documented in [`lean/docs/`](lean/docs/).

## How the results were produced

Results in this collection are produced through an orchestrated multi-lane research and verification programme run by Derek Blair. Problem exploration, literature prior-art checks, computational experiments, manuscript drafting, Lean 4 formalization, and adversarial review execute in separate specialized lanes across a dedicated build and verification fleet. Formalized statements are promoted only after passing clean Lean 4 kernel builds (`lake build` and `leanchecker`), zero-`sorry` checks, standard-axiom audits (`propext`, `Classical.choice`, `Quot.sound`), and independent cross-session review; refuted or over-scoped drafts are repaired or withdrawn openly in [`history.md`](history.md).

## Versions and citations

Public release history and disclosed corrections are preserved in [`history.md`](history.md), with previously released editions accessible in git history.

The October 23–24, 2026 corrections updated `overview.tex` and the LaTeX sources for the ES identity, ES barrier, `r47-sat184`, sieve-inverse, and absorption-forcing manuscripts. Their committed PDFs remain historical pre-correction artifacts pending TeX regeneration; the corrected `.tex` sources under `preprints/<slug>/build/main.tex`, the per-family scope docs under [`lean/docs/`](lean/docs/), and the Lean declarations under [`lean/`](lean/) are authoritative. See each paper's `preprints/<slug>/README.md` for supersession notices and rebuild notes.

To cite an individual manuscript, use the BibTeX block in its `preprints/<slug>/README.md`.
