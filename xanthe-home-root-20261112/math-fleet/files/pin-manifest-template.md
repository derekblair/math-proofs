# Pin Manifest — TEMPLATE (adopted 2026-10-26, Derek's order, from the OpenAI-study lessons)

Every standard-track candidate (novel result, formalization target, book node) gets a pin manifest BEFORE any proof/formalization lane launches. The manifest freezes the target: proof lanes may not edit it. A changed statement means a NEW manifest version, with the change and its reason recorded — never a silent edit.

Copy this file to `~/workspace/math-fleet/pins/<slug>.md`, fill every field, compute the hashes, and record the manifest path in the lane REGISTRY before launch.

```yaml
candidate: <slug — e.g. a111495-eq-a111499, merkle-rfc6962-soundness, rudin-10-43>
repo: <derekblair/math-proofs | derekblair/rudin-lean | derekblair/formalize-everything>
created: <YYYY-MM-DD>
frozen_by: <coordinator / lane that pinned it>
source:
  citation: <paper/book/RFC + section/theorem number>
  verbatim_quote: >
    <the source statement, quoted exactly — no paraphrase>
  strongest_published_form: >
    <the strongest known version of this claim in the literature, with citation;
     if the pin is weaker, the delta is stated here in one sentence>
statement_file:
  path: <repo-relative path of the .lean file carrying the pinned statement(s)>
  sha256: <hash of the file at pin time>
  commit: <repo commit the hash was taken at>
theorems:
  - name: <fully qualified Lean name>
    informal: <one-line restatement>
    # repeat per theorem/definition in scope
axiom_allowlist: [propext, Classical.choice, Quot.sound]
trust_policy:
  native_decide: forbidden
  ofReduceBool: forbidden
  custom_axioms: forbidden
  sorry_in_solution: forbidden   # sorries may exist only in the frozen statement file's placeholders, never in a solution closure
fidelity_notes: >
  <quantifier order, edge cases (empty/zero/degenerate), normalizations,
   and any hypothesis the source carries implicitly that the pin makes explicit>
delta_vs_source: >
  <NONE, or exactly how the pinned statement differs from the printed source
   and why — a weakened pin is reported as partial progress, never as the result>
review_route: <reviewer pool, which must differ from the author pool>
```

Rules:
- The pin is the contract. A solution that proves a different statement — however close — does not close the ticket (the PR #1 vacuous-statement lesson; the 10.43 rule).
- The manifest lives on the desk (this folder's `pins/`), not in the solution branch, so a proof lane cannot rewrite its own target.
- Verification evidence for a manifest is recorded per the review checklist (`review-checklist.md`): recorded outputs, never bare commands.
