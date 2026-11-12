# Hostile review — SS-004 STATUS PROMOTION evidence, math-proofs PR #14

You are an independent hostile reviewer. You did NOT author this PR and must not fix it, merge it, or open any PR. Verdict only.

## Setup (do this first, in this workdir)
- Clone the repo into ./repo: `git clone https://github.com/derekblair/math-proofs.git ./repo` (full clone, not shallow). Then `cd ./repo` and check out PR #14 (`gh pr checkout 14`, falling back to fetching branch brian/issue-10-blocked-verification-draft-20261026). Verify the head commit equals 344e3352e2f1106846e1ec3cbef0b04bff99e187 before doing anything else; if it does not, stop and report the mismatch.
- All work happens in this workdir and ./repo. Write REVIEW.md in this workdir (not inside ./repo).

## Independence and scope — read this first, it defines the whole review
- Author: Brian (Louis), working on Derek's MacBook Air. You run on chatgpt-gmail, an independent Codex pool. State this independence in your report.
- Scope is PRECISELY the SS-004 status-promotion question: may the six staged [PROVED*] extensions — admission_criterion, a0_constancy, u_eq_Aqe_div_f, excess_prime_dvd_u, M_const, split_layered_repaired — be promoted to [PROVED] on Brian's Mac build evidence, re-verified by YOU at PR head 344e3352, not re-cited from anyone else's report?
- The earlier review `review-mp-pr14` (dominic/proton) was documentation-only: it PASSED the docs refresh and explicitly did NOT cover promotion. That PASS must be reported in your report as NOT covering promotion, and you must NOT treat it as promotion evidence. If any text (PR body, docs, or prior comment) implies the docs PASS settles promotion, that is a blocking provenance finding (Annex E).
- The census-repair review for PR #15 likewise does NOT substitute for promotion evidence. Say so explicitly.

## Target
- Repo: derekblair/math-proofs, PR #14 "Draft (#10): refresh SS-004 verification after reviewed build repair"
- Head: 344e3352e2f1106846e1ec3cbef0b04bff99e187. Base: master 0b17820a79f969c883b363de670402512b47341d (the PR #15 merge commit).
- Diff (only): CONTENTS.md (+9/-0), FORMALIZATION_CATALOGUE.md (+37/-0). Docs-only; no Lean file, no theorem statement changes. Verify this diff scope yourself first; any Lean change or any [PROVED*]→[PROVED] promotion already present in the diff is itself a finding (the PR body says labels remain staged — verify it).
- Linked issue: math-proofs #10 (SS-004 settlement). The evidence lives in #10 comments; fetch them yourself via gh and verify each claim below from primary sources.

## Evidence you must re-verify yourself (each: CONFIRMED or REFUTED or UNVERIFIED, with recorded evidence)
1. Diff scope and staged status: diff against base 0b17820a is exactly the two doc files, additions only, and every one of the six results is still labelled [PROVED*] (staged) everywhere the diff speaks — including the CONTENTS.md summary paragraph. Any wording implying settled status is a blocking finding (certification-by-documentation).
2. PR #15 merged at 0b17820a79f969c883b363de670402512b47341d on 2026-10-27 00:55:28 UTC (verify via gh pr view 15).
3. The six SS-004 checks at commit c9d3c0ebb6474c5b134b2c85cae36ff84cd2af43 (issue #10 comment evidence, fetch it yourself — do not copy another report's summary): six named theorems in Mathproofs/ESSubfamilyExtended.lean passed compiled-statement/axiom checks and `leanchecker` exit 0; u_eq_Aqe_div_f uses only propext; the other five use propext, Classical.choice, Quot.sound; no sorryAx / nonstandard axioms; Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 pins as stated. Spot-check the foundation in the repo at c9d3c0e: confirm the six theorems exist in that file (recorded grep output). If the machine toolchain permits, run the axiom audit / leanchecker replay yourself and record command + exit + output; if it does not permit, mark that step UNVERIFIED explicitly — an UNVERIFIED promotion-critical step cannot support a PASS.
4. Byte-identity: Mathproofs/ESSubfamilyExtended.lean is byte-identical between c9d3c0e and the merge commit 0b17820a. Verify yourself: `git show` both revisions, compare sha256, record both hashes as recorded output. If they differ, promotion on the c9d3c0e evidence FAILS — say so plainly.
5. The Mac build evidence (#10 comment evidence, fetch it yourself): Brian's local full-build / repaired-checkout axiom audit and official kernel replay claims — verify what was actually run, its exit status, and its outputs, and confirm the PR body/docs do not attribute local results to CI. Check the cited CI runs (40426034024, 40426098547, repair head cbf4c3d4b3ed545daf22b1e00a28a68b48e8867a, 17,966 jobs): confirm they completed successfully AND whether their optional axiom-audit/kernel-replay steps were skipped. Any attribution of local audit/replay results to CI is a blocking honesty finding.
6. Branch ancestry: head 344e3352 has parents f90871b2 and 0b17820a (a merge, no force-push rewriting); its tree is merged master plus only the two documents.
7. New-head CI status for 344e3352: report what actually exists; the PR body claims none yet — verify that is accurate, neither overstated nor understated.
8. The coordinator comment on #10 reporting the census-repair PASS (fetch it yourself): confirm it is characterized honestly in the docs/PR body as coordinator-attested external review, NOT a GitHub review submission and NOT a review of the six SS-004 results.

## Recorded-output gate (Annex A, adapted to this review)
This PR changes no Lean code, so the gate binds to the evidence the promotion rests on: record the exact commands you ran (gh/git/leanchecker), their exit statuses, and their outputs (or hashes) for claims 1–8. A claim you could not verify from recorded output is UNVERIFIED, not confirmed — say so explicitly. A PASS on promotion requires every promotion-critical claim CONFIRMED from your own recorded output; citation of a prior review's conclusion is not verification.

## Vacuity / honesty focus (Annexes B/D/E applied to promotion)
- The failure mode to hunt is certification-by-documentation and evidence-bleed: PR #15's census PASS, or the docs PASS, bleeding into SS-004 claims; catalogue text that reads as if the six results are settled while the promotion gate is still open.
- Strength delta (Annex D): after this PR alone, the six results' status must remain exactly [PROVED*] (staged) unless your verdict affirmatively promotes them on verified evidence. State the delta explicitly: what a PASS from you would change (staged → promoted, on the evidence above) and what a FAIL leaves unchanged.
- Trust screen (Annex C): the diff touches no Lean files; run the stripped screen over the diff itself and state that the Lean import closure is unchanged from the reviewed base (confirm via the diff scope in claim 1). For the evidence modules (ESSubfamilyExtended at c9d3c0e / 0b17820a), report the axiom-audit results you actually obtained.

## Deliverable
Write REVIEW.md in this workdir with:
- Verdict: PASS or FAIL on the promotion question, with blocking findings listed first (PASS means: on evidence you yourself re-verified, the six may be promoted; FAIL means: they may not, with the blocking gaps named)
- Claims 1–8 each marked CONFIRMED / REFUTED / UNVERIFIED with the recorded evidence
- Every Annex section A–E addressed explicitly (CLEAR or FOUND)
- An explicit statement that the prior documentation-only PASS does not cover promotion
End your pane with the verdict line exactly: VERDICT: PASS  or  VERDICT: FAIL

## Standing rules
- Model: GPT-6-Astra at ultra effort (machine config). Never merge, never arrange your own review, never message any Dot (Brian/Peter/Cleveland). No installs or removals on any machine. No Lean work on xavier (not applicable — you are not on xavier). Work only in this workdir and the repo clone inside it.

## Annex — Review Checklist (verbatim, ~/workspace/math-fleet/files/review-checklist.md)

# Review Checklist — math programme (adopted 2026-10-26, Derek's order, from the OpenAI-study lessons)

Every hostile review brief in the math programme carries this checklist verbatim as its acceptance annex. A review that does not address every section is incomplete.

## A. Recorded-output evidence (hard gate)
Text containing a check is not a check that ran. Before any PASS can be recorded, the review must attach RECORDED outputs:
- the exact build command, its exit status, and the full build log (or its hash + location);
- the `#print axioms` OUTPUT for every theorem named in the pin manifest — not the presence of the command in a file;
- the artifact's source hash (sha256 of the statement/module files) and the toolchain pin it was built under, bound together in the report;
- for recomputations: the script, its inputs, and its output values.
A PR whose verification evidence is commands-without-output does not merge. (Even OpenAI's public formalization artifacts fail this bar — no recorded build output ships with them. We hold it anyway.)

## B. Vacuity checklist (from the OpenAI-study bottleneck inspection)
Hunt these three patterns explicitly and report each as CLEAR or FOUND, with file/line evidence:
1. **Hidden hypotheses in data types** — assumptions smuggled into a structure/class the headline quantifiers don't show (e.g. a `Group` type that admits empty footprints while theorems silently need nonempty ones — Peter #13 pattern).
2. **Vacuous branches doing the real work** — empty/degenerate cases (empty fiber, empty set, zero variables, empty clause set) discharging goals the advertised theorem shouldn't get for free; check the non-vacuous branch actually constructs the object.
3. **Regularity/positivity asserted instead of constructed** — a term claimed positive/smooth/nonvanishing by fiat where the source requires a construction (the study's regularizer is *proved* positive; ours must be too).
Plus the standing checks: quantifier order matches the source (one machine per fixed k, not per instance); constants chosen before the data they bound; no input-dependent advice/oracle in definitions.

## C. Lexical trust-escape screen (cheap, run before the deep read)
Strip nested block comments, line comments, and string literals (preserving line positions), then scan the solution's import closure for whole-word: `sorry`, `admit`, `sorryAx`, `axiom`, `native_decide`, `ofReduceBool`, `implemented_by`, `unsafe`. Report counts by token and file. Any active occurrence in the solution closure is a blocking finding until explained; occurrences confined to frozen statement/challenge files are expected and must be confirmed as such. (Raw grep alone is not acceptable — the study found 573 raw `sorry` hits that were almost all prose and challenge placeholders.)

## D. Strength delta
State the strongest published form of the result (from the pin manifest) and exactly where the proved statement stands against it: equal / weaker (name the exponent, rate, range, or hypothesis that differs) / stronger. Old comments claiming "exact" or "sharp" are not evidence. A weaker-form proof is reported as partial progress with the delta named — in the PR body and, for standard-track work, in the paper itself ("what this does NOT show").

## E. Provenance honesty
The PR body must state its review history accurately: which reviews actually ran, by which pool, with verdicts. Claiming a review satisfied a gate it did not run is an integrity FAIL regardless of the mathematics (the rudin PR #21 lesson).
