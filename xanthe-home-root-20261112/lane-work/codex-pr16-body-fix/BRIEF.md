# Forward-fix brief — math-proofs PR #16 PR-body wording (coordinator lane, NOT a review)

## Appointment
You are the coordinator's fix lane for math-proofs PR #16 (branch rule129-pin-freeze,
head 3fc2503c69dba90dcf438be5c5334079c9c41266, draft). The independent crossed
review by nibbles / chatgpt-proton (REVIEW.md harvested to the desk, 2026-10-28)
returned FAIL on two body/provenance findings only. The frozen source itself PASSED:
statement fidelity CONFIRMED, compile exit 0, axiom reports CONFIRMED (every theorem
contains sorryAx, as disclosed), recomputation CONFIRMED, trust screen CONFIRMED.
This lane fixes the body wording only. It does not certify a proof of anything.

## Blocking findings to fix (from the review)
- F1 — PR-body wording implying proof: the body lines 108-110 say "The pinned
  theorems prove both" the full Rule 126 result and Mathar's conjecture "with zero
  weakening", and lines 183-186 label the strength delta NONE, proving "the exact
  full-quantifier statement". These are present-tense proof claims. The actual
  theorem bodies are sorry placeholders at source lines 90, 95, 100, and every
  recorded axiom report contains sorryAx. The opening disclaimer is correct; the
  embedded manifest wording contradicts it.
- F2 — REFUTED citation: the body / PIN.md line 31 cites arXiv:1503.01168v3.
  The review found arXiv lists only v1 for that paper, v3 requests return 404,
  and section 6.1 of the v1 paper contains the relevant Rule 126 row-sum
  assertion. Verify this yourself against arXiv before changing anything.

## What to do (in order)
1. Fetch the live PR body with gh (gh pr view 16 --repo derekblair/math-proofs
   --json body,headRefOid,isDraft). Confirm the head is still
   3fc2503c69dba90dcf438be5c5334079c9c41266 before touching anything. If the
   head moved, STOP and report that in FIX-REPORT.md without editing.
2. Fix F1 in the PR body via gh pr edit: replace the unqualified proof wording
   with accurate wording stating BOTH facts distinctly: (a) the pinned statements
   have zero statement weakening against the target (same quantifiers and
   hypotheses as the published target), and (b) the theorems are currently sorry
   placeholders with zero proved theorem content; proof is future work, and this
   PR claims a statement freeze only, not a proof. Keep the existing accurate
   disclaimer. Do not soften (a) into a weaker statement claim, and do not leave
   any present-tense "proves" wording about the three theorems.
3. Fix F2 in the PR body: correct the citation to the version you verified on
   arXiv (expected v1), keeping the section reference accurate. Quote the exact
   arXiv history evidence you checked in the report.
4. DO NOT edit the Lean source file, DO NOT edit PIN.md (it is a frozen manifest;
   a changed statement needs a new manifest version, and this fix changes no
   statement). Record the PIN.md line-31 citation discrepancy in FIX-REPORT.md as
   an open manifest-version decision for the coordinator: the body is corrected,
   the frozen pin still carries the old citation string.
5. DO NOT merge, DO NOT mark the PR ready for review (it stays draft), DO NOT
   post a GitHub review or comment, DO NOT open a new PR, DO NOT change the
   branch. This lane edits the PR body only.
6. Verify: re-fetch the live PR body after the edit and confirm the corrected
   lines are present and no present-tense proof claim about the three theorems
   remains anywhere in the body. Record before/after excerpts (the exact changed
   lines) in FIX-REPORT.md.

## Deliverable
FIX-REPORT.md in this workdir: head confirmation, F1 before/after excerpts,
F2 arXiv verification evidence and before/after, the PIN.md citation open item,
the post-edit body verification, and a one-line verdict: BODY-FIXED or STOPPED
with the reason. When the report is written and the body verified, your work is
done; the session may exit. A fresh independent re-review by a different pool
(chatgpt-proton on a Lean machine, never chatgpt-gmail, never chatgpt-live) will
follow; you are not that reviewer.
