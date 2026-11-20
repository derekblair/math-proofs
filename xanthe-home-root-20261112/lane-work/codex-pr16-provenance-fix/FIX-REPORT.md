# PR #16 body provenance fix

Completed 2026-10-29 05:00:22 UTC on xanthe as the coordinator body-only fix lane, not the PR author or reviewer.

Target: https://github.com/derekblair/math-proofs/pull/16

## Body hashes and live verification

SHA256 is computed over the UTF-8 bytes of the live `body` field returned by `gh pr view`, with no added newline or whitespace normalization.

- Before: `f767cd45a4aa41319a27ad8219f6b2597fc223f53ab6e17275b037c04a794194` (`pr-body-before.md`; live response `pr-before.json`).
- After: `df09ea8ac69bd8d4565f9ee761a411da8718ec297ae83652705b23e86f182e24` (`pr-body-after.md`; live response `pr-after.json`).
- Fetched the live body via `gh` before editing and checked it again immediately before submission; there was no intervening body change.
- Submitted only the body using `gh pr edit 16 --repo derekblair/math-proofs --body-file pr-body-proposed.md`.
- Fetched the live PR again after the edit and confirmed its body exactly matches the submitted bytes.

## Exact changes

Inserted the following section immediately before `## Coordinator desk handoff`:

```markdown
## Review history

- 2026-10-28 crossed review — host `nibbles`, pool `chatgpt-proton`, verdict **FAIL**. Blocking findings: (F1) PR-body present-tense proof claims contradicted the three `sorry` placeholders; (F2) the citation arXiv:1503.01168v3 was refuted (arXiv lists only v1).
- 2026-10-28 coordinator body-only fix — host `xanthe`, pool `chatgpt-gmail`. Corrected F1 proof-status wording and F2 citation to arXiv:1503.01168v1, section 6.1, 2015; no Lean source or `PIN.md` change; head unchanged.
- 2026-10-28 post-fix crossed re-review — host `nibbles`, pool `chatgpt-proton`, verdict **FAIL**. Single blocking finding: provenance omission (the body did not yet record the prior review history). All technical freeze checks passed: head, statement hash `2bfada69046ed20429e039c895aae8eb2617663f86cf5027ec9600de64ad758e`, toolchain v4.34.1, compile, axiom outputs, recomputation, and trust screen.
- 2026-10-29 coordinator body-only provenance fix (this edit) — host `xanthe`. This edit adds the review history and corrects the review-gate wording; no Lean source or `PIN.md` change; head unchanged. The freeze gate remains **OPEN pending a fresh PASS re-review**. Neither crossed review returned PASS; this edit does not satisfy the gate.
```

Within the manifest rendering's `review_route`, replaced this exact line:

```text
  satisfies the cross-model review gate without pre-assigning a specific host machine).
```

with:

```text
  cross-model review gate remains OPEN pending a fresh PASS re-review).
```

These are the only body changes. Removing the inserted section and reversing that single-line replacement restores the original body byte-for-byte. The complete diff is in `pr-body.diff`.

## Prior corrections preserved exactly

(a) Zero statement weakening; all three current sorry placeholders; zero proved theorem content; future proof only; statement freeze only. These final lines remain byte-for-byte unchanged:

```text
    (dbl x), which excludes singleSeed. The pinned statements have zero statement weakening
    against the published targets: they retain the same quantifiers and hypotheses for the
    Rule 126 middle-column result for all n >= 0 and Mathar's full conjecture
    A267442(n) = A043545(n) for all n > 0. All three theorem bodies are currently sorry
    placeholders with zero proved theorem content. Proof is future work; this PR claims
    a statement freeze only, not a proof.
```

The second proof-status block is also unchanged:

```text
delta_vs_source: >
  NONE in statement weakening: the pinned statements retain the published targets'
  exact quantifiers and hypotheses, including Mathar's OEIS A267442 conjecture for all
  n > 0 from primary definitions and the equivalent all-n >= 0 Rule 126 middle-column
  result. All three theorem bodies are currently sorry placeholders with zero proved
  theorem content. Proof is future work; this PR claims a statement freeze only, not a proof.
```

The opening paragraph also still says: "The three theorem proofs remain `sorry`; this PR does not prove the conjecture."

(b) The final citation line remains byte-for-byte unchanged:

```text
    (arXiv:1503.01168v1, Sec. 6.1, 2015), and empirically via bivariate generating functions in
```

The only v3 mention in the final body is the required historical account that the prior v3 citation was refuted; the actual citation remains v1, section 6.1, 2015. No present-tense proof claim about the three pinned theorems was introduced.

## Head, draft status, and file integrity

- Head before and after: `3fc2503c69dba90dcf438be5c5334079c9c41266` — unchanged and equal to the required commit.
- Branch before and after: `rule129-pin-freeze` — unchanged.
- PR remains OPEN and draft (`isDraft: true`).
- No Lean source, other repository source, or `PIN.md` file was edited. The identical head commit identifies the same repository tree. This workdir is not a repository checkout and contains no Lean source or `PIN.md`; local writes were only the body snapshots, PR responses, diff, edit receipt, and this report.
- No branch or commit changes, merge, ready marking, review submission, comment, new PR, install, or removal was performed.
- Technical freeze checks listed in the history are attributed to the prior crossed re-review; this body-only lane did not rerun them or conduct a fresh crossed review.

The freeze gate remains **OPEN pending a fresh PASS re-review**. Both recorded crossed reviews returned **FAIL**; this body fix does not satisfy the gate.
