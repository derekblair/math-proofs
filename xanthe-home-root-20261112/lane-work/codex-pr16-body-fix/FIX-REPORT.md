# PR #16 body fix report

Recorded: 2026-10-29T04:06:37.405403+00:00
PR: https://github.com/derekblair/math-proofs/pull/16
Role: coordinator fix lane; not an independent review or proof certification.

## Head and scope confirmation

The first action fetched the live PR using:

```sh
gh pr view 16 --repo derekblair/math-proofs --json body,headRefOid,isDraft
```

Expected and observed head: `3fc2503c69dba90dcf438be5c5334079c9c41266`.
The PR was draft. The head, draft flag, and unchanged body were checked again immediately before editing. The post-edit fetch confirms the same head, branch `rule129-pin-freeze`, `isDraft: true`, and state `OPEN`.

Only the GitHub PR body was changed. The Lean source, frozen `PIN.md`, branch, and commits were not edited. No merge, ready transition, GitHub review/comment, new PR, Lean execution, or test suite occurred. Prior source-review findings in the brief were not re-certified by this lane.

Evidence: [initial response](pr-before.json), [immediate pre-edit response](pr-pre-edit.json), [post-edit response](pr-after.json), and [edit result](gh-edit-result.json).

## F1 — statement fidelity and proof status

Both offending passages now state zero statement weakening, preserving the published targets' quantifiers and hypotheses: Rule 126 for every `n >= 0`, and Mathar's full conjecture for every `n > 0` from primary definitions. Separately, both passages state that all three theorem bodies are currently `sorry` placeholders with zero proved theorem content; proof is future work, and this PR claims a statement freeze only.

### Strongest-published-form passage

Before (live body lines 108–110):

```text
    (dbl x), which excludes singleSeed. The pinned theorems prove both the Rule 126 middle-column
    theorem for all n >= 0 and Mathar's full conjecture A267442(n) = A043545(n) for all n > 0
    with zero weakening.
```

After (verified live body lines 108–113):

```text
    (dbl x), which excludes singleSeed. The pinned statements have zero statement weakening
    against the published targets: they retain the same quantifiers and hypotheses for the
    Rule 126 middle-column result for all n >= 0 and Mathar's full conjecture
    A267442(n) = A043545(n) for all n > 0. All three theorem bodies are currently sorry
    placeholders with zero proved theorem content. Proof is future work; this PR claims
    a statement freeze only, not a proof.
```

### Statement-strength delta

Before (live body lines 184–186):

```text
  NONE — proves the exact full-quantifier statement of Mathar's OEIS A267442 conjecture for all
  n > 0 from primary definitions alongside the equivalent all-n >= 0 Rule 126 middle-column
  theorem.
```

After (verified live body lines 187–191):

```text
  NONE in statement weakening: the pinned statements retain the published targets'
  exact quantifiers and hypotheses, including Mathar's OEIS A267442 conjecture for all
  n > 0 from primary definitions and the equivalent all-n >= 0 Rule 126 middle-column
  result. All three theorem bodies are currently sorry placeholders with zero proved
  theorem content. Proof is future work; this PR claims a statement freeze only, not a proof.
```

The original accurate opening disclaimer remains byte-for-byte unchanged:

> The three theorem proofs remain `sorry`; this PR does not prove the conjecture.

## F2 — arXiv version and section verification

Checked arXiv directly before editing, on 2026-10-29 UTC. The [arXiv abstract page](https://arxiv.org/abs/1503.01168) returned HTTP 200. Its complete Submission history contains exactly one version entry. Exact displayed history evidence:

```text
[v1]
Wed, 4 Mar 2015 00:22:02 UTC (180 KB)
```

The page's version-specific citation also links to [arXiv:1503.01168v1](https://arxiv.org/abs/1503.01168v1). A direct GET of [the claimed v3 abstract URL](https://arxiv.org/abs/1503.01168v3) returned HTTP 404, with that same URL after redirects.

The [v1 paper](https://arxiv.org/pdf/1503.01168v1) contains section “6.1 The 256 one-dimensional rules.” The section defines the count of ON cells after a generation from a single ON seed and includes the Rule 126 row-sum assertion (A071051). Thus the body now cites **v1**, retaining **Sec. 6.1, 2015**. This is verification of the citation and location, not certification of the pinned theorem proofs.

Saved evidence: [raw abstract HTML](arxiv-abs.html) (history at lines 167–170), [abstract response headers](arxiv-abs-headers.txt), [extracted abstract](.firecrawl/arxiv-1503.01168-abs.md) (history at lines 35–40), [v3 response headers](arxiv-v3-headers.txt), [v3 response body](arxiv-v3-response.html), and [extracted v1 paper](.firecrawl/arxiv-1503.01168v1.md) (section heading at line 837; Rule 126 at line 858).

Before (live body lines 104):

```text
    (arXiv:1503.01168v3, Sec. 6.1, 2015), and empirically via bivariate generating functions in
```

After (verified live body lines 104):

```text
    (arXiv:1503.01168v1, Sec. 6.1, 2015), and empirically via bivariate generating functions in
```

## Frozen manifest — open coordinator decision

**OPEN: manifest-version decision.** `PIN.md` line 31, as identified in the coordinator brief, still carries the old `arXiv:1503.01168v3` citation. The body is corrected to v1; the frozen pin was deliberately left untouched. `PIN.md` is not present in this workdir, so this lane does not claim a fresh direct read or byte comparison of that external file. The initial live body's embedded manifest independently contained the same old citation string.

The coordinator must decide how to version or annotate the frozen manifest's citation discrepancy. No statement changed, and this lane created no replacement manifest. The PR's recorded frozen-manifest SHA256 value remains unchanged.

Because the corrected body rendering now differs from the frozen file, three body-only provenance labels were also corrected: the hash label identifies the frozen file rather than the rendering; the handoff describes a corrected rendering rather than complete file contents; and the rendering heading explicitly says the frozen file is unchanged. Their exact before/after lines, along with F1 and F2, appear in the complete diff below.

## Post-edit body verification

Applied at 2026-10-29T04:05:45.648634+00:00 with exit 0:

```sh
gh pr edit 16 --repo derekblair/math-proofs --body-file pr-body-proposed.md
gh pr view 16 --repo derekblair/math-proofs --json body,headRefOid,isDraft,headRefName,state,url,files
```

The refetched live body equals [the proposed body](pr-body-proposed.md) exactly, and every intended replacement is present. The original opening paragraph is unchanged. No `arXiv:1503.01168v3`, `The pinned theorems prove both`, or `NONE — proves` remains in the live body.

The complete body and every proof-related occurrence were inspected. **No present-tense proof claim about any of the three pinned theorems remains anywhere in the body.** The sole remaining positive `proves` occurrence is at line 107 and attributes `LocalRule.finRule_two_dbl` to Mykola Palamarchuk; it is about a separate author's theorem and was preserved. Other proof wording records placeholders, future work, compile warnings, or the existing no-proof disclaimer.

The post-edit non-body metadata equals the pre-edit metadata, including the unchanged head and draft flag. The source file list is unchanged. The recorded validation text and statement identifiers were preserved.

Body SHA256 before: `a7cadb4b0b0d828233d91c3293562b56329d0d5aa3b8e029fea00e9a0ef6f367`.
Body SHA256 after: `f767cd45a4aa41319a27ad8219f6b2597fc223f53ab6e17275b037c04a794194`.

Fresh independent re-review remains for the coordinator to arrange through chatgpt-proton on a Lean machine, never chatgpt-gmail or chatgpt-live. This fix lane has not performed that review.

## Complete exact body diff

```diff
--- pr-body-before.md
+++ pr-body-after.md
@@ -8,7 +8,7 @@
 
 - Statement SHA256: `2bfada69046ed20429e039c895aae8eb2617663f86cf5027ec9600de64ad758e`
 - Freeze commit: `3fc2503c69dba90dcf438be5c5334079c9c41266`
-- Pin manifest SHA256 (UTF-8 file including heading/fence below): `8bc4bffc10b383bdf1ce557c37e70a2b93aafe56d627285a1a22c5f78b9d1e97`
+- Frozen pin manifest file SHA256 (unchanged file; not the corrected PR-body rendering below): `8bc4bffc10b383bdf1ce557c37e70a2b93aafe56d627285a1a22c5f78b9d1e97`
 - Branch: `rule129-pin-freeze`
 - Freeze executor: `derekblair@bakkie` (delegated coding lane `codex-rule129-freeze`, pool `chatgpt-live`)
 
@@ -67,9 +67,9 @@
 
 ## Coordinator desk handoff
 
-The populated manifest is saved at `/home/derekblair/lane-work/codex-rule129-freeze/pins/a267442-eq-a043545.md`; its complete file content appears below. The authoritative destination is `bossman-vm:~/workspace/math-fleet/pins/a267442-eq-a043545.md`, with registration in adjacent `REGISTRY.md`. Those coordinator writes remain pending: the fleet specification states that no fleet machine can SSH into the coordinator VM (§2, line 37; §6, line 382), and no coordinator filesystem connector is exposed to this lane. A precise registration entry is prepared in the lane's `REGISTRY-ENTRY.md`. No substitute bakkie desk was created and no proof lane was launched.
+The populated manifest is saved at `/home/derekblair/lane-work/codex-rule129-freeze/pins/a267442-eq-a043545.md`; a PR-body rendering with corrected proof-status wording and arXiv citation appears below. The frozen manifest file is unchanged. The authoritative destination is `bossman-vm:~/workspace/math-fleet/pins/a267442-eq-a043545.md`, with registration in adjacent `REGISTRY.md`. Those coordinator writes remain pending: the fleet specification states that no fleet machine can SSH into the coordinator VM (§2, line 37; §6, line 382), and no coordinator filesystem connector is exposed to this lane. A precise registration entry is prepared in the lane's `REGISTRY-ENTRY.md`. No substitute bakkie desk was created and no proof lane was launched.
 
-## Populated manifest (complete file)
+## Manifest rendering (PR-body corrections; frozen file unchanged)
 
 # Pin Manifest — a267442-eq-a043545
 
@@ -101,13 +101,16 @@
     conjecture (verified computationally for 1 <= n <= 1,048,576 in derekblair/math-proofs#5).
     On the equivalent Rule 126 side, C_126(n, 0) = A036987(n) is asserted without proof in
     OEIS A071035 (%Y), OEIS A267366 (Koeppl 2022), indirectly via row-sums in N. J. A. Sloane
-    (arXiv:1503.01168v3, Sec. 6.1, 2015), and empirically via bivariate generating functions in
+    (arXiv:1503.01168v1, Sec. 6.1, 2015), and empirically via bivariate generating functions in
     A. J. Macfarlane (DAMTP Cambridge unpublished note GFsForCAsOfEvenRuleNo.ps, Sec. 9 Eq. 67,
     2016); in formal libraries, Mykola Palamarchuk (lividgreen/lean-elementary-cellular-automata,
     ECA/Doubling.lean, 2026) proves LocalRule.finRule_two_dbl only on even-support doubled states
-    (dbl x), which excludes singleSeed. The pinned theorems prove both the Rule 126 middle-column
-    theorem for all n >= 0 and Mathar's full conjecture A267442(n) = A043545(n) for all n > 0
-    with zero weakening.
+    (dbl x), which excludes singleSeed. The pinned statements have zero statement weakening
+    against the published targets: they retain the same quantifiers and hypotheses for the
+    Rule 126 middle-column result for all n >= 0 and Mathar's full conjecture
+    A267442(n) = A043545(n) for all n > 0. All three theorem bodies are currently sorry
+    placeholders with zero proved theorem content. Proof is future work; this PR claims
+    a statement freeze only, not a proof.
 statement_file:
   path: Mathproofs/Rule129MiddleColumn.lean
   sha256: 2bfada69046ed20429e039c895aae8eb2617663f86cf5027ec9600de64ad758e
@@ -181,9 +184,11 @@
      frozen by this manifest; zero edits to any of these 10 declarations are permitted in a
      solution closure.
 delta_vs_source: >
-  NONE — proves the exact full-quantifier statement of Mathar's OEIS A267442 conjecture for all
-  n > 0 from primary definitions alongside the equivalent all-n >= 0 Rule 126 middle-column
-  theorem.
+  NONE in statement weakening: the pinned statements retain the published targets'
+  exact quantifiers and hypotheses, including Mathar's OEIS A267442 conjecture for all
+  n > 0 from primary definitions and the equivalent all-n >= 0 Rule 126 middle-column
+  result. All three theorem bodies are currently sorry placeholders with zero proved
+  theorem content. Proof is future work; this PR claims a statement freeze only, not a proof.
 review_route: >
   Codex review lane (OpenAI/Codex reviewer pool != Gemini/Argon author-side research pool;
   satisfies the cross-model review gate without pre-assigning a specific host machine).
```

BODY-FIXED — F1 and F2 corrected and verified in the live draft body; head unchanged; frozen PIN.md citation remains an open manifest-version decision.
