# GitHub evidence findings for the promotion review

Collected 2026-10-29 03:33–03:35 UTC. Evidence gathering only: no GitHub changes, messages, reviews, or installations. Every `gh` command below completed with exit 0. Exact argv, cwd, UTC timestamps, complete stdout/stderr, exit status, and stdout SHA256 are recorded in the named `evidence/gh_*.json` files. These are newly fetched primary GitHub records, not conclusions copied from the prior reviewer.

## Blocking evidence gap: claims 3 and 5 local execution

The original six-theorem comment [6405779931](https://github.com/derekblair/math-proofs/issues/10#issuecomment-6405779931) states compiled-statement/axiom audit exit 0 and `leanchecker --verbose Mathproofs.ESSubfamilyExtended` exit 0 at c9d3c0ebb6474c5b134b2c85cae36ff84cd2af43, Lean 4.34.1/compiler5045d0056413266e57c625dcd7c365b10e377c52, Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. It names the standard axiom sets and absence of sorryAx. It does **not** contain the per-theorem `#print axioms` output, the full audit command/script, the kernel replay output, or hashes/URLs of those output files. The existence and contents of the author's assertion are CONFIRMED; its actual execution/results remain UNVERIFIED by the GitHub records alone. Root's own replay attempt determines the rest of claim 3.

The repaired local-build comment [6429391792](https://github.com/derekblair/math-proofs/issues/10#issuecomment-6429391792) states `elan run leanprover/lean4:v4.34.1 lake build` exit 0, 17,966 jobs,36.1seconds, plus rebuilt repository-artifact audit/replay exit 0. It explicitly calls this LOCAL evidence. The PR15 body adds completion times22:57:29UTC/22:58:53UTC, a census source hash and census `.olean` hash, and says the local axiom audit covered five **census** theorems. These are useful provenance claims, but no complete original Mac log or original stdout is attached. The comment names `BUILD-REPAIR-APPLIED-REPORT.md` and `56-final-applied-repair-checkpoint.json` only as files in the existing Mac job, with no exact accessible path, log SHA256 or downloadable URL. The PR bodies/comments and repository tree did not supply those files; all four relevant Actions runs have zero downloadable artifacts. This does not claim the files do not exist on the Mac; that machine was outside this workdir-only review.

Thus claim5 overall should be **UNVERIFIED** for promotion-critical original local execution/output, with the CI and attribution subclaims **CONFIRMED**. Successful downloaded CI build logs are not a substitute for the six named axiom outputs or official kernel replay because those optional steps were skipped in every run examined.

Evidence: `gh_issue10_comments.json`, `gh_issue10.json`, `gh_pr14.json`, `gh_pr15.json`, `gh_repo_artifact_search.json`, `gh_no_raw_mac_artifacts.json`, `gh_artifacts15_push.json`, `gh_artifacts15_pr.json`, `gh_artifacts14_push.json`, `gh_artifacts14_pr.json`. Readable extracts: `issue10-readable.txt` lines7–14 (original six),33–40 (local repair); `pr15-readable.txt` lines7–16.

## Claim 2 — CONFIRMED

`gh pr view 15 --json number,title,body,state,isDraft,headRefOid,baseRefOid,mergeCommit,mergedAt,url,reviews,comments,statusCheckRollup` produced:

```text
state=MERGED
headRefOid=cbf4c3d4b3ed545daf22b1e00a28a68b48e8867a
mergeCommit.oid=0b17820a79f969c883b363de670402512b47341d
mergedAt=2026-10-27T00:55:28Z
```

Recorded in `gh_pr15.json` (exit0).

## Claim 5 — CONFIRMED CI subclaims, UNVERIFIED original Mac logs

All four CI runs are included here to prevent conflating original repair CI with new-head CI. Each had one GitHub Actions job; **17,966 is the Lake build-job/target count**, not the count of GitHub jobs.

| Run | Event | API associated head | Actual checkout in log | GitHub job completed UTC | Outcome |
|---|---|---|---|---|---|
|40426034024|push|cbf4c3d4|cbf4c3d4b3ed545daf22b1e00a28a68b48e8867a|2026-10-27 00:39:14|success;17966 Lake jobs|
|40426098547|pull_request|cbf4c3d4|d8cd10ab8687b8e8fc454f4072bef5f0b466e4d7|2026-10-27 00:37:02|success;17966 Lake jobs|
|40431654876|push|344e3352|344e3352e2f1106846e1ec3cbef0b04bff99e187|2026-10-27 01:19:02|success;17966 Lake jobs|
|40431659272|pull_request|344e3352|d3ea0c2d9604c9e15e7b81f5dbf0084c97663463|2026-10-27 01:19:28|success;17966 Lake jobs|

The two pull_request checkouts are GitHub synthetic merge commits. They have exactly the same source tree as their corresponding branch heads:

```text
cbf4c3d4 and d8cd10ab tree=3a74a89f5be99dd9685f97fa2dd30b6fd99c44b8
344e3352 and d3ea0c2 tree=34aafa3fc9415e8228465151eda9fe97e182ec1a
```

Recorded proof: `gh_synthetic15.json`, `gh_synthetic14.json` (`gh api repos/derekblair/math-proofs/git/commits/<sha> --jq '{sha,tree,parents}'`); `gh_headtrees.json` (`git show -s '--format=commit=%H tree=%T parents=%P' cbf4c3d4... 344e3352...`). All exit0.

Commands retrieving run metadata were `gh run view <id> --json databaseId,name,headSha,event,status,conclusion,createdAt,updatedAt,url,jobs`; commands retrieving complete logs were `gh run view <id> --log`. All exit0. JSON records use `gh_run<id>.json` and `gh_log<id>.json`. The complete decoded logs also reside at the locations below:

| Log path | Bytes | SHA256 |
|---|---:|---|
|`evidence/ci-40426034024.log`|1302124|`66c58712015d0c05bf8e8c941fce74922e0955c427df77fdae378028790d8a7f`|
|`evidence/ci-40426098547.log`|1298975|`6264a474d3685d184ab1dd57390731463b42f13662d96ffee92f4bac7f75820a`|
|`evidence/ci-40431654876.log`|183326|`87b7d6e694fba57a25b8108fd4acc4bbd2f6b53d44d04fb0b42aa10e171e39c7`|
|`evidence/ci-40431659272.log`|183779|`4be9c5a18b7ac02927e52110c55e0e81404998427e038a261195452ab11331eb`|

The pinned action commit24581d74d674803a25a81b10b059c5c0cdd344c6 invokes `scripts/lake_build.sh` with empty BUILD_ARGS. Newly fetched script in `gh_action_build_script.json` runs `eval "lake build $BUILD_ARGS"` under `set -e`, with an EXIT trap that distinguishes failure. Every logged build action concluded `outcome=success;conclusion=success`, establishing successful process completion; the log does not separately print a numeric `$?=0` line. Every log also prints Lean4.34.1/compiler5045d0056413266e57c625dcd7c365b10e377c52.

Exact decisive log lines:

|Run|Build completed successfully|Build action success|leanchecker start / skipped outcome|axiom-audit skipped outcome|tests/lint skipped|
|---|---|---|---|---|---|
|40426034024|10763|10766|10791/10792|10796|10768/10770|
|40426098547|10769|10772|10797/10798|10802|10774/10776|
|40431654876|1701|1704|1730/1731|1735|1706/1708|
|40431659272|1713|1716|1740/1741|1745|1718/1720|

Example exact optional-step output:

```text
##[start-action display=check environment with leanchecker;id=__leanprover_lean-action.__run_5]
##[end-action id=__leanprover_lean-action.__run_5;outcome=skipped;conclusion=skipped;duration_ms=0]
##[end-action id=__leanprover_lean-action.axiom-audit;outcome=skipped;conclusion=skipped;duration_ms=0]
```

`python3 ../github-ci-summary.py` recorded as `gh_ci_summary.json` extracts these exact lines, checkout SHAs, compiler pin, full log hashes, and counts zero appearances of each of the six target theorem names in all four logs. `gh_extracted.json` contains the broader extracted record and PR prose with line numbers. Lake's displayed `Replayed Mathproofs.ESSubfamilyExtended` in cached builds is not execution of the separately skipped official leanchecker action.

Honest separation of local versus CI is **CONFIRMED**: PR14 body line13 (`pr14-readable.txt`), catalogue lines125–133, and CONTENTS lines260–267 clearly separate their origins. `gh_docs_provenance.json` preserves the exact document lines. No claim was found that skipped CI axiom/replay steps actually ran.

## Claim 7 — actual current status CONFIRMED; “none yet” premise REFUTED

`gh api --paginate 'repos/derekblair/math-proofs/actions/runs?head_sha=344e3352e2f1106846e1ec3cbef0b04bff99e187&per_page=100'` returns exactly2 runs, both success. Check-runs endpoint likewise returns exactly2 completed successful build checks. Legacy commit-status endpoint returns state`pending`,statuses`[]`,total_count0; this means no **legacy status contexts**, not absent/failed CI. Both primary run and check endpoints resolve that apparent contradiction. Records: `gh_head_runs.json`, `gh_head_checks.json`, `gh_head_status.json`.

The body literally says “New-head CI is not yet claimed successful here” (line24), not “no CI exists.” It is conservative historical wording now incomplete as a live status report. The later coordinator comment explicitly acknowledges both successful new-head runs. Do not inflate this stale wording into an honesty blocker; report actual success and skipped audit/replay.

## Claim 8 — CONFIRMED; Annex E provenance screen CLEAR

Issue10 [coordinator comment6431013776](https://github.com/derekblair/math-proofs/issues/10#issuecomment-6431013776) identifies review-mp-pr15, dominic/chatgpt-proton, PASS for the **census repair**, five census theorems and exact repair headcbf4c3d4. It explicitly says this does not close#10. PR14 body line7 and catalogue lines137–140 call it coordinator-attested external review, not a GitHub review submission or independent review of the six SS-004 results. PR15 REST reviews returned`[]` (`gh_pr15_reviews.json`), as did PR14 (`gh_pr14_reviews.json`).

Prior documentation-only PASS: PR14 [coordinator comment6431817866](https://github.com/derekblair/math-proofs/pull/14#issuecomment-6431817866), fetched in `gh_pr14.json` and independently in `gh_pr14_timeline.json`, identifies review-mp-pr14, dominic/chatgpt-proton, PASS only for the documentation delta/cited evidence. Its explicit scope limit says it does NOT promote the six, does NOT independently certify their mathematical scope or re-execute original local axiom/replay streams, does NOT close#10, and leaves the SS-004/status-promotion gate open with labels[PROVED*]. No docs/PR/prior comment examined treats either older PASS as a promotion PASS. These statements characterize review history only; neither older review substitutes for this promotion evidence.

PR14 body's heading still says independent documentation review pending, but the later dated coordinator comment supplies the completed documentation-review history and explicit remaining promotion gate. No false gate completion was found.

## Claim 6 additional provenance support

`gh api --paginate 'repos/derekblair/math-proofs/issues/14/timeline?per_page=100'` (`gh_pr14_timeline.json`) returns7 events, including committedf90871b2 and committed344e3352, and **zero head_ref_force_pushed events**. Combined with the source agent's recorded parent graph, this supports the specific preservation/no-rewrite claim. Absence of a timeline event is not a complete audit of every possible historical ref operation; phrase the finding accordingly. Derived event listing/count is in `gh_extracted.json`.

No executed command in this GitHub evidence task failed. This task supplies evidence and does not itself issue a separate review or approval.
