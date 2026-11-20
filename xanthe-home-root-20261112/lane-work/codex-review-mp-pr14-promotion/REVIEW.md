# SS-004 status-promotion review — math-proofs PR #14

**Verdict: FAIL on promotion. All six results must remain [PROVED*].**

## Blocking findings

1. **The required independent compiled-statement/axiom audit and kernel replay remain UNVERIFIED.** This review obtained no executed `#print axioms` output for any of the six theorems and no independently replayed `leanchecker` result. `lake build`, `lake env lean ../ss004-audit.lean`, `lean --version`, and `leanchecker --verbose Mathproofs.ESSubfamilyExtended` could not launch: the executables were absent. The recorder returned 127 for each launch failure; these are not Lean proof failures. The brief explicitly makes an UNVERIFIED promotion-critical replay incompatible with PASS. See claims 3 and 5 and Annex A.
2. **The cited Mac comments do not supply the missing recorded output.** The fetched original SS-004 comment reports aggregate exit statuses and axiom sets, but contains neither the six actual compiled statements/axiom printouts nor the full replay log or an SS-004 compiled-artifact hash. The repaired-checkout comment likewise gives a narrative build/audit/replay summary and names two files in the Mac job without attaching them. Those files were not obtained in this review. Successful CI is independently confirmed, but all four relevant runs skipped optional axiom audit and kernel replay. Neither the summaries nor the CI build success fills this promotion evidence gap.

These are verification blockers, not a counterexample to the mathematics. Source identity, staged labeling, ancestry, successful CI builds, and honest separation of review scopes were verified. No blocking provenance misrepresentation was found in the inspected PR body, documents, or comments.

## Scope, independence, and evidence method

Reviewed on 2026-10-29 UTC at head `344e3352e2f1106846e1ec3cbef0b04bff99e187`, against base `0b17820a79f969c883b363de670402512b47341d`. The full clone and PR checkout matched the required head before substantive review; exact commands, outputs, and exit statuses are in `setup.log`.

This is the independent Codex / **chatgpt-gmail** review lane assigned by BRIEF.md, separate from author Brian (Louis), who worked on Derek's MacBook Air. I did not author this PR. Two supporting agents gathered source and GitHub evidence within this review; they were not separate approvals and did not review a fix authored here. No repository files were changed, no software was installed or removed, no PR was created or merged, and no message was sent to Brian, Peter, or Cleveland. The clone is clean (`evidence/root_final_repo_state.json`).

The decision concerns only `admission_criterion`, `a0_constancy`, `u_eq_Aqe_div_f`, `excess_prime_dvd_u`, `M_const`, and `split_layered_repaired` in `Mathproofs/ESSubfamilyExtended.lean`.

**The prior documentation-only PASS from `review-mp-pr14` (dominic / chatgpt-proton) does not cover promotion. The PR #15 census-repair PASS also does not substitute for promotion evidence.** I fetched the primary GitHub records anew and inspected source and CI output. Neither previous verdict was used as proof that the six checks ran successfully.

Every substantive evidence command is preserved in `evidence/*.json`, with exact argv, shell-rendered command, working directory, UTC timestamps, exit status, complete stdout/stderr, and output SHA256 hashes. [EVIDENCE-INDEX.md](/root/lane-work/codex-review-mp-pr14-promotion/EVIDENCE-INDEX.md) lists those commands and statuses; `EVIDENCE-SHA256SUMS` binds the files. Source and GitHub extraction scripts are included. Unless explicitly stated otherwise below, the cited evidence commands exited 0. A successful `gh` retrieval verifies what the retrieved record says, not the execution of an unattached Mac audit.

## Claims 1–8

### 1. Diff scope and staged status — CONFIRMED

Command: `git diff --no-ext-diff --numstat 0b17820a79f969c883b363de670402512b47341d HEAD`.

Recorded output (`evidence/src_numstat.json`):

```text
9       0       CONTENTS.md
37      0       FORMALIZATION_CATALOGUE.md
```

The full patch is recorded by `git diff --no-ext-diff --unified=10 0b17820a79f969c883b363de670402512b47341d HEAD` in `src_diff.json`. There are exactly 46 additions, no deletions, and no Lean, theorem-statement, dependency, toolchain, or workflow changes. `src_lean_diff.json` independently records the empty Lean/config diff.

Catalogue line 51 groups all six under `[PROVED*]`. Added lines 115–116 call them staged; lines 144–148 preserve the labels and expressly disclaim promotion. CONTENTS lines 260–267, including the summary's lines 265–266, preserve all six staged labels and distinguish census review from the SS-004 gate. The `[PROVED]` family heading at CONTENTS line 256 already existed in the base; line 258 distinguishes the staged extensions. It is not a status transition introduced by this patch. The PR body likewise says that labels remain staged. Recorded line evidence: `src_doc_lines.json`, `src_labels.json`, `root_docs_numbered.json`, and `gh_pr14.json`.

No certification-by-documentation finding was identified in this diff.

### 2. PR #15 merge — CONFIRMED

`gh pr view 15 --json number,title,body,state,isDraft,headRefOid,baseRefOid,mergeCommit,mergedAt,url,reviews,comments,statusCheckRollup` returned (`evidence/gh_pr15.json`):

```text
state: MERGED
headRefOid: cbf4c3d4b3ed545daf22b1e00a28a68b48e8867a
mergeCommit.oid: 0b17820a79f969c883b363de670402512b47341d
mergedAt: 2026-10-27T00:55:28Z
```

This matches the [PR #15 merge record](https://github.com/derekblair/math-proofs/pull/15) and the docs exactly.

### 3. Six SS-004 compiled checks and axioms at c9d3c0e — UNVERIFIED

**Confirmed subclaims:** the original primary-source assertion was fetched, the six source declarations exist, and the source pins match. **Unverified subclaims:** the six executed compiled-statement/axiom outputs, absence of `sorryAx`/nonstandard axioms in their compiled dependencies, and a successful independent kernel replay.

Command: `gh api --paginate 'repos/derekblair/math-proofs/issues/10/comments?per_page=100'` (`gh_issue10_comments.json`). [Brian's original comment 6405779931](https://github.com/derekblair/math-proofs/issues/10#issuecomment-6405779931), created 2026-10-26T00:50:59Z, reports the six checks and module replay exiting 0 at `c9d3c0ebb6474c5b134b2c85cae36ff84cd2af43`. It also explicitly says the original full build stopped at 17,959/17,966 targets, exit -15, and was not a full-build PASS. Its per-theorem axiom assertions are:

| Theorem | Axioms reported by Brian | Actual axiom output obtained in this review |
|---|---|---|
| `admission_criterion` | `propext`, `Classical.choice`, `Quot.sound` | None; UNVERIFIED |
| `a0_constancy` | `propext`, `Classical.choice`, `Quot.sound` | None; UNVERIFIED |
| `u_eq_Aqe_div_f` | `propext` | None; UNVERIFIED |
| `excess_prime_dvd_u` | `propext`, `Classical.choice`, `Quot.sound` | None; UNVERIFIED |
| `M_const` | `propext`, `Classical.choice`, `Quot.sound` | None; UNVERIFIED |
| `split_layered_repaired` | `propext`, `Classical.choice`, `Quot.sound` | None; UNVERIFIED |

This table labels the reported sets as assertions, not reproduced `#print axioms` output.

The exact source spot-check command was:

```bash
git grep -n -E '^theorem (admission_criterion|a0_constancy|u_eq_Aqe_div_f|excess_prime_dvd_u|M_const|split_layered_repaired)( |$)' c9d3c0ebb6474c5b134b2c85cae36ff84cd2af43 -- Mathproofs/ESSubfamilyExtended.lean
```

Its six recorded hits (`root_original_theorems.json`) are lines 351, 435, 441, 582, 611, and 687 for `admission_criterion`, `u_eq_Aqe_div_f`, `excess_prime_dvd_u`, `a0_constancy`, `M_const`, and `split_layered_repaired`, respectively. Full signatures and bodies are preserved in the source evidence.

`git show c9d3c0ebb6474c5b134b2c85cae36ff84cd2af43:lean-toolchain` returns `leanprover/lean4:v4.34.1`. The corresponding `lake-manifest.json` pins Mathlib to `d13f23b723b8a846827a245b89c10fc7d3f11612`. The source/config diff from that commit to HEAD is empty for `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` (`root_pins_original.json`, `root_manifest_original.json`, `root_pins_unchanged.json`). Compiler commit `5045d0056413266e57c625dcd7c365b10e377c52` is reported in the Mac comment and independently visible in the fetched Linux CI logs; I did not verify the Mac executable itself.

Tool discovery used `command -v`, `type -a`, `whereis`, and checks of the conventional Lean/elan installation directories; no executable or clone-local `.lake` directory was found (`root_local_tooling.json`, `root_tool_locations.json`). Direct launch attempts then recorded:

| Exact command | Recorder exit | Output/error |
|---|---:|---|
| `lake build` | 127 | No stdout; `[Errno 2] No such file or directory: 'lake'` |
| `lake env lean ../ss004-audit.lean` | 127 | No stdout; same missing `lake` error |
| `leanchecker --verbose Mathproofs.ESSubfamilyExtended` | 127 | No stdout; missing `leanchecker` error |
| `lean --version` | 127 | No stdout; missing `lean` error |

Records: `root_build_attempt.json`, `root_audit_attempt.json`, `root_kernel_attempt.json`, `root_compiler_attempt.json`. **127 is the recorder's launch-failure status; no Lean process ran or returned that code.** The supplied `ss004-audit.lean` contains all six `#check` and `#print axioms` commands, but its existence is not an audit result. Installation and remote-machine execution were outside the permitted review scope.

### 4. Byte identity — CONFIRMED

`python3 ../source_checks.py` invoked `git show <revision>:Mathproofs/ESSubfamilyExtended.lean` separately for each revision, checked command exits, computed SHA256 from the returned bytes, and compared byte strings (`evidence/src_hashes_screen.json`).

| Revision | Bytes | SHA256 |
|---|---:|---|
| `c9d3c0ebb6474c5b134b2c85cae36ff84cd2af43` | 33,832 | `4640f46d407482548dddf9c254e1892d31d78da4641913fd1f6eee44a32346c9` |
| `0b17820a79f969c883b363de670402512b47341d` | 33,832 | `4640f46d407482548dddf9c254e1892d31d78da4641913fd1f6eee44a32346c9` |
| `344e3352e2f1106846e1ec3cbef0b04bff99e187` | 33,832 | `4640f46d407482548dddf9c254e1892d31d78da4641913fd1f6eee44a32346c9` |

Recorded comparison: `BYTE_IDENTICAL_ALL_THREE: True`. This rules out source drift in the target module. It does not authenticate the unprovided historical compiled artifacts.

### 5. Mac build/audit/replay evidence and repair CI — UNVERIFIED overall

**Mac raw execution evidence remains UNVERIFIED; repair CI and separation of local/CI provenance are CONFIRMED.**

[Comment 6429391792](https://github.com/derekblair/math-proofs/issues/10#issuecomment-6429391792), fetched in `gh_issue10_comments.json`, reports:

- `elan run leanprover/lean4:v4.34.1 lake build`: exit 0, 17,966 jobs, 36.1 seconds on the repaired local checkout.
- Rebuilt artifact axiom audit and official kernel replay: exit 0; no `sorryAx` or nonstandard axioms.
- The repair was then uncommitted; the earlier six SS-004 artifacts remained intact.
- Evidence filenames `BUILD-REPAIR-APPLIED-REPORT.md` and `56-final-applied-repair-checkpoint.json` in the existing Mac job.

PR #15's body clarifies that the repaired audit concerned **five census theorems**, not a fresh six-theorem SS-004 audit. It reports a census source hash and census `.olean` hash; neither is an SS-004 compiled-artifact hash. These are fetched assertions, not raw Mac output obtained here. Searching the repository for the report names and SS-004 axiom output found only the catalogue's link to the comment (`root_committed_evidence_search.json`). The four relevant workflow artifact endpoints each return `total_count: 0` (`gh_artifacts*.json`). This does not establish that the Mac files do not exist; it establishes that this review did not obtain them from the inspected evidence sources.

The two cited repair runs were independently fetched using `gh run view <id> --json ...` and `gh run view <id> --log`; exact complete command arguments are in `gh_run40426034024.json`, `gh_run40426098547.json`, and the corresponding `gh_log*.json` records.

| Run | Event | Workflow result | Actual checkout | Build summary line | Kernel / axiom audit |
|---|---|---|---|---:|---|
| [40426034024](https://github.com/derekblair/math-proofs/actions/runs/40426034024) | push | completed / success | `cbf4c3d4b3ed545daf22b1e00a28a68b48e8867a` | 10,763 | skipped / skipped |
| [40426098547](https://github.com/derekblair/math-proofs/actions/runs/40426098547) | pull_request | completed / success | synthetic merge `d8cd10ab8687b8e8fc454f4072bef5f0b466e4d7` | 10,769 | skipped / skipped |

Both logs record `Build completed successfully (17966 jobs).` and build action `outcome=success;conclusion=success`. These are Lake build tasks, not 17,966 separate GitHub workflow jobs. GitHub's logs expose successful action outcomes rather than a separately printed numeric shell exit code; no numeric exit value has been invented here. The repair push actually built `Mathproofs.ESSubfamilyExtended` (log line 961).

The fetched action script at commit `24581d74d674803a25a81b10b059c5c0cdd344c6` invokes `eval "lake build $BUILD_ARGS"` under `set -e`; the recorded build arguments are empty, so the build command is `lake build` (`gh_action_build_script.json`, `gh_ci_summary.json`, full logs). This corroborates successful process completion without mistaking the `gh` download exit status for the build exit status.

The PR merge checkout and repair head have the same tree, `3a74a89f5be99dd9685f97fa2dd30b6fd99c44b8`, independently verified by `gh api .../git/commits/d8cd10ab...` and `git show -s --format=...` (`gh_synthetic15.json`, `gh_headtrees.json`). Thus both validate the repair tree, although only push checked out the head commit itself.

The explicit skipped leanchecker/axiom-audit outcomes are at log lines 10,792/10,796 for push and 10,798/10,802 for PR. Tests and lint were also skipped. Catalogue lines 125–133 and the PR body distinguish the local audit/replay claims from those skipped CI steps. No false attribution to CI was found.

### 6. Branch ancestry and tree — CONFIRMED

`git log -1 --format=fuller --parents HEAD` records:

```text
commit 344e3352e2f1106846e1ec3cbef0b04bff99e187 f90871b2fa73d82bb57e0804703a4b2e96b0a2a4 0b17820a79f969c883b363de670402512b47341d
```

Both `git merge-base --is-ancestor <parent> HEAD` checks exit 0 (`src_status_ancestry.json`, `src_branch_ancestors.json`). Claim 1 verifies that its tree is merged master plus only the two documents.

`gh api --paginate 'repos/derekblair/math-proofs/issues/14/timeline?per_page=100'` records seven events, including both original and merge commits, and no force-push event (`gh_pr14_timeline.json`; extracted in `gh_extracted.json`). Together with the retained original head as first parent, this confirms the claimed non-rewriting merge history in the available PR records. It is not a claim about unobservable server activity beyond those records.

### 7. New-head CI — REFUTED as to the “none yet” premise; actual success CONFIRMED

`gh api --paginate 'repos/derekblair/math-proofs/actions/runs?head_sha=344e3352e2f1106846e1ec3cbef0b04bff99e187&per_page=100'` returns **two** runs (`gh_head_runs.json`). The checks API independently returns two completed successful build checks; the legacy commit-status endpoint has zero statuses, which must not be mistaken for absent CI (`gh_head_checks.json`, `gh_head_status.json`).

| Run | Event | Result | Build check completed UTC | Actual checkout |
|---|---|---|---|---|
| [40431654876](https://github.com/derekblair/math-proofs/actions/runs/40431654876) | push | completed / success | 2026-10-27 01:19:02 | `344e3352e2f1106846e1ec3cbef0b04bff99e187` |
| [40431659272](https://github.com/derekblair/math-proofs/actions/runs/40431659272) | pull_request | completed / success | 2026-10-27 01:19:28 | synthetic merge `d3ea0c2d9604c9e15e7b81f5dbf0084c97663463` |

Both logs record the successful 17,966-task build, at lines 1,701 and 1,713. Both skip leanchecker and axiom audit (push lines 1,731/1,735; PR lines 1,741/1,745). The synthetic merge tree equals the head tree, `34aafa3fc9415e8228465151eda9fe97e182ec1a` (`gh_synthetic14.json`, `gh_headtrees.json`). These runs restore cached artifacts and contain Lake “Replayed” diagnostic entries; those entries are not official kernel replay.

The PR body's literal wording is “New-head CI is not yet claimed successful here.” It conservatively understates the now-observed build evidence; it does not literally assert that no runs exist. The existing coordinator comment already identifies the successful runs. This is a correction to the brief's premise, not a blocking honesty finding and not a substitute for the skipped audits.

### 8. Coordinator-attested census review — CONFIRMED

[Comment 6431013776 on issue #10](https://github.com/derekblair/math-proofs/issues/10#issuecomment-6431013776) reports the `review-mp-pr15` independent Codex review (dominic / chatgpt-proton), PASS, five census theorems, exact repair head `cbf4c3d4`, and the PR #15 merge. It says that #10 is not closed. This comment was independently fetched in `gh_issue10_comments.json`; its factual scope is census repair.

The PR body and catalogue lines 137–140 explicitly characterize this as **coordinator-attested external review**, not a GitHub review submission or review of the six SS-004 results. Both `gh api .../pulls/14/reviews` and `gh api .../pulls/15/reviews` return `[]` (`gh_pr14_reviews.json`, `gh_pr15_reviews.json`). The record supports the characterization of the attestation; it is not a fresh execution of that other review's checks.

## Annex A — FOUND: recorded-output gate remains unsatisfied

Exact source hashes and pins are recorded together under claims 3–4. Full CI logs, successful build outcomes, checkout identities, and skipped optional steps are attached. The local review's failed launch attempts are also attached without calling them executed proof checks. Missing are the six actual axiom printouts/compiled statements and successful independent SS-004 kernel replay. Historical Mac narrative assertions and prior PASS verdicts cannot replace them.

The full fetched CI log files and SHA256 values are:

| Full log location | SHA256 |
|---|---|
| `evidence/ci-40426034024.log` | `66c58712015d0c05bf8e8c941fce74922e0955c427df77fdae378028790d8a7f` |
| `evidence/ci-40426098547.log` | `6264a474d3685d184ab1dd57390731463b42f13662d96ffee92f4bac7f75820a` |
| `evidence/ci-40431654876.log` | `87b7d6e694fba57a25b8108fd4acc4bbd2f6b53d44d04fb0b42aa10e171e39c7` |
| `evidence/ci-40431659272.log` | `4be9c5a18b7ac02927e52110c55e0e81404998427e038a261195452ab11331eb` |

`github-extract.py` and `source_checks.py` preserve the extraction/hash procedures and their inputs. `gh_extracted.json` and `src_hashes_screen.json` record outputs. No numerical theorem recomputation is claimed. No fresh successful local build or audit log exists from this review.

## Annex B — CLEAR within the inspected statement scope

- **Hidden hypotheses in data types — CLEAR.** The signatures use natural numbers and finite sets with explicit positivity, integrality, prime-pinning, and parent-filter assumptions. `AdmCond` is an explicit conjunction at Lean lines 301–304. Admission's positive/integral inputs appear at 351–357; constancy's pinning assumptions at 582–588 and 611–617; split/layered's parent determination assumptions at 687–690. Parent determination remains a hypothesis, not a theorem established by this review.
- **Vacuous branches doing the real work — CLEAR for the repaired conditional claim.** `split_layered_repaired` requires `(P₁ ∪ P₂).Nonempty` for converses (693–695). The proof obtains an actual member at 712, splits on its membership at 713, and supplies that witness at 715 or 718. The two implications remain valid for empty sets; their validity does not prove the unrestricted biconditionals. The disjointness proof considers an arbitrary common member and both filter predicates (699–709). Arithmetic proofs explicitly exclude zero inputs.
- **Positivity asserted instead of constructed — CLEAR within the stated positive-input domain.** Input positivity is explicit. Derived gcd positivity and quotient nonzeroness are proved at 364–371 and 533–543; the quotient witness in `excess_prime_dvd_u` comes from divisibility and is proved nonzero at 448–453. The division formula uses positive `f` and cancellation at 435–438.

Shape parameters precede the claims they constrain; `a0_constancy_formula` identifies the expression `A / gcd A qe` independently of `k` (526–529), used at 589–590. No hidden input-dependent advice/oracle occurs in the six statements or their local predicate definition. Machine-per-instance asymptotics are not relevant to these statements. Evidence: `src_definitions.json`, `src_line_sections.json`, `src_paper_statements.json`. This bounded source inspection does not supply the missing compiled audit.

## Annex C — CLEAR for the adapted lexical screen; compiled axiom audit UNVERIFIED

`source_checks.py` strips nested block comments, line comments, and escaped string literals while preserving character/newline positions. It reconstructs added diff lines at their HEAD line numbers and scans whole-word tokens. `src_hashes_screen.json` records:

| File/scope | sorry | admit | sorryAx | axiom | native_decide | ofReduceBool | implemented_by | unsafe |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| CONTENTS.md additions | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 0 |
| FORMALIZATION_CATALOGUE.md additions | 0 | 0 | 1 | 3 | 0 | 0 | 0 | 0 |
| ESSubfamilyExtended.lean at c9d3c0e | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| ESSubfamilyExtended.lean at 0b17820a | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| ESSubfamilyExtended.lean at 344e3352 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

All diff hits are Markdown audit descriptions: CONTENTS 260 and catalogue 117, 122, 127, 132. None is an executable trust escape. The target module imports `Mathlib` at line 42. Claim 1 confirms the declared Lean import closure and pins are unchanged from the reviewed base. This is the brief's adapted diff screen, not a fresh lexical audit of the entire absent Mathlib checkout. **Actual axiom-audit output obtained for the evidence module at either historical revision: none.** The reported sets in claim 3 remain UNVERIFIED; lexical zero counts do not satisfy Annex A.

## Annex D — CLEAR: no mathematical or status-strength increase in this PR

The pinned statements are byte-identical. PR #14 alone leaves the six `[PROVED*]` labels unchanged. A promotion PASS would permit only these exact statements, with all their hypotheses, to move from staged to `[PROVED]`; it would not broaden their mathematical claims or authorize a merge. This FAIL leaves all six staged.

No separate theorem pin manifest was found in the clone; BRIEF.md supplies the six-name/commit pin and the published paper supplies the comparison. The paper's precise split/layered formulation (TeX lines 449–456) equals Lean's three clauses: distinct residues imply disjointness, equal residues imply equality, and both converses require nonempty union, all conditional on parent-set determination. It is weaker than the older unconditional biconditional, which the paper expressly labels false at 458–472. Promotion would not prove parent determination or restore that false statement.

The admission theorem matches the displayed positive/integral per-prime criterion (TeX 383–394; Lean 351–357). The constancy statements expose prime pinning, with admitted-divisor pinning derived by the separate local wrapper at Lean 594–608. The division formula requires positive `f` and `u*f=A*qe`; the excess-prime result requires positive/integral inputs and its valuation inequality. These hypotheses survive any eventual promotion. No rate, exponent, range, or quantifier is strengthened here. Evidence: `src_pin_manifest_search.json`, `src_paper_statements.json`, `src_line_sections.json`.

## Annex E — CLEAR: review provenance is kept separate

The [prior documentation-review coordinator comment](https://github.com/derekblair/math-proofs/pull/14#issuecomment-6431817866), fetched in `gh_pr14.json`, explicitly limits its PASS to the documentation delta and cited evidence. It says it does not promote the six, does not independently certify their mathematical scope or re-execute the original local audit/replay streams, does not close #10, and does not authorize merge. Its all-claims/Annex-CLEAR language is expressly under its documentation adaptation; it is not this promotion gate.

The census-review comment, docs, and PR body likewise distinguish the PR #15 external review from SS-004 review and from formal GitHub review submissions. Local Mac audits are not attributed to skipped CI steps. No inspected passage uses either prior PASS to settle promotion. The current CI understatement is documented under claim 7 without manufacturing an integrity violation.

**Required disposition:** preserve all six staged labels. Promotion requires the independent compiled-statement/axiom outputs and successful kernel replay bound to the verified source and pins; this review has not supplied them. No repair or publication action was taken.

VERDICT: FAIL
