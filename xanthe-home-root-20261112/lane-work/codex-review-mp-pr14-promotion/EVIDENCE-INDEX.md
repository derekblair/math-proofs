# Recorded evidence command index

All paths below are relative to this review workdir. The linked JSON records contain complete outputs, argv, cwd, UTC times, exit statuses, and output hashes.

The recorder invokes each command from `repo/`. An exit status of 127 in the four root tool-launch attempts represents an OSError before process launch, not a Lean result.

One broad paper search produced non-UTF8 bytes. Its JSON stdout is a replacement-decoded display; `evidence/src_paper_search.stdout.raw` preserves the raw bytes. The exact read-only command was repeated, raw lines reordered to their recorded display order (rg search order varied), and the reconstructed bytes matched the originally recorded SHA256. See `root_search_raw_recovery_ordered.json` and `recover_search_bytes.py`; the first recovery attempt is preserved as failed. All output hashes validate against UTF-8 text or that verified raw sidecar.

The exploratory `root_repo_pins` command exited 2 because a searched `scripts/` directory does not exist. Dedicated successful pin reads supersede that search. `root_lean_source` also records that incidental directory-search stderr; no proof conclusion relies on the missing directory.

Clone/checkout/head verification is in [setup.log](setup.log), with all three commands exit 0.

## gh_action_build_script

Record: [evidence/gh_action_build_script.json](evidence/gh_action_build_script.json). Exit: **0**. UTC: `2026-10-29T03:35:27.626633+00:00`.

```bash
gh api 'repos/leanprover/lean-action/contents/scripts/lake_build.sh?ref=24581d74d674803a25a81b10b059c5c0cdd344c6' --jq '.content|@base64d'
```

Stdout SHA256: `8fb46eddce41e784cb519922f0a5fdc45d64c7b47d95bc734070e1d87ee7a804`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_artifacts14_pr

Record: [evidence/gh_artifacts14_pr.json](evidence/gh_artifacts14_pr.json). Exit: **0**. UTC: `2026-10-29T03:34:14.521098+00:00`.

```bash
gh api repos/derekblair/math-proofs/actions/runs/40431659272/artifacts
```

Stdout SHA256: `244563f989470892c537c9a4622920af0d228ee4528f7d00c64a06d6cd95856c`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_artifacts14_push

Record: [evidence/gh_artifacts14_push.json](evidence/gh_artifacts14_push.json). Exit: **0**. UTC: `2026-10-29T03:34:14.523977+00:00`.

```bash
gh api repos/derekblair/math-proofs/actions/runs/40431654876/artifacts
```

Stdout SHA256: `244563f989470892c537c9a4622920af0d228ee4528f7d00c64a06d6cd95856c`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_artifacts15_pr

Record: [evidence/gh_artifacts15_pr.json](evidence/gh_artifacts15_pr.json). Exit: **0**. UTC: `2026-10-29T03:34:14.519732+00:00`.

```bash
gh api repos/derekblair/math-proofs/actions/runs/40426098547/artifacts
```

Stdout SHA256: `244563f989470892c537c9a4622920af0d228ee4528f7d00c64a06d6cd95856c`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_artifacts15_push

Record: [evidence/gh_artifacts15_push.json](evidence/gh_artifacts15_push.json). Exit: **0**. UTC: `2026-10-29T03:34:14.502398+00:00`.

```bash
gh api repos/derekblair/math-proofs/actions/runs/40426034024/artifacts
```

Stdout SHA256: `244563f989470892c537c9a4622920af0d228ee4528f7d00c64a06d6cd95856c`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_ci_summary

Record: [evidence/gh_ci_summary.json](evidence/gh_ci_summary.json). Exit: **0**. UTC: `2026-10-29T03:35:28.413564+00:00`.

```bash
python3 ../github-ci-summary.py
```

Stdout SHA256: `a00122567e6208c473e312991ff43a29515b16794e0193e9ef3e0a3263cd0c80`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_docs_provenance

Record: [evidence/gh_docs_provenance.json](evidence/gh_docs_provenance.json). Exit: **0**. UTC: `2026-10-29T03:35:35.224181+00:00`.

```bash
rg -n -C 4 'coordinator|CI runs|local repaired|17,966|independent|New-head|2026-10-27|6431013776|6429391792|6405779931' CONTENTS.md FORMALIZATION_CATALOGUE.md
```

Stdout SHA256: `7415fc98d71ebb741be2eb967d9e1ab8ae537e096c10a14d1e8d9997c2ffb965`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_extracted

Record: [evidence/gh_extracted.json](evidence/gh_extracted.json). Exit: **0**. UTC: `2026-10-29T03:34:35.745360+00:00`.

```bash
python3 ../github-extract.py
```

Stdout SHA256: `e1183ce4da85fd2a33ad7b25128358eb547928d442ce5da382512dfdf4b3b54d`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_head_checks

Record: [evidence/gh_head_checks.json](evidence/gh_head_checks.json). Exit: **0**. UTC: `2026-10-29T03:33:55.165193+00:00`.

```bash
gh api --paginate 'repos/derekblair/math-proofs/commits/344e3352e2f1106846e1ec3cbef0b04bff99e187/check-runs?per_page=100'
```

Stdout SHA256: `59afa10f8fc717c86b465384b466bf4cb0d9dc172fc639033dee507cbaca545f`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_head_runs

Record: [evidence/gh_head_runs.json](evidence/gh_head_runs.json). Exit: **0**. UTC: `2026-10-29T03:33:55.161550+00:00`.

```bash
gh api --paginate 'repos/derekblair/math-proofs/actions/runs?head_sha=344e3352e2f1106846e1ec3cbef0b04bff99e187&per_page=100'
```

Stdout SHA256: `1d5e0517265e8eab9944ee2a54ead0eaa134f55b455840bd6b2c949f877196f1`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_head_status

Record: [evidence/gh_head_status.json](evidence/gh_head_status.json). Exit: **0**. UTC: `2026-10-29T03:33:55.167623+00:00`.

```bash
gh api repos/derekblair/math-proofs/commits/344e3352e2f1106846e1ec3cbef0b04bff99e187/status
```

Stdout SHA256: `4fd659a577ff9affa0be9741ed98c8571b602a01c04f7dd2436dea9eceb10c09`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_headtrees

Record: [evidence/gh_headtrees.json](evidence/gh_headtrees.json). Exit: **0**. UTC: `2026-10-29T03:35:03.079393+00:00`.

```bash
git show -s '--format=commit=%H tree=%T parents=%P' cbf4c3d4b3ed545daf22b1e00a28a68b48e8867a 344e3352e2f1106846e1ec3cbef0b04bff99e187
```

Stdout SHA256: `ed5107177c1ac67bd0c35089a73516728e7d5ba6461a9579de2de4bcd305ba85`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_issue10

Record: [evidence/gh_issue10.json](evidence/gh_issue10.json). Exit: **0**. UTC: `2026-10-29T03:34:14.502403+00:00`.

```bash
gh issue view 10 --json number,title,body,url,state
```

Stdout SHA256: `2bab3df1ddeec0ac65d76f7c9ea63290727bafccf2c18dddc710ab104c236b25`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_issue10_comments

Record: [evidence/gh_issue10_comments.json](evidence/gh_issue10_comments.json). Exit: **0**. UTC: `2026-10-29T03:33:15.299572+00:00`.

```bash
gh api --paginate repos/derekblair/math-proofs/issues/10/comments
```

Stdout SHA256: `44cbc0bc74b4facdf3d3e0c7bc197f91cbacfa134d658cf3286ea5a28e92d26b`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_log40426034024

Record: [evidence/gh_log40426034024.json](evidence/gh_log40426034024.json). Exit: **0**. UTC: `2026-10-29T03:33:55.166974+00:00`.

```bash
gh run view 40426034024 --log
```

Stdout SHA256: `66c58712015d0c05bf8e8c941fce74922e0955c427df77fdae378028790d8a7f`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_log40426098547

Record: [evidence/gh_log40426098547.json](evidence/gh_log40426098547.json). Exit: **0**. UTC: `2026-10-29T03:33:55.161996+00:00`.

```bash
gh run view 40426098547 --log
```

Stdout SHA256: `6264a474d3685d184ab1dd57390731463b42f13662d96ffee92f4bac7f75820a`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_log40431654876

Record: [evidence/gh_log40431654876.json](evidence/gh_log40431654876.json). Exit: **0**. UTC: `2026-10-29T03:34:14.495329+00:00`.

```bash
gh run view 40431654876 --log
```

Stdout SHA256: `87b7d6e694fba57a25b8108fd4acc4bbd2f6b53d44d04fb0b42aa10e171e39c7`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_log40431659272

Record: [evidence/gh_log40431659272.json](evidence/gh_log40431659272.json). Exit: **0**. UTC: `2026-10-29T03:34:14.505520+00:00`.

```bash
gh run view 40431659272 --log
```

Stdout SHA256: `4be9c5a18b7ac02927e52110c55e0e81404998427e038a261195452ab11331eb`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_log_focus

Record: [evidence/gh_log_focus.json](evidence/gh_log_focus.json). Exit: **0**. UTC: `2026-10-29T03:34:48.494250+00:00`.

```bash
rg -n -e 'Run.*lake' -e 'lake.*build' -e 'Build completed successfully' -e leanchecker -e axiom-audit -e admission_criterion -e a0_constancy -e u_eq_Aqe_div_f -e excess_prime_dvd_u -e M_const -e split_layered_repaired ../evidence/ci-40426034024.log ../evidence/ci-40426098547.log ../evidence/ci-40431654876.log ../evidence/ci-40431659272.log
```

Stdout SHA256: `3374caa9a3b0513a7076d85775a26d40284743e920e0f1dfd0abfcdbc958b568`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_no_raw_mac_artifacts

Record: [evidence/gh_no_raw_mac_artifacts.json](evidence/gh_no_raw_mac_artifacts.json). Exit: **0**. UTC: `2026-10-29T03:35:35.295274+00:00`.

```bash
git grep -n -E 'BUILD-REPAIR-APPLIED-REPORT|56-final-applied-repair-checkpoint|6405779931|6429391792' HEAD
```

Stdout SHA256: `e00489311e5cd5c7a6696023627efe230afd613ff150685021230fa82ca3fce4`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_pr14

Record: [evidence/gh_pr14.json](evidence/gh_pr14.json). Exit: **0**. UTC: `2026-10-29T03:33:29.257617+00:00`.

```bash
gh pr view 14 --json number,title,body,state,isDraft,headRefOid,baseRefOid,mergeCommit,mergedAt,url,reviews,comments,statusCheckRollup
```

Stdout SHA256: `eb4f8c528ede3f5e72cfe18a836f2f6dd1dd2024ec1fe72aa17b41b5c0c66a97`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_pr14_reviews

Record: [evidence/gh_pr14_reviews.json](evidence/gh_pr14_reviews.json). Exit: **0**. UTC: `2026-10-29T03:34:14.499554+00:00`.

```bash
gh api --paginate 'repos/derekblair/math-proofs/pulls/14/reviews?per_page=100'
```

Stdout SHA256: `4f53cda18c2baa0c0354bb5f9a3ecbe5ed12ab4d8e11ba873c2f11161202b945`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_pr14_timeline

Record: [evidence/gh_pr14_timeline.json](evidence/gh_pr14_timeline.json). Exit: **0**. UTC: `2026-10-29T03:33:55.171921+00:00`.

```bash
gh api --paginate 'repos/derekblair/math-proofs/issues/14/timeline?per_page=100'
```

Stdout SHA256: `f9f9e7096f2dbf7686da932f87ef87b4f1426100cb5b2edd8a7b69a0818f9284`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_pr15

Record: [evidence/gh_pr15.json](evidence/gh_pr15.json). Exit: **0**. UTC: `2026-10-29T03:33:29.257675+00:00`.

```bash
gh pr view 15 --json number,title,body,state,isDraft,headRefOid,baseRefOid,mergeCommit,mergedAt,url,reviews,comments,statusCheckRollup
```

Stdout SHA256: `3aceeccda26b4630e77c889f2c634a29d99a123d59298a0091816e730ff45424`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_pr15_reviews

Record: [evidence/gh_pr15_reviews.json](evidence/gh_pr15_reviews.json). Exit: **0**. UTC: `2026-10-29T03:34:14.500613+00:00`.

```bash
gh api --paginate 'repos/derekblair/math-proofs/pulls/15/reviews?per_page=100'
```

Stdout SHA256: `4f53cda18c2baa0c0354bb5f9a3ecbe5ed12ab4d8e11ba873c2f11161202b945`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_repo_artifact_search

Record: [evidence/gh_repo_artifact_search.json](evidence/gh_repo_artifact_search.json). Exit: **0**. UTC: `2026-10-29T03:34:48.570598+00:00`.

```bash
git ls-tree -r --name-only HEAD
```

Stdout SHA256: `790040a861719bec41e547ccef72506c101054388669ebcb4b78513c89eebb1e`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_run40426034024

Record: [evidence/gh_run40426034024.json](evidence/gh_run40426034024.json). Exit: **0**. UTC: `2026-10-29T03:33:29.257717+00:00`.

```bash
gh run view 40426034024 --json databaseId,name,headSha,event,status,conclusion,createdAt,updatedAt,url,jobs
```

Stdout SHA256: `7e420022576b3aded3bcdffe8bb5d08cc5f00d79a0ab445e6ff518db65521a41`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_run40426098547

Record: [evidence/gh_run40426098547.json](evidence/gh_run40426098547.json). Exit: **0**. UTC: `2026-10-29T03:33:29.257714+00:00`.

```bash
gh run view 40426098547 --json databaseId,name,headSha,event,status,conclusion,createdAt,updatedAt,url,jobs
```

Stdout SHA256: `d8383d47d7af86b83503c1ee4a3f941ff40f1581337859436ff13795130fa6ea`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_run40431654876

Record: [evidence/gh_run40431654876.json](evidence/gh_run40431654876.json). Exit: **0**. UTC: `2026-10-29T03:35:03.077708+00:00`.

```bash
gh run view 40431654876 --json databaseId,name,headSha,event,status,conclusion,createdAt,updatedAt,url,jobs
```

Stdout SHA256: `e2399c7ac56917183b77ccf6ca3ee7af7266dcfeae8246650d75ea0faf193d07`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_run40431659272

Record: [evidence/gh_run40431659272.json](evidence/gh_run40431659272.json). Exit: **0**. UTC: `2026-10-29T03:35:03.086722+00:00`.

```bash
gh run view 40431659272 --json databaseId,name,headSha,event,status,conclusion,createdAt,updatedAt,url,jobs
```

Stdout SHA256: `4fb23a5e3592e00792931b050d0afddd5d7e8b546016cef53059b98cf75d582a`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_synthetic14

Record: [evidence/gh_synthetic14.json](evidence/gh_synthetic14.json). Exit: **0**. UTC: `2026-10-29T03:35:03.078052+00:00`.

```bash
gh api repos/derekblair/math-proofs/git/commits/d3ea0c2d9604c9e15e7b81f5dbf0084c97663463 --jq '{sha,tree,parents}'
```

Stdout SHA256: `9c36a486b3be0d050a0421ed87fb2ef9751ed1e87776d989bfc238e8139c0271`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## gh_synthetic15

Record: [evidence/gh_synthetic15.json](evidence/gh_synthetic15.json). Exit: **0**. UTC: `2026-10-29T03:35:03.083673+00:00`.

```bash
gh api repos/derekblair/math-proofs/git/commits/d8cd10ab8687b8e8fc454f4072bef5f0b466e4d7 --jq '{sha,tree,parents}'
```

Stdout SHA256: `7692081fe74c18581035d3303fd11ec25eb0d04cca5d7f37e98dbbfe7dffc1d9`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## root_audit_attempt

Record: [evidence/root_audit_attempt.json](evidence/root_audit_attempt.json). Exit: **127**. UTC: `2026-10-29T03:34:00.741905+00:00`.

```bash
lake env lean ../ss004-audit.lean
```

Stdout SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

Stderr SHA256: `9f2e3a1c5afdb63fc927c4cbc455b37717ed73ca4b36324aa1902f6cf305e59c`.

## root_build_attempt

Record: [evidence/root_build_attempt.json](evidence/root_build_attempt.json). Exit: **127**. UTC: `2026-10-29T03:34:00.741234+00:00`.

```bash
lake build
```

Stdout SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

Stderr SHA256: `9f2e3a1c5afdb63fc927c4cbc455b37717ed73ca4b36324aa1902f6cf305e59c`.

## root_committed_evidence_search

Record: [evidence/root_committed_evidence_search.json](evidence/root_committed_evidence_search.json). Exit: **0**. UTC: `2026-10-29T03:34:35.198101+00:00`.

```bash
git grep -n -i -e BUILD-REPAIR-APPLIED-REPORT -e 56-final-applied-repair-checkpoint -e 6405779931 -e '#print axioms ESSubfamilyExtended' -e 'depends on axioms' HEAD -- .
```

Stdout SHA256: `e00489311e5cd5c7a6696023627efe230afd613ff150685021230fa82ca3fce4`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## root_compiler_attempt

Record: [evidence/root_compiler_attempt.json](evidence/root_compiler_attempt.json). Exit: **127**. UTC: `2026-10-29T03:34:00.738527+00:00`.

```bash
lean --version
```

Stdout SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

Stderr SHA256: `3f32016c6ac09a6e8637b770037ce66e914760fc51ead8b631bc56b41e974d6b`.

## root_docs_numbered

Record: [evidence/root_docs_numbered.json](evidence/root_docs_numbered.json). Exit: **0**. UTC: `2026-10-29T03:34:00.746997+00:00`.

```bash
bash -c 'nl -ba FORMALIZATION_CATALOGUE.md | sed -n "1,165p"; nl -ba CONTENTS.md | sed -n "250,295p"'
```

Stdout SHA256: `48bbe7c5c34e7915bb89846899a7893bc104de466ca0717d72bee3eceb220c17`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## root_final_head

Record: [evidence/root_final_head.json](evidence/root_final_head.json). Exit: **0**. UTC: `2026-10-29T03:38:16.176996+00:00`.

```bash
git rev-parse HEAD
```

Stdout SHA256: `78521d8f85b26d5e756f47cfab635f673879474de97ca6cd0d9ab3865ea34f09`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## root_final_repo_state

Record: [evidence/root_final_repo_state.json](evidence/root_final_repo_state.json). Exit: **0**. UTC: `2026-10-29T03:35:43.655908+00:00`.

```bash
git status --porcelain=v1
```

Stdout SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## root_initial_scope

Record: [evidence/root_initial_scope.json](evidence/root_initial_scope.json). Exit: **0**. UTC: `2026-10-29T03:32:49.089851+00:00`.

```bash
git diff --stat 0b17820a79f969c883b363de670402512b47341d HEAD
```

Stdout SHA256: `d6950fc99882d131f0c582bbe96b817fa28f50b405845b30164f0e9dd7a11dee`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## root_kernel_attempt

Record: [evidence/root_kernel_attempt.json](evidence/root_kernel_attempt.json). Exit: **127**. UTC: `2026-10-29T03:34:00.736810+00:00`.

```bash
leanchecker --verbose Mathproofs.ESSubfamilyExtended
```

Stdout SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

Stderr SHA256: `9e1fa47f3f5e3f667510e33ca5c2ab5ccbecf2ace43adf606ac1dbedd88cfca3`.

## root_lean_source

Record: [evidence/root_lean_source.json](evidence/root_lean_source.json). Exit: **0**. UTC: `2026-10-29T03:33:18.457312+00:00`.

```bash
bash -c 'nl -ba Mathproofs/ESSubfamilyExtended.lean; rg --files Mathproofs .github scripts; git show c9d3c0ebb6474c5b134b2c85cae36ff84cd2af43:lean-toolchain; git show c9d3c0ebb6474c5b134b2c85cae36ff84cd2af43:lake-manifest.json'
```

Stdout SHA256: `385fd57f6eacd1f14d85d504e859e0e56c923bdfeb27bea143a9c350b22ace07`.

Stderr SHA256: `2f2ea09947d0173cbd8635efb321cf4a1157d3579b87a114172f84f759de7633`.

## root_local_tooling

Record: [evidence/root_local_tooling.json](evidence/root_local_tooling.json). Exit: **0**. UTC: `2026-10-29T03:33:18.456505+00:00`.

```bash
bash -c 'for tool in elan lean lake leanchecker; do command -v "$tool" || true; done; if command -v elan >/dev/null; then elan toolchain list; fi; for dir in /root/.elan/toolchains /root/.cache/mathlib /root/.cache/lean; do if [ -d "$dir" ]; then ls -ld "$dir" "$dir"/*; fi; done; if [ -d .lake ]; then ls -la .lake; fi'
```

Stdout SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## root_manifest_original

Record: [evidence/root_manifest_original.json](evidence/root_manifest_original.json). Exit: **0**. UTC: `2026-10-29T03:34:35.198202+00:00`.

```bash
git show c9d3c0ebb6474c5b134b2c85cae36ff84cd2af43:lake-manifest.json
```

Stdout SHA256: `a85c96a1e04acc58159b23da5706be186121ebf647b3075fa72c685300435e6e`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## root_original_theorems

Record: [evidence/root_original_theorems.json](evidence/root_original_theorems.json). Exit: **0**. UTC: `2026-10-29T03:34:00.747938+00:00`.

```bash
git grep -n -E '^theorem (admission_criterion|a0_constancy|u_eq_Aqe_div_f|excess_prime_dvd_u|M_const|split_layered_repaired)( |$)' c9d3c0ebb6474c5b134b2c85cae36ff84cd2af43 -- Mathproofs/ESSubfamilyExtended.lean
```

Stdout SHA256: `4ac9145cd009f96dec5bbccc57cfa424477546c611b554b05eaa1ca5f466a125`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## root_pins_original

Record: [evidence/root_pins_original.json](evidence/root_pins_original.json). Exit: **0**. UTC: `2026-10-29T03:34:35.198247+00:00`.

```bash
git show c9d3c0ebb6474c5b134b2c85cae36ff84cd2af43:lean-toolchain
```

Stdout SHA256: `d5edba4e4b8faad9c1baeadb265716d20d03be4d1a2647dc5e35b0c0325bea7b`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## root_pins_unchanged

Record: [evidence/root_pins_unchanged.json](evidence/root_pins_unchanged.json). Exit: **0**. UTC: `2026-10-29T03:34:35.198647+00:00`.

```bash
git diff c9d3c0ebb6474c5b134b2c85cae36ff84cd2af43 HEAD -- lean-toolchain lakefile.toml lake-manifest.json
```

Stdout SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## root_repo_pins

Record: [evidence/root_repo_pins.json](evidence/root_repo_pins.json). Exit: **2**. UTC: `2026-10-29T03:33:18.458152+00:00`.

```bash
bash -c 'cat lean-toolchain lakefile.toml lake-manifest.json; git status --short; rg -n "leanchecker|print axioms|SS-004|c9d3c0e|d13f23" .github scripts research FORMALIZATION_CATALOGUE.md CONTENTS.md'
```

Stdout SHA256: `dfead309bd35ddc342f3d5e46bba745b1bf9ea7df9ea24ec149bbd583b02497a`.

Stderr SHA256: `2f2ea09947d0173cbd8635efb321cf4a1157d3579b87a114172f84f759de7633`.

## root_search_raw_recovery

Record: [evidence/root_search_raw_recovery.json](evidence/root_search_raw_recovery.json). Exit: **1**. UTC: `2026-10-29T03:39:37.712659+00:00`.

```bash
python3 ../recover_search_bytes.py
```

Stdout SHA256: `181ff3da557f2d4790e6ff683c22848323a5bd04b14315632b032952ea9c11f0`.

Stderr SHA256: `b90443140a79b3de885f9456b2c9b326b120c038b162c089b94c258fc9c40569`.

## root_search_raw_recovery_ordered

Record: [evidence/root_search_raw_recovery_ordered.json](evidence/root_search_raw_recovery_ordered.json). Exit: **0**. UTC: `2026-10-29T03:40:02.737640+00:00`.

```bash
python3 ../recover_search_bytes.py
```

Stdout SHA256: `14e205db3bfcf270e7eb8bd8bb3548c37593f2340478e0da1dcde7884047887c`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## root_tool_locations

Record: [evidence/root_tool_locations.json](evidence/root_tool_locations.json). Exit: **0**. UTC: `2026-10-29T03:33:47.441666+00:00`.

```bash
bash -c 'for tool in lean lake elan leanchecker; do type -a "$tool"; whereis "$tool"; done; for dir in /root/.elan /opt/lean /opt/lean4 /usr/local/lean /usr/local/lib/lean /usr/lib/lean .lake; do if [ -e "$dir" ]; then ls -ld "$dir"; else printf "Absent: %s\n" "$dir"; fi; done'
```

Stdout SHA256: `6f74dcf20c982ad4edf9946bdbdcdb957bf1d9ad90bee669f9d5b6cc15e6d706`.

Stderr SHA256: `6b87a093a65cdcf2e6ff37ee574cbaa9cd47b43fa0f7aa22bef05e95fac91ed5`.

## root_workflow

Record: [evidence/root_workflow.json](evidence/root_workflow.json). Exit: **0**. UTC: `2026-10-29T03:33:47.441945+00:00`.

```bash
cat .github/workflows/lean_action_ci.yml
```

Stdout SHA256: `ee2346831f3d27d3c532e86b153c306b28d019f5b4cd9f0b863eb0ba57799fc6`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## src_branch_ancestors

Record: [evidence/src_branch_ancestors.json](evidence/src_branch_ancestors.json). Exit: **0**. UTC: `2026-10-29T03:33:51.763061+00:00`.

```bash
python3 -c 'import subprocess; refs=["f90871b2fa73d82bb57e0804703a4b2e96b0a2a4", "0b17820a79f969c883b363de670402512b47341d"]; [(print("COMMAND: git merge-base --is-ancestor",ref,"HEAD"),print("EXIT:",subprocess.run(["git","merge-base","--is-ancestor",ref,"HEAD"]).returncode)) for ref in refs]'
```

Stdout SHA256: `10b3c87b6b64d719a6c71435ac4aeaeaf28fd333df27c043e52a73a4cf028652`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## src_definitions

Record: [evidence/src_definitions.json](evidence/src_definitions.json). Exit: **0**. UTC: `2026-10-29T03:34:04.844185+00:00`.

```bash
rg -n -C 8 'def AdmCond|theorem adm_val_criterion_iff|^\| Result|^\| Theorem|hypoth|axiom' Mathproofs/ESSubfamilyExtended.lean FORMALIZATION_CATALOGUE.md
```

Stdout SHA256: `c9a0404d591140844887965a9b05071aee4b1d5f2d911b9b246945412875ca93`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## src_diff

Record: [evidence/src_diff.json](evidence/src_diff.json). Exit: **0**. UTC: `2026-10-29T03:33:05.694723+00:00`.

```bash
git diff --no-ext-diff --unified=10 0b17820a79f969c883b363de670402512b47341d HEAD
```

Stdout SHA256: `b31f86d56af4de302ccaa6a0a23c9a31bc000a4032e55055a2c692fa6e05dd31`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## src_doc_lines

Record: [evidence/src_doc_lines.json](evidence/src_doc_lines.json). Exit: **0**. UTC: `2026-10-29T03:33:51.763536+00:00`.

```bash
python3 -c 'from pathlib import Path; specs={"CONTENTS.md":[(250,270)],"FORMALIZATION_CATALOGUE.md":[(45,53),(110,148)]}; print("\n".join(f"{name}:{i}: {lines[i-1]}" for name,spans in specs.items() for lines in [Path(name).read_text().splitlines()] for lo,hi in spans for i in range(lo,min(hi,len(lines))+1)))'
```

Stdout SHA256: `dd5f35f0907ff96e9fe5c15ed4111194a5fa8c9c3f748a83e2985e414f948ad1`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## src_hashes_screen

Record: [evidence/src_hashes_screen.json](evidence/src_hashes_screen.json). Exit: **0**. UTC: `2026-10-29T03:33:36.613072+00:00`.

```bash
python3 ../source_checks.py
```

Stdout SHA256: `3183e9bcb86ba15d5010c79ee7b6bb82f8f495b9e95cf893d995a8967305bc8a`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## src_labels

Record: [evidence/src_labels.json](evidence/src_labels.json). Exit: **0**. UTC: `2026-10-29T03:33:12.071419+00:00`.

```bash
rg -n -C 3 'admission_criterion|a0_constancy|u_eq_Aqe_div_f|excess_prime_dvd_u|M_const|split_layered_repaired|PROVED\*|SS-004' CONTENTS.md FORMALIZATION_CATALOGUE.md Mathproofs/ESSubfamilyExtended.lean
```

Stdout SHA256: `09845ba634b2fd5b6f7942840fea144bd538b33c8bb2abeca5c6c357b4890796`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## src_lean_diff

Record: [evidence/src_lean_diff.json](evidence/src_lean_diff.json). Exit: **0**. UTC: `2026-10-29T03:33:51.763147+00:00`.

```bash
git diff --no-ext-diff --name-only 0b17820a79f969c883b363de670402512b47341d HEAD -- '*.lean' lean-toolchain lakefile.toml lake-manifest.json
```

Stdout SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## src_line_sections

Record: [evidence/src_line_sections.json](evidence/src_line_sections.json). Exit: **0**. UTC: `2026-10-29T03:33:51.762910+00:00`.

```bash
python3 -c 'from pathlib import Path; p=Path("Mathproofs/ESSubfamilyExtended.lean"); lines=p.read_text().splitlines(); spans=[(1,55),(230,275),(348,420),(434,465),(526,620),(635,738)]; print("\n".join(f"{p}:{i}: {lines[i-1]}" for lo,hi in spans for i in range(lo, min(hi,len(lines))+1)))'
```

Stdout SHA256: `26c49d726a0084d1217f695542ed7da3017872386d107ad7c1888e6b650c33a9`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## src_names

Record: [evidence/src_names.json](evidence/src_names.json). Exit: **0**. UTC: `2026-10-29T03:33:12.071388+00:00`.

```bash
git grep -n -E 'admission_criterion|a0_constancy|u_eq_Aqe_div_f|excess_prime_dvd_u|M_const|split_layered_repaired' c9d3c0ebb6474c5b134b2c85cae36ff84cd2af43 -- Mathproofs/ESSubfamilyExtended.lean
```

Stdout SHA256: `51f434695e38e504f108a4a0ed1b9c25536ffeaeee157316af4b5f314188f384`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## src_numstat

Record: [evidence/src_numstat.json](evidence/src_numstat.json). Exit: **0**. UTC: `2026-10-29T03:33:12.071920+00:00`.

```bash
git diff --no-ext-diff --numstat 0b17820a79f969c883b363de670402512b47341d HEAD
```

Stdout SHA256: `a418fd523cb36cf842a9f3ac60206c1c8435c5c99157cc1627b75b7e6e89cc83`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## src_paper_search

Record: [evidence/src_paper_search.json](evidence/src_paper_search.json). Exit: **0**. UTC: `2026-10-29T03:34:04.844362+00:00`.

```bash
rg -n 'R253|R261|R265|admission|constancy|nonempty|non-empty|split|layered|determin' papers/subfamily-ladder-ceiling-October-11-2026
```

Stdout SHA256: `ee72e6dde48421c618dcea5bd5c628679f9c5c8c514209230d6655cbf989b2ed`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## src_paper_statements

Record: [evidence/src_paper_statements.json](evidence/src_paper_statements.json). Exit: **0**. UTC: `2026-10-29T03:34:09.280785+00:00`.

```bash
python3 -c 'from pathlib import Path; p=Path("papers/subfamily-ladder-ceiling-October-11-2026/build/subfamily-ladder-ceiling-October-11-2026.tex"); lines=p.read_text().splitlines(); spans=[(279,315),(377,456),(458,476)]; print("\n".join(f"{p}:{i}: {lines[i-1]}" for lo,hi in spans for i in range(lo,hi+1)))'
```

Stdout SHA256: `1647bffb2d4c811b0acdca47c68cf972ccfc77211e8ac921dc7194840a545441`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## src_pin_manifest_search

Record: [evidence/src_pin_manifest_search.json](evidence/src_pin_manifest_search.json). Exit: **0**. UTC: `2026-10-29T03:34:04.844391+00:00`.

```bash
rg --files -g '*pin*' -g '*manifest*' -g '*265*' -g '*261*' -g '*253*' -g '*245*' -g '*subfamily*'
```

Stdout SHA256: `817396d408894e4e203b3b4bf7bc22115ae22237a33523a9980bea79d7940a3b`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## src_script_sha256

Record: [evidence/src_script_sha256.json](evidence/src_script_sha256.json). Exit: **0**. UTC: `2026-10-29T03:34:58.409686+00:00`.

```bash
sha256sum ../source_checks.py
```

Stdout SHA256: `c6205e8f9ec44c6fe59c6e546f36806233f97d100a4f79531836b0f3137ae8bb`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## src_source

Record: [evidence/src_source.json](evidence/src_source.json). Exit: **0**. UTC: `2026-10-29T03:33:12.071386+00:00`.

```bash
cat Mathproofs/ESSubfamilyExtended.lean
```

Stdout SHA256: `4640f46d407482548dddf9c254e1892d31d78da4641913fd1f6eee44a32346c9`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## src_status_ancestry

Record: [evidence/src_status_ancestry.json](evidence/src_status_ancestry.json). Exit: **0**. UTC: `2026-10-29T03:33:05.760850+00:00`.

```bash
git log -1 --format=fuller --parents HEAD
```

Stdout SHA256: `e4b99695678844644846105516bfa71027c04f9851906ceb9b7007dc942e5d58`.

Stderr SHA256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
