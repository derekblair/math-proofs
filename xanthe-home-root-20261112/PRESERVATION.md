# Preservation: xanthe /root/lane-work + /root/math-fleet

- Source machine: xanthe (100.105.121.30), paths /root/lane-work
  (Oct 28-29 2026) and /root/math-fleet (Oct 26-28 2026).
- Captured: 2026-11-12, home-root conformance fix.
- lane-work/: four coordinator lane workdirs — codex-pr16-body-fix and
  codex-pr16-provenance-fix (PR-body wording fixes for math-proofs PR #16,
  merged 2026-10-29; the merged PR body matches the provenance-fix output),
  codex-review-mp-pr14-promotion (hostile review evidence for math-proofs
  PR #14, still open), codex-rule129-paper (Rule 129 paper tex/pdf +
  audits).
- math-fleet/: six Argon research lane workdirs (Rule 129 audit / screen /
  proof-strategy / pinfreeze-prep, SHA-256 research, streaming-HMAC M1)
  plus files/pin-manifest-template.md. Authored outputs only.
- Excluded from this branch (public repo): the nested math-proofs
  checkout inside codex-review-mp-pr14-promotion/repo (clean,
  HEAD 344e3352 = live PR #14 head) and downloaded third-party material
  (scratch/ arXiv/OEIS/Gravner files, .firecrawl/ fetches). That material
  was moved intact on the machine to /root/projects/math/ and remains there.
- Status: preservation-only draft PR. Do not merge without review.
