# BRIEF — Argon High research lane: streaming SHA-256 + HMAC-SHA-256, milestone-1 statement-pinning dossier

Lane: argon-streaming-hmac-m1-20261026 · Harness: agy (Gemini Argon High, model gemini-4-argon-high) · Machine: bossman-vm (this desk VM) · Pool: google-ai-ultra
Type: RESEARCH ONLY. No coding, no repo writes, no GitHub writes. Your only deliverable is a file you write in this directory: DOSSIER.md.

## Context — read these first, in full

1. ~/workspace/math-fleet/lanes/argon-sha256-research-20261026/DOSSIER.md — the predecessor lane's completed dossier (harvested 2026-10-26). Its verdicts: one-shot SHA-256/224 two-level spec+equivalence is REFUTED-as-open (remix7531/fips-180-4-lean proves it, standard axioms, green CI); the strongest still-open target is a clean-room Apache-2.0, zero-dependency streaming init/update/finalize SHA-256 (chunk-invariance + FIPS 180-4 equivalence) plus streaming HMAC-SHA-256 (FIPS 198-1 / RFC 2104), decomposed there into milestones M1–M6 (§3).
2. ~/workspace/math-fleet/files/pin-manifest-template.md — the programme's pin-manifest template. Your dossier prepares (does not itself constitute) the M1 pin manifest.

## Task — produce DOSSIER.md in this directory with these sections

### 1. M1 scope, frozen
State exactly what milestone M1 from the predecessor dossier covers and what it excludes. Quote the predecessor's M1 definition verbatim, then note any ambiguity you find in it that a pin manifest must resolve.

### 2. Verbatim primary-source quotes
Quote verbatim, with source (document + section): (a) the FIPS 180-4 padding and message-schedule/compression definitions M1's specification layer must mirror; (b) the FIPS 198-1 / RFC 2104 HMAC construction steps, insofar as M1's state/invariant design must anticipate them (predecessor §2's prefix-parameterized simulation invariant `Hasher.ModelsFrom`). If you cannot access a primary text, say so and mark the quote UNVERIFIED — never paraphrase and present it as a quote.

### 3. Proposed exact theorem statements (pin-manifest grade)
For M1, draft the exact Lean-facing theorem statements a future proof lane would be pinned to: names, signatures in words (state type, update/finalize, chunk-invariance: finalize after any chunk split equals the one-shot FIPS digest of the concatenation; midstate export/import soundness if M1 includes it), and for each: the strongest published form it must match or exceed, and what a vacuous or weakened version would look like (so a reviewer can spot strength loss).

### 4. Test-vector and evidence plan
NIST CAVP (or other) vector sources for streaming/chunked cases; how vectors are used WITHOUT native_decide / ofReduceBool trust (predecessor §2's decide +kernel over a Nat-word evaluator, or an alternative you argue for); the recorded-output evidence a future M1 proof lane must produce (build command + exit status + log, #print axioms output per pinned theorem, artifact hash + toolchain pin v4.34.1).

### 5. Risks, overlaps, open questions
Anything that could kill or shrink M1 (e.g. a repo the predecessor missed that already does streaming SHA-256 in Lean — sweep for this specifically and cite what you checked), licence contamination risks from GPL-3.0 fips-180-4-lean, and every question you cannot resolve, listed plainly.

## Working rules
- Research only: web reading and reasoning. Do not clone repos into programme trees, do not write code, do not open issues or PRs. Writing DOSSIER.md (and scratch notes in this directory) is the only file output.
- Claims name their evidence inline. Include a short "What this dossier does NOT show" paragraph at the end.
- Write DOSSIER.md incrementally as you go; end the file with a one-line marker: DOSSIER COMPLETE.
