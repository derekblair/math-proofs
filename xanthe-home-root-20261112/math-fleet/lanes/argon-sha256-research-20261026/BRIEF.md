# BRIEF — Argon High research lane: SHA-256 two-level formalization dossier

Lane: argon-sha256-research-20261026 · Harness: agy (Gemini Argon High, model gemini-4-argon-high) · Machine: bossman-vm (this desk VM) · Pool: google-ai-ultra
Type: RESEARCH ONLY. No coding, no repo writes, no GitHub writes. Your only deliverable is a file you write in this directory: DOSSIER.md.

## Context

The formalize-everything programme is considering a SHA-256 formalization target. A prior-art pass already exists and you MUST read it first, in full, including its ERRATUM:

  ~/workspace/formalization/research/prior-art-sha256.md

Key facts from that file (verify, do not just repeat):
- LeanSha256 (Etheorem project) is a pure-Lean, kernel-reducible SHA-256 whose correctness evidence is CAVP test-vector gates plus a handful of structural conformance lemmas — implementation-as-spec, no independently stated FIPS 180-4 specification with a proved equivalence theorem.
- The original pass concluded the two-level artifact (independent FIPS 180-4 spec + proved-equivalent implementation, standard axioms only) was OPEN in Lean.
- THE ERRATUM at the end of that file REFUTES that conclusion: a live Google/GitHub check on 2026-10-26 found remix7531/fips-180-4-lean — a literate Lean 4 FIPS 180-4 development with separate spec/, impl/ and equiv/ trees and proved sha256_correct / compress_correct theorems (standard axioms per its AxiomCheck). On that evidence the programme closed its SHA-256 ticket (#17) before any lane started.

Your job is to independently test whether that closure was right, and to map precisely what — if anything — remains open.

## Task — produce DOSSIER.md in this directory with these four sections

### 1. Prior-art sweep (test the standing claim)
Sweep proof assistants AND crypto-verification tools for SHA-256 specification/correctness work: Lean 4 (LeanSha256, remix7531/fips-180-4-lean, sha2-fv, Freigen, LNSym, CatCrypt, anything newer), Coq (Appel/VST), F* (HACL*), Cryptol/SAW, Isabelle, others you find.
For the two decisive Lean artifacts, go to the primary source (the repositories themselves) and report:
- remix7531/fips-180-4-lean: exact theorem statements for sha256_correct / compress_correct; whether spec/ is genuinely independent of impl/ (not the same definitions renamed); sorry/axiom status as evidenced in the repo (AxiomCheck or equivalent); scope — one-shot only or streaming/init-update-final too? padding proved? SHA-224 included? Last activity / maintenance state; license.
- sha2-fv: locate the actual repository behind the crates.io listing; report theorem statements, sorry status, activity. If you cannot locate or inspect it, say so — listing-grade evidence only.
Rules: cite a source (URL + what you read there) for every factual claim. Anything you cannot verify from a primary or strong secondary source gets marked UNVERIFIED — never assert it. State a final verdict on the standing claim ("LeanSha256 is implementation-as-spec AND the two-level spec+equivalence artifact is open"): each conjunct CONFIRMED / REFUTED / UNVERIFIED, with the evidence.

### 2. Spec architecture (for whatever remains open — or the best remaining target)
Given the sweep, identify the strongest still-open SHA-256-adjacent artifact at the programme's bar (candidates to evaluate: discharging SizzLean's three *_eq_spec FFI-bridge axioms with real theorems; a streaming init/update/final API proved equivalent to the one-shot spec; HMAC-SHA-256 as a construction proved from a SHA-256 spec; SHA-224; a maintained standalone spec library others can import). For the one you judge best, give:
- the abstract spec layer (how FIPS 180-4 should be stated: words/rotations/schedule/compression as functions over BitVec 32 / vectors; padding as a proved construction),
- the executable implementation layer,
- the equivalence-proof plan (what the bridge lemmas are, where the hard steps sit),
- the test-vector source (e.g. NIST CAVP) and how vectors should be used WITHOUT native_decide trust (kernel-checkable evidence only).

### 3. Milestone decomposition
Break the chosen target into milestones sized for future single lanes (each: name, scope, deliverable, acceptance evidence at the kernel bar — full build, #print axioms output showing only propext / Classical.choice / Quot.sound, zero sorries). Order them by dependency. Note which milestones are independent and could run in parallel.

### 4. Risks and open questions
What could kill or shrink the target (e.g. fips-180-4-lean turns out to already cover the bridge/streaming too; sha2-fv's proofs are stronger than the listing suggests; maintenance/duplication politics of building on someone else's repo), and every question you could not resolve, listed plainly.

## Working rules
- Research only: web reading and reasoning. Do not clone repos into programme trees, do not write code, do not open issues or PRs. Writing DOSSIER.md (and scratch notes in this directory) is the only file output.
- Claims name their evidence inline. Include a short "What this dossier does NOT show" paragraph at the end.
- Write DOSSIER.md incrementally as you go (section by section), so partial progress is visible on disk; end the file with a one-line marker: DOSSIER COMPLETE.
