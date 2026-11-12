# BRIEF — Argon High research lane: Rule 129 / Rule 126 proof-strategy dossier

Lane: argon-rule129-proof-strategy-20261028 · Harness: agy (Gemini Argon High, model gemini-4-argon-high) · Pool: google-ai-ultra
Type: RESEARCH ONLY. No coding, no repo writes, no GitHub writes. Your only deliverable is a file you write in this directory: DOSSIER.md.

## Context — read first, verify, do not just repeat

- math-proofs PR #16 (freeze only) MERGED 2026-10-28 (merge commit 437b890a32ede43ad1dfbc6ef0839e8d9ea16a7d).
  Its single file, Mathproofs/Rule129MiddleColumn.lean, contains locked definitions and three
  `sorry` theorem placeholders. NOTHING is proved yet. The next pipeline step is a Codex proof-attempt
  lane on these pinned statements, and this dossier is its strategy input.
- Frozen pin manifest (do not edit; quote it, do not paraphrase its statements):
  ~/workspace/math-fleet/pins/a267442-eq-a043545.md
  Statement-file sha256 2bfada69046ed20429e039c895aae8eb2617663f86cf5027ec9600de64ad758e,
  commit 3fc2503c69dba90dcf438be5c5334079c9c41266 (now on master via the merge above).
- The three pinned theorems (namespace Mathproofs.Rule129MiddleColumn):
  1. rule126_middle_column_iff — Rule 126 single-ON-seed middle column at generation n >= 0 is ON
     iff n = 2 ^ m - 1 for some m : Nat.
  2. rule126_middle_column_eq_a036987 — that middle column equals OEIS A036987(n) for all n.
  3. a267442_eq_a043545 — Mathar's OEIS A267442 conjecture: a267442 n = a043545 n for all n > 0
     (a267442 n = Rule 129 middle column; a043545 n = maximal base-2 digit of n minus minimal
     base-2 digit of n, defined directly from Nat.digits 2 n; at n = 0 the two sides differ, hence n > 0).
- Locked definitions: ecaRule (Wolfram bit encoding), ecaStep (one synchronous global step on total
  configurations Int -> Bool), singleSeed (x = 0 true, all else false), ecaOrbit (iterate of ecaStep),
  a267442, a036987 (Classical if over exists m, n = 2 ^ m - 1), a043545. Zero edits to these 10
  declarations are permitted in a solution closure.
- Axiom allowlist: [propext, Classical.choice, Quot.sound] ONLY. Trust policy: native_decide,
  ofReduceBool, and custom axioms are FORBIDDEN in a solution closure; sorry is forbidden in a
  solution (the current sorries are placeholders to be replaced, not a pattern to extend).
- Strongest published form per the manifest: Mathar's conjecture is unproved as stated (computational
  check to 1,048,576 in math-proofs#5 only); the Rule 126 middle-column identity is asserted without
  proof in OEIS A071035 / A267366 (Koeppl 2022), indirectly via row-sums in Sloane arXiv:1503.01168
  §6.1 (note: the frozen PIN.md line 31 cites v3; the PR body correctly uses v1 — treat the arXiv
  version question as open and verify it yourself), and empirically via bivariate generating
  functions in Macfarlane's unpublished DAMTP note (Sec. 9 Eq. 67, 2016). Palamarchuk's
  lividgreen/lean-elementary-cellular-automata proves a doubling lemma only on even-support doubled
  states, which excludes singleSeed.
- Non-duplication: this dossier is NOT Brian's queue. Brian's open math-proofs issues are #6 (Seam B
  triage), #7 (A111495/A111499 bounds audit), #8 (Seam A screen batch 4), #10 (SS-004 verification).
  Do not re-do those; if a source overlaps them, cite the overlap and move on.
- Prior programme material you may consult (verify against primary sources before relying on it):
  ~/workspace/math-fleet/lanes/codex-rule129-paper-20261027/ (PAPER-NOTES.md, paper.tex — an
  earlier draft; its claims are NOT evidence until you verify them).

## Task — produce DOSSIER.md in this directory with these four sections

### 1. Prior-art sweep (test the standing claim)
Sweep the literature and formal libraries for proofs or proof sketches of: the Rule 126
single-seed middle-column identity; the Fredholm–Rueppel sequence characterizations; Mathar's
A267442 = A043545 conjecture; and any Rule 129 middle-column result. Cover Wolfram's
A New Kind of Science material, OEIS entries and their references, Sloane's row-sum work,
Macfarlane's generating-function note, Palamarchuk's ECA library, and anything newer.
For each source report: exact statement proved (or asserted), proof method in outline, and whether
it transfers to the pinned Lean definitions (total configurations on Int, Wolfram bit encoding,
singleSeed) or only to a neighbouring formalization. Cite a source (URL + what you read there) for
every factual claim. Anything you cannot verify from a primary or strong secondary source gets
marked UNVERIFIED — never assert it. End with a verdict on the standing claim ("the pinned
theorems are unproved in the literature and in every formal library you checked"):
CONFIRMED / REFUTED / UNVERIFIED per conjunct, with the evidence.

### 2. Proof architecture (the strategy the Codex proof lane will follow)
Propose a lemma decomposition for proving all three pinned theorems at the programme's kernel bar,
in dependency order. Address, at minimum:
- The relationship between the Rule 129 statement and the Rule 126 statements: what bridge lemma
  (if any) reduces a267442_eq_a043545 to the Rule 126 theorems, and what it costs.
- The induction structure for the middle-column identity: what invariant over generations is
  actually inductible (support bounds, the 2^m - 1 generation structure, behaviour between
  successive Mersenne generations), and where a naive induction breaks.
- The binary-expansion side: how a043545's max-minus-min digit characterization connects to the
  2^m - 1 condition, and which Mathlib lemmas about Nat.digits, Nat.testBit, and powers of two
  are the load-bearing ones (name them; check they exist in the pinned Mathlib revision's API
  surface as far as you can from documentation — mark anything unchecked UNVERIFIED).
- The infinite-line traps: background behaviour outside |x| <= n, the iterate API
  (Mathlib.Logic.Function.Iterate), and any place where a finite-window argument silently assumes
  what the total-configuration definitions do not give.
- For each proposed lemma: statement sketch, why it is true (in outline), and the hard step.
  Flag any lemma whose truth you are not sure of as CONJECTURAL, with the reason.

### 3. Milestone decomposition
Break the proof into milestones sized for future single Codex lanes (each: name, scope,
deliverable, acceptance evidence at the kernel bar — full build, #print axioms output showing
only propext / Classical.choice / Quot.sound, zero sorries). Order them by dependency. Note
which milestones are independent and could run in parallel, and which milestone (if any) should
be attempted first as a risk-retiring spike.

### 4. Risks and open questions
What could kill or shrink the strategy (e.g. the Rule 129↔126 bridge fails at the pinned
definitions; the inductible invariant is stronger than the middle column alone; a key Mathlib
lemma does not exist at the pinned revision; a literature proof you missed already covers a
theorem — in which case the pipeline's novelty bar, not just its proof bar, is affected).
List every question you could not resolve, plainly.

## Working rules
- Research only: web reading and reasoning. Do not clone repos into programme trees, do not write
  code, do not open issues or PRs. Writing DOSSIER.md (and scratch notes in this directory) is
  the only file output.
- Claims name their evidence inline. Include a short "What this dossier does NOT show" paragraph
  at the end.
- Write DOSSIER.md incrementally as you go (section by section), so partial progress is visible
  on disk; end the file with a one-line marker: DOSSIER COMPLETE.
