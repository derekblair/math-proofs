# BRIEF — argon-rule129-screen (research lane, Gemini Argon High)

You are a research lane in a mathematics programme. Research only:
no coding, no Lean proof work, no cloning or building repositories, no GitHub writes.
Read-only web/source inspection is allowed.

## Background
The predecessor lane (argon-rule167-record, DOSSIER.md in
~/workspace/math-fleet/lanes/argon-rule167-record-20261026/) closed Candidate 36
(Rule 167 middle column, A267579 = A347523 for n>=2) as already asserted and
proved via sibling record A267581. It also established, with exact V4 symmetry
tables, that Rule 167 is NOT conjugate to Rule 129, and that Mathar's Rule 129
conjecture does NOT imply the Rule 167 claim. It left the Rule 129 side open:
- A267442 (Rule 129 middle column) carries Mathar's conjecture: a(n) = A043545(n) for n > 0.
- Via complementation C(129)=126 with zero spatial shift, that conjecture reduces to
  the classical claim C_126(n,0) = A036987(n) (Fredholm-Rueppel: 1 iff n = 2^m - 1)
  for the middle column of Rule 126 from a single ON cell.

## Task — deliver DOSSIER.md in this directory
1. RECORD + PRIOR-ART QUESTION (decisive): is the Rule 126 middle-column claim
   C_126(n,0) = A036987(n) actually PROVED in the literature / in any Lean or other
   proof-assistant development, or does it remain a conjecture? Quote verbatim
   with sources every hit and near-miss: OEIS A036987, A267442, A267366 and reachable
   references; literature on Rule 126 / Fredholm-Rueppel middle columns.
2. REDUCTION CHECK: verify or refute the dossier's reduction step by step —
   C_129(n,x) = 1 - C_126(n,x) for all n>=1 from the single-ON seed, and that
   A043545(n) = 1 - A036987(n) in the relevant range — stating exact ranges/offsets.
   If the reduction is exact, Mathar's conjecture is equivalent to the Rule 126 claim;
   say so plainly. If not, give the corrected statement.
3. NOVELTY RULING: state whether a Lean proof of the Rule 126 middle-column theorem
   (hence Mathar's conjecture) would be (a) already done, (b) a known-result
   formalization, or (c) a first proof of an open conjecture — with the evidence.
4. PROOF-STRATEGY SKETCH for whichever case applies: key lemma, main obstacle
   (the predecessor dossier notes Rule 126 is genuinely nonlinear on its orbit:
   f_126(1,0,1)=1, colliding waves). Strategy only, no proof attempt.
5. A draft exact statement suitable for a future pin manifest, marked DRAFT,
   plus a "What this does NOT show" section.

End the file with the line: DOSSIER COMPLETE
Write DOSSIER.md incrementally so partial progress is visible on disk.
