# BRIEF — codex-rule129-paper (Codex, GPT-6-Astra ultra, xanthe, chatgpt-gmail pool)

You are a writing lane in Derek's math programme. Draft the preprint white
paper for the Rule 129 / Rule 126 middle-column result. This is a DRAFT for
the eventual math-proofs pull request (whose standard is: novel + interesting
result + Lean proof + preprint white paper). The Lean proof is still in
progress — the paper must be honest about that everywhere it matters.

## Inputs in this workdir
- `REPORT-consolidation.md` — the consolidated finite-evidence statement for
  the popcount series (popcount p, n ≥ 3·2^(p−1)−1 ⇒ exactly 2^(p+1) True
  cells at the lower-part submask union; sole exception the Mersenne
  n = 2^p − 1), uniform across p = 1..18, all checks recorded.
- `REPORT-threshold.md` — the threshold-sharpness tranche: T_p = 3·2^(p−1) − 1
  is the second-smallest p-bit integer, so no p-bit n sits strictly between
  the Mersenne exception and T_p; at n = T_p the union has exactly 2^p
  distinct values, no collisions, count 2^(p+1); at the Mersenne n the union
  produces 0 exactly once and count 2^(p+1) − 1.

## Task
Write `paper.tex` (LaTeX, standard article class, self-contained) with:
1. Title, author block (Derek Blair), abstract. Mark it as a preliminary
   draft in a header comment AND a footnote on page 1: "Preliminary draft —
   Lean formalization in progress; computational evidence complete, proof
   pinned and in preparation."
2. Introduction: elementary cellular automata Rule 126 / Rule 129 (complements
   under the exact complementation reduction), the middle column from a
   single seed, and the three OEIS sequences in play (A267442, A036987,
   A043545) — the headline identity is A267442 = A043545 with the middle
   column characterized via A036987.
3. The main theorem, stated exactly: for n with popcount p and
   n ≥ 3·2^(p−1) − 1, n ≠ 2^p − 1, the generation-n middle-column behaviour
   is characterized by the lower-part submask union (state it in the
   consolidation report's form), with the Mersenne exception handled.
4. The proof strategy section: complementation reduction, the closed-form
   binomial-parity (Lucas) route, the submask criterion — presented as the
   proof ROADMAP it currently is, clearly labelled as such.
5. Computational evidence section: the popcount series 1–18 and the
   threshold-sharpness result, with the exact bounds verified (analytic rows,
   converse ranges, simulation ranges per tier — take the numbers from the
   two reports, do not round or inflate them).
6. Novelty and prior art, honestly: the result's novelty case requires a
   folklore disclosure (the submask/Lucas mechanism is folklore-grade; the
   specific characterization and identity appear unpublished). Say exactly
   that; claim no more.
7. References: OEIS A267442 / A036987 / A043545, Lucas's theorem source,
   Rudin-style ECA references as appropriate (Wolfram's ANKOS for Rules
   126/129 basics).

## Gates
- Finite evidence is NOT a proof: the words "proved/proven" may only appear
  for the roadmap's individual established ingredients (Lucas etc.), never
  for the main theorem. Use "verified computationally for …" with bounds.
- If `pdflatex` is available, compile and fix errors until it builds; if
  LaTeX is absent on this machine, deliver the .tex uncompiled and say so in
  PAPER-NOTES.md. NO installs.
- No GitHub writes in this lane. No changes outside this workdir.
- If a Codex update prompt appears, choose Skip.

## Reporting
- `PAPER-NOTES.md` in this workdir: what is drafted, what awaits the proof
  (theorem numbers to finalize, figures if any), compile status, and any
  place where the reports' numbers were ambiguous.
