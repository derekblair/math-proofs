# Math Proofs

Lean 4.34.1 and Mathlib v4.34.1 formalizations, with accompanying manuscripts
where available. The exact exported statements determine what is proved.
Some larger research claims still require bridges or inputs that are not
formalized; these limits are recorded in the catalogue.

- [Contents](CONTENTS.md): manuscripts and result families.
- [Formalization catalogue](FORMALIZATION_CATALOGUE.md): checked statements and scope.
- [Machine-readable catalogue](formalization.yaml).
- [Changelog](CHANGELOG.md): disclosed corrections, including the 2026-10-23 review fixes.

## Complete finite and arithmetic results

`es_covering_217mod264` in [ESIdentity.lean](Mathproofs/ESIdentity.lean)
proves that every natural `n ≡ 217 (mod 264)` has positive natural
denominators `x,y,z` satisfying `4x=n+3`, `y=n(n+3)`, `11z=n(n+3)` and
`4/n=1/x+1/y+1/z`. The original rational equality remains available as
`es_identity_217mod264`. [ESIdentityCRT.lean](Mathproofs/ESIdentityCRT.lean)
proves the six covered subclasses modulo 9240 and the exact one-out-of-eleven
residue count for each parent class. These use only standard Lean axioms.

`SidonSat184.r47_sat184` in [SidonSat184.lean](Mathproofs/SidonSat184.lean)
proves that `{16,62,66,74,88,104,117,122,123}` has nine elements and is a
Sidon subset of `[1,184]` with no admissible extension in that interval.
The finite computations are checked by Lean's kernel. The nine displayed
one-hole rows, their coverage counts, saturated ten-element extensions, and
the two C28 gate counterexamples are now checked in
[SidonSat184Census.lean](Mathproofs/SidonSat184Census.lean). Search exhaustiveness,
minimality, and priority claims are not part of this theorem.

The refined-sieve residue theorems in
[ESRefinedSieveInverse.lean](Mathproofs/ESRefinedSieveInverse.lean) now use
kernel proofs; their former native-computation certificate axioms were removed.

## Explicitly scoped kernels

- `es_crt_escape` proves infinitely many escaping primes from explicit local
  quadratic obstructions. It uses Mathlib's proved general Dirichlet theorem.
  The old inconsistent axioms and false rational-polynomial `es_barrier`
  statement were removed. The Schinzel–Mordell implication from integer
  polynomial identities to those obstructions remains unformalized.
- The Collatz modules prove analytic/continued-fraction identities and
  conditional argmin assemblies. [CollatzGapFactor.lean](Mathproofs/CollatzGapFactor.lean)
  defines the explicit Q-ratio times power-of-two-ratio, proves its logarithmic
  difference bridge, and proves its unique odd-block minimum under C22's
  quantitative hypotheses. Specialization to the continued fraction of log₂3
  and Collatz dynamics remains outside these statements.
- QR counting now proves `|Q|=|S|/2^k` for actual residues modulo
  `24*∏p`: S consists of units congruent to 1 modulo 24, and Q consists of
  squares in S. The CRT equivalences are constructed in the proof. Matching
  an externally filtered frontier remains a separate task.
- The three mod-7 families, T1 w=20 classes, and T2 q=7 fibers now produce
  positive natural Egyptian-fraction witnesses for every progression member.
  [ESDescentCovering.lean](Mathproofs/ESDescentCovering.lean) turns the
  descended slope and intercept divisibilities into positive identities on
  the parent progression. External normalization, class censuses, and R74
  descent exclusions remain unverified.
- Q-adic classification is conditional on the explicit QQ/M23/R74 inputs;
  the external sweep has not been proved in this repository.
  [ESQadicBoundary.lean](Mathproofs/ESQadicBoundary.lean) proves the independent
  bounds α≤1 and ρ≤1 and supplies a concrete generic type-(0,1) witness showing
  why the R74 premise cannot simply be deleted.
- Girth-5 results use corrected local reattachment conditions and prove the
  identity-score floor. `emittedGraph` constructs a simple girth-at-least-five
  graph for every feasible move on a distinct triple.
  [Girth5Extremal.lean](Mathproofs/Girth5Extremal.lean) counts unordered edges
  and derives the score ceiling, rigidity, and gap −1 from global edge
  maximality among all girth-at-least-five graphs on the same vertex type.

## Verification and labels

```bash
lake exe cache get
lake build
```

`[PROVED]` means the named Lean statement is checked using only standard
axioms. `[CONDITIONAL]` identifies a larger interpretation whose remaining
inputs are explicit theorem arguments. `[PROVED*]` is reserved for staged
publication status and never silently asserts end-to-end verification of a
larger claim. `[COMPUTED]` identifies external computations not certified by
the Lean kernel. No result is justified by a proof placeholder.

The 2026-10-23 correction updates the `.tex` sources. Existing PDFs for the
overview, ES identity, ES barrier, r47, and sieve-inverse papers are historical
pre-correction artifacts; they were not regenerated because no TeX toolchain
is installed in this lane. Read the corrected sources and catalogues for
current statements. Their BUILD files explain regeneration.
