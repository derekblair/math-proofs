# Mathematics manuscript collection

**12 catalogued manuscripts covering 15 result families** *(plus [`preprints/rule129/`](preprints/rule129/) and 22 post-scope Seam B / Seam C preprints under [`preprints/`](preprints/)).*

[**Read the overview PDF**](overview.pdf) ([LaTeX source](overview.tex)).

Named Lean statements are checked; not every manuscript claim has an end-to-end formalization. Manuscripts are organized into families — each family groups a principal result with companion arguments, consequences, or alternative proofs.

Built with **Lean 4.34.1** + **Mathlib v4.34.1**. See [`lean/formalization.yaml`](lean/formalization.yaml) and [`lean/docs/`](lean/docs/) for per-family verification status, Comparator challenges, and axiom dependencies.

The corrected `.tex` sources govern the October 23–24, 2026 changes. The overview, ES identity, ES barrier, `r47-sat184`, sieve-inverse, and absorption-forcing PDFs are historical pre-correction artifacts pending regeneration; see each preprint's `README.md`.

## Manuscript map

Each result description is followed by its constituent manuscripts and their abstracts. Paper titles link directly to PDFs.

<table>
<thead><tr><th>Result</th></tr></thead>
<tbody><tr>
<td>

<a name="family-001"></a>**001. Erdős–Straus identities and obstructions.** Proves positive natural covering witnesses for `n ≡ 217 (mod 264)`, the exact six covered subclasses modulo 9240 with one-out-of-eleven residue counts, and CRT escape from explicit local quadratic obstructions on square classes modulo 840. ([Lean](lean/docs/001.md))

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[An Erdős–Straus Covering Identity for n ≡ 217 (mod 264)](preprints/erdos-straus-identity-217mod264-October-3-2026/paper.pdf) *(historical PDF; [README](preprints/erdos-straus-identity-217mod264-October-3-2026/README.md))*

Gives a Lean formalization of the covering identity `4/n = 1/((n+3)/4) + 1/(n(n+3)) + 1/(n(n+3)/11)` for every natural `n ≡ 217 (mod 264)` with positive integral denominators, covering the prime 1009 and one-eleventh of each of the six hard square residue classes modulo 840. The former novelty claim is withdrawn in light of Lopez (2024), arXiv:2206.10319v4.

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[CRT Escape from Local Quadratic Obstructions on Square Classes Modulo 840](preprints/erdos-straus-finite-identity-barrier-October-4-2026/paper.pdf) *(historical PDF; [README](preprints/erdos-straus-finite-identity-barrier-October-4-2026/README.md))*

Proves a scoped Chinese Remainder Theorem escape theorem via Mathlib's general Dirichlet theorem: for finitely many progressions `Aᵢ t + Bᵢ` with `8 ∣ Aᵢ` where each `Bᵢ` has an explicit odd-prime nonsquare or mod-8 obstruction, infinitely many primes in each of `{1, 121, 169, 289, 361, 529} (mod 840)` avoid every progression. The Schinzel–Mordell implication from integer polynomial identities remains unformalized.

</td>
</tr></tbody>
<tbody><tr>
<td>

<a name="family-002"></a>**002. Collatz convergent control (gap-factor theory).** Proves general continued-fraction identities, analytic `sinh` and convexity estimates, C26 margin-duality trichotomy, C29 strict interior discrepancy positivity, the C64/C64b hump-law identity kernel, and unique odd-block minimization of the explicit analytic gap factor under C22's quantitative hypotheses. ([Lean](lean/docs/002.md))

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;*Preprint in preparation — see [`lean/docs/002.md`](lean/docs/002.md) and [CC-001](#cc-001).*

</td>
</tr></tbody>
<tbody><tr>
<td>

<a name="family-003"></a>**003. Erdős–Straus witness-complex and QR-core theory.** Proves witness-complex vacuity and fiber-collision arithmetic, T1/T2 prime-square obstructions, actual unit/square CRT cardinality `|Q| = |S|/2^k` modulo `24 ∏ p`, positive natural covering witnesses for all three mod-7 universal families and 5/7 forcing classes, descent transfer kernels, and a pair-specific SDR endgame. ([Lean](lean/docs/003.md))

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;*Preprint in preparation — see [`lean/docs/003.md`](lean/docs/003.md) and [ES-003](#es-003).*

</td>
</tr></tbody>
<tbody><tr>
<td>

<a name="family-004"></a>**004. Girth-5 extremal graphs.** Proves corrected local three-vertex reattachment feasibility, cycle exclusion and `emittedGraph` girth-≥5 preservation, exact unordered-edge balance `e(G') + D = e(G) + score`, and derives the score ceiling, three-vertex rigidity, and gap `−1` from global edge maximality. ([Lean](lean/docs/004.md))

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;*Preprint in preparation — see [`lean/docs/004.md`](lean/docs/004.md) and [G5-001](#g5-001).*

</td>
</tr></tbody>
<tbody><tr>
<td>

<a name="family-005"></a>**005. q-adic classification of Erdős–Straus witnesses.** Proves the conditional branch-1 q-adic valuation bound `v_q(r) ≤ v_q(A)` under explicit QQ/M23/R74 inputs, independent bounds `α ≤ 1` and `ρ ≤ 1` without R74, and a concrete generic type-`(0,1)` witness showing R74 cannot simply be deleted. ([Lean](lean/docs/005.md))

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;*Preprint in preparation — see [`lean/docs/005.md`](lean/docs/005.md) and [QA-001](#qa-001).*

</td>
</tr></tbody>
<tbody><tr>
<td>

<a name="family-006"></a>**006. Saturated Sidon sets.** Kernel-checks a saturated 9-element Sidon subset of `[1, 184]`, the general unique-extension saturation lemma, nine displayed one-hole 183-coverage sets with saturated 10-element extensions, and two counterexamples refuting the C28 gate conjecture. ([Lean](lean/docs/006.md))

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[A Saturated 9-Element Sidon Set in [1,184]: A Kernel-Checked Finite Witness](preprints/r47-sat184-October-7-2026/paper.pdf) *(historical PDF; [README](preprints/r47-sat184-October-7-2026/README.md))*

Exhibits `A⋆ = {16, 62, 66, 74, 88, 104, 117, 122, 123} ⊂ [1, 184]` and proves by Lean's kernel that all 45 pair sums are distinct and all 175 complementary positions in `[1, 184]` are blocked, alongside kernel checks of nine one-hole rows and two C28 counterexamples.

</td>
</tr></tbody>
<tbody><tr>
<td>

<a name="family-007"></a>**007. Erdős–Straus fiber compatibility and suppression.** Proves the prime-power and composite-modulus Fiber-Compatibility Theorems, fiber-`{6, 11}` thinned-tiling impossibility, composite suppression and tower-refinement operator laws, branch-2 degeneracy, the 92-identity `s ≡ 73 (mod 264)` covering family, and the formal mod-8 refutation of the naive claim. ([Lean](lean/docs/007.md))

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[Fiber-Compatibility and Composite Suppression in Erdős–Straus Covering Families](preprints/fiber-compatibility-composite-suppression-October-11-2026/paper.pdf) *([README](preprints/fiber-compatibility-composite-suppression-October-11-2026/README.md))*

Reports five formalized components on residue-covering families for `4/n = 1/x + 1/y + 1/z`: the forced Hensel digit involution `A_r` characterizing inverse closure for prime powers and composites `m = nD` (`D ∣ n`), thinned-tiling obstructions on fibers `{6, 11}`, composite suppression coefficients and T4–T8 R-operators, and branch-2 degeneracy with the divisor-closed family identity.

</td>
</tr></tbody>
<tbody><tr>
<td>

<a name="family-008"></a>**008. Sidon hole suppression and absorption.** Proves the hole-capability margin dichotomy, saturation-forcing lemmas, absorbed-regime exclusions for `R ∈ {1, 2, 3, 6}`, and the repaired self-bound `c ≤ 320` for absorbed quads with `13 ∣ h`, `13 ∤ R`, `R ∣ 30030`. ([Lean](lean/docs/008.md))

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[Hole Suppression and Absorption in Saturated Sidon Families](preprints/hole-suppression-absorption-October-11-2026/paper.pdf) *([README](preprints/hole-suppression-absorption-October-11-2026/README.md))*

Formalizes hole-suppression finite-set lemmas (`t2_iff`, `t5_saturation`, `t5_double_saturation`), the T5′ arithmetic exclusions for `R ∈ {1, 2, 3, 6}`, and the corrected T4 self-bound `c ≤ 320` in the absorbed `13 ∣ h` regime.

</td>
</tr></tbody>
<tbody><tr>
<td>

<a name="family-009"></a>**009. Translation marches and dip mechanics.** Proves blocked-set translation rigidity, deterministic forward/backward hole sweeping for saturated and unsaturated Sidon seeds, corrected chain-width bounds, hole-twin forcing at chain dips, and sliding-window dip-march mechanics with `φ`-duality. ([Lean](lean/docs/009.md))

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[Translation Marches, Hole-Twin Dips, and Dip-March Mechanics](preprints/translation-march-dip-October-11-2026/paper.pdf) *([README](preprints/translation-march-dip-October-11-2026/README.md))*

Develops the blocked-set theory of translating Sidon subsets of `[1, N]`: holes of `A + t` match shadow gaps of the raw blocked set `W(A)` in a sliding window, extending to unsaturated seeds with additive bounds, clean-window hole-twin forcing, and exact continuation/break/reset/perfect window classification.

</td>
</tr></tbody>
<tbody><tr>
<td>

<a name="family-010"></a>**010. Sub-family dichotomy and ladder ceilings.** Proves the R245 generalized Erdős–Straus sub-family identity, staged prime-valuation admission pinning and `A₀`-constancy extensions, repaired conditional split/layered dichotomy, and the two-sided march ladder-length ceiling. ([Lean](lean/docs/010.md))

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[Sub-Family Dichotomy and Ladder Ceilings: Generalized Erdős–Straus Identities, Admission Pinning, and the March Ladder Bound](preprints/subfamily-ladder-ceiling-October-11-2026/paper.pdf) *([README](preprints/subfamily-ladder-ceiling-October-11-2026/README.md))*

Establishes the explicit infinite family `4/(M't + s) = 1/x + 1/(nAC) + 1/(BC)` on `s ≡ -m + 4qeV₀ (mod 4qeA₀)`, its admission criterion and `A₀`-constancy, the repaired conditional split/layered dichotomy (documenting the refutation of the unconditional form), and the two-sided ladder ceiling for hole-twin marches.

</td>
</tr></tbody>
<tbody><tr>
<td>

<a name="family-011"></a>**011. Sigma transfer and fiber overlap.** Proves `σ`-spectrum Pareto down-set membership, T5 locality, T6 independence models, reflection-dual exclusion, the Sidon autocorrelation bound `|A ∩ (A + t)| ≤ 1`, distinct pair-sum fiber overlap `≤ 1`, and conditional top-interval sparsity. ([Lean](lean/docs/011.md))

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[Sigma Transfer and Fiber Overlap: Pareto Transitions of the March-Graph Spectrum and the Sidon Fiber-Overlap Bound](preprints/sigma-transfer-fiber-overlap-October-11-2026/paper.pdf) *([README](preprints/sigma-transfer-fiber-overlap-October-11-2026/README.md))*

Formalizes Pareto transition locality, abstract independence models, and reflection-dual exclusion for the march-graph `σ`-spectrum together with the single-point overlap bound for distinct pair-sum fibers of Sidon sets.

</td>
</tr></tbody>
<tbody><tr>
<td>

<a name="family-012"></a>**012. Abstract locks and transition DAGs.** Proves the repaired consecutive-firing laws for abstract lock frames (with sharpness witness `W = {0, 2}`), the axiom-free D7′ dual-ascent barrier on Pareto transition DAGs, reflection-cardinality invariance, and finite-DAG ascent-depth bounds. ([Lean](lean/docs/012.md))

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[Abstract Locks and Transition DAGs: Repaired Consecutive-Firing Laws, the Dual-Ascent Barrier, and Ascent-Depth Bounds](preprints/abstract-lock-transdag-October-11-2026/paper.pdf) *([README](preprints/abstract-lock-transdag-October-11-2026/README.md))*

Axiomatizes firing behavior of lock frames (repairing T3(iii) after the `W = {0, 2}` counterexample) and proves the axiom-free order-theoretic dual-ascent barrier (`no_dual_target_demote`, `no_dual_source_promote`), reflection cardinality preservation, and finite-DAG ascent-depth bounds.

</td>
</tr></tbody>
<tbody><tr>
<td>

<a name="family-013"></a>**013. Void frames and defect calculus.** Proves void-frame union-identity and zero-triple laws V1–V8, void-exclusion locks, the parameterized annotated defect monoid `N′_W`, D2(c) repair and maximal-family tiling, defect-homomorphism rigidity (H1), non-additivity of literal products (C4), and mixed-family splitting witnesses. ([Lean](lean/docs/013.md))

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[Void Frames, Defect Calculus, and Defect Homomorphisms](preprints/void-frames-defect-October-11-2026/paper.pdf) *([README](preprints/void-frames-defect-October-11-2026/README.md))*

Develops the algebra of void frames from union-forcing laws V1–V8 through the parameterized defect monoid `N′_W`, proving that every monoid homomorphism into a cancellative additive monoid is zero and that literal products of nontrivial families are never defect-additive.

</td>
</tr></tbody>
<tbody><tr>
<td>

<a name="family-014"></a>**014. ES absorption order and forcing spectrum.** Proves the ES absorption partial order, datum-equality characterization under `G.C.Nonempty`, redundancy-rank superadditivity and absorption collapse under `H.C.Nonempty`, singleton factorization in a finite ambient family `𝒢 ⊇ S`, the ES forcing-spectrum partition, and checked components of the forcing decomposition. ([Lean](lean/docs/014.md))

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[Absorption Order and Forcing Spectrum in Erdős–Straus Families](preprints/es-absorption-forcing-October-11-2026/paper.pdf) *(PDF superseded; [README](preprints/es-absorption-forcing-October-11-2026/README.md))*

Studies the absorption order and redundancy rank `ρ` on Erdős–Straus union groups (with repaired local nonemptiness and finite ambient-family hypotheses), the forcing-spectrum partition S2(a)′/S2(b–d)/S3/S4, and the checked CRT/scaling/filter/cardinality components of the forcing decomposition.

</td>
</tr></tbody>
<tbody><tr>
<td>

<a name="family-015"></a>**015. Sieve inversion and branch isolation.** Proves by pure kernel proofs the 44-CRT selectivity equivalence, exact six-class support and multiplicative inverse closure modulo 3960, exact projection equality at `q = 19`, and the H-clique u-branch isolation and u-side degree bound lemmas. ([Lean](lean/docs/015.md))

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[Sieve Inversion and Branch Isolation](preprints/sieve-inverse-branch-isolation-October-11-2026/paper.pdf) *(historical PDF; [README](preprints/sieve-inverse-branch-isolation-October-11-2026/README.md))*

Characterizes the refined sieve's six-class inverse-closed support modulo 3960 via the 44-CRT selectivity channel (kernel-checked with former `native_decide` calls removed) and proves the u-branch isolation and u-side degree bound lemmas for H-cliques.

</td>
</tr></tbody>
</table>

---

## Labeling convention

- **`[PROVED]`** — machine-checked by Lean, no extra axioms beyond Lean's standard ones (`propext`, `Classical.choice`, `Quot.sound`).
- **`[CONDITIONAL]`** — the larger interpretation has explicit, unformalized inputs.
- **`[PROVED*]`** — staged publication status; the scope docs state the checked scope.
- **`[COMPUTED]`** — external computation not certified by the Lean kernel.
- Nothing here is claimed on the basis of a `sorry`.

## Detailed family notes (per-paper index)

### Family 001 — Erdős–Straus identities and obstructions

#### <a id="es-001"></a>ES-001 — An Erdős–Straus covering identity — [PROVED]

For `n ≡ 217 (mod 264)`:

> `4/n = 1/((n+3)/4) + 1/(n(n+3)) + 1/(n(n+3)/11)`

Covers the prime **1009**. The novelty claim is withdrawn in light of
[Lopez (2024), arXiv:2206.10319v4](https://arxiv.org/html/2206.10319v4);
see the manuscript's prior-art correction. The exact six covered subclasses modulo 9240 and the one-out-of-eleven residue count are proved in [`ESIdentityCRT.lean`](lean/Mathproofs/NumberTheory/ESIdentityCRT.lean).

- Paper: [`preprints/erdos-straus-identity-217mod264-October-3-2026/`](preprints/erdos-straus-identity-217mod264-October-3-2026/)
  ([PDF (historical)](preprints/erdos-straus-identity-217mod264-October-3-2026/paper.pdf),
  [source](preprints/erdos-straus-identity-217mod264-October-3-2026/build/main.tex),
  [README / build / citation](preprints/erdos-straus-identity-217mod264-October-3-2026/README.md))
- Lean: [`lean/Mathproofs/NumberTheory/ESIdentity.lean`](lean/Mathproofs/NumberTheory/ESIdentity.lean) (`es_covering_217mod264`, `es_identity_217mod264`), [`lean/Mathproofs/NumberTheory/ESIdentityCRT.lean`](lean/Mathproofs/NumberTheory/ESIdentityCRT.lean), scope [`lean/docs/001.md`](lean/docs/001.md), comparator [`lean/ComparatorChallenges/ESIdentity.lean`](lean/ComparatorChallenges/ESIdentity.lean).

#### <a id="es-002"></a>ES-002 — CRT escape from local quadratic obstructions modulo 840 — [PROVED]

The checked result is `es_crt_escape`: for progressions with `8 ∣ Aᵢ` and explicit odd-prime nonsquare or 2-adic residue obstructions, infinitely many primes in each listed square class modulo 840 avoid every progression. Uses Mathlib's general Dirichlet theorem with no custom axioms. The Schinzel–Mordell implication from integer polynomial identities to those local obstructions remains unformalized.

- Paper: [`preprints/erdos-straus-finite-identity-barrier-October-4-2026/`](preprints/erdos-straus-finite-identity-barrier-October-4-2026/)
  ([PDF (historical)](preprints/erdos-straus-finite-identity-barrier-October-4-2026/paper.pdf),
  [corrected source](preprints/erdos-straus-finite-identity-barrier-October-4-2026/build/main.tex),
  [README / build / citation](preprints/erdos-straus-finite-identity-barrier-October-4-2026/README.md))
- Lean: [`lean/Mathproofs/NumberTheory/ESBarrier.lean`](lean/Mathproofs/NumberTheory/ESBarrier.lean) (`es_crt_escape`), scope [`lean/docs/001.md`](lean/docs/001.md), comparator [`lean/ComparatorChallenges/ESBarrier.lean`](lean/ComparatorChallenges/ESBarrier.lean).

### Family 002 — Collatz convergent control (gap-factor theory)

#### <a id="cc-001"></a>CC-001 — Analytic/continued-fraction kernels and conditional gap selectors — [CONDITIONAL]

Twelve modules under [`lean/Mathproofs/NumberTheory/`](lean/Mathproofs/NumberTheory/) (`CollatzGapCF`, `CollatzGapC24`, `CollatzGapC24Lemma3`, `CollatzGapC23`, `CollatzGapC22C25`, `CollatzGapFactor`, `CollatzGapDelta`, `CollatzGapConvex`, `CollatzGapSinh`, `CollatzGapC29`, `CollatzGapC29Mirror`, `CollatzGapHump`) prove continued-fraction identities, analytic bounds, and conditional odd-block argmin assemblies using standard axioms only. Specialization to `log₂ 3` continued fractions and Collatz dynamics remains unformalized.

- Scope: [`lean/docs/002.md`](lean/docs/002.md).
- Paper: preprint in preparation.

### Family 003 — Erdős–Straus witness-complex and QR-core theory

#### <a id="es-003"></a>ES-003 — Witness-complex and QR arithmetic kernels — [PROVED]

Thirteen modules across [`lean/Mathproofs/Topology/`](lean/Mathproofs/Topology/) (`WitnessComplexThm2`, `WitnessComplexThm13`) and [`lean/Mathproofs/NumberTheory/`](lean/Mathproofs/NumberTheory/) (`ESPrimeSquareT2`, `EST1TwoCase`, `ESQRCore`, `ESQRCoreCount`, `ESCovering`, `ESFiveSevenForcing`, `ESMod7UniversalFamilies`, `ESX0S1S3`, `ESDescentTransfer`, `ESDescentCovering`, `ESBranchSDREndgame`).

- Scope: [`lean/docs/003.md`](lean/docs/003.md); comparators [`ESQRCoreCount.lean`](lean/ComparatorChallenges/ESQRCoreCount.lean), [`ESMod7UniversalFamilies.lean`](lean/ComparatorChallenges/ESMod7UniversalFamilies.lean).
- Paper: preprint in preparation.

### Family 004 — Girth-5 extremal graphs

#### <a id="g5-001"></a>G5-001 — The 3v floor theorem for girth-5 graphs — [PROVED]

- Lean: [`lean/Mathproofs/Combinatorics/Girth5Floor3v.lean`](lean/Mathproofs/Combinatorics/Girth5Floor3v.lean), [`lean/Mathproofs/Combinatorics/Girth5Floor3vRegression.lean`](lean/Mathproofs/Combinatorics/Girth5Floor3vRegression.lean), [`lean/Mathproofs/Combinatorics/Girth5Extremal.lean`](lean/Mathproofs/Combinatorics/Girth5Extremal.lean), scope [`lean/docs/004.md`](lean/docs/004.md), comparator [`lean/ComparatorChallenges/Girth5Extremal.lean`](lean/ComparatorChallenges/Girth5Extremal.lean).
- Paper: preprint in preparation.

### Family 005 — q-adic classification of Erdős–Straus witnesses

#### <a id="qa-001"></a>QA-001 — Conditional branch-1 q-adic type theorem — [CONDITIONAL]

- Lean: [`lean/Mathproofs/NumberTheory/ESQadicBranch1.lean`](lean/Mathproofs/NumberTheory/ESQadicBranch1.lean), [`lean/Mathproofs/NumberTheory/ESQadicBoundary.lean`](lean/Mathproofs/NumberTheory/ESQadicBoundary.lean), scope [`lean/docs/005.md`](lean/docs/005.md).
- Paper: preprint in preparation.

### Family 006 — Saturated Sidon sets

#### <a id="ss-001"></a>SS-001 — A saturated 9-element Sidon set in [1,184] — [PROVED]

- Paper: [`preprints/r47-sat184-October-7-2026/`](preprints/r47-sat184-October-7-2026/)
  ([PDF (historical)](preprints/r47-sat184-October-7-2026/paper.pdf),
  [corrected source](preprints/r47-sat184-October-7-2026/build/main.tex),
  [README / build / citation](preprints/r47-sat184-October-7-2026/README.md))
- Lean: [`lean/Mathproofs/Combinatorics/SidonSat184.lean`](lean/Mathproofs/Combinatorics/SidonSat184.lean), [`lean/Mathproofs/Combinatorics/SidonSat184Census.lean`](lean/Mathproofs/Combinatorics/SidonSat184Census.lean), scope [`lean/docs/006.md`](lean/docs/006.md), comparator [`lean/ComparatorChallenges/SidonSat184.lean`](lean/ComparatorChallenges/SidonSat184.lean).

### Family 007 — Erdős–Straus fiber compatibility and suppression

#### <a id="es-004"></a>ES-004 — Fiber-compatibility and composite suppression — [PROVED]

- Paper: [`preprints/fiber-compatibility-composite-suppression-October-11-2026/`](preprints/fiber-compatibility-composite-suppression-October-11-2026/)
  ([PDF](preprints/fiber-compatibility-composite-suppression-October-11-2026/paper.pdf),
  [source](preprints/fiber-compatibility-composite-suppression-October-11-2026/build/main.tex),
  [README / build / citation](preprints/fiber-compatibility-composite-suppression-October-11-2026/README.md))
- Lean: [`ESFiberCompat.lean`](lean/Mathproofs/NumberTheory/ESFiberCompat.lean), [`ESFiberCompatComposite.lean`](lean/Mathproofs/NumberTheory/ESFiberCompatComposite.lean), [`ESFiberTiling.lean`](lean/Mathproofs/NumberTheory/ESFiberTiling.lean), [`CompositeSuppression.lean`](lean/Mathproofs/NumberTheory/CompositeSuppression.lean), [`ESBranchTwo.lean`](lean/Mathproofs/NumberTheory/ESBranchTwo.lean); scope [`lean/docs/007.md`](lean/docs/007.md).

### Family 008 — Sidon hole suppression and absorption

#### <a id="ss-002"></a>SS-002 — Hole suppression and absorption — [PROVED]

- Paper: [`preprints/hole-suppression-absorption-October-11-2026/`](preprints/hole-suppression-absorption-October-11-2026/)
  ([PDF](preprints/hole-suppression-absorption-October-11-2026/paper.pdf),
  [source](preprints/hole-suppression-absorption-October-11-2026/build/main.tex),
  [README / build / citation](preprints/hole-suppression-absorption-October-11-2026/README.md))
- Lean: [`HoleSuppression.lean`](lean/Mathproofs/NumberTheory/HoleSuppression.lean), [`AbsorbedRegime.lean`](lean/Mathproofs/NumberTheory/AbsorbedRegime.lean), [`AbsorbedBound.lean`](lean/Mathproofs/NumberTheory/AbsorbedBound.lean); scope [`lean/docs/008.md`](lean/docs/008.md).

### Family 009 — Translation marches and dip mechanics

#### <a id="ss-003"></a>SS-003 — Translation marches and dip mechanics — [PROVED]

- Paper: [`preprints/translation-march-dip-October-11-2026/`](preprints/translation-march-dip-October-11-2026/)
  ([PDF](preprints/translation-march-dip-October-11-2026/paper.pdf),
  [source](preprints/translation-march-dip-October-11-2026/build/main.tex),
  [README / build / citation](preprints/translation-march-dip-October-11-2026/README.md))
- Lean: [`TranslationMarch.lean`](lean/Mathproofs/NumberTheory/TranslationMarch.lean), [`CorrectedMarch.lean`](lean/Mathproofs/NumberTheory/CorrectedMarch.lean), [`TranslationMarchUnsat.lean`](lean/Mathproofs/NumberTheory/TranslationMarchUnsat.lean), [`HoleTwinDip.lean`](lean/Mathproofs/NumberTheory/HoleTwinDip.lean), [`DipMarch.lean`](lean/Mathproofs/NumberTheory/DipMarch.lean); scope [`lean/docs/009.md`](lean/docs/009.md).

### Family 010 — Sub-family dichotomy and ladder ceilings

#### <a id="ss-004"></a>SS-004 — Sub-family dichotomy and ladder ceilings — [PROVED]

- Paper: [`preprints/subfamily-ladder-ceiling-October-11-2026/`](preprints/subfamily-ladder-ceiling-October-11-2026/)
  ([PDF](preprints/subfamily-ladder-ceiling-October-11-2026/paper.pdf),
  [source](preprints/subfamily-ladder-ceiling-October-11-2026/build/main.tex),
  [README / build / citation](preprints/subfamily-ladder-ceiling-October-11-2026/README.md))
- Lean: [`ESSubfamilyExtended.lean`](lean/Mathproofs/NumberTheory/ESSubfamilyExtended.lean), [`MarchLadderCeiling.lean`](lean/Mathproofs/NumberTheory/MarchLadderCeiling.lean); scope [`lean/docs/010.md`](lean/docs/010.md).

### Family 011 — Sigma transfer and fiber overlap

#### <a id="ss-005"></a>SS-005 — Sigma transfer and fiber overlap — [PROVED]

- Paper: [`preprints/sigma-transfer-fiber-overlap-October-11-2026/`](preprints/sigma-transfer-fiber-overlap-October-11-2026/)
  ([PDF](preprints/sigma-transfer-fiber-overlap-October-11-2026/paper.pdf),
  [source](preprints/sigma-transfer-fiber-overlap-October-11-2026/build/main.tex),
  [README / build / citation](preprints/sigma-transfer-fiber-overlap-October-11-2026/README.md))
- Lean: [`SigmaTrans.lean`](lean/Mathproofs/NumberTheory/SigmaTrans.lean), [`FiberOverlap.lean`](lean/Mathproofs/NumberTheory/FiberOverlap.lean); scope [`lean/docs/011.md`](lean/docs/011.md).

### Family 012 — Abstract locks and transition DAGs

#### <a id="ss-006"></a>SS-006 — Abstract locks and transition DAGs — [PROVED]

- Paper: [`preprints/abstract-lock-transdag-October-11-2026/`](preprints/abstract-lock-transdag-October-11-2026/)
  ([PDF](preprints/abstract-lock-transdag-October-11-2026/paper.pdf),
  [source](preprints/abstract-lock-transdag-October-11-2026/build/main.tex),
  [README / build / citation](preprints/abstract-lock-transdag-October-11-2026/README.md))
- Lean: [`AbstractLock.lean`](lean/Mathproofs/NumberTheory/AbstractLock.lean), [`TransDAG.lean`](lean/Mathproofs/NumberTheory/TransDAG.lean); scope [`lean/docs/012.md`](lean/docs/012.md).

### Family 013 — Void frames and defect calculus

#### <a id="ss-007"></a>SS-007 — Void frames and defect calculus — [PROVED] (`VoidMonoidParam` `[PROVED*]` staged)

- Paper: [`preprints/void-frames-defect-October-11-2026/`](preprints/void-frames-defect-October-11-2026/)
  ([PDF](preprints/void-frames-defect-October-11-2026/paper.pdf),
  [source](preprints/void-frames-defect-October-11-2026/build/main.tex),
  [README / build / citation](preprints/void-frames-defect-October-11-2026/README.md))
- Lean: [`VoidUnion.lean`](lean/Mathproofs/NumberTheory/VoidUnion.lean), [`VoidLock.lean`](lean/Mathproofs/NumberTheory/VoidLock.lean), [`VoidMonoidParam.lean`](lean/Mathproofs/NumberTheory/VoidMonoidParam.lean), [`VoidMonoid.lean`](lean/Mathproofs/NumberTheory/VoidMonoid.lean), [`VoidDefectHom.lean`](lean/Mathproofs/NumberTheory/VoidDefectHom.lean); scope [`lean/docs/013.md`](lean/docs/013.md).

### Family 014 — ES absorption order and forcing spectrum

#### <a id="es-005"></a>ES-005 — Absorption order and forcing spectrum — [PROVED]

- Paper: [`preprints/es-absorption-forcing-October-11-2026/`](preprints/es-absorption-forcing-October-11-2026/)
  ([PDF (superseded)](preprints/es-absorption-forcing-October-11-2026/paper.pdf),
  [corrected source](preprints/es-absorption-forcing-October-11-2026/build/main.tex),
  [README / supersession note / build / citation](preprints/es-absorption-forcing-October-11-2026/README.md))
- Lean: [`ESAbsorptionOrder.lean`](lean/Mathproofs/NumberTheory/ESAbsorptionOrder.lean), [`ESForcingSpectrum.lean`](lean/Mathproofs/NumberTheory/ESForcingSpectrum.lean), [`ESForcingDecomp.lean`](lean/Mathproofs/NumberTheory/ESForcingDecomp.lean); scope [`lean/docs/014.md`](lean/docs/014.md).

### Family 015 — Sieve inversion and branch isolation

#### <a id="es-006"></a>ES-006 — Sieve inversion and branch isolation — [PROVED]

- Paper: [`preprints/sieve-inverse-branch-isolation-October-11-2026/`](preprints/sieve-inverse-branch-isolation-October-11-2026/)
  ([PDF (historical)](preprints/sieve-inverse-branch-isolation-October-11-2026/paper.pdf),
  [corrected source](preprints/sieve-inverse-branch-isolation-October-11-2026/build/main.tex),
  [README / build / citation](preprints/sieve-inverse-branch-isolation-October-11-2026/README.md))
- Lean: [`ESRefinedSieveInverse.lean`](lean/Mathproofs/NumberTheory/ESRefinedSieveInverse.lean), [`ESUBranchIsolation.lean`](lean/Mathproofs/NumberTheory/ESUBranchIsolation.lean); scope [`lean/docs/015.md`](lean/docs/015.md).

---

## Additional preprints (family numbers pending)

- [`preprints/rule129/`](preprints/rule129/) ([PDF](preprints/rule129/paper.pdf), [README](preprints/rule129/README.md)) — formalized under [`lean/Mathproofs/Dynamics/`](lean/Mathproofs/Dynamics/) (`Rule129ClosedForm`, `Rule129Lucas`, `Rule129Digits`, `Rule129MiddleColumn`; comparator [`Rule129MiddleColumn.lean`](lean/ComparatorChallenges/Rule129MiddleColumn.lean)).
- 22 post-scope Seam B / Seam C OEIS preprints under [`preprints/`](preprints/) (`a186424`, `c018-a189640`, `c037-a203568`, `c042-a191579`, `c047-a317933`, `c049-a372556`, `c050-a266222`, `c051-a266439`, `c052-a266256`, `c053-a266662`, `c054-a266258`, `c055-a266664`, `c056-a266220`, `c057-a266437`, `c085-a294912`, `s001-a392002`, `s003-a385590`, `s006-a363166`, `s010-a401714`, `s012-a401496`, `s017-a401673`, `s019-a381494`), formalized under `lean/Mathproofs/`, `lean/MathProofs/SeamB/`, and `lean/SeamC/`. *(Of the 13 `*Statement.lean` files under `lean/`, 11 are unbuilt `MathProofs/SeamB/*/Statement.lean` stubs excluded from default `lake build`, and 2 are built, sorry-free `SeamC/*/Statement.lean` modules.)*

## Versions and citations

Corrections and revisions are recorded as new versions, with previously released versions remaining accessible in git history — see [`history.md`](history.md). To cite an individual manuscript, use the BibTeX block in its `preprints/<slug>/README.md`.
