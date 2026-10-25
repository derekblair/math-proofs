# Five stated-open OEIS pairs: status and proof-route audit

Research draft for derekblair/math-proofs#5 — Brian (canonical Louis), 2026-10-25 UTC. Research only; independent programme review and coordinator merge gates remain outstanding.

## Result first

No FIRST-PROOF CANDIDATE is recommended. The two cellular-automaton pairs and the Motzkin connection-coefficient pair have elementary routes from published rules/formulas and are classified **TRIVIAL for triage, not newly certified resolutions**. The totient pair is likewise elementary mathematically, but its exact named-pair assertion was not located: its required source-assertion status is **UNVERIFIED**, not an invented conjecture attribution. The Collatz pair is elementary on convergent trajectories; asserting finite values for every positive input retains the universal Collatz obstruction. All five are DROP as novelty/first-proof targets.

| Exact requested pair | Audit status | Recommendation | Supplied finite evidence only |
|---|---|---|---|
| A071051(n)=A267447(n), n>=1 | TRIVIAL from published local rules; not RESOLVED-by-located-paper | DROP | n=1..1,048,576 |
| A043545(n)=A267442(n), n>=1 | TRIVIAL from the same rules and published central-column bridge | DROP | n=1..1,048,576 |
| A225530(n)=A384710(n), n>=1 | UNVERIFIED exact-pair attribution; mathematically TRIVIAL | DROP | n=1..50,000,000 |
| A112695(n)=A139399(n), n>=3 | OPEN universal-totality qualification; conditional identity TRIVIAL | DROP | n=3..100,000,000 |
| A097724(m)=A191579(m+1), m>=0 | TRIVIAL generating-function route from published formulas, pending independent review | DROP | m=0..4,504,500 |

“OPEN” means no verified resolution located in the specified search, never a global certification. “TRIVIAL” is the ticket's routine-consequence classification, supported below by published definitions plus explicitly marked elementary reasoning; it does not claim we located a published proof of the exact pair, established novelty, or passed programme proof gates. “UNVERIFIED” concerns a missing exact attributed assertion, not numerical disagreement. No pair is marked RESOLVED because no independently established exact-pair resolution was located during this audit.

## Evidence and scope

The supplied 2026-10-25 recomputation report and machine-readable result report zero mismatches on exactly the table's intervals. They were read, not rerun. All bounds are computational evidence, not infinite proofs. The source screen is the 2026-10-23 batch-2 finalist report; its STATED-BUT-OPEN labels were hypotheses to audit, not current-status authority. Verified input revisions supplied with the job: screen `65e8423d6dce901962472`, recomputation report `65eb1bfb23bc501962472`, result `65eb1bfcb727b01962472`.

Primary OEIS entries, attributed COMMENTS/FORMULA/CROSSREFS, linked primary mathematics, and actual search queries were checked on 2026-10-25 UTC. Web retrieval may return indexed snapshots rather than a live revision; fetch failures and assertion gaps are disclosed below. Exact-pair searches are bounded discovery searches, not exhaustive bibliographic coverage or an audit of every proposed proof. Short quotations preserve original notation; explanations outside quotation marks are our interpretations or expressly marked derivations.

## 1. A071051(n) = A267447(n), n >= 1

Exact source assertion, A267447 FORMULA: **“Conjecture: a(n) = A071051(n), n>0.”** Attribution: R. J. Mathar, January 17, 2016. A267447 NAME describes **“Number of OFF (white) cells”** in Rule 129's nth single-black-seed evolution. Both offsets are 0; at n=0 the respective values are 1 and 0. [A267447](https://oeis.org/A267447)

Primary definition, A071051 NAME: **“Number of 1's in n-th row of triangle in A071035.”** Its COMMENTS identify that triangle as single-seed Rule 126. [A071051](https://oeis.org/A071051). The triangle source specifies row length 2n+1, so its row is the finite causal window [-n,n]. [A071035](https://oeis.org/A071035). Rule129 uses that same window, with an infinite white background at n=0 and black background thereafter; its full-background example is explicitly supplied by Mathar, August 7, 2025. [A267417](https://oeis.org/A267417)

**Reason for TRIVIAL (our elementary inference, not a located named-pair proof):** Let F be the Rule126 global update and C the pointwise color complement. Rule126 has rule word 01111110, so its local output is 0 exactly for neighborhoods 000 and 111. Therefore F(Cx)=F(x). Rule129 has word 10000001, hence G=CF. These are the published rule-number definitions; Wolfram's original presentation explicitly groups rules126/129 by color interchange. [Wolfram, *A New Kind of Science*, p.55](https://www.wolframscience.com/nks/p55--more-cellular-automata/). For identical single-seed initial configurations x0=y0, y1=Cx1. If yn=Cxn, then y(n+1)=CF(Cxn)=CF(xn)=Cx(n+1). Thus configurations are complementary for n>=1, on the whole lattice and hence on the same finite counting window. The OFF count in yn is the ON count in xn. Crucially, this includes the initial-step check and input-complement invariance; a bare claim that two rule words complement each other would not suffice.

**Difficulty / obstruction:** Elementary, once background and counting window are explicit. The only important pitfall is falsely freezing Rule129's outside background at zero. **Disposition: DROP** as a substantive first-proof target; do not label the surviving OEIS conjecture flag as evidence of difficulty or novelty. A short independently reviewed clarification could be useful, but no OEIS edit or publication is authorized here.

**Computational evidence:** supplied independent packet reports HOLDS-EXTENDED for n=1..1,048,576. This finite bound is not used in the argument and does not constitute proof.

## 2. A043545(n) = A267442(n), n >= 1

Exact source assertion, A267442 FORMULA: **“Conjecture: a(n) = A043545(n), n>0.”** Attribution: R. J. Mathar, January 17, 2016. Primary NAME begins **“Middle column”**, describing single-ON-seed Rule129. [A267442](https://oeis.org/A267442)

Primary definition, A043545 NAME: **“(Maximal base-2 digit of n) - (minimal base-2 digit of n).”** Published FORMULA, attributed Michael Somos, August25 2003: **“a(n) = 1 - A036987(n).”** Both offsets0; at0 their values are respectively0 and1. [A043545](https://oeis.org/A043545)

**Reason for TRIVIAL (our consequence of published identifications):** The first pair's complement induction says Rule129's center is one minus Rule126's center for n>=1. A071035 CROSSREFS identifies **“Cf. A036987 (central column).”** This is an explicit editorial cross-reference with an explicit column identification, not its automatically generated sequence-in-context neighbors. [A071035](https://oeis.org/A071035). Combining that published identification with Somos's formula gives the exact second equality. The auxiliary record independently describes A036987 as the Mersenne-index indicator, with value1 precisely at n=2^k-1. [A036987](https://oeis.org/A036987)

**Difficulty / obstruction:** Elementary conditional on the published Rule126-central-column identification; no isolated proof of that identification was retrieved in this bounded search. A fully self-contained verification could derive its binary recurrence from Rule126, but that is not necessary to classify the proposed relation as a routine consequence of published sequence data. **Disposition: DROP** as a substantive first-proof target; preserve the distinction between published facts and our inference. If a programme gate requires a primary theorem proof rather than OEIS's explicit identification, that is the narrow remaining source-strength check, not evidence the conjectured comparison is novel.

**Computational evidence:** supplied independent packet reports HOLDS-EXTENDED for n=1..1,048,576, with the evolving infinite background handled correctly. This bound is finite evidence, not proof.

## Actual bounded search and source limits

On 2026-10-25 the web tool opened A071051, A043545, A267442, A071035, A267417, A036987 and Wolfram p.55; all returned primary text. Direct A267447 opens returned “Cache miss”, and /internal and text-format variants were inaccessible. Exact-pair searches nevertheless returned the primary oeis.org/A267447 record including NAME, OFFSET, FORMULA, Mathematica window code, CROSSREFS and author. Its accessible indexed text still carries the exact Mathar conjecture; freshness is limited by search indexing and is not a guaranteed live revision read.

Queries actually executed: `"A267447" proof`; `"A267442" proof`; `"Rule 129" "Rule 126" proof`; `"A071051" "A267447"`; `"A043545" "A267442"`; `"cellular automaton" "129" "126" complement`; both exact pairs with `proof -site:sequencedb.net`; `"Rule 126" "central" "Mersenne"`. Exact-pair results found the conjecture-bearing entries and automatic sequence-context neighbors, not a later proof/refutation. Identifier-only searches produced substantial unrelated commercial/legal noise. SequenceMachine matches were not used as proof. This is a bounded negative literature finding, not certification of worldwide openness.

Sloane's primary paper [*On the Number of ON Cells in Cellular Automata*, arXiv:1503.01168](https://arxiv.org/html/1503.01168), §4, supplies the established Rule126 count in terms of binary weight with a Mersenne exception. Its retrieved full HTML had no substantive Rule129 passage; its lone search hit for129 was a reference anchor. Therefore that paper is background, not a located proof of the named Rule129 comparison. The Wolfram property-table PDF search exposed rules126/129 and their rule words, but opening the PDF failed with content-too-large (22,303,232 bytes); no unseen PDF theorem is relied upon.


## 3. A225530(n) = A384710(n), n >= 1

**Mathematical status: TRIVIAL; exact named-pair attribution: UNVERIFIED. DROP as a first-proof target.** The located conjectural statement does not name A384710. No verbatim assertion of that exact named pair was located; this is a source mismatch to report, not permission to reconstruct an attributed conjecture.

Primary definitions: [A225530](https://oeis.org/A225530), NAME, counts ordered nonnegative pairs with “i + j = n and gcd(i,j) <= 1.” Robert Price authored the entry May 09 2013. Its COMMENTS assertion is “Apparently a(n) = A000010(n), n >= 2.” — R. J. Mathar, May 11 2013. [A384710](https://oeis.org/A384710), NAME, Peter Luschny, Jun 07 2025: “a(n) = Sum_{k=0..n} [gcd(k, n) = 1]”; its COMMENTS identifies A000010 for n>=2. These are common-target statements, not a located exact-pair quote.

Elementary inference from those definitions, not a newly located publication: map k to (k,n−k). This is a bijection between k=0,...,n and the ordered pairs summing to n; their gcds agree by subtracting one argument from the other. For n>0 their gcd cannot be zero, so the condition <=1 is precisely =1. This establishes the mathematical reason for the TRIVIAL classification. At n=1 both counts are 2; at n=0 the respective values are 1 and 0, so the lower bound matters. Difficulty: elementary. Obstruction: attribution/qualification only, not mathematics. This argument is a research triage derivation, not independently reviewed programme proof completion.

Bounded search performed 2026-10-25 UTC: exact quoted identifiers together; A225530 totient proof; OEIS-targeted A225530 gcd/Mathar/Apparently queries; inspected full search-returned primary entry and A384710 NAME/COMMENTS/FORMULA/CROSSREFS. Direct A225530 page and internal fetch failed; search returned its full entry text (indexed older snapshot). No separate exact-pair publication was located. This freshness/access limitation prevents certifying current editorial wording. The supplied verified recomputation packet reports HOLDS-EXTENDED only on n=1..50,000,000; it is not used as proof.

## 4. A112695(n) = A139399(n), n >= 3

**OPEN only for universal finite-valued interpretation; TRIVIAL on trajectories reaching 1; DROP as a first-proof target.** The exact-pair cross-reference is located, but is not a universal convergence theorem.

[A112695](https://oeis.org/A112695), NAME, Wolfdieter Lang, Oct 31 2005: “Number of steps needed to reach 4,2,1 in Collatz' 3*n+1 conjecture.” CROSSREFS says “Essentially the same sequence as A139399.” The displayed FORMULA is the total stopping time A006577 minus two for n>=3, with exceptional values 1,2. No separate author is attached to that formula or cross-reference, so the entry author must not be passed off as a line-level attribution.

[A139399](https://oeis.org/A139399), NAME, Reinhard Zumkeller, Apr 18 2008: “Number of steps to reach a cycle in Collatz problem.” COMMENTS: “a(n) = A006577(n) - 2 for n > 2 (if the conjecture holds).” That line has no separately signed attribution. Its reverse cross-reference names A112695. Programs target the known cycle, whereas the NAME speaks of any cycle: this distinction cannot be erased.

Reasoning: for a positive n>=3 whose trajectory reaches 1, its first entry into {1,2,4} is 4. An earlier first entry at 1 would have predecessor2; one at2 would have predecessor4, contradictions. Thus both finite hitting times agree on this domain. Universal finiteness for A112695 still requires all starts to reach the known cycle; a nontrivial cycle or divergent orbit is not ruled out by equality on tested starts. Difficulty: elementary conditional identity; extraordinarily difficult universal totality. Recommendation: DROP, not a promising new sequence-equality proof problem.

Bounded search 2026-10-25 UTC: quoted exact pair, quoted pair plus proof, and Collatz proof2026/Tao almost-all; read both primary entries and [Tao, arXiv:1909.03562v7](https://arxiv.org/abs/1909.03562v7), revised Jul 16 2026, published Forum of Mathematics Pi10(2022)e12. Tao's theorem gives almost-all logarithmic-density descent below any bound tending to infinity, not all-input arrival at1. This is a theorem boundary, not evidence certifying that every contemporary purported proof is invalid. No verified resolution was located within this bounded search. Search surfaced purported-proof preprints; they were not treated as accepted resolutions merely from titles. Reported packet agreement is only n=3..100,000,000 (99,999,998 inputs); no new computation or trajectory analysis was performed here.

## 5. A097724(m) = A191579(m+1), m >= 0

Audit date: 2026-10-25 UTC. Research only for math-proofs issue #5; no new computation or Lean verification. Exact target: **A097724(m) = A191579(m+1), m >= 0**. For row r and column k, m=r(r+1)/2+k, 0<=k<=r. Offsets are respectively 0 and 1; there is no row reversal in this flattened equality.

### Primary assertion and definitions

- [A097724 NAME](https://oeis.org/A097724/internal), Emeric Deutsch, September 11, 2004: “number of left factors of Motzkin paths without peaks, having length n and endpoint height k.” The NAME specifies a triangle read by rows. Its published FORMULA gives the bivariate generating function G(z)/(1-tzG(z)); G is the RNA/peakless-Motzkin excursion generating function. COMMENTS retain Deléham's January 26, 2014 apparent identity and Bala's June 26, 2025 conjectural Chebyshev connection-coefficient interpretation. The latter is not a published resolution.
- [A191579 COMMENTS](https://oeis.org/A191579/internal), R. J. Mathar, August 1, 2011: **“Is this (apart from offsets) the same as A097724?”** This is the exact authored source assertion. Its NAME describes a “Triangular array related to continued fractions”; author Kenneth J. Ramsey, June 7, 2011. FORMULA defines rows by solving linear equations in the auxiliary array A192062. The prose swaps the array indices relative to its explicit fourth-row EXAMPLE; using that EXAMPLE and the auxiliary formula is essential, not silently taking the prose literally.
- [A192062 FORMULA](https://oeis.org/A192062/internal), Kenneth J. Ramsey, June 21, 2011: the even-row subsequence has initial values 1 and j+2 and obeys **“T(n+2,j) = (j+2)*T(n,j)-T(n-2,j).”** The same section explicitly expands T(2n,j) in T(2k,j-1) with the A191579 row coefficients. This fixes the index orientation and identifies a monic polynomial basis, so the row is uniquely specified.

### Classification and recommendation

**TRIVIAL (routine consequence of published generating-function/recurrence identities), DROP as a substantive first-proof target.** This is a research triage classification under the ticket's routine-consequence rule, **not** a claim that an independently reviewed proof of this exact named pair has been published or that this audit passes programme proof gates. The current OEIS wording remains tentative; no explicit published pair-proof was located in the bounded search below. The basis/series reduction below supplies a concrete reason not to nominate it as a deep or cleanly novel theorem.

### Candidate algebraic justification for reviewer checking

This paragraph is our inference, not a quoted theorem or a new computation. Let P_0(x)=1, P_1(x)=x+2 and P_r(x)=(x+2)P_(r-1)(x)-P_(r-2)(x). A192062 identifies P_r(j)=T(2r+2,j); its defining connection system asks for coefficients of P_r(x+1) in the P_k(x) basis. The monic degrees are distinct, giving uniqueness.

Write w=zG(z). The published quadratic defining G implies

    z(1+w^2) = w(1-z+z^2),  G(0)=1.

Consequently, in formal power series (no numerical approximation),

    G(z) * sum_{k>=0} P_k(x) w^k
      = G(z)/(1-(x+2)w+w^2)
      = 1/(1-(x+3)z+z^2)
      = sum_{r>=0} P_r(x+1) z^r.

The published A097724 generating function makes its kth column z^k G^(k+1). Substituting those columns into the left-hand side gives the required basis expansion. Reviewer tasks are to confirm the source orientation, the quadratic's formal branch, and coefficient extraction. These are short algebra/index checks, not an unbounded search or difficult asymptotic obstruction. Difficulty: **low**, with source-index hygiene the principal pitfall. No claim of novelty follows from the lack of an indexed exact-pair proof.

### Actual bounded literature search

On 2026-10-25, opened all three full OEIS internal pages (COMMENTS, FORMULA, EXAMPLE, CROSSREFS); searched web queries `"A097724" "A191579" proof`, `"A191579" Chebyshev`, `"peakless Motzkin" "connection" Chebyshev`, `"A097724" "Bala" conjecture`, `"Chebyshev" "translation" "Motzkin"`, and A191579 excluding OEIS with collision exclusions. Relevant exact-pair hits returned the OEIS tentative assertions; identifier collisions were discarded, not counted as mathematical evidence.

Inspected the linked primary [Cameron–Nkwanta (2005) paper](https://cs.uwaterloo.ca/journals/JIS/VOL8/Cameron/cameron46.pdf): its Riordan-group framework treats the RNA triangle and pseudo-involutions; no Chebyshev match was found in the searchable PDF text. Inspected [Nkwanta–Tefera (2013)](https://cs.uwaterloo.ca/journals/JIS/VOL16/Nkwanta/nkwanta4.pdf): Proposition 3 gives the RNA generating function quadratic; the located Chebyshev discussion concerns first-kind moment polynomials, not an explicit A191579 equality. Searches of that PDF for A191579 and A097724 returned no matches. These checks establish neither exhaustive literature coverage nor proof absence. The linked 2021 Cameron–Sullivan DOI could not be fetched: HTTP 500 redirect to inaccessible linkinghub.elsevier.com, reported non-retryable; its full text was not inspected and no conclusion is drawn from it.

### Supplied finite evidence and limits

The verified supplied `stated-open-REPORT.md` reports HOLDS-EXTENDED for **m=0..4,504,500**, i.e. rows r=0..3000 and A191579 indices 1..4,504,501. This audit did not rerun those computations. The finite bound is corroboration only, not evidence of published status or an infinite proof.


## What this does NOT show

This is not a proof-completion or novelty certificate. No independent extended computation, new trajectory test, Lean implementation, compilation, or formal verification occurred. No universal equality is inferred from any finite bound. No accepted solution of Collatz is claimed. No explicit published resolution of any exact named pair was located; the routine-consequence classifications are shown as reviewable inferences from cited published definitions and formulas. The totient exact-pair source assertion remains UNVERIFIED. Indexed-page freshness, the failed primary-page fetches and the inaccessible 2021 paper limit this search; no exhaustive or worldwide-open claim is made. No OEIS edit or merge is part of this delivery. Independent review and coordinator publication gates remain mandatory.
