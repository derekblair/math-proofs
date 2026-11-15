# Seam A — static Lean-reachability ranking

**Coverage exception: the supplied file has 300 pairs, not 4,650.**
All 300 supplied pairs are scored exactly once in [scores.json](scores.json).
The remaining 4,350 advertised pairs were not supplied and cannot be scored.
This is a complete pass over the available input, **not a claim to have assessed 4,650 pairs**.
No pairs or missing definition text were invented.

**What the rank means.** This is an ordinal construction-cost screen for stating and
working with the two sequence definitions in Lean. It is not a probability that their
purported identity is true, a proof-difficulty measurement, or a certificate of Mathlib
coverage. A false equation can have very easy definitions. There are
**13 title-level counterexamples among the top 100** under the explicit
assumptions below; exclude these from a proof shortlist unless corrected offsets or
transform semantics change the claim. They retain their construction scores to keep the
four requested axes honest. No Lean code was compiled and no Lean proof is claimed.

**Evidence and scope.** The sole sequence source is [pass3_finalists.json](pass3_finalists.json),
SHA256 `b55fda86d151318d6828c5f9b21249972854c3c92284bbab01a0504537f3aec7` (186,938 bytes).
The reproducible [input audit](input_audit.json) finds 300 unique pairs and 600 endpoint IDs.
The 300 disjoint families contain 1,867 IDs; all within-family unordered pairs would
number 54,946, not 4,650. The extra family members lack titles and cannot substitute for
missing finalist records. Only this directory was used for analysis; no other lane's
outputs or external OEIS/Mathlib content were consulted, and no packages were installed.

The source supplies names/titles (some with formulas), domain tags, one prefix and mining
metadata, not complete OEIS definitions, formula sections, offsets, both prefixes or the
transform implementation. There are
299 prefixes of length 40 and one of length 37. Reported `agree` exceeds stored length
for 277 pairs, and all 51 `abs` records retain negative stored terms. Thus neither the
matches nor their alignments can be reconstructed from `terms`. All shared-formula lists
are empty; both domain lists are empty for 116 pairs. `recorded` and `conjectured` are
identical for all 300 rows (83 true, 217 false), with undocumented meanings. None of these
fields is treated as proof or an independent confirmation. Mining scores, agreement
lengths, and family sizes do not contribute to the ranking.

**Method.** Each of the 300 title pairs was assigned an explicit, reviewable assessment
in [assessments.tsv](assessments.tsv). D, M and F reflect the harder visible side of the
pair; easy vocabulary on one side does not cancel an opaque prerequisite on the other.
These are qualitative judgments, not measured recursive depths or calibrated costs.
Every score record quotes both original titles, preserves its one-based source index,
records uncertainties, and supplies a pair-specific rationale. References that merely
alias a fully described function (such as mu or sigma) are not automatically penalized.
Undefined referenced sequences, omitted Comments/Formula sections, unclear domains and
missing search conventions do lower D. Domain tags are retained for provenance but do
not override the titles: the periodic first title, for example, carries a `graphs` tag.

Each subscore is an integer 0–5, with higher meaning more approachable on that axis.
The deliberately conservative weighting is
**total = 6D + 4M + 3T + 7F**, out of 100. Thus the four maximum contributions are
30, 20, 15 and 35. Finite character has substantial weight so decimal-constant matches
are deprioritized even when their transform is cheap. There is no hidden fifth score.
Weights and bucket boundaries are an explicit prioritization choice, not an empirical
prediction. Nearby scores should be read as ties in practical difficulty.

| Score | D: definition accessibility / self-reference | M: Mathlib-presence **signal only** | F: finite vs analytic character |
| ---: | --- | --- | --- |
| 5 | Explicit nonrecursive formula or fully listed period | Elementary arithmetic and finite-list vocabulary | Discrete integer/rational predicates, counts and finite combinatorics |
| 4 | Bounded count/predicate or ordinary discrete enumeration | Standard number-theory, algebra or digit primitives | Formal coefficients, constructible words or exact algebraic-real expressions |
| 3 | Standard recurrence, finite-state construction or coefficient extraction | Generic combinatorics, recursion, series or real-function scaffolding | Mixed analytic/coefficient or specialized algebraic/geometric interface |
| 2 | Missing external dependency, convention, domain or search bound | Specialist or weakly specified primitive | Transcendental comparisons, constants, continued fractions or analytic functions |
| 1 | Greedy/global extension, nested self-reference or opaque specialist object | Mostly opaque names and little visible construction | Primarily analytic/non-Archimedean construction without a visible finite reduction (unused here) |
| 0 | Major unspecified growth dependency or unresolved totality/nontermination | No usable primitive signal | Decimal constant digits, including signed sums of those digits |

M is a vocabulary/prerequisite proxy. Polynomial, factorial, prime, partition,
continued-fraction and similar terms identify *possible* library interfaces; no exact
declaration, import, theorem coverage or absence was checked. The specialized-object
flags mean “investigate this prerequisite”; they do **not** assert that Monster series,
class groups, Kolakoski, Collatz or any other named object is unformalized. The JSON
uses `known_unformalized: null` and `exact_recursion_depth: null` rather than fabricating
answers. Finite Goldbach decomposition **counts** and finite no-three-in-line maxima
are distinguished from choosing a least Goldbach decomposition without an existence
or default convention. A stopping-time function may have a noncomputable classical
definition; its low D score flags executable construction and proof obligations, not
logical impossibility. A Riesel equivalence might avoid settling every prime search.

| Variant | Count | T | Assumed cost interpretation, not a verified implementation |
| --- | ---: | ---: | --- |
| raw | 129 | 5 | Identity/no transformation label |
| drop1 | 65 | 4 | Cheap one-term deletion; affected side and offsets unspecified |
| drop2 | 44 | 4 | Cheap two-term deletion; affected side and offsets unspecified |
| abs | 51 | 4 | Pointwise absolute value; cheap but loses sign information |
| stripz | 11 | 1 | Assumed deletion of zeros; requires reindexing and a nonzero-productivity argument |

No arithmetic-transform variants occur in this input. For future data, differences,
partial sums and arithmetic combinations would require additional recurrence/index
proofs and a separately documented T=2 or T=3 policy; none was silently assigned here.
Binary zero filtering can collapse all surviving terms to 1, so `stripz` is particularly
weak evidence of a substantive identity. Integer decimal/base digit predicates remain
discrete; only digits of fixed constants (or their transforms) receive F=0. Formal
generating-function coefficients are not mistaken for decimal expansions. Digit-length
formulas have a discrete route despite logarithm notation; the A000523 definition of
Log2 is absent and is flagged separately. P-adic continued-fraction convergent numerators
can use finite rational recurrences once partial quotients are known, so their F score
is not reduced solely because the title says p-adic. Finite groups/modules and class
numbers retain a discrete F score, with specialized prerequisites penalized in D/M.

The deterministic sort is descending total, then positive title-level sanity check,
unchecked, counterexample (only to break equal totals), then descending D, M, F, T,
then lexical IDs and variant. It never uses the mining score. The top/bottom tables show
global ranks; the bottom 50 are displayed in rank order 251–300. The middle 150 are
fully available in `scores.json`.

**Computed sanity checks and interpretation.** [sanity_checks.py](sanity_checks.py)
reproduces 29 exact checks in [sanity_checks.json](sanity_checks.json):
7 positive structural checks and
22 counterexamples, all conditional on the
stated title interpretations. The other 271 pairs are unchecked,
not presumed true. This is a targeted sanity sample, not exhaustive identity testing.
The check JSON gives operands, computed results, full source titles and assumptions.

For periodic words, checking every residue of the least common period establishes the
displayed pointwise absolute-value identity **when origins align**. For the cyclotomic
checks, “inverse” means formal reciprocal at x=0: exact integer polynomial division
constructs the cyclotomic polynomial and a convolution recurrence checks its inverse
coefficients. Any positive polynomial-substitution check is likewise conditional on
that interpretation and aligned powers. These are mathematical/computational arguments,
not verified Mathlib lemmas or Lean proofs.

For the rational floors, a mismatch at n equal to the larger numerator survives
deleting one or two initial terms **from both n=1-indexed sequences**; it does not
certify what an unavailable asymmetric `dropN` implementation does. Other same-argument
witnesses do not infer omitted OEIS offsets. The finite divisor-set comparison assumes
positive divisors without padding. These caveats appear in every underlying check.

The positive-check candidates to review first, independently of construction rank, are:
A057079/A131556 (rank 1, 97/100); A103368/A166446 (rank 2, 97/100); A134668/A309970 (rank 3, 97/100); A014018/A014027 (rank 135, 74/100); A014036/A014063 (rank 136, 74/100); A014474/A014939 (rank 137, 74/100); A014534/A015059 (rank 138, 74/100).
All six constant-digit pairs receive F=0: input 20: rank 299, 38/100; input 170: rank 261, 58/100; input 227: rank 300, 32/100; input 233: rank 272, 54/100; input 259: rank 271, 54/100; input 262: rank 245, 62/100.

| Input row | Pair | Construction rank | Exact check result (subject to assumptions above) |
| ---: | --- | ---: | --- |
| 21 | A000005 / A179941 | 57 | same n=101: 2 versus 0 |
| 64 | A033402 / A033403 | 11 | same n=83: 0 versus 1; common-drop assumption |
| 68 | A033416 / A033417 | 13 | same n=97: 0 versus 1; common-drop assumption |
| 73 | A057079 / A131556 | 1 | absolute periods agree at all 6 residues; aligned origins |
| 80 | A033408 / A033409 | 12 | same n=89: 0 versus 1; common-drop assumption |
| 82 | A028903 / A081599 | 14 | same n=100: 64 versus 80 |
| 99 | A033392 / A033393 | 9 | same n=73: 0 versus 1; common-drop assumption |
| 102 | A054898 / A343609 | 15 | same n=81: 10 versus 9 |
| 118 | A103368 / A166446 | 2 | absolute periods agree at all 12 residues; aligned origins |
| 119 | A134668 / A309970 | 3 | absolute periods agree at all 12 residues; aligned origins |
| 123 | A033398 / A033399 | 10 | same n=79: 0 versus 1; common-drop assumption |
| 167 | A033390 / A033391 | 8 | same n=71: 0 versus 1; common-drop assumption |
| 173 | A033380 / A033381 | 6 | same n=61: 0 versus 1; common-drop assumption |
| 189 | A033386 / A033387 | 7 | same n=67: 0 versus 1; common-drop assumption |
| 195 | A033378 / A033379 | 5 | same n=59: 0 versus 1; common-drop assumption |
| 228 | A015790 / A015816 | 110 | reciprocal coefficient at degree 137: -1 versus 0 |
| 229 | A015862 / A016168 | 114 | reciprocal coefficient at degree 109: -1 versus 0 |
| 231 | A015912 / A016176 | 115 | reciprocal coefficient at degree 173: -1 versus 0 |
| 239 | A015854 / A016124 | 113 | reciprocal coefficient at degree 123: 1 versus 0 |
| 276 | A003592 / A192716 | 58 | 100 fixed divisors versus at least 101 distinct smooth numbers |
| 286 | A015813 / A016077 | 111 | reciprocal coefficient at degree 82: 1 versus 0 |
| 293 | A014474 / A014939 | 137 | Phi_(2m)(x)=Phi_m(-x) checked at all 241 polynomial coefficients; formal inversion gives absolute coefficient equality |
| 294 | A014534 / A015059 | 138 | Phi_(2m)(x)=Phi_m(-x) checked at all 241 polynomial coefficients; formal inversion gives absolute coefficient equality |
| 295 | A015918 / A016056 | 116 | reciprocal coefficient at degree 83: -1 versus 0 |
| 296 | A015836 / A015962 | 112 | reciprocal coefficient at degree 87: 1 versus 0 |
| 297 | A016141 / A016245 | 117 | reciprocal coefficient at degree 82: 1 versus 0 |
| 298 | A014036 / A014063 | 136 | Phi_(2m)(x)=Phi_m(-x) checked at all 19 polynomial coefficients; formal inversion gives absolute coefficient equality |
| 299 | A015752 / A015878 | 109 | reciprocal coefficient at degree 83: 1 versus 0 |
| 300 | A014018 / A014027 | 135 | Phi_(2m)(x)=Phi_m(-x) checked at all 7 polynomial coefficients; formal inversion gives absolute coefficient equality |

**Score distributions across all 300 supplied pairs.**

| Subscore | 0 | 1 | 2 | 3 | 4 | 5 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| definition_accessibility | 7 | 35 | 111 | 49 | 70 | 28 |
| mathlib_presence_signal | 0 | 24 | 36 | 105 | 116 | 19 |
| transform_simplicity | 0 | 11 | 0 | 0 | 160 | 129 |
| finite_character | 6 | 0 | 21 | 7 | 72 | 194 |

**Top 100 by static construction score.** Counterexample labels are substantive
exclusions from an identity-proof shortlist under the stated assumptions, even when
the definitions earn a high score. D/M/T/F uses the rubric above.

| Rank | Input row | Pair | Variant | D/M/T/F | Total /100 | Per-pair rationale |
| ---: | ---: | --- | --- | --- | ---: | --- |
| 1 | 73 | A057079 / A131556 | abs | 5/5/4/5 | 97 | Both periods are fully listed; absolute values can be compared over one common period. **POSITIVE, conditional:** absolute periods agree at all 6 residues; aligned origins. |
| 2 | 118 | A103368 / A166446 | abs | 5/5/4/5 | 97 | Both periods are fully listed; absolute values can be checked over their common period of length 12. **POSITIVE, conditional:** absolute periods agree at all 12 residues; aligned origins. |
| 3 | 119 | A134668 / A309970 | abs | 5/5/4/5 | 97 | Both periods are fully listed; absolute values can be checked over their common period of length 12. **POSITIVE, conditional:** absolute periods agree at all 12 residues; aligned origins. |
| 4 | 201 | A022998 / A257088 | drop1 | 5/5/4/5 | 97 | Both titles give explicit parity-based formulas with a stated exception at zero. |
| 5 | 195 | A033378 / A033379 | drop2 | 5/5/4/5 | 97 | Both titles are explicit rational floors with constants 58 and 59. **COUNTEREXAMPLE, conditional:** same n=59: 0 versus 1; common-drop assumption. |
| 6 | 173 | A033380 / A033381 | drop1 | 5/5/4/5 | 97 | Both titles are explicit rational floors with constants 60 and 61. **COUNTEREXAMPLE, conditional:** same n=61: 0 versus 1; common-drop assumption. |
| 7 | 189 | A033386 / A033387 | drop1 | 5/5/4/5 | 97 | Both titles are explicit rational floors with constants 66 and 67. **COUNTEREXAMPLE, conditional:** same n=67: 0 versus 1; common-drop assumption. |
| 8 | 167 | A033390 / A033391 | drop1 | 5/5/4/5 | 97 | Both titles are explicit rational floors with constants 70 and 71. **COUNTEREXAMPLE, conditional:** same n=71: 0 versus 1; common-drop assumption. |
| 9 | 99 | A033392 / A033393 | drop1 | 5/5/4/5 | 97 | Both titles are explicit rational floors with constants 72 and 73. **COUNTEREXAMPLE, conditional:** same n=73: 0 versus 1; common-drop assumption. |
| 10 | 123 | A033398 / A033399 | drop1 | 5/5/4/5 | 97 | Both titles are explicit rational floors with constants 78 and 79. **COUNTEREXAMPLE, conditional:** same n=79: 0 versus 1; common-drop assumption. |
| 11 | 64 | A033402 / A033403 | drop2 | 5/5/4/5 | 97 | Both titles are explicit rational floors with constants 82 and 83; shared initial quotients need not persist. **COUNTEREXAMPLE, conditional:** same n=83: 0 versus 1; common-drop assumption. |
| 12 | 80 | A033408 / A033409 | drop1 | 5/5/4/5 | 97 | Both titles are explicit rational floors with constants 88 and 89. **COUNTEREXAMPLE, conditional:** same n=89: 0 versus 1; common-drop assumption. |
| 13 | 68 | A033416 / A033417 | drop1 | 5/5/4/5 | 97 | Both titles are explicit rational floors with constants 96 and 97. **COUNTEREXAMPLE, conditional:** same n=97: 0 versus 1; common-drop assumption. |
| 14 | 82 | A028903 / A081599 | raw | 5/4/5/5 | 96 | Whole-digit base reinterpretation and a single quotient/remainder substitution are both explicit but have different scope. **COUNTEREXAMPLE, conditional:** same n=100: 64 versus 80. |
| 15 | 102 | A054898 / A343609 | raw | 4/5/5/5 | 94 | An eventually-zero sum of integer quotients meets its first summand only. **COUNTEREXAMPLE, conditional:** same n=81: 10 versus 9. |
| 16 | 207 | A054897 / A132292 | drop1 | 4/5/4/5 | 91 | An eventually-zero sum of base-8 quotients meets a single shifted quotient formula. |
| 17 | 95 | A065475 / A114637 | drop1 | 4/5/4/5 | 91 | Both sets exclude finitely many natural numbers; starting-index and natural/nonnegative conventions determine alignment. |
| 18 | 181 | A225530 / A384710 | drop1 | 4/5/4/5 | 91 | Both sides are bounded gcd counts; i+j=n permits a standard arithmetic comparison once the n=0 boundary is fixed. |
| 19 | 182 | A002266 / A301506 | raw | 4/4/5/5 | 90 | Repeated integers meet bounded counting by largest prime factor; finite definitions alone do not imply equal counts. |
| 20 | 246 | A007520 / A294912 | raw | 4/4/5/5 | 90 | Prime residue classes meet explicit modular-exponential conditions; pseudoprime-style coincidences need separate truth checks. |
| 21 | 226 | A007642 / A353004 | raw | 4/4/5/5 | 90 | Both enumerate integers satisfying a polynomial primality predicate; composite and semiprime are different conditions. |
| 22 | 55 | A007959 / A102492 | raw | 4/4/5/5 | 90 | Digit permutations and base-20 admissibility are finite integer predicates. |
| 23 | 257 | A011542 / A260688 | raw | 4/4/5/5 | 90 | Both coin-change constructions have finite search bounds; their denomination sets and optimization rules differ. |
| 24 | 113 | A022336 / A025655 | raw | 4/4/5/5 | 90 | Both sequences rank products of powers of two fixed integer bases and read an exponent; enumeration order matters. |
| 25 | 112 | A022337 / A025687 | raw | 4/4/5/5 | 90 | Both sequences rank products of powers of two fixed integer bases and read an exponent; enumeration order matters. |
| 26 | 107 | A031487 / A047422 | raw | 4/4/5/5 | 90 | Finite base-8 digit counts meet residue-class enumeration. |
| 27 | 218 | A032945 / A236402 | raw | 4/4/5/5 | 90 | Both are finite base-10 digit predicates, including adjacent-pair sums and substring tests. |
| 28 | 137 | A037840 / A037894 | raw | 4/4/5/5 | 90 | Finite base-8 digit sums compare adjacent differences with reversal displacement. |
| 29 | 60 | A037841 / A037895 | raw | 4/4/5/5 | 90 | Finite base-9 digit sums compare adjacent differences with reversal displacement. |
| 30 | 141 | A037845 / A037881 | raw | 4/4/5/5 | 90 | Finite base-4 digit sums compare adjacent decreases with sorted displacement. |
| 31 | 74 | A037848 / A037884 | raw | 4/4/5/5 | 90 | Finite base-7 digit sums compare adjacent decreases with sorted displacement. |
| 32 | 34 | A037849 / A037885 | raw | 4/4/5/5 | 90 | Both sides use finite base-8 digit lists and sorting; adjacent variation and sorted displacement are different definitions. |
| 33 | 180 | A037854 / A037872 | raw | 4/4/5/5 | 90 | Finite base-4 digit sums compare adjacent increases with reverse-sorted displacement. |
| 34 | 77 | A037858 / A037876 | raw | 4/4/5/5 | 90 | Finite base-8 digit sums compare adjacent increases with reverse-sorted displacement. |
| 35 | 237 | A039055 / A047504 | raw | 4/4/5/5 | 90 | Finite base-8 digit counts meet residue-class enumeration. |
| 36 | 256 | A039244 / A047263 | raw | 4/4/5/5 | 90 | Finite base-12 digit counts meet residue-class enumeration. |
| 37 | 56 | A039259 / A047226 | raw | 4/4/5/5 | 90 | Base-12 digit counts meet congruence enumeration with an explicit floor formula. |
| 38 | 39 | A043288 / A353786 | raw | 4/4/5/5 | 90 | Finite base-14 run lengths meet a bounded divisibility count for numbers of the form 2^k-1. |
| 39 | 2 | A052382 / A209931 | raw | 4/4/5/5 | 90 | Both sides are integer digit/divisor predicates; decimal here describes integers, not a constant's digit stream. |
| 40 | 249 | A053669 / A236454 | raw | 4/4/5/5 | 90 | For positive n, a prime divisor of n+1 cannot divide n, and n^2+1 cannot divide n^2; these bound both least-excluded-divisor searches. |
| 41 | 72 | A061217 / A102684 | raw | 4/4/5/5 | 90 | Both count digits in finite ranges or concatenations; no real decimal constant is involved. |
| 42 | 183 | A072495 / A246422 | raw | 4/4/5/5 | 90 | Both are integer suffix/power congruence predicates with finite digit lengths. |
| 43 | 247 | A072670 / A333750 | raw | 4/4/5/5 | 90 | Both are bounded integer representation or prime-power divisor counts; sqrt(n) can use an integer-square bound. |
| 44 | 248 | A081676 / A167185 | raw | 4/4/5/5 | 90 | Both take bounded maxima of perfect-power or nonprime-prime-power sets; small-input empty cases need conventions. |
| 45 | 8 | A085971 / A387421 | raw | 4/4/5/5 | 90 | Prime powers, divisor sums and the powerful part are named; prime-factor decomposition is the likely discrete construction. |
| 46 | 241 | A091010 / A324849 | raw | 4/4/5/5 | 90 | Both are bounded divisor or prime-index divisibility predicates on integers. |
| 47 | 258 | A122258 / A332220 | raw | 4/4/5/5 | 90 | Both count prime subclasses below n; the Mersenne-exponent sequence is named, so bounded prime tests are visible. |
| 48 | 255 | A136809 / A136813 | raw | 4/4/5/5 | 90 | Both finite digit predicates constrain k and k^2 but allow different digit alphabets. |
| 49 | 243 | A136874 / A136881 | raw | 4/4/5/5 | 90 | Both finite digit predicates constrain k and k^2 but allow different digit alphabets. |
| 50 | 10 | A193304 / A240370 | raw | 4/4/5/5 | 90 | Squarefree factorization meets a finite universal predicate on residues modulo n. |
| 51 | 61 | A273404 / A281976 | raw | 4/4/5/5 | 90 | Both are bounded sums-of-four-squares counts; the extra square condition is an explicit predicate difference. |
| 52 | 101 | A273432 / A284343 | raw | 4/4/5/5 | 90 | Both are bounded four-square counts, but a cube condition is replaced by zero-or-power-of-eight. |
| 53 | 250 | A291624 / A291635 | raw | 4/4/5/5 | 90 | Both count bounded four-square representations with prime constraints; the extra p+10 predicate can change the result. |
| 54 | 66 | A300360 / A300396 | raw | 4/4/5/5 | 90 | Both are bounded Diophantine counts with explicit square and power constraints. |
| 55 | 48 | A308621 / A308623 | raw | 4/4/5/5 | 90 | Both count bounded nonnegative representations by triangular numbers and powers; differing exponent patterns need comparison. |
| 56 | 200 | A352259 / A352286 | raw | 4/4/5/5 | 90 | Both count bounded nonnegative polynomial representations; the w^6 versus w in {0,1} distinction changes the search set. |
| 57 | 21 | A000005 / A179941 | raw | 4/4/5/5 | 90 | Divisor counting and a fixed 100 by 100 multiplication table are finite definitions with different scopes. **COUNTEREXAMPLE, conditional:** same n=101: 2 versus 0. |
| 58 | 276 | A003592 / A192716 | raw | 4/4/5/5 | 90 | One side enumerates an infinite multiplicative semigroup; the other is the finite divisor set of 10^9. **COUNTEREXAMPLE, conditional:** 100 fixed divisors versus at least 101 distinct smooth numbers. |
| 59 | 133 | A184580 / A184622 | raw | 5/4/5/4 | 89 | Both titles give explicit algebraic-root floor formulas with different rational intercepts. |
| 60 | 54 | A184583 / A184735 | raw | 5/4/5/4 | 89 | Both titles give exact algebraic-root floor formulas; complement references are redundant to those formulas. |
| 61 | 209 | A187976 / A197879 | raw | 5/4/5/4 | 89 | Both titles are explicit floors involving sqrt(2) or sqrt(8) and integer parity. |
| 62 | 19 | A001222 / A086436 | drop1 | 4/4/4/5 | 87 | Prime multiplicity and maximum factorization length are finite arithmetic constructions; the second title explicitly names bigomega. |
| 63 | 267 | A007875 / A339887 | drop1 | 4/4/4/5 | 87 | Both are bounded factorization counts using coprimality, primes and squarefree semiprimes. |
| 64 | 44 | A032797 / A039161 | drop1 | 4/4/4/5 | 87 | A finite product divisibility test meets base-11 digit counting; both predicates are discrete. |
| 65 | 78 | A037860 / A037878 | drop2 | 4/4/4/5 | 87 | Finite base-10 digit sums compare adjacent increases with reverse-sorted displacement. |
| 66 | 171 | A045331 / A191868 | drop2 | 4/4/4/5 | 87 | Prime congruence enumeration meets bounded divisor product, sum and count arithmetic. |
| 67 | 42 | A048669 / A049298 | drop2 | 4/4/4/5 | 87 | Both titles refer to maximal gaps in reduced residue systems; wraparound and the dRSSS spelling require clarification from definitions. |
| 68 | 23 | A053139 / A127705 | drop1 | 4/4/4/5 | 87 | Totient-style phi and conventional mu notation with finite divisor sums signal arithmetic; mu is identified only by A008683, so notation interpretation remains an assumption. |
| 69 | 121 | A068344 / A323377 | abs | 4/4/4/5 | 87 | A signed comparison array meets prime-indexed Kronecker symbols; antidiagonal orientations need alignment. |
| 70 | 150 | A104124 / A359549 | drop2 | 4/4/4/5 | 87 | A bounded factor representation count meets a squarefree-square indicator. |
| 71 | 115 | A171893 / A355497 | drop2 | 4/4/4/5 | 87 | A finite-exclusion set meets an integer-root test for a quadratic built from digits. |
| 72 | 67 | A255270 / A262438 | drop1 | 4/4/4/5 | 87 | Integer fourth-root extraction and hexadecimal digit length admit finite integer definitions. |
| 73 | 40 | A302777 / A355937 | drop1 | 4/4/4/5 | 87 | Both are prime-power/divisor-count indicators; noncomposite needs an explicit convention, especially at 1. |
| 74 | 252 | A322075 / A354353 | drop1 | 4/4/4/5 | 87 | Finite squarefree factorization counts meet an explicit indicator; multiplicities and factor order require conventions. |
| 75 | 6 | A322437 / A322438 | drop1 | 4/4/4/5 | 87 | Both sides count bounded factorizations; divides versus properly divides changes the predicate. |
| 76 | 46 | A343639 / A380706 | drop1 | 4/4/4/5 | 87 | A digit-sum quotient meets rank among integers sharing a digit set; rank and leading-zero conventions matter. |
| 77 | 275 | A161036 / A161087 | raw | 4/3/5/5 | 86 | Both count finite restricted partitions with different allowed parts and the same threshold 12. |
| 78 | 230 | A161037 / A161088 | raw | 4/3/5/5 | 86 | Both count finite restricted partitions with different allowed parts and the same threshold 13. |
| 79 | 36 | A033324 / A329678 | drop2 | 4/3/4/5 | 83 | A rational floor meets bounded Motzkin path enumeration with local step restrictions. |
| 80 | 194 | A161038 / A161089 | drop1 | 4/3/4/5 | 83 | Both count finite restricted partitions, with different allowed part sets and the same multiplicity threshold. |
| 81 | 281 | A161076 / A161115 | drop1 | 4/3/4/5 | 83 | Both count finite restricted partitions with different part sets and a common multiplicity threshold. |
| 82 | 130 | A163300 / A272651 | drop1 | 4/3/4/5 | 83 | The no-three-in-line maximum is over a finite grid, so the definition is bounded despite difficult possible identities. **Specialist/research review; formalization status unknown.** |
| 83 | 93 | A077814 / A131728 | stripz | 4/5/1/5 | 82 | A bounded modular count meets explicit residue-class formulas; zero filtering introduces reindexing. |
| 84 | 197 | A003961 / A045965 | drop1 | 3/4/4/5 | 81 | Both give prime-index substitution under factorization; the exceptional value at 1 and sequence offsets matter. |
| 85 | 142 | A065620 / A104895 | abs | 3/4/4/5 | 81 | Both binary-index recurrences explicitly reduce to smaller indices with a supplied initial value. |
| 86 | 75 | A128999 / A168092 | drop1 | 3/4/4/5 | 81 | A one-step parity recurrence meets a bounded integer-interval count. |
| 87 | 89 | A209635 / A355689 | abs | 3/4/4/5 | 81 | Moebius on the odd part meets a Dirichlet inverse of an explicitly described arithmetic indicator. |
| 88 | 154 | A061570 / A292661 | drop2 | 4/4/4/4 | 80 | An explicit linear formula meets ranking among algebraic-root multiples, requiring exact real order comparisons. |
| 89 | 3 | A230799 / A237353 | drop1 | 4/4/4/4 | 80 | Cyclotomic coefficient counting versus a minimum of prime-factor counts; the admissible g,h domain is unstated. |
| 90 | 192 | A046584 / A046585 | raw | 3/3/5/5 | 80 | Both filter rational Pascal-triangle entries; triangle and numerator/denominator ordering conventions need construction. |
| 91 | 162 | A001918 / A268616 | raw | 2/4/5/5 | 78 | Least primitive-root searches require existence bounds, especially after imposing squarefreeness. |
| 92 | 22 | A002375 / A240708 | raw | 2/4/5/5 | 78 | Goldbach decomposition counting is bounded; the other summand set A240699 is unspecified, not licensed by the conjecture name. |
| 93 | 16 | A004216 / A297038 | raw | 2/4/5/5 | 78 | Integer logarithmic digit length has a discrete route; the second title leaves the meaning of pieces to Comments. |
| 94 | 240 | A007814 / A265330 | raw | 2/4/5/5 | 78 | Integer valuation is explicit; bijective-base reversal and its row-index reference need missing definitions. |
| 95 | 210 | A055032 / A323072 | raw | 2/4/5/5 | 78 | The power-sum denominator is explicit; its gcd expression still depends on unexplained A060681 and A323071. |
| 96 | 290 | A092028 / A092067 | raw | 2/4/5/5 | 78 | Both seek least divisors of variable-exponent expressions; the starting domain and no-solution conventions need specification. |
| 97 | 18 | A123240 / A131181 | raw | 2/4/5/5 | 78 | Divisor and Fibonacci predicates are visible; the complement description relies on an undefined A026416. |
| 98 | 51 | A171611 / A240712 | raw | 2/4/5/5 | 78 | Prime-pair counting is finite; the second summand set A240710 is not defined here. |
| 99 | 100 | A171970 / A172475 | stripz | 5/4/1/4 | 77 | Equilateral-triangle height and floor(n*sqrt(3)/2) share an elementary exact geometric formula. |
| 100 | 94 | A023120 / A167970 | raw | 3/4/5/4 | 77 | Both are orderings generated by algebraic slopes; enumerating the infinite sorted grid needs a bounded-prefix argument. |

**Bottom 50 sanity check.** These have the lowest construction scores among the
supplied 300; a low score can reflect missing evidence rather than inherent difficulty.

| Rank | Input row | Pair | Variant | D/M/T/F | Total /100 | Per-pair rationale |
| ---: | ---: | --- | --- | --- | ---: | --- |
| 251 | 178 | A030124 / A061578 | drop1 | 1/2/4/5 | 61 | Hofstadter terminology signals a potentially self-referential dependency, but neither source sequence is defined here. **Specialist/research review; formalization status unknown.** |
| 252 | 37 | A088568 / A294448 | abs | 1/2/4/5 | 61 | Both sides depend on the self-generating Kolakoski sequence; its definition and discrepancy convention are absent. **Specialist/research review; formalization status unknown.** |
| 253 | 125 | A317092 / A349810 | raw | 2/3/5/3 | 60 | Prime multiplicity predicates meet a cubic-field condition; the intended meaning of purely real requires clarification. |
| 254 | 216 | A113431 / A116915 | abs | 2/2/4/4 | 60 | Both are Ramanujan theta coefficient expressions with no formal definitions of the specialized functions supplied. |
| 255 | 12 | A118828 / A118831 | abs | 2/2/4/4 | 60 | Both p-adic continued fractions depend on absent entries; rational convergent numerators have a finite-recurrence route once partial quotients are supplied. **Specialist/research review; formalization status unknown.** |
| 256 | 53 | A119910 / A229216 | abs | 2/2/4/4 | 60 | The period is explicit, while the Koch snowflake traversal is only named despite specified direction vectors. |
| 257 | 132 | A143987 / A144185 | abs | 2/2/4/4 | 60 | Eigentriangle and named triangle descriptions omit entry rules; row sums alone do not define a triangle. |
| 258 | 85 | A203568 / A257628 | abs | 2/2/4/4 | 60 | Unexplained sequence differences meet Ramanujan theta coefficients; required definitions are absent. |
| 259 | 279 | A022931 / A373217 | raw | 3/3/5/2 | 59 | Counting exponential powers between Pi powers needs real inequalities; the other side has locally finite formal coefficients. |
| 260 | 269 | A046069 / A108129 | drop2 | 0/3/4/5 | 59 | Riesel least-prime searches include an explicit no-solution default; computability is unclear, though an equivalence need not settle every search. **Specialist/research review; formalization status unknown.** |
| 261 | 170 | A188485 / A188934 | drop2 | 5/4/4/0 | 58 | Both sequences are decimal digits of algebraic constants; shared tails concern representation rather than equality of constants. |
| 262 | 185 | A306384 / A323832 | raw | 0/2/5/5 | 58 | Both are hitting-time definitions with never-reached defaults and omitted digit-deletion maps. **Specialist/research review; formalization status unknown.** |
| 263 | 65 | A070563 / A374053 | raw | 1/2/5/4 | 57 | Ramanujan tau is a specialist modular-form coefficient object; the other side supplies a multiplicative rule. **Specialist/research review; formalization status unknown.** |
| 264 | 49 | A130259 / A363832 | drop1 | 3/3/4/2 | 56 | A Fibonacci index bound meets a greedy representation in base e; real digit-boundary reasoning is required. |
| 265 | 166 | A158333 / A246411 | drop2 | 3/3/4/2 | 56 | Integer power digit transitions meet trigonometric inequalities on integer arguments. |
| 266 | 271 | A057362 / A371627 | stripz | 2/3/1/4 | 55 | A rational floor meets an algebraic-slope optimization with no tie or admissible-y convention supplied. |
| 267 | 213 | A125122 / A144608 | stripz | 2/3/1/4 | 55 | A rational-slope Christoffel word meets differences of an undefined source, then zero filtering. |
| 268 | 90 | A189664 / A284817 | stripz | 2/3/1/4 | 55 | One morphism is explicit; the other side depends on unexplained A284776 before zero filtering. |
| 269 | 164 | A061641 / A177729 | drop2 | 0/2/4/5 | 55 | Both predicates depend on Collatz orbits, with pure-number terminology and unbounded orbit exclusion unresolved. **Specialist/research review; formalization status unknown.** |
| 270 | 172 | A112695 / A139399 | drop2 | 0/2/4/5 | 55 | Both are Collatz stopping times; existence or a nontermination convention is not supplied. **Specialist/research review; formalization status unknown.** |
| 271 | 259 | A113209 / A154542 | drop1 | 5/3/4/0 | 54 | Both are decimal digits of logarithmic constants; stripping a leading digit concerns representation, not direct constant equality. |
| 272 | 233 | A123092 / A222068 | drop1 | 5/3/4/0 | 54 | Both give explicit Pi-based constant formulas followed by decimal extraction; the infinite-sum presentation also supplies its closed form. |
| 273 | 280 | A329962 / A329987 | raw | 2/3/5/2 | 53 | A trigonometric root-selected slope meets an implicitly defined exponential slope; root selection and real comparisons need proof. |
| 274 | 222 | A111495 / A111499 | drop2 | 3/2/4/2 | 52 | Prime counting is finite, but logarithmic-integral Li comparisons introduce analytic obligations and conventions. |
| 275 | 135 | A224067 / A224165 | drop1 | 0/1/4/5 | 51 | Complex Collatz hitting times with never-hits defaults require a specified map and treatment of nontermination. **Specialist/research review; formalization status unknown.** |
| 276 | 219 | A300403 / A356852 | drop2 | 0/1/4/5 | 51 | SSCG is an undefined specialist growth object in a least-index search; the other finite extremal basis problem is also nontrivial. **Specialist/research review; formalization status unknown.** |
| 277 | 157 | A019425 / A265722 | drop2 | 2/3/4/2 | 50 | Continued fractions of tan(1/2) meet ON-cell counting for Rule 1; both the transcendental input and missing observation window need review. |
| 278 | 204 | A120701 / A127451 | drop1 | 2/3/4/2 | 50 | Circle-packing counts meet a transcendental Beatty slope involving e and Pi powers. |
| 279 | 143 | A195182 / A226190 | drop1 | 2/3/4/2 | 50 | A floor involving e meets an unbounded harmonic-threshold search against log(n), with boundary conventions missing. |
| 280 | 193 | A058526 / A112153 | abs | 1/1/4/4 | 50 | Two named Monster McKay-Thompson series lack defining coefficient formulas. **Specialist/research review; formalization status unknown.** |
| 281 | 179 | A058544 / A112156 | abs | 1/1/4/4 | 50 | Two named Monster McKay-Thompson series lack defining coefficient formulas. **Specialist/research review; formalization status unknown.** |
| 282 | 261 | A058589 / A112164 | abs | 1/1/4/4 | 50 | Two named Monster McKay-Thompson series lack defining coefficient formulas. **Specialist/research review; formalization status unknown.** |
| 283 | 120 | A058648 / A112174 | abs | 1/1/4/4 | 50 | Two named Monster McKay-Thompson series lack defining coefficient formulas. **Specialist/research review; formalization status unknown.** |
| 284 | 110 | A058650 / A112177 | abs | 1/1/4/4 | 50 | Two named Monster McKay-Thompson series lack defining coefficient formulas. **Specialist/research review; formalization status unknown.** |
| 285 | 45 | A093085 / A112171 | abs | 1/1/4/4 | 50 | Ramanujan theta coefficients meet a named Monster series; neither specialized construction is supplied. **Specialist/research review; formalization status unknown.** |
| 286 | 69 | A112166 / A112167 | abs | 1/1/4/4 | 50 | Two named Monster McKay-Thompson series lack defining coefficient formulas. **Specialist/research review; formalization status unknown.** |
| 287 | 122 | A112197 / A112198 | abs | 1/1/4/4 | 50 | Two named Monster McKay-Thompson series lack defining coefficient formulas. **Specialist/research review; formalization status unknown.** |
| 288 | 70 | A112201 / A112203 | abs | 1/1/4/4 | 50 | Two named Monster McKay-Thompson series lack defining coefficient formulas. **Specialist/research review; formalization status unknown.** |
| 289 | 43 | A112207 / A112208 | abs | 1/1/4/4 | 50 | Both objects are named Monster McKay-Thompson coefficient series with no construction supplied. **Specialist/research review; formalization status unknown.** |
| 290 | 191 | A059566 / A329826 | raw | 2/2/5/2 | 49 | A Beatty slope invokes an unexplained gamma constant and exponentials; the other is an algebraic root. |
| 291 | 138 | A064994 / A329993 | raw | 2/2/5/2 | 49 | Beatty floors depend on Khinchin's constant and an implicitly defined exponential root; definitions and real inequalities are needed. **Specialist/research review; formalization status unknown.** |
| 292 | 236 | A064995 / A329994 | raw | 2/2/5/2 | 49 | A named Khintchin constant and an implicitly defined exponential root feed Beatty sequences. **Specialist/research review; formalization status unknown.** |
| 293 | 81 | A097509 / A245219 | raw | 2/2/5/2 | 49 | An algebraic-root multiplicity meets a continued fraction of a supremum defined through another sequence and recursion. |
| 294 | 165 | A000934 / A213443 | drop1 | 1/2/4/3 | 47 | Surface chromatic numbers require a substantial topological graph framework; no Heawood formula is supplied. **Specialist/research review; formalization status unknown.** |
| 295 | 24 | A211665 / A276502 | drop2 | 2/2/4/2 | 46 | Iterated real logarithms meet a least-k divisibility search in an undefined A045876. |
| 296 | 291 | A115573 / A115579 | raw | 1/1/5/3 | 46 | Betti numbers of Weyl-group elements in an external ordering require substantial specialized definitions. **Specialist/research review; formalization status unknown.** |
| 297 | 52 | A115576 / A115581 | raw | 1/1/5/3 | 46 | Betti numbers of Weyl-group elements in an external ordering require substantial specialized definitions. **Specialist/research review; formalization status unknown.** |
| 298 | 7 | A071936 / A355437 | abs | 1/2/4/2 | 40 | Kronecker symbols are explicit but Maslanka's constant A(n) has no defining formula here. **Specialist/research review; formalization status unknown.** |
| 299 | 20 | A069159 / A306389 | abs | 3/2/4/0 | 38 | Both titles sum signed decimal digits of Pi; finite sums do not remove the constant-digit dependency. |
| 300 | 227 | A143280 / A227569 | drop1 | 2/2/4/0 | 32 | Both are decimal constant expansions; one uses an infinite sum and the other an undefined extremal function from Comments. |

**Reproduction and validation.** From this directory, run:

```sh
python3 audit_input.py
python3 sanity_checks.py
python3 rank_seam_a.py
python3 validate_deliverables.py
```

Only Python's standard library is used. The generator checks the input checksum,
assessment coverage and row identities. The independent validator checks one-to-one
coverage, all score bounds, weighted totals, ranking order, source quotations, the six
decimal cases, sanity-check links and exactly 100/50 report entries. Deliverable
coverage remains 300/4,650 because no further input records are present.

