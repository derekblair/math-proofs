# Finite-evidence audit

Audited on 2026-10-28. Scope: `BRIEF.md`, `REPORT-consolidation.md`, and `REPORT-threshold.md` only. No original tranche logs, scripts, Lean files, or pinfreeze dossier were supplied. This audit checks the drafting inputs; it does not independently reproduce the tranche experiments.

## Exact tier table

All thresholds below occur explicitly in the consolidation report and equal `T_p = 3*2^(p-1)-1`. Remaining columns are exact arithmetic expansions of the two reports' formulas, not additional empirical observations. `M_p = 2^p-1`; `|U| = 2^p` applies at both reported endpoints, while the row counts differ because zero has only one signed realization.

| Popcount p | Threshold T_p | Mersenne M_p | Endpoint union size 2^p | Row count at T_p | Row count at M_p | Threshold enumeration size p+1 |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | 2 | 1 | 2 | 4 | 3 | 2 |
| 2 | 5 | 3 | 4 | 8 | 7 | 3 |
| 3 | 11 | 7 | 8 | 16 | 15 | 4 |
| 4 | 23 | 15 | 16 | 32 | 31 | 5 |
| 5 | 47 | 31 | 32 | 64 | 63 | 6 |
| 6 | 95 | 63 | 64 | 128 | 127 | 7 |
| 7 | 191 | 127 | 128 | 256 | 255 | 8 |
| 8 | 383 | 255 | 256 | 512 | 511 | 9 |
| 9 | 767 | 511 | 512 | 1024 | 1023 | 10 |
| 10 | 1535 | 1023 | 1024 | 2048 | 2047 | 11 |
| 11 | 3071 | 2047 | 2048 | 4096 | 4095 | 12 |
| 12 | 6143 | 4095 | 4096 | 8192 | 8191 | 13 |
| 13 | 12287 | 8191 | 8192 | 16384 | 16383 | 14 |
| 14 | 24575 | 16383 | 16384 | 32768 | 32767 | 15 |
| 15 | 49151 | 32767 | 32768 | 65536 | 65535 | 16 |
| 16 | 98303 | 65535 | 65536 | 131072 | 131071 | 17 |
| 17 | 196607 | 131071 | 131072 | 262144 | 262143 | 18 |
| 18 | 393215 | 262143 | 262144 | 524288 | 524287 | 19 |

## Which bounds are actually supplied

| Tier | Original analytic/generation row set in supplied reports | Converse interval in supplied reports | Direct simulation interval in supplied reports |
| --- | --- | --- | --- |
| 1 | Not reproduced | Not reproduced | Not reproduced |
| 2 | Not reproduced | Not reproduced | Not reproduced |
| 3 | Not reproduced | Not reproduced | Not reproduced |
| 4 | Not reproduced | Not reproduced | Not reproduced |
| 5 | Not reproduced | Not reproduced | Not reproduced |
| 6 | Not reproduced | Not reproduced | Not reproduced |
| 7 | Not reproduced | Not reproduced | Not reproduced |
| 8 | Not reproduced | Not reproduced | Not reproduced |
| 9 | Not reproduced | Not reproduced | Not reproduced |
| 10 | Not reproduced | Not reproduced | Not reproduced |
| 11 | Not reproduced | Not reproduced | Not reproduced |
| 12 | Not reproduced | Not reproduced | Not reproduced |
| 13 | Not reproduced | Not reproduced | Not reproduced |
| 14 | Not reproduced | Not reproduced | Not reproduced |
| 15 | Not reproduced | Not reproduced | Not reproduced |
| 16 | Not reproduced | Not reproduced | Not reproduced |
| 17 | Not reproduced | Not reproduced | Not reproduced |
| 18 | Threshold report identifies original generation list with G_18, defined below: 19 values reported as <=524288 | 2 <= n <= 512000, inclusive | Not reproduced; bitset section (F) exists, but no bounds are given |

Do not replace any missing interval with `[T_p, infinity)`, `[1,512000]`, `[2,512000]` copied from p=18, an assumed power-of-two cutoff, or the threshold enumeration cutoff. The consolidation explicitly describes a finite-evidence summary over each tier's own recorded ranges; it does not supply those other ranges.

The threshold checks provide additional explicitly specified finite sets for **all** p=1,...,18. These are separate from the omitted original analytic and simulation ranges.

## Threshold enumeration and endpoint checks

For each p=1,...,18, the threshold report's S2 enumerates all sums of p distinct powers with positions in `{0,...,p}`. Equivalently, the checked generation set is

`G_p = {2^(p+1)-1-2^j : 0 <= j <= p}`.

This has exactly `p+1` members, and is the complete set of p-popcount integers below `2^(p+1)`. It does **not** include all integers below that cutoff. Its smallest member is `M_p`, its second is `T_p`, and its largest is `2^(p+1)-2`. Exactly two members are `<=T_p`; no p-popcount integer lies strictly between `M_p` and `T_p`.

For p=18 this is a set of **19 generations**, from `262143` through `524286` with gaps. The source phrase “19 values <=524288” is correct but loose: `524288` is not a member (its popcount is 1), and no continuous range through 524288 was checked by that enumeration. The source says this set equals the popcount-18 tranche's generation list; it does not give that equality for the other 17 tiers.

The claim that any p-popcount n having a bit at position >=p+1 “exceeds 2^(p+1)” should be expressed as `n >= 2^(p+1) > T_p`. Strict `n > 2^(p+1)` fails for p=1, n=4, although the needed threshold comparison remains true.

S1 checks each endpoint `n=T_p`: `2^(p-1)` submasks generate `2^p` distinct absolute positions with minimum `2^(p-1)>0`, yielding the direct symmetry count `2^(p+1)`. The report qualifies its independent pinned `math.comb` evaluation with **n<=1000**. This qualification is attached to S1 and must not be described as a simulation sweep of every n<=1000. At threshold samples it covers p=1,...,9 (`T_9=767`; `T_10=1535`).

S3 checks each endpoint `n=M_p`: union size `2^p`, zero produced exactly once, and direct row count `2^(p+1)-1`. The source does not separately attach the `math.comb` cutoff to S3, so do not silently expand that claim.

S4 checks the minimum-value identity at every enumerated n in G_p: `min U = n-2*kmax-1`, with kmax the lower part. This is an arithmetic property of the candidate union; the report does not claim fresh full Rule126 recurrence simulations at all these generations.

## Evidence provenance and completion markers

The consolidation is a check of existing recorded logs, not a fresh computation. It reports both `ALL CHECKS PASS` and `TOTAL failures: 0` for all 18 tier outputs. The p=18 output has both markers twice, corresponding to sections (A)–(E) and the bitset section (F); this is **not** 19 tiers or a duplicate independent coverage interval.

The support tranches `mersenne-rows`, `lucas-submask`, `diagonals`, and `rowcounts` contain `ALL CHECKS PASS`. The method/support tranches `a1a4-truthtables`, `a3lucas`, `closedform`, and `recurrence` use a different marker convention and are explicitly excluded from tier evidence in the consolidation. Their absence of those marker strings is not a reported failure.

The threshold report separately records exit 0 and both completion markers for its Python/numpy script. Neither supplied report contains the underlying `compute.py` or `output.txt`, and neither invokes Lean.

## Status and drafting limits

1. Every finite-evidence claim should be attributed to the supplied reports. Completion of their recorded checks is not a universal verification over n, a Lean proof, or an independent rerun in this writing lane.
2. The main theorem may be stated as the target universal statement, clearly marked pending proof. A p<=18 finite tranche record does not establish the all-p statement, nor all generations within any fixed popcount tier.
3. The reports' threshold statement is combinatorial ordering: the next p-popcount integer after M_p is T_p. It is not an observed series of failed cases in a nonempty gap. The source explicitly says the anticipated defect branch was vacuous and corrected.
4. The required page-one phrase “proof pinned and in preparation” is in tension with both reports' final status: compile/commit/freeze of the pin is still an awaited next step and no proof lane runs without a frozen pin. Retain the required phrase only with a clear adjacent qualification that this is brief-supplied program status and no frozen pin or Lean artifact was provided or audited. Do not represent pin completion as a fact established by these reports.
5. `count_S=0` at the Mersenne row needs an explicit cone convention. Under same-seed Rule129, the full infinite row has True cells outside the finite Rule126 cone. The source's symbol is undefined in the supplied packet, so document the chosen finite-cone reading.
6. A phrase such as “verified computationally for p=1,...,18” needs its finite-domain qualification in the same paragraph. Otherwise it can misleadingly suggest all infinitely many p-popcount n were verified.

## Draft review

Reviewed the complete `paper.tex` draft on 2026-10-28 against both reports. The following correction is required:

- In “Provenance of the supplied evidence,” the text says the four support tranches `mersenne-rows`, `lucas-submask`, `diagonals`, and `rowcounts` “also have the markers,” following a sentence naming both `ALL CHECKS PASS` and `TOTAL failures: 0`. The consolidation only says those supporting tranches carry `ALL CHECKS PASS`. Replace the phrase with “also carry `ALL CHECKS PASS`.” The plural formulation would assert an additional terminal marker not specified for that group.

All 18 table thresholds and candidate counts were checked individually against the formulas and agree. The p=18 converse interval, the 19-generation set and its exact endpoints, all 18 threshold/Mersenne cases, the S1 cutoff, and the S4 domain are accurately stated. Missing source ranges are clearly marked and no wider empirical interval is inferred. The strict-inequality source issue for p=1 is avoided correctly.

The target theorem is clearly distinguished from finite evidence, the `p<=18` limit does not imply all generations of those tiers, and the status footnote is explicitly qualified. No standalone occurrence of “proved” or “proven” appears in the reviewed manuscript. The source-packet count_S ambiguity is disclosed. Reference-based prior-art claims were outside this evidence audit's remit and are assigned to the references audit.

The editorial phrases “pending proof” and “no frozen artifact” accurately retain the two reports' limits. The draft meets the numerical-fidelity and proof-status gates after the single marker-wording correction above; PDF placement and compilation are for the main lane to verify.
