# Seam B status reconciliation for issue #6

Brian (Louis), updated 2026-11-15 after PR20 merge. **Documentary reconciliation, not mathematical verification or final programme acceptance.**

## Purpose and scope

Resume [6900922777](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6900922777) limits this work to reconciling the original inventory with completed coordinator reports. No Carbon scoping, computations, Lean work or literature searches were repeated. Active Seam C and U-series work remains with its current workers. GitHub is the coordination and delivery record.

Population ruling [6405513569](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6405513569) fixes **91 retained entries C001–C091**, plus four duplicate occurrences D001–D004 and 24 ambiguous/supplementary U001–U024. Thus 119 passage headings are accounted for, but the research denominator is 91, not 119. The historical inventory was pinned by [6405374274](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6405374274). This document does not reinterpret D/U passages as retained conjectures.

## Evidence hierarchy

Every status below is a **coordinator report read on issue #6**, not a newly checked primary source or an independently audited proof. GO means a scoping recommendation, never PROVED. A report that prior art or a counterexample exists warrants withdrawing a stale recommendation, but does not justify claiming we independently validated the paper/certificate. Exact issue-comment links preserve the distinction.

## Changes that matter

The historical provisional shortlist must not continue to recommend C001 as a first proof: [6888095358](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6888095358) reports prior art covering C001–C004. C036 is not an independent new-identity recommendation: [6892116927](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6892116927) folds it into C037 and identifies a classical reduction. C049 remains only a reported scoped candidate. C085, C048 and C064 have reported counterexamples; C089 has only a **component-specific** refutation. These are disposition corrections, not fresh proof claims.

## Completed-report map

|Entries|Report-level status|Evidence|Qualification|
|---|---|---|---|
|C001 C002 C003 C004|REPORTED PRIOR ART|[6888095358](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6888095358)|Ashburn preprint reportedly proves all four. Retire the old first-proof recommendation pending direct archival verification; source-access gap is not erased.|
|C018|REPORTED GO|[6888662264](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6888662264)|Scoping complete; proof remains gated, not proved.|
|C036|FOLDED INTO FAMILY|[6892116927](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6892116927)|Coordinator identifies classical Rogers–Fine/Ramanujan reduction; adjudicated within C037 rather than independent novelty.|
|C037|REPORTED GO|[6892116927](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6892116927)|Polynomial family pinned; no kernel proof read or run here.|
|C042|REPORTED GO|[6888661960](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6888661960)|Four-claim triangle bundle scoped; bounded checks are not a universal proof.|
|C047|REPORTED GO|[6888008876](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6888008876)|Record-value/position bundle scoped; preserve global record conditions.|
|C048|REPORTED REFUTATION|[6896705879](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6896705879)|Reported n=6298 witness and prior Lean refutation; no repeated tests or independent certificate verification here.|
|C049|REPORTED GO|[6887378532](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6887378532)|Jacobsthal bound scoped; DP checks do not prove the all-n statement.|
|C050|REPORTED GO|[6887652299](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6887652299)|Rule 7 OFF bundle; do not split recurrence/generating-function claims.|
|C051|REPORTED GO|[6889227182](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6889227182)|Rule 23 OFF bundle.|
|C052 C057|REPORTED GO|[6889820865](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6889820865)|Rule 11 ON and Rule 23 ON respectively; separate source definitions.|
|C053 C054|REPORTED GO|[6890416759](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6890416759)|Rule 47 ON and Rule 11 OFF respectively; shared proof families are not independent discoveries.|
|C055|REPORTED GO|[6890924816](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6890924816)|Rule 47 OFF bundle.|
|C056|REPORTED GO|[6889225321](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6889225321)|Rule 7 ON bundle.|
|C064|REPORTED REFUTATION|[6891468865](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6891468865)|Reported n=239 counterexample; not re-executed here.|
|C082|REPORTED BLOCKED|[6894725485](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6894725485)|Global addition/star-chain barrier. A local-memory counterexample is not a refutation of the unrestricted conjecture.|
|C083|REPORTED BLOCKED|[6895889857](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6895889857)|Global optimality barrier; local sorting fails but does not itself refute the global claim.|
|C085|REPORTED REFUTATION|[6887056583](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6887056583)|Reported biconditional counterexample k=93041293345. No novelty/refutation certification by this consolidation.|
|C088|REPORTED BLOCKED|[6894030275](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6894030275)|Reduction to open Wieferich-prime inequality; not a universal result.|
|C089|REPORTED PARTIAL REFUTATION|[6892738029](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6892738029)|No-1111 component reportedly false; binary-digit component remains open. Do not mark both components refuted.|

## Complete retained-inventory ledger

All 91 IDs appear exactly once below. The 25 completed-report entries retain their later scoping supersessions; the other 66 now map to the exact row of the frozen §4.2 disposition ledger at commit8203e01. REPORTED EXCLUSION is that dated triage's selection decision, not a newly verified mathematical theorem, proof of impossibility, or assertion that the underlying question is currently open. Immutable source-line links preserve the full stated reason without silently rewriting it. C017 is now recorded as the triage's Dekking2020 prior-art exclusion, rather than lacking an adjudication.

|Entry|Current documentary disposition|Issue evidence|
|---|---|---|
|C001|REPORTED PRIOR ART|[6888095358](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6888095358)|
|C002|REPORTED PRIOR ART|[6888095358](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6888095358)|
|C003|REPORTED PRIOR ART|[6888095358](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6888095358)|
|C004|REPORTED PRIOR ART|[6888095358](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6888095358)|
|C005|REPORTED EXCLUSION: Analytic/geometric constant & unproved repair dependency|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L318)|
|C006|REPORTED EXCLUSION: Intractable self-referential dynamics — Van Eck|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L319)|
|C007|REPORTED EXCLUSION: Intractable self-referential dynamics — Van Eck|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L320)|
|C008|REPORTED EXCLUSION: Intractable self-referential dynamics — Van Eck|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L321)|
|C009|REPORTED EXCLUSION: Deep multiplicative/additive sieve barrier|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L322)|
|C010|REPORTED EXCLUSION: Subsumes powerful Odd Perfect Number conjecture|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L323)|
|C011|REPORTED EXCLUSION: Famous open problem — Binary Goldbach|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L324)|
|C012|REPORTED EXCLUSION: Famous open problem — Hardy–Littlewood Goldbach asymptotic|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L325)|
|C013|REPORTED EXCLUSION: Famous open problem — Goldbach lower bound|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L326)|
|C014|REPORTED EXCLUSION: Famous open problem — Restricted Goldbach|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L327)|
|C015|REPORTED EXCLUSION: Intractable greedy permutation dynamics|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L328)|
|C016|REPORTED EXCLUSION: Intractable greedy permutation dynamics|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L329)|
|C017|REPORTED EXCLUSION: PROVED in published literature — Dekking 2020|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L330)|
|C018|REPORTED GO|[6888662264](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6888662264)|
|C019|REPORTED EXCLUSION: Famous open problem — Keane's Kolakoski conjecture|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L332)|
|C020|REPORTED EXCLUSION: Analytic constant / special-value identity, §1.1.2|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L333)|
|C021|REPORTED EXCLUSION: Deep open additive representation — Zhi-Wei Sun|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L334)|
|C022|REPORTED EXCLUSION: Deep open additive representation — Zhi-Wei Sun|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L335)|
|C023|REPORTED EXCLUSION: Deep open restricted Goldbach — Zhi-Wei Sun|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L336)|
|C024|REPORTED EXCLUSION: Kolakoski-dependent global bound|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L337)|
|C025|REPORTED EXCLUSION: Deep open restricted 4-square conjecture — Zhi-Wei Sun|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L338)|
|C026|REPORTED EXCLUSION: Deep open restricted 4-square uniqueness — Zhi-Wei Sun|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L339)|
|C027|REPORTED EXCLUSION: Deep open restricted 4-square conjecture — Zhi-Wei Sun|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L340)|
|C028|REPORTED EXCLUSION: Deep open restricted 4-square uniqueness — Zhi-Wei Sun|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L341)|
|C029|REPORTED EXCLUSION: Deep open restricted square decomposition — Zhi-Wei Sun|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L342)|
|C030|REPORTED EXCLUSION: Deep open restricted square uniqueness — Zhi-Wei Sun|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L343)|
|C031|REPORTED EXCLUSION: Deep open restricted square decomposition — Zhi-Wei Sun|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L344)|
|C032|REPORTED EXCLUSION: Deep open restricted square decomposition — Zhi-Wei Sun|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L345)|
|C033|REPORTED EXCLUSION: Deep open restricted square decomposition — Zhi-Wei Sun|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L346)|
|C034|REPORTED EXCLUSION: Deep open restricted square uniqueness — Zhi-Wei Sun|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L347)|
|C035|REPORTED EXCLUSION: Famous open problem — Scholz–Brauer / Knuth–Stolarsky|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L348)|
|C036|FOLDED INTO FAMILY|[6892116927](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6892116927)|
|C037|REPORTED GO|[6892116927](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6892116927)|
|C038|REPORTED EXCLUSION: Deep open restricted 4-square conjecture — Zhi-Wei Sun|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L351)|
|C039|REPORTED EXCLUSION: Deep open restricted 4-square conjecture — Zhi-Wei Sun|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L352)|
|C040|REPORTED EXCLUSION: Deep open restricted 4-square conjecture — Zhi-Wei Sun|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L353)|
|C041|REPORTED EXCLUSION: Deep open 17-polynomial 4-square bundle — Zhi-Wei Sun|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L354)|
|C042|REPORTED GO|[6888661960](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6888661960)|
|C043|REPORTED EXCLUSION: Hard analytic/power-series nonvanishing problem|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L356)|
|C044|REPORTED EXCLUSION: Hard analytic/power-series nonvanishing + huge certificate|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L357)|
|C045|REPORTED EXCLUSION: Famous open problem — Guy–Kelly No-Three-In-Line|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L358)|
|C046|REPORTED EXCLUSION: Intractable Collatz-type nontermination problem|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L359)|
|C047|REPORTED GO|[6888008876](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6888008876)|
|C048|REPORTED REFUTATION|[6896705879](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6896705879)|
|C049|REPORTED GO|[6887378532](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6887378532)|
|C050|REPORTED GO|[6887652299](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6887652299)|
|C051|REPORTED GO|[6889227182](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6889227182)|
|C052|REPORTED GO|[6889820865](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6889820865)|
|C053|REPORTED GO|[6890416759](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6890416759)|
|C054|REPORTED GO|[6890416759](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6890416759)|
|C055|REPORTED GO|[6890924816](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6890924816)|
|C056|REPORTED GO|[6889225321](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6889225321)|
|C057|REPORTED GO|[6889820865](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6889820865)|
|C058|REPORTED EXCLUSION: Famous open problem — Classical Collatz conjecture|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L371)|
|C059|REPORTED EXCLUSION: Constant-digit record `F=0` & speculative spectral number theory|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L372)|
|C060|REPORTED EXCLUSION: Figure-dependent geometric construction & trigonometric constant|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L373)|
|C061|REPORTED EXCLUSION: Famous open problem — Erdős least prime primitive root|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L374)|
|C062|REPORTED EXCLUSION: Collatz-like base-10 dynamical termination problem|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L375)|
|C063|REPORTED EXCLUSION: Collatz-like base-10 dynamical termination problem|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L376)|
|C064|REPORTED REFUTATION|[6891468865](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6891468865)|
|C065|REPORTED EXCLUSION: Open prime-gap / multiplicative covering problem — Meyers|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L378)|
|C066|REPORTED EXCLUSION: Deep open cubic-quadratic representation — Zhi-Wei Sun|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L379)|
|C067|REPORTED EXCLUSION: Deep open cubic-quadratic representation — Zhi-Wei Sun|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L380)|
|C068|REPORTED EXCLUSION: Deep open cubic-quadratic representation — Zhi-Wei Sun|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L381)|
|C069|REPORTED EXCLUSION: Deep open cubic-quadratic representation — Zhi-Wei Sun|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L382)|
|C070|REPORTED EXCLUSION: Deep open cubic-quadratic representation — Zhi-Wei Sun|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L383)|
|C071|REPORTED EXCLUSION: Intractable greedy digit-divisibility permutation|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L384)|
|C072|REPORTED EXCLUSION: Famous open problem — Giuga's Conjecture, 1950|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L385)|
|C073|REPORTED EXCLUSION: Large finite extremal additive-basis search|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L386)|
|C074|REPORTED EXCLUSION: Famous open problem — Erdős–Turán Conjecture, 1941|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L387)|
|C075|REPORTED EXCLUSION: Analytic logarithmic-integral step bound, §1.1.2|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L388)|
|C076|REPORTED EXCLUSION: Analytic prime-counting step bound, §1.1.2|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L389)|
|C077|REPORTED EXCLUSION: Intractable greedy running-sum divisor permutation|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L390)|
|C078|REPORTED EXCLUSION: Intractable greedy running-sum divisor permutation bundle|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L391)|
|C079|REPORTED EXCLUSION: Internal duplicate target of `C077`|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L392)|
|C080|REPORTED EXCLUSION: Decimal-constant record `F=0`, Seam A Rank 300/300, §1.1.2|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L393)|
|C081|REPORTED EXCLUSION: Decimal-constant `F=0` & famous open 4D Sphere Packing conjecture|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L394)|
|C082|REPORTED BLOCKED|[6894725485](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6894725485)|
|C083|REPORTED BLOCKED|[6895889857](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6895889857)|
|C084|REPORTED EXCLUSION: Hard shortest-program / addition-chain variant|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L397)|
|C085|REPORTED REFUTATION|[6887056583](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6887056583)|
|C086|REPORTED EXCLUSION: Implies Prime Triplets conjecture — Zhi-Wei Sun|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L399)|
|C087|REPORTED EXCLUSION: Implies Prime Quadruplets conjecture — Zhi-Wei Sun|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L400)|
|C088|REPORTED BLOCKED|[6894030275](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6894030275)|
|C089|REPORTED PARTIAL REFUTATION|[6892738029](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6892738029)|
|C090|REPORTED EXCLUSION: Famous open problem — Riesel problem `k = 509,203`|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L403)|
|C091|REPORTED EXCLUSION: Deep open pairwise-nondivisible smooth-shifted sum — Zhi-Wei Sun|[Frozen §4.2 row](https://github.com/derekblair/math-proofs/blob/8203e01b9c356df8678f39239360bddcc115db43/research/dossiers/seam-b-triage-20261114/TRIAGE-SEAMB.md#L404)|

## Source delivery and remaining acceptance work

The coordinator delivered the frozen triage, inputs and evidence in commit8203e01, now merged via PR20 at63727b01. The input-delivery request is satisfied. Exact content checks matched CONJECTURES SHA-256 f0650fc6574de8848ab012e3c9fbaeb79db0155a6a06deb2586f483ecedc1498 and RANKED-SEAM-A ae595756a4661b4e27e61c4bc649dd921ce0c4747b5a3abc1515738f692cc3d6. Structural checks found25 ranked rows,91 retained rows,4 duplicates and24 supplementary rows.

Step2 from [coordinator comment6902304547](https://github.com/derekblair/math-proofs/issues/6#issuecomment-6902304547) is implemented here as a66-row documentary join. All25 later-report rows are unchanged. The frozen source remains untouched; its historical shortlist recommendations for C085 and C001 are superseded by the report map above. Its5 shortlisted /86 excluded accounting describes the dated selection, not current open-status counts.

Remaining: independent review of this mapping and final acceptance on the issue. The coordinator's PR20 PASS was explicitly inventory-only, not issue completion. The full REVIEW-MP-PR20.md with NB-1–NB-4 was not supplied in the branch or located by filename search; no attempt is made to guess those detailed findings. Any source-prose corrections should be separately attributed in this reconciliation, never silently applied to the frozen report.

No independent mathematical/literature validation is inferred from the documentary join. Historical source-read gaps remain historical facts; the newly available archived records do not retroactively certify prior checks. The merged4,650-pair ranking remains unavailable; the source expressly covers300 pairs. No new proof jobs, toolchain changes, or overlapping Carbon work are authorized by this mapping.

## What this does NOT show

No proof, compilation, kernel audit, globally exhaustive novelty search, independently verified counterexample, final25 checked candidates, or issue completion is claimed. No new execution or theorem code was produced. No self-review or merge is authorized. The next action is evidence-bundle reconciliation on this same draft, not repeating already-completed Carbon tests or launching overlapping research.
