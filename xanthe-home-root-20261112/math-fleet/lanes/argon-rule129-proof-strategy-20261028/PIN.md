# Pin Manifest — a267442-eq-a043545

```yaml
candidate: a267442-eq-a043545
repo: derekblair/math-proofs
created: 2026-10-28
frozen_by: derekblair@bakkie
source:
  citation: >
    OEIS A267442 (Robert Price, Jan 15 2016, rev. #13; FORMULA conjecture by R. J. Mathar,
    Jan 17 2016), paired with OEIS A043545 (Clark Kimberling, offset 0, rev. #55), OEIS A036987
    (N. J. A. Sloane, Fredholm-Rueppel sequence, offset 0, rev. #249), and OEIS A071035 / A267366
    (Hans Havermann 2002, rev. #38; Robert Price 2016 / Dominik Koeppl 2022, rev. #20: Rule 126
    single-ON-seed evolution and middle column).
  verbatim_quote: |
    %N A267442 Middle column of the "Rule 129" elementary cellular automaton starting with a single ON (black) cell.
    %F A267442 Conjecture: a(n) = A043545(n), n>0. - _R. J. Mathar_, Jan 17 2016
    %O A267442 0
    %N A043545 (Maximal base-2 digit of n) - (minimal base-2 digit of n).
    %O A043545 0,1
    %N A036987 Fredholm-Rueppel sequence.
    %F A036987 1 followed by a string of 2^k - 1 0's. Also a(n)=1 iff n = 2^m - 1.
    %O A036987 0,1
    %Y A071035 Cf. A036987 (central column).
    %C A267366 The middle column itself is A036987. [Noticed by _Dominik Koeppl_, Oct 21 2022]
  strongest_published_form: >
    On the Rule 129 side, Mathar's Jan 17 2016 statement in OEIS A267442 stands as an unproved
    conjecture (verified computationally for 1 <= n <= 1,048,576 in derekblair/math-proofs#5).
    On the equivalent Rule 126 side, C_126(n, 0) = A036987(n) is asserted without proof in
    OEIS A071035 (%Y), OEIS A267366 (Koeppl 2022), indirectly via row-sums in N. J. A. Sloane
    (arXiv:1503.01168v3, Sec. 6.1, 2015), and empirically via bivariate generating functions in
    A. J. Macfarlane (DAMTP Cambridge unpublished note GFsForCAsOfEvenRuleNo.ps, Sec. 9 Eq. 67,
    2016); in formal libraries, Mykola Palamarchuk (lividgreen/lean-elementary-cellular-automata,
    ECA/Doubling.lean, 2026) proves LocalRule.finRule_two_dbl only on even-support doubled states
    (dbl x), which excludes singleSeed. The pinned theorems prove both the Rule 126 middle-column
    theorem for all n >= 0 and Mathar's full conjecture A267442(n) = A043545(n) for all n > 0
    with zero weakening.
statement_file:
  path: Mathproofs/Rule129MiddleColumn.lean
  sha256: 2bfada69046ed20429e039c895aae8eb2617663f86cf5027ec9600de64ad758e
  commit: 3fc2503c69dba90dcf438be5c5334079c9c41266
theorems:
  - name: Mathproofs.Rule129MiddleColumn.rule126_middle_column_iff
    informal: >
      [Pinned theorem] Starting from singleSeed on Z, cell x = 0 at generation n >= 0 of ECA
      Rule 126 is ON (true) iff n = 2 ^ m - 1 for some m : Nat.
  - name: Mathproofs.Rule129MiddleColumn.rule126_middle_column_eq_a036987
    informal: >
      [Pinned theorem] For every n : Nat, the 0/1-valued Rule 126 single-ON-seed middle column
      (ecaOrbit 126 n 0).toNat equals a036987 n.
  - name: Mathproofs.Rule129MiddleColumn.a267442_eq_a043545
    informal: >
      [Pinned theorem] Mathar's conjecture (OEIS A267442, Jan 17 2016): for every n : Nat with
      0 < n, a267442 n = a043545 n.
  - name: Mathproofs.Rule129MiddleColumn.ecaRule
    informal: >
      [Locked def] Wolfram ECA local rule R on Bool reading bit 4 * p.toNat + 2 * q.toNat + r.toNat
      via Nat.testBit.
  - name: Mathproofs.Rule129MiddleColumn.ecaStep
    informal: >
      [Locked def] One synchronous global ECA step of rule R on total configurations Int -> Bool.
  - name: Mathproofs.Rule129MiddleColumn.singleSeed
    informal: >
      [Locked def] Initial configuration Int -> Bool with x = 0 set to true and all x != 0 false.
  - name: Mathproofs.Rule129MiddleColumn.ecaOrbit
    informal: >
      [Locked def] Generation-n configuration (ecaStep R)^[n] singleSeed under rule R.
  - name: Mathproofs.Rule129MiddleColumn.a267442
    informal: >
      [Locked def] OEIS A267442(n) defined as (ecaOrbit 129 n 0).toNat.
  - name: Mathproofs.Rule129MiddleColumn.a036987
    informal: >
      [Locked noncomputable def] OEIS A036987(n) defined via Classical if (exists m : Nat,
      n = 2 ^ m - 1) then 1 else 0.
  - name: Mathproofs.Rule129MiddleColumn.a043545
    informal: >
      [Locked def] OEIS A043545(n) defined on Nat.digits 2 n as 0 on [] and
      (ds.foldl max d - ds.foldl min d) on d :: ds.
axiom_allowlist: [propext, Classical.choice, Quot.sound]
trust_policy:
  native_decide: forbidden
  ofReduceBool: forbidden
  custom_axioms: forbidden
  sorry_in_solution: forbidden
fidelity_notes: |
  1. Infinite-line dynamics: ecaStep acts on total configurations (Int -> Bool) using Wolfram's
     standard bit encoding b_{4p + 2q + r}(R), matching Mathematica's
     CellularAutomaton[129, {{1}, 0}, rows-1, {All, All}] in OEIS A267442 (%t) and A267417
     (where the infinite background outside |x| <= n starts at 0 at n = 0, transitions 0 -> 1 at
     n = 1, and remains 1 for all n >= 1 since f_129(0,0,0) = 1 and f_129(1,1,1) = 1).
  2. Seed, iterate import, and indexing: singleSeed sets x = 0 to true and all x != 0 to false;
     ecaOrbit R n = (ecaStep R)^[n] singleSeed is backed by explicit import
     Mathlib.Logic.Function.Iterate, with generation n = 0 equal to singleSeed, matching
     %O A267442 0 (a(0) = 1) and %O A071035 0,1.
  3. Primary definitions of A043545 and A036987: a043545 n is defined directly from Nat.digits 2 n
     as (maximal base-2 digit) - (minimal base-2 digit) without assuming Somos's 1 - A036987(n)
     complement formula; in Mathlib4, Nat.digits 2 0 = [] (Nat.digits_zero), which the explicit
     `| [] => 0` branch maps to 0 so a043545 0 = 0, matching conventional 0 = (0)_2
     (max {0} - min {0} = 0) and %S A043545. Meanwhile a036987 n retains the primary %F A036987
     characterization `exists m : Nat, n = 2 ^ m - 1` (using Classical.choice, permitted by
     axiom_allowlist) rather than a secondary bitwise formula.
  4. Domain bound 0 < n in a267442_eq_a043545: exact match to Mathar's "n>0" (%F A267442; at
     n = 0, a267442 0 = 1 != 0 = a043545 0), while rule126_middle_column_iff and
     rule126_middle_column_eq_a036987 quantify over all n : Nat (n >= 0).
  5. Locked declaration scope: all 7 definitions (ecaRule, ecaStep, singleSeed, ecaOrbit,
     a267442, a036987, a043545) and all 3 theorem headers (rule126_middle_column_iff,
     rule126_middle_column_eq_a036987, a267442_eq_a043545) in Mathproofs.Rule129MiddleColumn are
     frozen by this manifest; zero edits to any of these 10 declarations are permitted in a
     solution closure.
delta_vs_source: >
  NONE — proves the exact full-quantifier statement of Mathar's OEIS A267442 conjecture for all
  n > 0 from primary definitions alongside the equivalent all-n >= 0 Rule 126 middle-column
  theorem.
review_route: >
  Codex review lane (OpenAI/Codex reviewer pool != Gemini/Argon author-side research pool;
  satisfies the cross-model review gate without pre-assigning a specific host machine).
```
