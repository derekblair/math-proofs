Pins the Rule 129 / Rule 126 middle-column target by adding `Mathproofs/Rule129MiddleColumn.lean`, extracted byte-for-byte from the supplied pin-freeze dossier Deliverable (A). The seven definitions and three theorem statements are preserved. The three theorem proofs remain `sorry`; this PR does not prove the conjecture. `Mathproofs.lean` is unchanged.

The baseline `master` checkout was clean before and after fast-forwarding to `0b17820a79f969c883b363de670402512b47341d`. The frozen statement is the only changed file. Static checks found zero `native_decide`, `bv_decide`, `ofReduceBool`, or `axiom ` occurrences. The dossier has three indented standalone `sorry` lines (and zero unindented literal `sorry` lines); verbatim extraction and the dossier's whitespace-tolerant check were preserved.

Validation used `leanprover/lean4:v4.34.1` (Lean commit `5045d0056413266e57c625dcd7c365b10e377c52`) with the repository's locked Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`. `lake exe cache get` completed successfully. Both compile commands and the exact dossier sanity suite exited 0. All three eval outputs match their expected lists; every definition's axiom report stays within `[propext, Classical.choice, Quot.sound]`.

## Freeze identifiers

- Statement SHA256: `2bfada69046ed20429e039c895aae8eb2617663f86cf5027ec9600de64ad758e`
- Freeze commit: `3fc2503c69dba90dcf438be5c5334079c9c41266`
- Frozen pin manifest file SHA256 (unchanged file; not the corrected PR-body rendering below): `8bc4bffc10b383bdf1ce557c37e70a2b93aafe56d627285a1a22c5f78b9d1e97`
- Branch: `rule129-pin-freeze`
- Freeze executor: `derekblair@bakkie` (delegated coding lane `codex-rule129-freeze`, pool `chatgpt-live`)

## Compile evidence (verbatim)

`lake env lean Mathproofs/Rule129MiddleColumn.lean` — exit 0:

```text
Mathproofs/Rule129MiddleColumn.lean:88:8: warning: declaration uses `sorry`
Mathproofs/Rule129MiddleColumn.lean:93:8: warning: declaration uses `sorry`
Mathproofs/Rule129MiddleColumn.lean:98:8: warning: declaration uses `sorry`
```

`lake build Mathproofs.Rule129MiddleColumn` — exit 0:

```text
⚠ [834/834] Built Mathproofs.Rule129MiddleColumn (592ms)
warning: Mathproofs/Rule129MiddleColumn.lean:88:8: declaration uses `sorry`
warning: Mathproofs/Rule129MiddleColumn.lean:93:8: declaration uses `sorry`
warning: Mathproofs/Rule129MiddleColumn.lean:98:8: declaration uses `sorry`
Build completed successfully (834 jobs).
```

## Sanity suite output (verbatim)

`lake env lean --stdin` with dossier §2.3 step 3: ten `#check` commands, seven definition `#print axioms` commands, and the three `#eval` commands — exit 0:

```text
ecaRule : ℕ → Bool → Bool → Bool → Bool
ecaStep : ℕ → (ℤ → Bool) → ℤ → Bool
singleSeed : ℤ → Bool
ecaOrbit : ℕ → ℕ → ℤ → Bool
a267442 : ℕ → ℕ
a036987 : ℕ → ℕ
a043545 : ℕ → ℕ
rule126_middle_column_iff : ∀ (n : ℕ), ecaOrbit 126 n 0 = true ↔ ∃ m, n = 2 ^ m - 1
rule126_middle_column_eq_a036987 : ∀ (n : ℕ), (ecaOrbit 126 n 0).toNat = a036987 n
a267442_eq_a043545 : ∀ (n : ℕ), 0 < n → a267442 n = a043545 n
'Mathproofs.Rule129MiddleColumn.ecaRule' depends on axioms: [propext]
'Mathproofs.Rule129MiddleColumn.ecaStep' depends on axioms: [propext]
'Mathproofs.Rule129MiddleColumn.singleSeed' does not depend on any axioms
'Mathproofs.Rule129MiddleColumn.ecaOrbit' depends on axioms: [propext]
'Mathproofs.Rule129MiddleColumn.a267442' depends on axioms: [propext]
'Mathproofs.Rule129MiddleColumn.a036987' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mathproofs.Rule129MiddleColumn.a043545' depends on axioms: [propext, Classical.choice, Quot.sound]
[1, 1, 0, 1, 0, 0, 0, 1, 0]
[1, 0, 1, 0, 1, 1, 1, 0, 1]
[0, 0, 1, 0, 1, 1, 1, 0, 1]
```

## Provenance and review boundary

The supplied dossier records the Rule 126 middle-column identification as existing folklore: OEIS A071035 and A267366, Sloane (2015), and Macfarlane (2016). This freeze makes no new proof or novelty claim. The manifest below retains that disclosure and the audited exact statement scope.

This PR stays **draft**. Review and merge belong to the coordinator on a different pool from this coding lane. The manifest's Codex review route concerns independence from the Gemini/Argon research author pool; this freeze execution is not that review.

## Review history

- 2026-10-28 crossed review — host `nibbles`, pool `chatgpt-proton`, verdict **FAIL**. Blocking findings: (F1) PR-body present-tense proof claims contradicted the three `sorry` placeholders; (F2) the citation arXiv:1503.01168v3 was refuted (arXiv lists only v1).
- 2026-10-28 coordinator body-only fix — host `xanthe`, pool `chatgpt-gmail`. Corrected F1 proof-status wording and F2 citation to arXiv:1503.01168v1, section 6.1, 2015; no Lean source or `PIN.md` change; head unchanged.
- 2026-10-28 post-fix crossed re-review — host `nibbles`, pool `chatgpt-proton`, verdict **FAIL**. Single blocking finding: provenance omission (the body did not yet record the prior review history). All technical freeze checks passed: head, statement hash `2bfada69046ed20429e039c895aae8eb2617663f86cf5027ec9600de64ad758e`, toolchain v4.34.1, compile, axiom outputs, recomputation, and trust screen.
- 2026-10-29 coordinator body-only provenance fix (this edit) — host `xanthe`. This edit adds the review history and corrects the review-gate wording; no Lean source or `PIN.md` change; head unchanged. The freeze gate remains **OPEN pending a fresh PASS re-review**. Neither crossed review returned PASS; this edit does not satisfy the gate.

## Coordinator desk handoff

The populated manifest is saved at `/home/derekblair/lane-work/codex-rule129-freeze/pins/a267442-eq-a043545.md`; a PR-body rendering with corrected proof-status wording and arXiv citation appears below. The frozen manifest file is unchanged. The authoritative destination is `bossman-vm:~/workspace/math-fleet/pins/a267442-eq-a043545.md`, with registration in adjacent `REGISTRY.md`. Those coordinator writes remain pending: the fleet specification states that no fleet machine can SSH into the coordinator VM (§2, line 37; §6, line 382), and no coordinator filesystem connector is exposed to this lane. A precise registration entry is prepared in the lane's `REGISTRY-ENTRY.md`. No substitute bakkie desk was created and no proof lane was launched.

## Manifest rendering (PR-body corrections; frozen file unchanged)

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
    (arXiv:1503.01168v1, Sec. 6.1, 2015), and empirically via bivariate generating functions in
    A. J. Macfarlane (DAMTP Cambridge unpublished note GFsForCAsOfEvenRuleNo.ps, Sec. 9 Eq. 67,
    2016); in formal libraries, Mykola Palamarchuk (lividgreen/lean-elementary-cellular-automata,
    ECA/Doubling.lean, 2026) proves LocalRule.finRule_two_dbl only on even-support doubled states
    (dbl x), which excludes singleSeed. The pinned statements have zero statement weakening
    against the published targets: they retain the same quantifiers and hypotheses for the
    Rule 126 middle-column result for all n >= 0 and Mathar's full conjecture
    A267442(n) = A043545(n) for all n > 0. All three theorem bodies are currently sorry
    placeholders with zero proved theorem content. Proof is future work; this PR claims
    a statement freeze only, not a proof.
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
  NONE in statement weakening: the pinned statements retain the published targets'
  exact quantifiers and hypotheses, including Mathar's OEIS A267442 conjecture for all
  n > 0 from primary definitions and the equivalent all-n >= 0 Rule 126 middle-column
  result. All three theorem bodies are currently sorry placeholders with zero proved
  theorem content. Proof is future work; this PR claims a statement freeze only, not a proof.
review_route: >
  Codex review lane (OpenAI/Codex reviewer pool != Gemini/Argon author-side research pool;
  cross-model review gate remains OPEN pending a fresh PASS re-review).
```
