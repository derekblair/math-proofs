# DOSSIER — Pin-Freeze Preparation for Rule 129 / Rule 126 Middle Column (`a267442-eq-a043545`)

- **Lane:** `argon-rule129-pinfreeze-prep-20261027`
- **Model / Harness:** `agy`, Gemini 4 Argon (High) · Machine: `xanthe` · Pool: `google-ai-ultra`
- **Date:** 2026-10-27
- **Mode:** Research-only pin-freeze preparation (no coding, no Lean execution, no repo writes, no GitHub writes; `BRIEF.md` lines 3–4, 19)
- **Inputs Synthesized:**
  - `SCREEN-DOSSIER.md` (`argon-rule129-screen-20261026`): prior-art audit (novelty case `(c)` with mandatory folklore disclosure, §1 & §3), exact complementation reduction (§2), Route A closed-form binomial-parity strategy (§4.2), `DRAFT` pin manifest (§5.1, lines 277–343), and `DRAFT` statement file `Mathproofs/Rule129MiddleColumn.lean` (§5.1, lines 348–400).
  - `AUDIT-DOSSIER.md` (`argon-rule129-audit-20261026`): adversarial Route A verdicts (`Lemma A1` `SOUND`, `Lemma A2` `SOUND-WITH-REPAIR`, `Lemma A3` `SOUND-WITH-REPAIR`, `Lemma A4` `SOUND`, reduction `SOUND (NON-CIRCULAR)`), formalization repairs `A2-1`–`A2-3` and `A3-1`–`A3-2` (§1.4–§1.6), 6 pin-manifest gate checks (§3.1), 7 mandatory pre-freeze items (§3.2, lines 263–271), and statement-file hazards `S1`–`S5` (§3.3, lines 277–293).

---

## 1. Corrected Draft Statement File (`Mathproofs/Rule129MiddleColumn.lean`)

### 1.1 Hazard S1 Resolution: Choice, Free Unfolding Lemmas, and Recorded Cost

To resolve **Hazard S1** (`AUDIT-DOSSIER.md` §3.3 item 1, lines 277–279; §3.2 item 3, line 265), where `SCREEN-DOSSIER.md` lines 349 & 368 used `(ecaStep R)^[n] singleSeed` under `import Mathlib.Data.Nat.Digits.Defs` alone without explicitly importing `Nat.iterate`, **this preparation selects Option 1: adding explicit `import Mathlib.Logic.Function.Iterate` while preserving `def ecaOrbit (R : Nat) (n : Nat) : Int → Bool := (ecaStep R)^[n] singleSeed` verbatim** (`SCREEN-DOSSIER.md` lines 367–368). Directly inspecting Mathlib4 at the target revision `v4.34.1` (`Mathlib/Logic/Function/Iterate.lean` lines 40–45) confirms that `def Nat.iterate` and the global notation `f "^[" n "]"` are declared inside `Mathlib.Logic.Function.Iterate` (`@[expose] public section`), so the explicit import eliminates reliance on fragile transitive imports through `Mathlib.Tactic.Ring` in `Mathlib/Data/Nat/Digits/Defs.lean` (lines 7–12) while keeping **zero definition-body delta** across all 7 locked `def` declarations (`AUDIT-DOSSIER.md` §3.2 item 6, line 270) and matching Mathlib's standard dynamical-system iterate idiom (`AUDIT-DOSSIER.md` Summary table, line 21). Under this choice, the proof lane receives for free from `Mathlib.Logic.Function.Iterate` (`v4.34.1` lines 53–176) the simp/definitional base and one-step lemmas `@[simp] Function.iterate_zero : f^[0] = id` (`rfl`), `Function.iterate_zero_apply : f^[0] x = x` (`rfl`), and `@[simp high] Function.iterate_one : f^[1] = f` (directly discharging generation `0` in Lemma A2 and generation `1` in Lemma A4), the inner-step `rfl` lemmas `@[simp] Function.iterate_succ : f^[n.succ] = f^[n] ∘ f` and `Function.iterate_succ_apply : f^[n.succ] x = f^[n] (f x)`, the outer-step unfolding lemmas `Function.iterate_succ' : f^[n.succ] = f ∘ f^[n]` and `Function.iterate_succ_apply' : f^[n.succ] x = f (f^[n] x)` (needed by Repair A2-3), and composition/semiconjugacy lemmas (`Function.iterate_add_apply`, `Function.iterate_mul`, `Function.Semiconj.iterate_right`). **Recorded cost vs. direct `Nat` recursion:** (1) one extra Mathlib import line in the frozen header (negligible build-graph cost because `Mathlib.Data.Nat.Digits.Defs` already imports `Mathlib.Tactic.Ring`), and (2) non-definitional outer-step unfolding — because `Nat.iterate` recurses on its starting state (`f^[n + 1] a = f^[n] (f a)` by `rfl`, `Iterate.lean` line 42), `ecaOrbit R (n + 1)` does **not** reduce by `rfl` to `ecaStep R (ecaOrbit R n)`, requiring the proof lane to invoke `Function.iterate_succ_apply'` explicitly (`rw [ecaOrbit, Function.iterate_succ_apply', ← ecaOrbit]`, i.e., Repair A2-3, `AUDIT-DOSSIER.md` lines 156–157 & 182) in the inductive steps of Lemma A2 and Lemma A4.

### 1.2 Summary of Repairs & Hazard Dispositions Applied to Statement File `(A)`

1. **Zero theorem or definition weakening (`delta vs audited draft = NONE`):**
   - All **3** pinned theorem declarations (`rule126_middle_column_iff`, `rule126_middle_column_eq_a036987`, `a267442_eq_a043545`) and all **7** locked `def` declarations (`ecaRule`, `ecaStep`, `singleSeed`, `ecaOrbit`, `a267442`, `a036987`, `a043545`) retain the **exact** signatures, quantifiers, and bodies of `SCREEN-DOSSIER.md` lines 355–400 (`AUDIT-DOSSIER.md` §3.1 Gates 3 & 6, lines 252, 255; §3.2 item 6, line 270).
   - The sole executable code edit relative to `SCREEN-DOSSIER.md` lines 348–400 is adding `import Mathlib.Logic.Function.Iterate` on line 3 of `(A)`, flagged inline with `-- [Audit §3.2 Item 3 / §3.3 Hazard S1]`.
2. **Route A formalization repairs (`A2-1`, `A2-2`, `A2-3`, `A3-1`, `A3-2`) embedded in structured comments (`BRIEF.md` line 11):**
   - Because none of the 3 pinned theorem statements references the auxiliary Route A closed form `B`, central-binomial parity `g`, or Lucas's theorem (`SCREEN-DOSSIER.md` lines 386–399), adding `def B` or `import Mathlib.Data.Nat.Choose.Lucas` as executable code in the statement file is unnecessary and would improperly expand the 7-definition lock (`AUDIT-DOSSIER.md` line 270). Instead, all five audited Route A repairs are recorded verbatim inside the statement file's `/-! ... -/` implementation-notes block so any proof lane opening `Mathproofs/Rule129MiddleColumn.lean` inherits the repaired specifications directly:
     - **Repair A2-1 (`AUDIT-DOSSIER.md` §1.4, lines 152–153):** Uniform `Bool` return type across both branches of `B`: `def B (n : Nat) (x : Int) : Bool := if x.natAbs ≤ n then Nat.choose n ((n - x.natAbs) / 2) % 2 == 1 else false` (replacing `SCREEN-DOSSIER.md` line 236's mixed `Prop`/`Bool` expression).
     - **Repair A2-2 (`AUDIT-DOSSIER.md` §1.4, lines 17, 154–155):** Truncated-subtraction-safe formulation: keep `n - x.natAbs` strictly guarded inside `if x.natAbs ≤ n`; after spatial reflection (`B n (-x) = B n x`, `ecaRule 126 r q p = ecaRule 126 p q r`), parametrize `0 ≤ x` via `Int.le_total 0 x` as `x = (m : Int)` (`m : Nat`, with interior `m = m' + 1` so `(x - 1).natAbs = m'`, `x.natAbs = m' + 1`, `(x + 1).natAbs = m' + 2`), and write `u = 2 * (j' + 1)` in Case 4a and `n = 2 * (k' + 1)` in Case 5a so `Nat.choose_succ_succ'` (`Mathlib/Data/Nat/Choose/Basic.lean` `v4.34.1` line 66) applies without `j - 1` or `k - 1` subtraction preconditions.
     - **Repair A2-3 (`AUDIT-DOSSIER.md` §1.4, lines 156–157 & §1.6, line 182):** Outer-step iterate unfolding via `Function.iterate_succ_apply'` (`rw [ecaOrbit, Function.iterate_succ_apply', ← ecaOrbit]`).
     - **Repair A3-1 (`AUDIT-DOSSIER.md` §1.5, lines 171–172):** Exact Mathlib4 `v4.34.1` identifier `Choose.choose_modEq_choose_mod_mul_choose_div_nat` in `Mathlib.Data.Nat.Choose.Lucas` (`Lucas.lean` line 67, namespace `Choose`, **not** `Nat`), paired with `haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩` from `Mathlib.Data.Nat.Prime.Defs` (`Defs.lean` line 171).
     - **Repair A3-2 (`AUDIT-DOSSIER.md` §1.5, lines 173–174 & §1.6, line 186):** Explicit `Bool`-to-`Nat` bridges: `B n 0 = true ↔ g n = 1` (for `g n := n.choose (n / 2) % 2` via `Nat.mod_two_eq_zero_or_one`) to establish `rule126_middle_column_iff` first; `by_cases h : ∃ m : Nat, n = 2 ^ m - 1` (`if_pos` / `if_neg` on `(ecaOrbit 126 n 0).toNat`) to derive `rule126_middle_column_eq_a036987`; and `∀ b : Bool, (!b).toNat = 1 - b.toNat` (`cases b <;> rfl`) to derive `a267442_eq_a043545`.
3. **Statement-file hazards `S2`–`S5` honoured and flagged inline (`AUDIT-DOSSIER.md` §3.3, lines 281–293; `BRIEF.md` line 11):**
   - **Hazard S2 (lines 281–283):** `noncomputable def a036987` retains `open Classical in if ∃ m : Nat, n = 2 ^ m - 1 then 1 else 0` verbatim (primary `%F A036987` characterization; no bitwise `n &&& (n + 1)` substitution).
   - **Hazard S3 (lines 285–286):** `def a043545` retains `match Nat.digits 2 n with | [] => 0 | d :: ds => ds.foldl max d - ds.foldl min d` verbatim, with inline doc comment clarifying that `Nat.digits 2 0 = []` (`Digits/Defs.lean` line 84) maps to `0` via the `| [] => 0` branch (`AUDIT-DOSSIER.md` §3.2 item 5, line 269).
   - **Hazard S4 (lines 288–289):** `ecaRule` and `ecaStep` retained verbatim with inline verification note on bit order `4 * p.toNat + 2 * q.toNat + r.toNat`.
   - **Hazard S5 (lines 291–293; `BRIEF.md` line 11):** Statement file `(A)` contains **zero occurrences** of the forbidden reflection/native tactic tokens anywhere in code or comments; the inline `[Audit §3.3 Hazard S5]` guardrail positively mandates `cases p <;> cases q <;> cases r <;> rfl` or kernel `Decidable.decide` only.

### 1.3 Deliverable `(A)` — Corrected Draft Statement File (`Mathproofs/Rule129MiddleColumn.lean`)

> **Coordinator lift block `(A)`:** Ready to write verbatim to `Mathproofs/Rule129MiddleColumn.lean` in `derekblair/math-proofs` and compile under `leanprover/lean4:v4.34.1` per the checklist in §2.3.

```lean
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Logic.Function.Iterate -- [Audit §3.2 Item 3 / §3.3 Hazard S1] Explicit import for Nat.iterate (f^[n])

/-!
# OEIS A267442 / A043545 / A036987: Rule 129 and Rule 126 Single-Seed Middle Columns

Pinned target statements for candidate `a267442-eq-a043545` (`derekblair/math-proofs`).
Do NOT modify any `def` or `theorem` signature or definition body in this file once frozen.

## Audited Route A Proof-Lane Notes (Informational — Not Pinned Declarations)

* **[Audit §1.4 Repair A2-1 — Uniform `Bool` closed form]:** Define the Rule 126 space-time
  closed form with uniform `Bool` branches (avoiding `Prop`/`Bool` branch mismatch):
  `def B (n : Nat) (x : Int) : Bool :=`
  `  if x.natAbs ≤ n then Nat.choose n ((n - x.natAbs) / 2) % 2 == 1 else false`
* **[Audit §1.4 Repair A2-2 — Truncated-subtraction-safe indexing]:** Keep `n - x.natAbs`
  strictly inside `if x.natAbs ≤ n` so exterior cells (`x.natAbs > n`) never evaluate truncated
  `0`. After spatial reflection (`B n (-x) = B n x` and `ecaRule 126 r q p = ecaRule 126 p q r`),
  split `0 ≤ x` via `Int.le_total 0 x` and write `x = (m : Int)` for `m : Nat` (with `m = m' + 1`
  on positive interior cells so `(x - 1).natAbs = m'`, `x.natAbs = m' + 1`,
  `(x + 1).natAbs = m' + 2`). In positive even subcases, write `u = 2 * (j' + 1)` (interior
  Case 4a) and `n = 2 * (k' + 1)` (origin Case 5a) so `Nat.choose_succ_succ'` applies directly
  with zero `j - 1` or `k - 1` subtraction obligations.
* **[Audit §1.4 Repair A2-3 — Outer-step iterate unfolding]:** `(ecaStep R)^[n + 1] singleSeed`
  reduces definitionally (`Function.iterate_succ_apply`) to `(ecaStep R)^[n] (ecaStep R singleSeed)`,
  not `ecaStep R ((ecaStep R)^[n] singleSeed)`. Start inductive steps on `n` by rewriting with
  `Function.iterate_succ_apply'` (`rw [ecaOrbit, Function.iterate_succ_apply', ← ecaOrbit]`).
* **[Audit §1.5 Repair A3-1 — Exact Mathlib Lucas theorem identifier]:** In Mathlib `v4.34.1`
  (`Mathlib.Data.Nat.Choose.Lucas` + `Mathlib.Data.Nat.Prime.Defs`), one-step Lucas mod `p` lives
  in namespace `Choose` (not `Nat`): supply `haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩` and
  apply `Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 2 * k + 1) (k := k) (p := 2)`.
* **[Audit §1.5 Repair A3-2 — `Bool`-to-`Nat` bridges]:** Relate `B n 0 : Bool` to
  `g n := n.choose (n / 2) % 2 : Nat` via `B n 0 = true ↔ g n = 1` (`Nat.mod_two_eq_zero_or_one`)
  to prove `rule126_middle_column_iff` first; deduce `rule126_middle_column_eq_a036987` via
  `by_cases h : ∃ m : Nat, n = 2 ^ m - 1` (`if_pos` / `if_neg` on `Bool.toNat`); and deduce
  `a267442_eq_a043545` for `0 < n` using `∀ b : Bool, (!b).toNat = 1 - b.toNat`.
* **[Audit §3.3 Hazard S5 — Kernel-only finite `Bool` proofs]:** Discharge 3-bit `Bool` truth-table
  identities (`Lemma A1`, `C0`, `C1`) strictly via explicit case splits
  (`cases p <;> cases q <;> cases r <;> rfl`) or kernel `Decidable.decide`. Never invoke
  compiler-backed reduction or SAT/bitvector reflection tactics, which emit forbidden trust axioms
  outside `[propext, Classical.choice, Quot.sound]`.
-/

namespace Mathproofs.Rule129MiddleColumn

-- [Audit §3.3 Hazard S4] Verified exact Wolfram bit encoding b_{4p + 2q + r}(R) via Nat.testBit.
/-- Wolfram elementary cellular automaton local rule `R` (`0 ≤ R < 256`) on `Bool`:
neighborhood `(p, q, r)` reads bit `4 * p + 2 * q + r` of `R`. -/
def ecaRule (R : Nat) (p q r : Bool) : Bool :=
  R.testBit (4 * p.toNat + 2 * q.toNat + r.toNat)

-- [Audit §3.2 Item 5 & §3.3 Hazard S4] Total configuration Int → Bool preserves Rule 129 background
-- (0 at n = 0, transitioning 0 -> 1 at n = 1 and remaining 1 for all n ≥ 1 outside the light cone).
/-- One global synchronous step of rule `R` on the infinite integer lattice `Int → Bool`. -/
def ecaStep (R : Nat) (c : Int → Bool) : Int → Bool :=
  fun x => ecaRule R (c (x - 1)) (c x) (c (x + 1))

/-- Single ON (black) cell at `x = 0` in an infinite OFF (white) background. -/
def singleSeed : Int → Bool :=
  fun x => x == 0

-- [Audit §3.3 Hazard S1 & §1.4 Repair A2-3] Unchanged definition backed by explicit
-- `import Mathlib.Logic.Function.Iterate`; unfold generation `n + 1` via `Function.iterate_succ_apply'`.
/-- Configuration at generation `n` starting from `singleSeed` under rule `R`. -/
def ecaOrbit (R : Nat) (n : Nat) : Int → Bool :=
  (ecaStep R)^[n] singleSeed

/-- OEIS A267442: middle column (`x = 0`) of ECA Rule 129 from `singleSeed` (`0`/`1`-valued). -/
def a267442 (n : Nat) : Nat :=
  (ecaOrbit 129 n 0).toNat

-- [Audit §3.3 Hazard S2] Retains primary `∃ m : Nat, n = 2 ^ m - 1` characterization (%F A036987);
-- legitimately uses `Classical.choice` (allowed by pin manifest) — do not substitute bitwise expressions.
/-- OEIS A036987 (Fredholm-Rueppel sequence): `1` iff `n = 2 ^ m - 1` for some `m : Nat`, else `0`. -/
noncomputable def a036987 (n : Nat) : Nat :=
  open Classical in
  if ∃ m : Nat, n = 2 ^ m - 1 then 1 else 0

-- [Audit §3.2 Item 5 & §3.3 Hazard S3] Primary Kimberling %N A043545 digit-spread definition;
-- in Mathlib `Nat.digits 2 0 = []`, which the explicit `| [] => 0` branch maps to `0` (`0 = (0)_2`).
/-- OEIS A043545: `(maximal base-2 digit of n) - (minimal base-2 digit of n)`, offset `0`. -/
def a043545 (n : Nat) : Nat :=
  match Nat.digits 2 n with
  | [] => 0
  | d :: ds => ds.foldl max d - ds.foldl min d

/-- Rule 126 middle-column theorem (iff form): `C_126(n, 0) = true ↔ ∃ m, n = 2 ^ m - 1`. -/
theorem rule126_middle_column_iff (n : Nat) :
    ecaOrbit 126 n 0 = true ↔ ∃ m : Nat, n = 2 ^ m - 1 := by
  sorry

/-- Rule 126 middle-column theorem (sequence form): `(C_126(n, 0)).toNat = A036987(n)` for all `n`. -/
theorem rule126_middle_column_eq_a036987 (n : Nat) :
    (ecaOrbit 126 n 0).toNat = a036987 n := by
  sorry

/-- R. J. Mathar's conjecture (OEIS A267442, Jan 17 2016): `A267442(n) = A043545(n)` for all `n > 0`. -/
theorem a267442_eq_a043545 (n : Nat) (hn : 0 < n) :
    a267442 n = a043545 n := by
  sorry

end Mathproofs.Rule129MiddleColumn
```

---

## 2. Corrected Draft Pin Manifest (`~/workspace/math-fleet/pins/a267442-eq-a043545.md`)

### 2.1 Disposition of Mandatory Pre-Freeze Items 1–7 (`AUDIT-DOSSIER.md` §3.2)

1. **Item 1 — Remove non-schema `status: DRAFT` key and target coordinator desk path (`AUDIT-DOSSIER.md` §3.2 item 1, line 263; `pin-manifest-template.md` lines 5–8):**
   - `status: DRAFT` (`SCREEN-DOSSIER.md` line 278) is removed; Deliverable `(B)` begins directly with `candidate: a267442-eq-a043545` and is structured for verbatim materialization at `~/workspace/math-fleet/pins/a267442-eq-a043545.md` and registration in the coordinator's lane `REGISTRY`.
2. **Item 2 — Leave `frozen_by` as an explicit coordinator-only field (`AUDIT-DOSSIER.md` §3.2 item 2, line 264; `BRIEF.md` line 12):**
   - Per `BRIEF.md` line 12, `frozen_by` is **not** populated with this research-prep lane's identity; it is set to the explicit coordinator marker `<COORDINATOR_TO_FILL_AT_FREEZE>` for population at freeze execution (Step 5 of §2.3).
3. **Item 3 — Import fix applied in `(A)`; compilation, commit, `sha256`, and `commit` deferred to coordinator (`AUDIT-DOSSIER.md` §3.2 item 3, line 265; `BRIEF.md` lines 12, 19):**
   - The `Mathlib.Logic.Function.Iterate` import fix (`Hazard S1`) is applied in Deliverable `(A)` (§1.3). Compiling under `leanprover/lean4:v4.34.1`, committing `Mathproofs/Rule129MiddleColumn.lean` to `derekblair/math-proofs`, and populating `statement_file.sha256` (`<STATEMENT_SHA256_AT_FREEZE>`) and `statement_file.commit` (`<STATEMENT_COMMIT_AT_FREEZE>`) are **COORDINATOR-ONLY** actions specified step-by-step in §2.3 below.
4. **Item 4 — Switch `verbatim_quote: >` to `verbatim_quote: |` and include verbatim `%O` and `%Y A071035` lines (`AUDIT-DOSSIER.md` §3.1 Gate 1, line 250 & §3.2 item 4, line 266):**
   - `verbatim_quote` now uses literal block scalar `|` (preserving exact line breaks rather than YAML space-folding) and quotes verbatim from live OEIS text records (`A267442` `#13`, `A043545` `#55`, `A036987` `#249`, `A071035` `#38`, `A267366` `#20`) all 10 required lines, adding `%O A267442 0`, `%O A043545 0,1`, `%O A036987 0,1`, and `%Y A071035 Cf. A036987 (central column).`. In `strongest_published_form`, Palamarchuk's 2026 `ECA/Doubling.lean` (`LocalRule.finRule_two_dbl` on even-support doubled states) is also recorded per `AUDIT-DOSSIER.md` §3.1 Gate 2 (line 251) and `SCREEN-DOSSIER.md` §1.3 item 2 (lines 114–126).
5. **Item 5 — Fix `fidelity_notes` item 1 background stabilization wording and item 3 `Nat.digits 2 0 = []` wording (`AUDIT-DOSSIER.md` §3.2 item 5, lines 267–269 & §2.1 item 1, lines 198–200):**
   - `fidelity_notes` item 1 replaces `"alternates 0 -> 1 -> 1 -> ..."` (`SCREEN-DOSSIER.md` line 331) with `"starts at 0 at n = 0, transitions 0 -> 1 at n = 1, and remains 1 for all n >= 1"` (since $f_{129}(0,0,0) = 1$ and $f_{129}(1,1,1) = 1$), and cites Robert Price's exact `%t A267442` call `CellularAutomaton[129, {{1}, 0}, rows-1, {All, All}]` (`AUDIT-DOSSIER.md` line 199).
   - `fidelity_notes` item 3 replaces `"with 0 having single digit 0"` (`SCREEN-DOSSIER.md` line 335) with the exact Mathlib4 behavior: `Nat.digits 2 0 = []` (`Nat.digits_zero`), which the explicit `| [] => 0` branch maps to `0` to match conventional $0 = (0)_2$ ($\max\{0\} - \min\{0\} = 0$).
6. **Item 6 — Enumerate all 7 locked `def` declarations alongside the 3 pinned `theorem` declarations (`AUDIT-DOSSIER.md` §3.2 item 6, line 270; `pin-manifest-template.md` line 26):**
   - All 7 locked definitions (`ecaRule`, `ecaStep`, `singleSeed`, `ecaOrbit`, `a267442`, `a036987`, `a043545`) are explicitly listed by fully-qualified Lean name in `theorems:` (following `pin-manifest-template.md` line 26: `# repeat per theorem/definition in scope`) and cross-referenced in `fidelity_notes` item 5 so reviewers enforce zero silent edits to definitions as well as theorem headers.
7. **Item 7 — Bind `review_route` concretely to a Codex review lane (`AUDIT-DOSSIER.md` §3.2 item 7, line 271; `BRIEF.md` line 12):**
   - `review_route` names a **Codex review lane** (`OpenAI/Codex` reviewer pool $\ne$ `Gemini/Argon` author-side research pool across `argon-rule129-screen-20261026`, `argon-rule129-audit-20261026`, and `argon-rule129-pinfreeze-prep-20261027`), without inventing a specific machine name.

### 2.2 Deliverable `(B)` — Corrected Freeze-Ready Draft Pin Manifest

> **Coordinator lift block `(B)`:** Target desk location `~/workspace/math-fleet/pins/a267442-eq-a043545.md`. Contains **zero** draft schema keys; only `frozen_by`, `statement_file.sha256`, and `statement_file.commit` await coordinator freeze execution per §2.3.

```yaml
candidate: a267442-eq-a043545
repo: derekblair/math-proofs
created: 2026-10-27
frozen_by: <COORDINATOR_TO_FILL_AT_FREEZE>
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
  sha256: <STATEMENT_SHA256_AT_FREEZE>
  commit: <STATEMENT_COMMIT_AT_FREEZE>
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

### 2.3 Coordinator Compile-and-Freeze Checklist (Execute in Exact Order)

The coordinator executes Steps 1–6 in order on the coordinator host (`BRIEF.md` line 12; `AUDIT-DOSSIER.md` §3.2 items 1–3 & §3.3 Hazard S2; `pin-manifest-template.md` lines 5, 42–45). Every command below is runnable verbatim; only the two repository-derived freeze hashes (`<STATEMENT_SHA256_AT_FREEZE>`, `<STATEMENT_COMMIT_AT_FREEZE>`) and the coordinator identity marker (`<COORDINATOR_TO_FILL_AT_FREEZE>`) are substituted into the manifest in Step 5.

1. **Sync a clean `derekblair/math-proofs` checkout on `master` and verify toolchain `leanprover/lean4:v4.34.1`:**
   ```bash
   REPO_DIR="${MATH_PROOFS_DIR:-$HOME/projects/math-proofs}"
   if [ ! -d "$REPO_DIR/.git" ]; then
     git clone git@github.com:derekblair/math-proofs.git "$REPO_DIR"
   fi
   cd "$REPO_DIR"
   git checkout master
   git pull --ff-only origin master
   test -z "$(git status --porcelain)"
   grep -Fx 'leanprover/lean4:v4.34.1' lean-toolchain
   lake env lean --version
   lake exe cache get
   ```

2. **Write Deliverable `(A)` verbatim to `Mathproofs/Rule129MiddleColumn.lean` and run static trust-policy checks (leaving `Mathproofs.lean` untouched so `defaultTargets` stays `sorry`-free until proof closure):**
   ```bash
   DOSSIER_FILE="${PINFREEZE_DOSSIER:-/root/math-fleet/lanes/argon-rule129-pinfreeze-prep-20261027/DOSSIER.md}"
   # Override PINFREEZE_DOSSIER if copied to another path on the coordinator host:
   awk '/^```lean$/{flag=1; next} /^```$/ && flag{flag=0; exit} flag' "$DOSSIER_FILE" \
     > "$REPO_DIR/Mathproofs/Rule129MiddleColumn.lean"
   cd "$REPO_DIR"
   ! grep -nE 'native_decide|bv_decide|ofReduceBool|axiom ' Mathproofs/Rule129MiddleColumn.lean
   test "$(grep -cE '^[[:space:]]*sorry$' Mathproofs/Rule129MiddleColumn.lean)" -eq 3
   ```

3. **Compile `Mathproofs/Rule129MiddleColumn.lean` under `leanprover/lean4:v4.34.1` and run non-mutating `#check` / `#print axioms` / `#eval` sanity checks (`AUDIT-DOSSIER.md` §3.2 item 3 & §3.3 Hazard S2):**
   ```bash
   cd "$REPO_DIR"
   lake env lean Mathproofs/Rule129MiddleColumn.lean
   lake build Mathproofs.Rule129MiddleColumn
   lake env lean --stdin <<'EOF'
   import Mathproofs.Rule129MiddleColumn
   open Mathproofs.Rule129MiddleColumn
   #check @ecaRule
   #check @ecaStep
   #check @singleSeed
   #check @ecaOrbit
   #check @a267442
   #check @a036987
   #check @a043545
   #check @rule126_middle_column_iff
   #check @rule126_middle_column_eq_a036987
   #check @a267442_eq_a043545
   #print axioms ecaRule
   #print axioms ecaStep
   #print axioms singleSeed
   #print axioms ecaOrbit
   #print axioms a267442
   #print axioms a036987
   #print axioms a043545
   #eval List.map (fun n => (ecaOrbit 126 n 0).toNat) (List.range 9) -- expected: [1, 1, 0, 1, 0, 0, 0, 1, 0]
   #eval List.map a267442 (List.range 9)                             -- expected: [1, 0, 1, 0, 1, 1, 1, 0, 1]
   #eval List.map a043545 (List.range 9)                             -- expected: [0, 0, 1, 0, 1, 1, 1, 0, 1]
   EOF
   ```

4. **Commit `Mathproofs/Rule129MiddleColumn.lean` to `derekblair/math-proofs`, push `master`, and record `statement_file.sha256` + `statement_file.commit`:**
   ```bash
   cd "$REPO_DIR"
   git add Mathproofs/Rule129MiddleColumn.lean
   test "$(git diff --cached --name-only)" = "Mathproofs/Rule129MiddleColumn.lean"
   git commit -m "Pin statement: Rule 129 / Rule 126 middle column (a267442-eq-a043545)"
   git push origin master
   STMT_SHA256="$(sha256sum Mathproofs/Rule129MiddleColumn.lean | awk '{print $1}')"
   STMT_COMMIT="$(git rev-parse HEAD)"
   printf 'Recorded statement_file.sha256: %s\nRecorded statement_file.commit: %s\n' "$STMT_SHA256" "$STMT_COMMIT"
   ```

5. **Materialize `~/workspace/math-fleet/pins/a267442-eq-a043545.md` from Deliverable `(B)`, fill `<STATEMENT_SHA256_AT_FREEZE>`, `<STATEMENT_COMMIT_AT_FREEZE>`, and `frozen_by`, and verify zero placeholders remain:**
   ```bash
   mkdir -p "$HOME/workspace/math-fleet/pins"
   PIN_FILE="$HOME/workspace/math-fleet/pins/a267442-eq-a043545.md"
   COORDINATOR_HANDLE="${COORDINATOR_ID:-$(whoami)@$(hostname -s)}"
   FREEZE_DATE="$(date -u +%F)"
   {
     printf '# Pin Manifest — a267442-eq-a043545\n\n```yaml\n'
     awk '/^```yaml$/{flag=1; next} /^```$/ && flag{flag=0; exit} flag' "$DOSSIER_FILE"
     printf '```\n'
   } > "$PIN_FILE"
   sed -i \
     -e "s|^created: .*|created: ${FREEZE_DATE}|" \
     -e "s|<COORDINATOR_TO_FILL_AT_FREEZE>|${COORDINATOR_HANDLE}|g" \
     -e "s|<STATEMENT_SHA256_AT_FREEZE>|${STMT_SHA256}|g" \
     -e "s|<STATEMENT_COMMIT_AT_FREEZE>|${STMT_COMMIT}|g" \
     "$PIN_FILE"
   ! grep -nE '<[A-Z0-9_]+>|^status:' "$PIN_FILE"
   cat "$PIN_FILE"
   ```

6. **Register the frozen manifest in the coordinator's lane `REGISTRY` (`~/workspace/math-fleet/REGISTRY.md`) and record verification outputs before any proof-lane launch (`pin-manifest-template.md` lines 5, 44–45):**
   ```bash
   ls -l "$HOME/workspace/math-fleet/pins/a267442-eq-a043545.md"
   sha256sum "$HOME/workspace/math-fleet/pins/a267442-eq-a043545.md"
   # Record ~/workspace/math-fleet/pins/a267442-eq-a043545.md, $STMT_SHA256, $STMT_COMMIT,
   # and review_route (Codex review lane) in ~/workspace/math-fleet/REGISTRY.md prior to launching any proof lane.
   ```


---

## 3. Gate-by-Gate Self-Audit Table

Every mandatory pre-freeze item (`AUDIT-DOSSIER.md` §3.2, lines 263–271), Route A formalization repair (`AUDIT-DOSSIER.md` §1.4–§1.6), statement-file hazard (`AUDIT-DOSSIER.md` §3.3, lines 277–293), and pin-manifest gate (`AUDIT-DOSSIER.md` §3.1, lines 250–255) is mapped below to its exact section and 1-based line numbers in this `DOSSIER.md`, or explicitly marked `NOT DISCHARGED` with the governing reason (`BRIEF.md` line 13).

### 3.1 Pre-Freeze Items 1–7 (`AUDIT-DOSSIER.md` §3.2)

| Item | Requirement (`AUDIT-DOSSIER.md` / `BRIEF.md`) | Status | Location in `DOSSIER.md` / Reason if Not Discharged |
|---|---|---|---|
| **Item 1 (Schema)** | Remove non-schema `status: DRAFT` key so manifest begins with `candidate:` (`AUDIT-DOSSIER.md` line 263; `BRIEF.md` line 12) | **DISCHARGED** | §2.1 (lines 152–153); Deliverable `(B)` (§2.2, line 173); enforced in §2.3 Step 5 grep check (line 378). |
| **Item 1 (Desk & `REGISTRY` write)** | Materialize frozen manifest at `~/workspace/math-fleet/pins/a267442-eq-a043545.md` and register in lane `REGISTRY` (`AUDIT-DOSSIER.md` line 263) | **NOT DISCHARGED (COORDINATOR-ONLY)** | Research-only lane (`BRIEF.md` lines 4, 12, 19: no writes outside this lane folder, and freeze cannot precede Lean compilation/commit). Exact commands provided in §2.3 Steps 5–6 (lines 361–388). |
| **Item 2** | Prepare `frozen_by` as a clearly-marked coordinator field (NOT filled with prep-lane identity) and `created` date (`AUDIT-DOSSIER.md` line 264; `BRIEF.md` line 12) | **DISCHARGED AS FREEZE-READY DRAFT** *(live value COORDINATOR-ONLY)* | §2.1 (lines 154–155); Deliverable `(B)` (§2.2, lines 175–176: `frozen_by: <COORDINATOR_TO_FILL_AT_FREEZE>`); populated at freeze in §2.3 Step 5 (lines 365–374). |
| **Item 3a (Imports)** | Fix statement-file imports before compilation (`AUDIT-DOSSIER.md` line 265 & §3.3 Hazard S1) | **DISCHARGED** | §1.1 (line 17); §1.2 (line 23); Deliverable `(A)` (§1.3, line 43: `import Mathlib.Logic.Function.Iterate`). |
| **Item 3b (Compile, Commit & Hashes)** | Compile under `leanprover/lean4:v4.34.1`, commit to `derekblair/math-proofs`, populate `statement_file.sha256` + `statement_file.commit` (`AUDIT-DOSSIER.md` line 265; `BRIEF.md` line 12) | **NOT DISCHARGED (COORDINATOR-ONLY)** | Forbidden in this research lane (`BRIEF.md` lines 4, 12, 19: no Lean execution, no repo writes, no GitHub writes). Marked via `<STATEMENT_SHA256_AT_FREEZE>` and `<STATEMENT_COMMIT_AT_FREEZE>` in Deliverable `(B)` (§2.2, lines 209–210); exact ordered coordinator commands in §2.3 Steps 1–5 (lines 292–380). |
| **Item 4** | Switch `verbatim_quote: >` to `verbatim_quote: |` and include `%O A267442 0`, `%O A043545 0,1`, `%O A036987 0,1`, and `%Y A071035 Cf. A036987 (central column).` (`AUDIT-DOSSIER.md` lines 250, 266) | **DISCHARGED** | §2.1 (lines 158–159); Deliverable `(B)` (§2.2, lines 184–194; plus Palamarchuk 2026 formal near-miss added to `strongest_published_form` on lines 202–204 per `AUDIT-DOSSIER.md` line 251). |
| **Item 5** | Fix `fidelity_notes` item 1 (`0 -> 1` at `n = 1` and remains `1` for `n >= 1`, plus exact `%t A267442`) and item 3 (`Nat.digits 2 0 = []` mapped by `| [] => 0` to `0`) (`AUDIT-DOSSIER.md` lines 199, 267–269) | **DISCHARGED** | §2.1 (lines 160–162); Deliverable `(B)` (§2.2, `fidelity_notes` item 1 on lines 255–259 and item 3 on lines 264–270); mirrored in Deliverable `(A)` comments (§1.3, lines 93–94 & 120–121). |
| **Item 6** | Enumerate all 7 locked `def` declarations (`ecaRule`, `ecaStep`, `singleSeed`, `ecaOrbit`, `a267442`, `a036987`, `a043545`) in `theorems` or `fidelity_notes` (`AUDIT-DOSSIER.md` line 270) | **DISCHARGED** | §2.1 (lines 163–164); Deliverable `(B)` (§2.2, `theorems:` entries on lines 224–247 and `fidelity_notes` item 5 on lines 274–278). |
| **Item 7** | Bind `review_route` concretely to a Codex review lane (`reviewer pool != Gemini/Argon author pool`, no invented machine; `AUDIT-DOSSIER.md` line 271; `BRIEF.md` line 12) | **DISCHARGED** | §2.1 (lines 165–166); Deliverable `(B)` (§2.2, `review_route:` lines 283–285). |

### 3.2 Route A Repairs (`A2-1`–`A3-2`), Hazards (`S1`–`S5`), and Pin Gates (`Gates 1–6`)

| Audit Item / Gate | Requirement (`AUDIT-DOSSIER.md` / `BRIEF.md`) | Status | Location in `DOSSIER.md` |
|---|---|---|---|
| **Repair A2-1** | Uniform `Bool` return type across branches of `B : Nat → Int → Bool` (`AUDIT-DOSSIER.md` §1.4, lines 152–153; `BRIEF.md` line 11) | **DISCHARGED** *(in comments)* | §1.2 (line 26); Deliverable `(A)` docblock (§1.3, lines 53–56). |
| **Repair A2-2** | Truncated-subtraction-safe formulation: `n - x.natAbs` guarded inside `if x.natAbs ≤ n`, `x = (m : Int)` (`m = m' + 1`), and `u = 2 * (j' + 1)` / `n = 2 * (k' + 1)` (`AUDIT-DOSSIER.md` §1.4, lines 17, 154–155; `BRIEF.md` line 11) | **DISCHARGED** *(in comments)* | §1.2 (line 27); Deliverable `(A)` docblock (§1.3, lines 57–64). |
| **Repair A2-3** | Outer-step iterate unfolding via `Function.iterate_succ_apply'` (`AUDIT-DOSSIER.md` §1.4, lines 156–157 & §1.6, line 182; `BRIEF.md` line 11) | **DISCHARGED** | §1.1 (line 17); §1.2 (line 28); Deliverable `(A)` executable import (line 43) and inline notes (lines 65–68, 103–104). |
| **Repair A3-1** | Correct Mathlib4 `v4.34.1` name `Choose.choose_modEq_choose_mod_mul_choose_div_nat` with `Fact (Nat.Prime 2)` (`AUDIT-DOSSIER.md` §1.5, lines 171–172; `BRIEF.md` line 11) | **DISCHARGED** *(in comments)* | §1.2 (line 29); Deliverable `(A)` docblock (§1.3, lines 69–72). |
| **Repair A3-2** | Explicit `Bool`-to-`Nat` bridges (`B n 0 = true ↔ g n = 1`, `if_pos`/`if_neg` on `Bool.toNat`, `(!b).toNat = 1 - b.toNat`; `AUDIT-DOSSIER.md` §1.5, lines 173–174 & §1.6, line 186; `BRIEF.md` line 11) | **DISCHARGED** *(in comments)* | §1.2 (line 30); Deliverable `(A)` docblock (§1.3, lines 73–77). |
| **Hazard S1** | Choose ONE of explicit `import Mathlib.Logic.Function.Iterate` or recursive `ecaOrbit`; justify choice, free unfolding lemmas, and cost (`AUDIT-DOSSIER.md` §3.3, lines 277–279; `BRIEF.md` lines 11, 17) | **DISCHARGED** *(Option 1 selected)* | Choice, free `Function.iterate_*` lemmas, and recorded cost in §1.1 (line 17); applied in Deliverable `(A)` (§1.3, line 43 & lines 103–107) and Deliverable `(B)` (§2.2, lines 260–263). |
| **Hazard S2** | Keep primary `∃ m : Nat, n = 2 ^ m - 1` characterization of `a036987`; do not substitute bit-hack (`AUDIT-DOSSIER.md` §3.3, lines 281–283; `BRIEF.md` line 11) | **DISCHARGED** | §1.2 (line 32); Deliverable `(A)` (§1.3, lines 113–118); Deliverable `(B)` (§2.2, lines 240–243, 268–270); `#eval` exclusion honoured in §2.3 Step 3 (lines 341–345). |
| **Hazard S3** | Retain exact `foldl max` / `foldl min` definition of `a043545` with `[] => 0` (`AUDIT-DOSSIER.md` §3.3, lines 285–286) | **DISCHARGED** | §1.2 (line 33); Deliverable `(A)` (§1.3, lines 120–126); Deliverable `(B)` (§2.2, lines 244–247, 264–268). |
| **Hazard S4** | Retain verified `Nat.testBit` Wolfram encoding in `ecaRule` and `Int → Bool` carrier in `ecaStep` (`AUDIT-DOSSIER.md` §3.3, lines 288–289) | **DISCHARGED** | §1.2 (line 34); Deliverable `(A)` (§1.3, lines 87–97); Deliverable `(B)` (§2.2, lines 224–230, 255–259). |
| **Hazard S5** | Zero `bv_decide` / `native_decide` anywhere in statement file (including comments); kernel-only finite `Bool` proof rule (`AUDIT-DOSSIER.md` §3.3, lines 291–293; `BRIEF.md` line 11) | **DISCHARGED** | §1.2 (line 35); Deliverable `(A)` (§1.3, lines 41–144: 0 occurrences of forbidden tactic tokens; positive kernel-only rule on lines 78–82); Deliverable `(B)` (`trust_policy`, lines 249–253); §2.3 Step 2 grep check (line 314). |
| **Gates 1–6 (`§3.1`)** | Verbatim quotes (`Gate 1`), strongest published form (`Gate 2`), exact theorem names (`Gate 3`), `axiom_allowlist` (`Gate 4`), `trust_policy` (`Gate 5`), and `delta_vs_source = NONE` + zero theorem-strength change (`Gate 6`; `AUDIT-DOSSIER.md` lines 250–255; `BRIEF.md` line 11) | **DISCHARGED** | §1.2 (lines 21–23); Deliverable `(A)` (§1.3, lines 128–143); Deliverable `(B)` (§2.2, lines 184–206, 211–253, 279–282). |


---

## 4. What This Preparation Does NOT Show

1. **A corrected draft pin manifest is NOT a frozen pin:** Deliverable `(B)` (§2.2) remains an unmaterialized, unhashed preparation artifact inside this research lane's folder (`BRIEF.md` lines 4, 12, 14). Until a coordinator executes the compile-and-freeze checklist (§2.3 Steps 1–6), writes `~/workspace/math-fleet/pins/a267442-eq-a043545.md` with populated `frozen_by`, `statement_file.sha256`, and `statement_file.commit`, and registers that path in the lane `REGISTRY` (`pin-manifest-template.md` lines 5, 42–45; `AUDIT-DOSSIER.md` §3.2 items 1–3, lines 263–265), no frozen pin contract exists.
2. **A corrected draft statement file is NOT a Lean 4 compilation:** Under this lane's `RESEARCH ONLY` rules (`BRIEF.md` lines 3–4, 19), no `lean` or `lake` binary was invoked. While `import Mathlib.Logic.Function.Iterate`, `import Mathlib.Data.Nat.Digits.Defs`, and all referenced Mathlib `v4.34.1` identifiers were verified against the upstream `leanprover-community/mathlib4` `v4.34.1` source tree, actual elaboration of Deliverable `(A)` (§1.3) against `derekblair/math-proofs`'s `leanprover/lean4:v4.34.1` toolchain (`AUDIT-DOSSIER.md` §4 item 2, line 299) is established only when the coordinator runs `lake env lean Mathproofs/Rule129MiddleColumn.lean` and `lake build Mathproofs.Rule129MiddleColumn` in §2.3 Step 3.
3. **Inline Route A repair notes are NOT a formal or mathematical proof:** Embedding Repairs `A2-1`–`A2-3` and `A3-1`–`A3-2` in Deliverable `(A)`'s comment block (§1.3, lines 51–83) leaves all three pinned theorems (`rule126_middle_column_iff`, `rule126_middle_column_eq_a036987`, `a267442_eq_a043545`) terminated by placeholder `sorry` (`AUDIT-DOSSIER.md` §4 item 1, line 298). Neither Mathar's conjecture (`A267442(n) = A043545(n)` for $n > 0$) nor the Rule 126 middle-column theorem ($C_{126}(n, 0) = A036987(n)$ for $n \ge 0$) is proved until a post-freeze solution replaces every `sorry`, compiles cleanly under `lake build`, passes `#print axioms` restricted to `[propext, Classical.choice, Quot.sound]`, and clears the cross-model Codex review lane (`Deliverable (B)`, lines 248–253, 283–285).
4. **Nothing in this dossier authorizes launching a proof lane:** Preparing lift-ready drafts `(A)` and `(B)` does not waive coordinator pin-freeze execution (§2.3), `REGISTRY` recording (`pin-manifest-template.md` line 5), or coordinator scheduling authorization (`BRIEF.md` line 14; `AUDIT-DOSSIER.md` §4 item 3, line 300).
5. **No extension beyond the bounded scope of the two input dossiers:** Per `BRIEF.md` line 17, this dossier imports no prior-art or mathematical claims beyond `SCREEN-DOSSIER.md` and `AUDIT-DOSSIER.md`: bibliographic absence of prior proofs remains bounded by reachable public corpora (`SCREEN-DOSSIER.md` §5.2 item 2, line 406; `AUDIT-DOSSIER.md` §4 item 4, line 301), conservative disclosure of the empirical Rule 126 middle-column folklore (`A071035`, `A267366`, Sloane 2015, Macfarlane 2016; `SCREEN-DOSSIER.md` §3 item 3, lines 210–213) remains mandatory in any downstream PR or OEIS submission, and all results remain strictly restricted to `singleSeed` rather than general ECA initial configurations (`SCREEN-DOSSIER.md` §5.2 item 5, line 409; `AUDIT-DOSSIER.md` §4 item 5, line 302).

DOSSIER COMPLETE
