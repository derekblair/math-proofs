# LEAN_REVIEW — C064 Refutation (OEIS `A115861` / `A391736`)

## 1. Module Map

| File (repo-relative under `lean/`) | Role | Proof Parts Covered |
|---|---|---|
| `ComparatorChallenges/C064CarrylessBound.lean` | Standalone Mathlib-only comparator challenge file (`sorry` by design) | Defines `clMul`, `rowA391736Values`, `A115861_set`, `A115861`; pins the 4 headline theorem signatures (`c064_witness`, `c064_refutation_card`, `c064_refutation_pointwise`, `c064_refutation_doubling`). |
| `ComparatorChallenges/C064CarrylessBound.json` | Comparator configuration | Maps challenge module to `MathProofs.SeamB.C064.Solution`, lists the 4 definitions, 4 theorems, and allowed axioms `[propext, Quot.sound, Classical.choice]`. |
| `MathProofs/SeamB/C064/Statement.lean` | Frozen Seam B statement stub (`sorry` by design) | Exact transcription of definitions and 4 headline theorem signatures from `PIN-C064.md` v1. |
| `MathProofs/SeamB/C064/Solution.lean` | Complete sorry-free proof (843 LOC) | **§1**: XOR/bit algebraic lemmas + `clMul_le_mul`, `clMul_two_mul`, `clMul_two_mul_left`, and `clMul_testBit` (exact $\mathbb{F}_2[X]$ polynomial convolution equivalence).<br>**§2**: Zero-recursion 9-bit GMP XOR (`xor9`, `xor_low_9`) and verified multiplication chain checker (`checkClMulChain`, `clMul_of_chain`).<br>**§3**: General carry-automaton soundness (`carryEq_parity`, `carryEq_zero`, `carryEq_step_even`, `carryEq_step_odd`).<br>**§4**: 73-state indexed carry-automaton certificate (`certRows`, `checkCert_eq_true : checkCert = true := rfl`) proving `no_sol_lt_2pow28` ($\forall i \in [1, 2^{28}),\; 215 \cdot i \ne 239 \otimes i$).<br>**§5**: 29-step verified product `clMul_239_302775165`, Karttunen's lower bound `rowA391736_card_ge`, general strict-increase lemmas `rowA391736_card_gt_of_new` & `A115861_lt_double_of_new`, and all 4 headline theorems (`c064_witness`, `c064_refutation_card`, `c064_refutation_pointwise`, `c064_refutation_doubling`).<br>**§6**: Secondary kernel-verified product identities `c064_secondary_n4` ($n=391 > 391^4$) and `c064_secondary_n5` ($n=511 > 511^5$). |

## 2. Exact Replay Commands

From `repo/lean/` (with `.lake/packages` symlinked to `/home/derekblair/lean-cache/mathlib-d13f23b7/packages`, toolchain `leanprover/lean4:v4.34.1`):

```bash
# 1. Build solution (0 errors, 0 warnings, 0 sorry; ~2.5s)
lake build MathProofs.SeamB.C064.Solution

# 2. Independent Lean 4.34.1 kernel replay via leanchecker
lake env leanchecker MathProofs.SeamB.C064.Solution

# 3. Print axioms for all pinned and auxiliary theorems
lake env lean --stdin <<'EOF'
import MathProofs.SeamB.C064.Solution
#print axioms C064.c064_witness
#print axioms C064.c064_refutation_card
#print axioms C064.c064_refutation_pointwise
#print axioms C064.c064_refutation_doubling
#print axioms C064.clMul_testBit
#print axioms C064.no_sol_lt_2pow28
#print axioms C064.rowA391736_card_ge
#print axioms C064.c064_secondary_n4
#print axioms C064.c064_secondary_n5
EOF
```

## 3. Axiom Audit Results (Recorded Verbatim)

From `evidence/lean_axioms.log` (`2026-11-27T03:23Z`):

```text
'C064.c064_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'C064.c064_refutation_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'C064.c064_refutation_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound]
'C064.c064_refutation_doubling' depends on axioms: [propext, Classical.choice, Quot.sound]
'C064.clMul_testBit' depends on axioms: [propext, Classical.choice, Quot.sound]
'C064.no_sol_lt_2pow28' depends on axioms: [propext, Classical.choice, Quot.sound]
'C064.rowA391736_card_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'C064.c064_secondary_n4' depends on axioms: [propext, Classical.choice, Quot.sound]
'C064.c064_secondary_n5' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **Standard axioms only:** `[propext, Classical.choice, Quot.sound]`.
- **Forbidden trust escapes:** `0` occurrences of `sorry`, `admit`, `axiom`, `native_decide`, `Lean.ofReduceBool`, `Lean.trustCompiler`, `implemented_by`, or `unsafe` in `Solution.lean`.

## 4. Statement Identity & Comparator Audit

1. **Dual-environment kernel `Expr` identity check (`evidence/lean_expr_identity.log`):**
   ```text
   DEF C064.clMul: type_eq=true, body_eq=true
   DEF C064.rowA391736Values: type_eq=true, body_eq=true
   DEF C064.A115861_set: type_eq=true, body_eq=true
   DEF C064.A115861: type_eq=true, body_eq=true
   THM C064.c064_witness: type_eq=true
   THM C064.c064_refutation_card: type_eq=true
   THM C064.c064_refutation_pointwise: type_eq=true
   THM C064.c064_refutation_doubling: type_eq=true
   ALL 4 DEFINITIONS AND ALL 4 HEADLINE THEOREMS: EXACT EXPR IDENTITY PASS
   ```
2. **Independent `leanchecker` replay (`evidence/lean_checker.log`):**
   `lake env leanchecker MathProofs.SeamB.C064.Solution` → `exit=0`.
3. **External comparator / v4.36.0 export attempt (`evidence/comparator_attempt.log`):**
   `comparator`, `landrun`, and `lean4export` are not present on `bakkie`. Probing bakkie's `v4.36.0` `leanexport`, `leanchecker-paranoid`, and `lean4lean` against the `v4.34.1`-compiled `.olean` fails with:
   `failed to read file '.../MathProofs/SeamB/C064/Solution.olean', incompatible header`.
   Accordingly, full external `comparator` compliance is **not** claimed; the verified fallback status is **dual-environment `Expr` identity PASS + allowlist-only axiom audit PASS + v4.34.1 `leanchecker` PASS**.
