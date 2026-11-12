# Source evidence for SS-004 promotion review

This is an evidence-gathering component of the current independent review, not a separate approval or review of our own work. All substantive commands and complete outputs are recorded in `evidence/src_*.json`; every command below exited 0. No tracked repository files changed and no Lean commands ran in this component.

## Claims 1, 4 and 6

**Claim 1 — CONFIRMED.** `git diff --no-ext-diff --numstat 0b17820a79f969c883b363de670402512b47341d HEAD` returns exactly:

```text
9   0   CONTENTS.md
37  0   FORMALIZATION_CATALOGUE.md
```

The exact diff is `evidence/src_diff.json`; count output is `src_numstat.json`. No Lean or pin changes appear (`src_lean_diff.json`, empty output). The catalogue's unchanged row 51 lists all six `[PROVED*]`. Added catalogue lines 115–116 call them staged, lines 144–148 explicitly preserve the labels and state that no theorem is promoted. Added CONTENTS lines 265–266 expressly preserve the six staged labels and distinguish census review from SS-004/status-promotion review. CONTENTS line 256's `[PROVED]` family heading already existed in base and line 258 already distinguished the staged extensions; the addition does not turn that heading into a promotion of the six. Line evidence: `src_doc_lines.json`, `src_labels.json`.

**Claim 4 — CONFIRMED.** `python3 ../source_checks.py` executes and records `git show <revision>:Mathproofs/ESSubfamilyExtended.lean` independently at all three revisions, hashes the returned bytes, and compares equality. The result is `BYTE_IDENTICAL_ALL_THREE: True` (`src_hashes_screen.json`). Each has 33,832 bytes and SHA256:

```text
c9d3c0ebb6474c5b134b2c85cae36ff84cd2af43  4640f46d407482548dddf9c254e1892d31d78da4641913fd1f6eee44a32346c9
0b17820a79f969c883b363de670402512b47341d  4640f46d407482548dddf9c254e1892d31d78da4641913fd1f6eee44a32346c9
344e3352e2f1106846e1ec3cbef0b04bff99e187  4640f46d407482548dddf9c254e1892d31d78da4641913fd1f6eee44a32346c9
```

**Claim 6 — graph/tree portion CONFIRMED.** `git log -1 --format=fuller --parents HEAD` (`src_status_ancestry.json`) returns:

```text
commit 344e3352e2f1106846e1ec3cbef0b04bff99e187 f90871b2fa73d82bb57e0804703a4b2e96b0a2a4 0b17820a79f969c883b363de670402512b47341d
```

Both `git merge-base --is-ancestor <parent> HEAD` commands exit 0 (`src_branch_ancestors.json`). The base-to-head tree difference is exclusively the two document additions above. This proves preservation of the earlier PR head and merge ancestry, rather than rebasing it away. A Git graph alone does not prove that no historical force push ever occurred; inspect the GitHub timeline before making that broader assertion.

## Annex B — CLEAR in the bounded source inspection

This is a status-promotion review with no statement changes. The following direct source inspection avoids relying on historical prose claims that the proofs were reviewed. It does not replace the required compiled-statement and axiom replay.

1. **Hidden hypotheses in data types — CLEAR.** The six theorem signatures use `Nat` and `Finset Nat`, with arithmetic, positivity, pinning and parent-determination assumptions explicitly in the signatures. `AdmCond` is the explicit conjunction at `Mathproofs/ESSubfamilyExtended.lean:301–304`. `admission_criterion` requires positive `A, qe, f, k` and `f ∣ A*qe` (351–357). `a0_constancy` and `M_const` expose each divisor's prime-pinning assumption (582–588 and 611–617). `split_layered_repaired` exposes both parent-filter equalities (687–690); these are hypotheses, not an independently proved determination theorem. The paper also calls determination an unproved assumption (TeX 306–315 and 449–456). Evidence: `src_definitions.json`, `src_line_sections.json`, `src_paper_statements.json`.
2. **Vacuous branches doing the real work — CLEAR for the stated repaired result.** The split/layered theorem allows empty parent sets only for the two forward implications; its equivalences explicitly require `(P₁ ∪ P₂).Nonempty` at lines 693–695. The nonempty branch obtains an actual member at 712, branches on which set contains it at 713, and uses that witness at 715 or 718. The underlying restatement obtains a witness at 649 and uses it to derive residue equality; it obtains a witness again at 660 to rule out self-disjointness. The one-way disjointness proof checks an arbitrary common member against both filter predicates (699–709), rather than assuming the sets empty. Arithmetic proofs exclude zero inputs explicitly and prove quotient nonzeroness (351–371, 441–455, 526–543). Evidence: `src_line_sections.json`.
3. **Positivity asserted instead of constructed — CLEAR within the explicit positive-input scope.** Input positivity is a declared domain restriction; derived gcd positivity and quotient nonzeroness are proved at 364–371 and 533–543. The quotient witness in `excess_prime_dvd_u` comes from `hfint` at 448 and is proved nonzero at 449–453. `u_eq_Aqe_div_f` requires `0 < f` and proves cancellation at 437–438. These are not claims of constructing arbitrary positive parameters. Evidence: `src_line_sections.json`.

Quantifiers and constants: all shape parameters are universally quantified; the constancy proof factors through the explicit shape-only expression `A / gcd A qe` (526–529, 589–590), independent of `k`. The modulus and residue data in the finite-set theorem are explicit universally quantified inputs. No input-dependent oracle or advice definition occurs in these six statements or the visible local `AdmCond` definition. No asymptotic machine/instance quantifier comparison is applicable.

## Annex C — CLEAR for active changes; lexical occurrences explained

The scanner in `source_checks.py` blanks nested Lean block comments, line comments and escaped string literals while preserving character and newline positions. It reconstructs just added diff lines at their HEAD file line numbers. Complete command/output: `src_hashes_screen.json`; scanner hash: `src_script_sha256.json`.

| File/scope | sorry | admit | sorryAx | axiom | native_decide | ofReduceBool | implemented_by | unsafe |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| CONTENTS.md added lines | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 0 |
| FORMALIZATION_CATALOGUE.md added lines | 0 | 0 | 1 | 3 | 0 | 0 | 0 | 0 |
| ESSubfamilyExtended.lean at c9d3c0e | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| ESSubfamilyExtended.lean at 0b17820a | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| ESSubfamilyExtended.lean at 344e3352 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

The diff hits are Markdown discussion of audits: CONTENTS 260; catalogue 117, 127 and 132 for `axiom`; catalogue 122 for `sorryAx`. They are not executable declarations or proof escapes. The module's only import is `import Mathlib` at line 42. All Lean sources and dependency/toolchain manifests are unchanged against the reviewed base (`src_numstat.json`, `src_lean_diff.json`), hence the declared Lean import closure is unchanged. This scanner did **not** freshly audit all of Mathlib's implementation; the brief's adapted requirement is the diff screen. Root must report actual axiom-replay results separately, without substituting these zero lexical counts for compiled axiom output.

## Annex D — CLEAR as to statement/status delta

The six statements are byte-identical at the audited, merged and proposed heads. This PR alone changes no mathematical strength and leaves all six `[PROVED*]`. A promotion PASS would authorize the status change of these exact conditional statements to `[PROVED]` only; a FAIL leaves their staged status and all mathematical hypotheses unchanged.

For mathematical scope, the published TeX expressly limits the split/layered result to parent-set determination and adds nonemptiness for converses (449–456). The Lean statement is equal to that precise three-clause formulation; it is weaker than the older unconditional biconditional, which the same paper labels false (458–472). Promotion would not prove determination or resurrect those unconditional biconditionals. Admission matches the displayed positive/integral per-prime criterion (TeX 383–394, Lean 351–357); constancy matches the explicit pinning-based constancy statements, with admitted-divisor pinning supplied by separate local lemmas (Lean 594–608). No new exponent, rate, range or assumption is introduced by the diff. There is no separate pin manifest found in the clone beyond the project's dependency manifest; the brief itself pins the six named statements and exact commits. Evidence: `src_paper_statements.json`, `src_line_sections.json`, `src_pin_manifest_search.json`.

The earlier documentation-only PASS and PR #15 census-repair PASS cannot supply any missing compiled statement, axiom or kernel replay evidence for these six statements. No newly added document passage says otherwise.
