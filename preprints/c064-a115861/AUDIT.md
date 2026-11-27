# AUDIT — C064 Refutation (OEIS `A115861` / `A391736`)

## 1. Honest Disposition

**DISPOSITION: REFUTED (PASS — formal Lean 4.34.1 disproof + 3-path independent computational verification; external `comparator` binary unavailable on host, fallback PASS recorded explicitly; remote `git push` / draft PR creation blocked by absent `gh` CLI in sandbox).**

- The target conjecture (`PIN-C064.md` v1, `OEIS A391736` `%C` / `A115861` `%C`) is **FALSE**.
- The smallest counterexample in $\mathbb{N}$ is $(n, m, i) = (239, 215, 302{,}775{,}165)$, with $215 \cdot 302{,}775{,}165 = 65{,}096{,}660{,}475 = 239 \otimes 302{,}775{,}165$ and $i = 302{,}775{,}165 > 13{,}651{,}919 = 239^3$.
- The refutation (`c064_witness`, `c064_refutation_card`, `c064_refutation_pointwise`, `c064_refutation_doubling`) is machine-checked in Lean `v4.34.1` (`MathProofs.SeamB.C064.Solution`) with zero `sorry`, zero `native_decide`, zero `ofReduceBool`, standard axioms only (`[propext, Classical.choice, Quot.sound]`), and independent `leanchecker` PASS.

## 2. Verifier Blob Hashes and Environment Versions

Recorded on host `bakkie` (`Intel Core Ultra X9 388H`, 16 hardware threads, x86-64 with `PCLMULQDQ` / `VPCLMULQDQ`), `2026-11-27T02:46Z` – `2026-11-27T03:24Z`:

- **OS / Kernel:** `Linux 7.2.8-9-omarchy x86_64 GNU/Linux`
- **C Compiler:** `gcc (GCC) 16.2.1 20260810`
- **Python Interpreter:** `Python 3.14.8` (standard library only; zero third-party packages)
- **Lean Toolchain (pinned in `repo/lean/lean-toolchain`):** `leanprover/lean4:v4.34.1`
- **Mathlib Pin (`repo/lean/lake-manifest.json`):** `d13f23b723b8a846827a245b89c10fc7d3f11612` (symlinked read-only from `/home/derekblair/lean-cache/mathlib-d13f23b7/packages`)
- **LaTeX Engine:** `Tectonic 0.17.0`

| Artifact | SHA-256 |
|---|---|
| `PIN-C064.md` (frozen before search) | `6adc03a67107741a685c3a22bf637ae995d140bee9e235e4ae6f256055410e84` |
| `evidence/oeis_A115861_live.txt` | `9b4aa36c023ba7406c738e77161bd02b8b865f93815329bd7bd99377c2f33e8f` |
| `evidence/oeis_A391736_live.txt` | `c5f9ef5f7b37ea4a6070422ed5c43f8bb5dc990d8bcad8f017c956380b0f2745` |
| `evidence/oeis_A391735_live.txt` | `7a32f8a0a1c1f76863c2d48d3d0910d9d00bb2f0a6feb645ffd591d68c9ce790` |
| `evidence/oeis_A048720_live.txt` | `23f15cc85bda4c6e934234b39da5985d5b193570ca618d5c9a005df8c92875f2` |
| `verify_counterexample.py` | `b2c4cddf00a1eb234c5401426bf259cb9598c7459417f2c2e49eb03b985580ca` |
| `search_c064.c` | `7d7d420866b6d402ad2ad6bcf4eede550db7fff0fdf671b4fd8085b66c47fd97` |
| `automaton_c064.c` | `dc1d7286fd46bb1de25540f27d75611e9096c431fd93cb2e10a8702cb442742e` |
| `repo/lean/ComparatorChallenges/C064CarrylessBound.lean` | `cfdbd64690ba36fc8c29a9a9dbc4eb2cb9d26310092d380924d03dee3f326935` |
| `repo/lean/ComparatorChallenges/C064CarrylessBound.json` | `1927772fa50e3ef810c5e476644e5e6f906db3b1dd2e4b03ade136f48d5f95b8` |
| `repo/lean/MathProofs/SeamB/C064/Statement.lean` | `3ace53ada2f5c7029076751027560d858c48faa2b3741679677a881fc6adef48` |
| `repo/lean/MathProofs/SeamB/C064/Solution.lean` | `be39e32aef68728324f9637032a42de6e0a19e5a5bce99373d2f83c8b8a19da6` |

## 3. Boundedness of the Priority Search

Prior-art / novelty checks were executed on `2026-11-27T02:46Z` (before freezing `PIN-C064.md`):
- **Live OEIS fetch:** Retrieved full text records of `A115861` (rev `#25`, Dec 19 2025), `A391736` (rev `#11`, Dec 18 2025), `A391735` (rev `#7`, Dec 18 2025), `A048720`, plus headers/comments/formulas of related sequences `A115859`, `A115869`, `A115871`, `A115872`, `A391725`, `A391726`, `A391572`, `A391573`. All confirmed open with no published resolution.
- **Web / literature search:** Queried Google Search via `search_web` for `"A115861" OR "A391736" oeis carryless`, `"A115861" "A391736" OR "A391735" OR "1+A115861"`, `"carryless" "A048720" "m*i" OR "cross-domain congruence"`, and site-scoped queries across `arxiv.org`, `mathoverflow.net`, `math.stackexchange.com`, and `github.com`.
- **Boundedness caveat:** The search is bounded to indexed public web pages and live OEIS records as of `2026-11-26` (UTC `2026-11-27T02:46Z`). Private correspondence, unindexed preprints, or OEIS edits queued in draft moderation are outside visibility.

## 4. Buzzard Q1–Q4 Verification Scorecard

| Criterion | Status | Evidence |
|---|---|---|
| **Q1 (Statement matches informal statement)** | **PASS** | `clMul` proved equivalent to exact $\mathbb{F}_2[X]$ polynomial bit-convolution (`clMul_testBit`); `A115861` and `rowA391736Values` transcribe OEIS `%N`/`%C` verbatim; `c064_refutation_card`, `c064_refutation_pointwise`, and `c064_refutation_doubling` negate the exact published statements. |
| **Q2 (Code compiles cleanly)** | **PASS** | `lake build MathProofs.SeamB.C064.Solution` completes in 2.47s with exit code 0, zero warnings, zero `sorry` (`evidence/lean_build.log`). |
| **Q3 (Code proves the theorem as stated)** | **PASS (fallback)** | Dual-environment Lean 4 `Expr` comparison confirms exact `type_eq=true` and `body_eq=true` for all 4 definitions and `type_eq=true` for all 4 headline theorems between `ComparatorChallenges.C064CarrylessBound` and `MathProofs.SeamB.C064.Solution` (`evidence/lean_expr_identity.log`). External `comparator` binary unavailable (see §6). |
| **Q4 (No kernel exploit / trust escape)** | **PASS** | `#print axioms` on all 9 theorems reports exclusively `[propext, Classical.choice, Quot.sound]` (`evidence/lean_axioms.log`); independent v4.34.1 `leanchecker` exits `0` (`evidence/lean_checker.log`); zero `native_decide`, zero `ofReduceBool`, zero `implemented_by`, zero `unsafe`. |

## 5. Cost Record (Twist T2) and Funnel Report

- **Wall time:** ~40 minutes total (live OEIS check + pin freeze: 3 min; C direct search + carry-automaton discovery & scans to $n \le 3000$: 4 min; independent Python verification: 2 min; Lean 4 challenge + kernel-clean proof + optimization + verification: 26 min; Davis package + preprint + catalogue: 5 min).
- **Compute / Machine-hours:** `< 0.02` machine-hours on `bakkie` (16-core Intel Core Ultra X9 388H):
  - `search_c064 100 4`: `0.187s` wall (~`3.0` CPU-sec)
  - `search_c064 239 4`: `12.565s` wall (~`201` CPU-sec)
  - `automaton_c064 200`: `0.003s` wall
  - `automaton_c064 2000`: `2.927s` wall (~`46` CPU-sec)
  - `automaton_c064 3000`: `31.143s` wall (~`498` CPU-sec)
  - `verify_counterexample.py`: `2.79s` wall (single-threaded)
  - `lake build MathProofs.SeamB.C064.Solution`: `2.474s` wall (`5.1s` CPU)
- **Attempts:**
  - Search attempts: 1 direct brute-force run (`n ≤ 100` to $n^4$: 0 witnesses) + 1 exact automaton run (`n ≤ 2000`: **186 witnesses**, smallest $n = 239$) + 1 confirming direct brute-force run (`n ≤ 239` to $n^4$: confirmed unique witness $(239, 215, 302{,}775{,}165)$) + 1 landscape run (`n ≤ 3000`: 384 witnesses).
  - Lean build iterations: 4 (diagnosed `Nat.xor`/`WellFounded.fix` kernel blowup → replaced with flat `xor9` + verified chains; diagnosed `omega` on 9 nested divs → replaced with `rw`+`ring`; diagnosed `O(73^2)` certificate check → upgraded to `O(73)` indexed `certRows`; diagnosed `simp` unfolding computable `A115861_set 239` → factored general polymorphic lemmas). Final build: `2.47s`, 0 warnings.
- **Funnel Progression:** `F1–F10 screen (8P/2U/0F)` → `Live OEIS check (OPEN)` → `PIN-C064 frozen` → `Probe Rung 1 (n ≤ 100 to n^4: clean)` → `Exact carry-automaton breakthrough (n = 239 witness)` → `3-path independent verification PASS` → `Comparator challenge frozen` → `Lean 4.34.1 formalization + leanchecker PASS` → `Davis 7-artifact package + LaTeX/PDF preprint complete` → `Ready for orchestrator push, draft PR, and crossed-machine review`.

## 6. Recorded Blockers / Toolchain Gaps

1. **Comparator toolchain mismatch (non-blocking; fallback PASS):** `comparator`, `landrun`, and `lean4export` are not installed on `bakkie`, and bakkie's `v4.36.0` `leanexport`, `leanchecker-paranoid`, and `lean4lean` binaries reject `v4.34.1` `.olean` headers (`failed to read file '.../Solution.olean', incompatible header`, logged verbatim in `evidence/comparator_attempt.log`). Per `BRIEF.md`, we do **not** claim full external `comparator` compliance and instead record the fallback PASS (dual-environment `Expr` identity + axiom audit + v4.34.1 `leanchecker`).
2. **Remote push / draft PR creation blocked in sandbox (no `gh` CLI or SSH key):** `gh` is absent from PATH (disabled under `.local/bin/.disabled/mise-wrappers/gh`; lane rules forbid installs or bypassing disabled wrappers) and `git@github.com` returns `Permission denied (publickey)`. All commits are authored cleanly as `Derek Blair <derekblair@protonmail.com>` on branch `c064-counterexample` in `repo/` (based on `origin/master` `dfe79a2a`), ready for one-command push and draft PR creation by the orchestrator or Derek.

## 7. What This Does NOT Show

1. **No asymptotic lower bound as $n \to \infty$:** Although we exhibit counterexamples breaking $n^3, n^4, n^5, n^6, n^7$ (up to $\log_{2047} i_{\min} = 7.917$ for $n \le 3000$) and prove the finite-automaton upper bound $i_{\min}(n, m) < 2^{n^2/2}$, we do **not** prove whether $\max_{m \in Q(n)} i_{\min}(n, m)$ grows polynomially of unbounded degree, super-polynomially, or exponentially as $n \to \infty$.
2. **Minimality of $n = 239$ is computational, not Lean-formalized:** The Lean proof proves that $n = 239$ is a counterexample (and that $215 \cdot i \ne 239 \otimes i$ for all $1 \le i < 2^{28}$), not that every $n < 239$ satisfies the conjecture. Minimality of $n = 239$ is certified computationally by `automaton_c064.c` (unbounded over $i \in \mathbb{N}$ for all odd $n < 239$) and corroborated for $i \le n^4$ by `search_c064.c`.
3. **Unrestricted row counts remain doubling-invariant:** The refutation `c064_refutation_doubling` refutes `A115861(2*n) = A115861(n)` for the published $n^3$-truncated sequence `A115861`. It does **not** refute $|Q(2n)| = |Q(n)|$ for the *unrestricted* row quotient set $Q(n)$, which in fact holds identically for all $n \ge 1$.
4. **No merge performed:** Per lane rules, this lane has not merged any branch; cross-machine review on an independent machine/pool is required before merge.
