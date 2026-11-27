# C064 — Refutation of the $n^3$ Carryless Binary Product Quotient Bound (OEIS `A115861` / `A391736`)

**Status:** **REFUTED** (minimal counterexample discovered, independently verified across three independent code paths, and formally machine-checked in Lean 4.34.1 with zero `sorry` and standard axioms only).

## Headline Result

Antti Karttunen's conjecture on OEIS [`A391736`](https://oeis.org/A391736) (`%C`, Dec 18 2025) and open question on [`A115861`](https://oeis.org/A115861) (`%C`, Dec 15 & Dec 19 2025) assert that for carryless base-2 multiplication $\otimes = \mathrm{A048720}$, restricting the search for solutions to $m \cdot i = n \otimes i$ ($1 \le m < n$) to $1 \le i \le n^3$ captures every quotient occurring on row $n$ of `A391736` — i.e., that $|Q(n)| = 1 + \mathrm{A115861}(n)$ for all $n \ge 1$.

We **refute** this conjecture and establish the **provably minimal counterexample** across all $n \ge 1$:
- **$n = 239$, $m = 215$, $i_{\min} = 302{,}775{,}165$** (29 bits, odd):
  $$215 \cdot 302{,}775{,}165 = 65{,}096{,}660{,}475 = 239 \otimes 302{,}775{,}165,$$
  while $i_{\min} = 302{,}775{,}165 > 239^3 = 13{,}651{,}919$ and **no** integer $i$ with $1 \le i < 2^{28} = 268{,}435{,}456$ satisfies $215 \cdot i = 239 \otimes i$.
- For row $n = 239$, $\mathrm{A115861}(239) = 3$ (quotients $m \in \{91, 139, 203\}$ appearing at $i \in \{31, 23, 631\}$), so the conjectured count is $1 + 3 = 4$, whereas the exact set of row values is $Q(239) = \{91, 139, 203, 215, 239\}$ of size **$5 > 4$**.
- **Corollary (`%F A115861` refuted):** Under the published $n^3$-truncated definition of `A115861`, the listed formula `a(2*n) = a(n)` **fails at $n = 478$**: $478^3 = 109{,}215{,}352 < 302{,}775{,}165 \le 956^3 = 873{,}722{,}816$, so $\mathrm{A115861}(478) = 3 < 4 = \mathrm{A115861}(956)$.
- **Structural resolution of Karttunen's well-definedness question:** For every odd $n$ and odd $m < n$, the equation $m \cdot i = n \otimes i$ is governed by an exact finite-state LSB-to-MSB **carry-automaton** on at most $m \cdot 2^{\lfloor \log_2 n \rfloor - 1} < n^2 / 2$ parity-valid states. Hence the unrestricted quotient count $|Q(n)|$ is **well-defined and finitely decidable** for every $n \ge 1$, with unconditional upper bound $i_{\min}(n, m) < 2^{n^2 / 2}$. Across all odd $n \le 3000$, our exact automaton finds **384 counterexample pairs** across **282 distinct odd $n$**, breaking not only $n^3$ (at $n = 239$) but also $n^4$ ($n = 391$), $n^5$ ($n = 511$), $n^6$ ($n = 991$), and $n^7$ ($n = 1775$, and reaching $\log_n i_{\min} = 7.917$ at $n = 2047$, $m = 1895$, 88-bit $i_{\min}$).

## Seven-Artifact Package Index

| # | Artifact | Path (task dir / repo) |
|---|---|---|
| 1 | Package README | `README.md` / `preprints/c064-a115861/README.md` |
| 2 | Proof & Certificate | `PROOF.md` / `preprints/c064-a115861/PROOF.md` (and `preprints/c064-a115861/paper.{tex,pdf}`) |
| 3 | Independent Exact Verifier | `verify_counterexample.py` / `preprints/c064-a115861/verify_counterexample.py` |
| 4 | Audit, Cost, Scorecard & Funnel | `AUDIT.md` / `preprints/c064-a115861/AUDIT.md` |
| 5 | Lean Review & Axiom Audit | `LEAN_REVIEW.md` / `preprints/c064-a115861/LEAN_REVIEW.md` |
| 6 | Comparator Challenge File | `repo/lean/ComparatorChallenges/C064CarrylessBound.{lean,json}` + `repo/lean/MathProofs/SeamB/C064/Statement.lean` |
| 7 | Frozen Pin & Evidence Logs | `PIN-C064.md`, `search_c064.c`, `automaton_c064.c`, `evidence/`, `logs/`, `ATTACK-C064_DONE` |

## Quick Replay

```bash
# 1. Independent Python verifier (two independent carryless-multiply paths + exhaustive scan to 239^3 + automaton BFS)
python3 verify_counterexample.py

# 2. Lean 4.34.1 kernel build, axiom audit, and independent leanchecker replay
cd repo/lean
lake build MathProofs.SeamB.C064.Solution
lake env leanchecker MathProofs.SeamB.C064.Solution
```

## What This Does NOT Show

- **Asymptotic growth rate of $\max_{m \in Q(n)} i_{\min}(n, m)$:** While we show that $n^3$ fails at $n = 239$ and record concrete witnesses exceeding $n^4, n^5, n^6, n^7$ (up to $\log_{2047} i_{\min} = 7.917$), and prove the finite-automaton upper bound $i_{\min}(n, m) < 2^{n^2/2}$, we do **not** prove an asymptotic lower bound (e.g., super-polynomial or exponential growth in $n$) for $\max_{m \in Q(n)} i_{\min}(n, m)$ as $n \to \infty$.
- **Exact minimality of $n = 239$ in Lean:** The Lean formalization proves the refutation witness $(239, 215, 302775165)$, the exact non-existence bound $\forall i \in [1, 2^{28}),\; 215 \cdot i \ne 239 \otimes i$, the exact cardinality refutation (`c064_refutation_card`), the pointwise refutation (`c064_refutation_pointwise`), and the doubling refutation at $n = 478$ (`c064_refutation_doubling`). That no $n < 239$ fails is established computationally by both the direct C scan (`search_c064.c`, $n \le 239$ to $n^4$) and the exact unbounded carry-automaton (`automaton_c064.c`, all odd $n \le 3000$), not formalized in Lean.
- **Unrestricted `a(2*n) = a(n)`:** Our refutation of `A115861(2*n) = A115861(n)` applies specifically to the published $n^3$-truncated sequence `A115861`. For the *unrestricted* quotient count $|Q(n)| - 1$, doubling invariance $|Q(2n)| = |Q(n)|$ **does** hold for all $n \ge 1$ because $m \cdot i = (2n) \otimes i \iff (m/2) \cdot i = n \otimes i$ for odd $i$.
- **External `comparator` binary:** Because `comparator`/`landrun`/`lean4export` are not installed on `bakkie` and the v4.36.0 `leanexport`/`lean4lean` binaries reject v4.34.1 `.olean` headers, full external `comparator` compliance is **not** claimed; instead we report a fallback PASS (dual-environment exact `Expr` identity check + axiom audit + v4.34.1 `leanchecker`).
