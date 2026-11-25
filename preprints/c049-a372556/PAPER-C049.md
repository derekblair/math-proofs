# A Two-Value Bound on the Largest Summand in Minimal Jacobsthal Representations: Proof and Lean 4 Formalization of Karttunen's OEIS A372556 Conjecture

**Preprint Draft (`PAPER-C049.md`) — 2026-11-15**  
**Repository / Module:** `derekblair/math-proofs` (`MathProofs/SeamB/C049_A372556.lean`, `namespace C049`)  
**Toolchain & Mathlib Pin:** `leanprover/lean4:v4.34.1` (`commit 5045d0056413266e57c625dcd7c365b10e377c52`), Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`  
**Target Contract:** `PIN-C049.md` v1 (`SHA-256: 056e5e9d5022179baad4295fee1892df5d43ad6bcd0a33c60a5929755f2e1743`, `delta_vs_source: NONE`)

---

## Abstract

Let $(J_k)_{k \ge 0} = (0, 1, 1, 3, 5, 11, 21, 43, 85, \dots)$ denote the Jacobsthal sequence (`OEIS A001045`), defined by $J_0 = 0$, $J_1 = 1$, and $J_{k+2} = J_{k+1} + 2 J_k$. For each integer $n \ge 0$, let $L(n)$ (`OEIS A372555`) be the minimum number of Jacobsthal summands (with unrestricted repetition) whose sum is $n$, let $g(n) = \lfloor \log_2(3n + 1) \rfloor = \max\{k \ge 0 : J_k \le n\}$ (`OEIS A130249`) be the greedy summand index, and let $a(n)$ (`OEIS A372556`) be the largest index $k \in [1, g(n)]$ appearing in at least one $L(n)$-minimal Jacobsthal multiset representation of $n$ (with $a(0) = 0$, and index $2$ dominating index $1$ for $J_1 = J_2 = 1$). On May 10, 2024, Antti Karttunen conjectured in `OEIS A372556` that for every $n \ge 0$, either $a(n) = g(n)$ or $a(n) = g(n) - 1$.

Unlike Zeckendorf-type Fibonacci representations, the greedy Jacobsthal algorithm (`OEIS A265745`) fails to minimize summand count (first at $n = 63 = 21 + 21 + 21$, where $L(63) = 3 < 5$ and $a(63) = 6 < 7 = g(63)$), and naive local $(m, m-1, m-2)$ summand-exchange arguments fail because minimal representations can require multi-stage non-local carries across arbitrarily wide even-index gaps (as shown explicitly by comparing $n_1 = 21{,}843$ and $n_2 = 22{,}184$). We resolve Karttunen's conjecture unconditionally for all $n \in \mathbb{N}$—and establish the stronger parity law that $a(n) = g(n)$ whenever $g(n)$ is even—by combining a six-identity Jacobsthal carry system `(E1)–(E6)` with global maximization of the additive exponential potential $\Phi(M) = \sum_{k \in M} 6^k$ over $L(n)$-minimal multisets. This yields a self-contained two-step even-barrier induction showing that every $\Phi$-canonical minimal multiset supported on $\{2, \dots, 2K + 1\}$ has sum at most $J_{2K+2} - 1$. The proof, the parity refinement, and an executable dynamic-programming mirror formally proved equivalent to the multiset specification are machine-checked in Lean 4 with zero `sorry`s, zero custom axioms, and no `native_decide` or `ofReduceBool` trust escapes.

---

## 1. Introduction and Primary-Source Context

### 1.1 Minimal-Summand Jacobsthal Representations vs. Greedy Numeration

The Jacobsthal numbers (`OEIS A001045`) are defined by the linear recurrence
$$J_0 = 0, \qquad J_1 = 1, \qquad J_{k+2} = J_{k+1} + 2 J_k \quad (k \ge 0),$$
with closed form $J_k = \bigl(2^k - (-1)^k\bigr)/3$. Carlitz, Scoville, and Hoggatt [2] studied unique canonical $0$-$1$ Jacobsthal digit expansions (related to greedy subtraction of $J_{g(n)}$, `OEIS A265745`), where summand repetition is syntactically restricted. By contrast, unrestricted-multiplicity additive change-making over $\{J_k : k \ge 1\}$ asks for the *minimum number of summands*
$$L(n) := \min\Bigl\{ |M| : M \text{ is a finite multiset of } \mathbb{N} \text{ with } \sum_{k \in M} J_k = n \Bigr\} \qquad (\text{`OEIS A372555`}).$$

Because the characteristic polynomial $x^2 - x - 2 = (x - 2)(x + 1)$ has root $-1$ of unit modulus, the greedy algorithm $n \mapsto n - J_{g(n)}$ does **not** achieve $L(n)$ in general. The first failure occurs at $n = 63$: the largest Jacobsthal number at most $63$ is $J_7 = 43$ ($g(63) = 7$), for which greedy subtraction gives the five-summand representation $63 = 43 + 11 + 5 + 3 + 1$, whereas repeating $J_6 = 21$ three times gives $63 = 21 + 21 + 21$, so $L(63) = 3$ and no three-summand representation of $63$ contains $J_7 = 43$ (since $L(63 - 43) = L(20) = 4$, giving $1 + L(20) = 5 > 3$).

To compute $L(n)$ recursively and analyze how far an optimal largest summand can drop below the greedy summand $J_{g(n)}$, Antti Karttunen introduced `OEIS A372556` on May 7, 2024 [1]:
$$a(0) = 0, \qquad a(n) = \max\bigl\{ 1 \le k \le g(n) : L(n - J_k) = L(n) - 1 \bigr\} \quad (n \ge 1),$$
where $g(n) = \mathrm{A130249}(n) = \lfloor \log_2(3n + 1) \rfloor = \max\{k \ge 0 : J_k \le n\}$. On May 10, 2024, Karttunen formulated the following conjecture (`OEIS A372556`, `%C` line 13 [1]):

> **Conjecture (Karttunen, May 10, 2024).** *For all $n \ge 0$, either $a(n) = g(n)$ or $a(n) = g(n) - 1$. Equivalently, every $n \ge 1$ admits a minimum-length Jacobsthal representation whose largest summand is either $J_{g(n)}$ or $J_{g(n)-1}$.*

### 1.2 Main Results

We prove Karttunen's conjecture unconditionally for all $n \in \mathbb{N}$, together with a sharp parity refinement explaining the empirical distribution of the exception set `OEIS A372558` $= \{n \ge 1 : a(n) \ne g(n)\}$:

- **Theorem 1.1 (Main Theorem — `C049.a_eq_g_or_pred`).** *For every $n \in \mathbb{N}$, $a(n) = g(n)$ or $a(n) = g(n) - 1$.*
- **Theorem 1.2 (Even-Index Exactness — `C049.a_eq_g_of_even_g`).** *For every $n \in \mathbb{N}$, if $g(n)$ is even, then $a(n) = g(n)$. Consequently, $a(n) = g(n) - 1 < g(n)$ can occur only when $g(n)$ is odd (in fact only for odd $g(n) \ge 7$, starting at $n = 63$).*
- **Theorem 1.3 (Verified Dynamic-Programming Equivalence — `C049.L_dp_eq_L`, `C049.a_dp_eq_a`).** *The noncomputable multiset definitions $L(n)$ and $a(n)$ agree for every $n \in \mathbb{N}$ with bottom-up dynamic-programming recurrences `L_dp` and `a_dp`, establishing in Lean's kernel both the small edge cases $n \in \{0, 1, 2, 3, 4\}$ and non-vacuity witnesses such as $g(63) = 7, L(63) = 3, a(63) = 6$ (`C049.exists_a_eq_g_pred_lt`).*

---

## 2. Formal Definitions, Exactness of $g(n)$, and Equivalence of Readings

In Lean 4 (`MathProofs/SeamB/C049_A372556.lean`, `namespace C049`), the five pinned objects of `PIN-C049.md` v1 are defined directly over `Multiset ℕ`:

```lean
def J : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | k + 2 => J (k + 1) + 2 * J k

def g (n : ℕ) : ℕ :=
  Nat.log 2 (3 * n + 1)

noncomputable def L (n : ℕ) : ℕ :=
  Nat.find (h_exists n)

noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 (g n)).filter (fun k => ∃ M : Multiset ℕ, M.card = L n ∧ (M.map J).sum = n ∧ k ∈ M)).sup id
```

Three foundational equivalences confirm that these definitions capture Karttunen's `OEIS A372556` specification with zero convention drift (`delta_vs_source: NONE`):

1. **Exactness of $g(n) = \lfloor \log_2(3n + 1) \rfloor$ (`J_g_le`, `lt_J_g_succ`, `le_g_of_J_le`).** From the recurrence, simultaneous induction on $t \ge 0$ (`J_step_pair` and `three_mul_J_pair`) yields
   $$J_{2t+1} = 2 J_{2t} + 1, \quad 2 J_{2t+1} = J_{2t+2} + 1, \quad 3 J_{2t} + 1 = 2^{2t}, \quad 3 J_{2t+1} = 2^{2t+1} + 1.$$
   Let $k = \lfloor \log_2(3n + 1) \rfloor$, so $2^k \le 3n + 1 < 2^{k+1}$.
   - If $k = 2t$ is even, $3 J_{2t} + 1 = 2^{2t} \le 3n + 1$ gives $J_{2t} \le n$, while $3n + 1 \le 2^{2t+1} - 1 = 3 J_{2t+1} - 2$ gives $n < J_{2t+1}$.
   - If $k = 2t + 1$ is odd, substituting $2^{2t+1} = 3 J_{2t+1} - 1$ into $2^{2t+1} \le 3n + 1$ gives $3 J_{2t+1} \le 3n + 2$; since the left-hand side is divisible by $3$, $3 J_{2t+1} \le 3n$, hence $J_{2t+1} \le n$. Meanwhile $3n + 1 < 2^{2t+2} = 3 J_{2t+2} + 1$ gives $n < J_{2t+2}$.
   By monotonicity of $J$ (`J_mono`), $g(n) = \max\{k \in \mathbb{N} : J_k \le n\}$ for **all** $n \in \mathbb{N}$ (including $g(0) = 0, g(1) = 2, g(2) = 2$).

2. **Automatic exclusion of $0$ and Bellman equivalence (`zero_notMem_of_min`, `mem_min_iff_bellman`).** Because $J_0 = 0$, erasing $0$ from any multiset preserves its $J$-sum while decreasing its cardinality by $1$; hence $0 \notin M$ for every $L(n)$-minimal multiset $M$. For $n \ge 1$ and $1 \le k \le g(n)$, $k$ belongs to at least one $L(n)$-minimal multiset for $n$ if and only if $L(n - J_k) + 1 = L(n)$. Thus `C049.a` (the supremum of all indices appearing across $L(n)$-minimal multisets) coincides identically with Karttunen's downward-scan Bellman definition in `OEIS A372556`.

3. **Dominance of index $2$ over index $1$ (`a_ne_one`).** Since $J_1 = J_2 = 1$, replacing any occurrence of $1$ by $2$ in an $L(n)$-minimal multiset preserves both cardinality and $J$-sum. Consequently, $a(1) = 2 = g(1)$, $a(2) = 2 = g(2)$, and $a(n) \ne 1$ for every $n \in \mathbb{N}$.

---

## 3. Why Naive Local Summand-Exchange Sketches Fail

An initial heuristic approach to `C049` (recorded in the Seam B triage dossier prior to scoping) attempted to prove Karttunen's bound by local inspection of the multiplicities $(c_m, c_{m-1}, c_{m-2})$ at the maximum summand index $m$ of an arbitrary $L(n)$-minimal multiset, appealing to the putative identities $2 J_k + J_{k-2} = J_{k+1} + J_{k-1}$ and $4 J_m = J_{m+2} - J_{m-1}$ (for even $m$). Scoping analysis (`SCOPING-C049.md` §1.2, Steps 3–4 and 11) refuted that literal sketch on two independent grounds:

### 3.1 Algebraic Refutation of the Naive Identities

1. **Failure of $2 J_k + J_{k-2} = J_{k+1} + J_{k-1}$ for every $k \ge 2$ (`C049.triage_id2_false`).** Expanding via $J_{k+1} = J_k + 2 J_{k-1}$ and $J_k = J_{k-1} + 2 J_{k-2}$ yields
   $$(J_{k+1} + J_{k-1}) - (2 J_k + J_{k-2}) = 2 J_{k-1} - 3 J_{k-2} = \frac{2^{k-2} + 5(-1)^{k-2}}{3} \ne 0 \qquad (\forall k \ge 2).$$
   For instance, at $k = 2, 3, 4$, the left-hand side $2 J_k + J_{k-2}$ equals $2, 7, 11$ whereas $J_{k+1} + J_{k-1}$ equals $4, 6, 14$. (The identity holds for Fibonacci numbers because $F_k = F_{k-1} + F_{k-2}$ has unit coefficient on $F_{k-2}$, whereas Jacobsthal has coefficient $2$.)
2. **Failure of $4 J_m = J_{m+2} - J_{m-1}$ for even $m \ge 4$.** At $m = 4$, $4 J_4 = 20 \ne 18 = 21 - 3 = J_6 - J_3$; in general $J_{2t+2} - 4 J_{2t} = 1 = J_2$, not $J_{2t-1}$.

### 3.2 Structural Failure of Bounded-Window Rewriting ($n_1 = 21{,}843$ vs. $n_2 = 22{,}184$)

Even using true Jacobsthal identities, **no fixed-width local window** near the maximum index of an arbitrary $L(n)$-minimal multiset can decide whether the top index upgrades:

- Take $n_1 = 21{,}843$. Since $J_{15} = 10{,}923 \le 21{,}843 < 21{,}845 = J_{16}$, we have $g(21{,}843) = 15$. Dynamic programming gives $L(21{,}843) = 7$ and $1 + L(21{,}843 - J_{15}) = 9 > 7$, so $a(21{,}843) = 14 = g(21{,}843) - 1$. The multiset
  $$M_1 = \{14, 14, 14, 12, 12, 12, 12\} \qquad (3 \cdot 5461 + 4 \cdot 1365 = 21{,}843,\ |M_1| = 7)$$
  is $L(n_1)$-minimal and **cannot** be upgraded to index $15$ without adding summands.
- Now adjoin a single summand $J_{10} = 341$ to form $n_2 = 21{,}843 + 341 = 22{,}184$. Here $J_{16} = 21{,}845 \le 22{,}184 < 43{,}691 = J_{17}$, so $g(22{,}184) = 16$, and $L(22{,}184) = 8$. Thus
  $$M_2 = \{14, 14, 14, 12, 12, 12, 12, 10\} \qquad (\text{sum } = 22{,}184,\ |M_2| = 8 = L(22{,}184))$$
  is **genuinely $L(n_2)$-minimal** with $\max(M_2) = 14 = g(n_2) - 2$.
- On the top four indices $(14, 13, 12, 11)$, $M_1$ and $M_2$ have the **exact same multiplicity vector $(3, 0, 4, 0)$**. Upgrading $M_2$ to index $16$ at length $8$ requires a **two-stage non-local carry cascade** using $4 J_{2t} + J_{2u} = J_{2t+2} + 4 J_{2u-2}$:
  $$\{14^3, 12^4, 10\} \longmapsto \{14^4, 8^4\} \longmapsto \{16, 8^3, 6^4\},$$
  where the second rewrite reaches across index gap $14 - 8 = 6$. Extending this construction produces arbitrary-depth even-index carry chains across unbounded index gaps.

---

## 4. The Six-Identity Carry System `(E1)–(E6)` and Base-6 Potential $\Phi$

### 4.1 The Six Verified Jacobsthal Carry Identities

From $J_{k+2} = J_{k+1} + 2 J_k$ and the alternating doubling laws $J_{2t+1} = 2 J_{2t} + 1$ and $2 J_{2t+1} = J_{2t+2} + 1$ (`J_step_pair`), we derive six exact identities on $\mathbb{N}$ (`jacobsthal_E1` through `jacobsthal_E6`):

| Label | Identity | Domain | Multiset Exchange Effect (`LHS ↦ RHS`) |
| :--- | :--- | :--- | :--- |
| `(E1)` | $J_k + 2 J_{k-1} = J_{k+1}$ | $k \ge 1$ | $\{k, k-1, k-1\} \mapsto \{k+1\}$ ($3 \to 1$, $\Delta|M| = -2$) |
| `(E2)` | $2 J_{2t+1} = J_{2t+2} + J_2$ | $t \ge 0$ | $\{2t+1, 2t+1\} \mapsto \{2t+2, 2\}$ ($2 \to 2$, promotes $2t+1 \mapsto 2t+2$ for $t \ge 1$) |
| `(E3)` | $2 J_{2t} + J_2 = J_{2t+1}$ | $t \ge 0$ | $\{2t, 2t, 2\} \mapsto \{2t+1\}$ ($3 \to 1$, $\Delta|M| = -2$) |
| `(E4)` | $4 J_{2t} + J_2 = J_{2t+2}$ | $t \ge 0$ | $\{2t, 2t, 2t, 2t, 2\} \mapsto \{2t+2\}$ ($5 \to 1$, $\Delta|M| = -4$) |
| `(E5)` | $4 J_{2t} + J_{2u+1} = J_{2t+2} + 2 J_{2u}$ | $t, u \ge 0$ | $\{2t^4, 2u+1\} \mapsto \{2t+2, 2u, 2u\}$ ($5 \to 3$, $\Delta|M| = -2$) |
| `(E6)` | $4 J_{2t} + J_{2u} = J_{2t+2} + 4 J_{2u-2}$ | $t \ge 0,\ u \ge 1$ | $\{2t^4, 2u\} \mapsto \{2t+2, (2u-2)^4\}$ ($5 \to 5$, promotes $2t \mapsto 2t+2$ when $2 \le u \le t$) |

*Proofs of `(E4)–(E6)`.* Doubling $J_{2t+1} = 2 J_{2t} + 1$ gives $2 J_{2t+1} = 4 J_{2t} + 2$; substituting $2 J_{2t+1} = J_{2t+2} + 1$ yields $4 J_{2t} + 1 = J_{2t+2}$, which is `(E4)` since $J_2 = 1$. Adding $4 J_{2t} + 1 = J_{2t+2}$ and $2 J_{2u} + 1 = J_{2u+1}$ cancels $+1$ to give `(E5)`. Writing $u = v + 1 \ge 1$ and adding $4 J_{2t} + 1 = J_{2t+2}$ to $J_{2v+2} = 4 J_{2v} + 1$ cancels $+1$ to give `(E6)`. $\square$

### 4.2 Canonical Minimal Representations via $\Phi(M) = \sum_{k \in M} 6^k$

To eliminate explicit carry-cascade tracking, define the **additive base-6 potential** (`C049.Phi`):
$$\Phi(M) := \sum_{k \in M} 6^k.$$
A multiset $M$ of natural numbers is **canonical** (`C049.IsCanonical`) if:
1. every $k \in M$ satisfies $k \ge 2$;
2. $|M| = L\bigl(\sum_{k \in M} J_k\bigr)$ ($M$ is $L$-minimal for its sum); and
3. for every multiset $M'$ with $\min(M') \ge 2$, $|M'| = |M|$, and $\sum_{k \in M'} J_k = \sum_{k \in M} J_k$, one has $\Phi(M') \le \Phi(M)$.

**Lemma 4.1 (Existence — `C049.exists_canonical_min_rep`).** *Every $n \in \mathbb{N}$ admits at least one canonical multiset $M$ with $\sum_{k \in M} J_k = n$.*

*Proof.* Start from any $L(n)$-minimal multiset $M_0$ for $n$. Since $0 \notin M_0$, replacing every occurrence of $1$ by $2$ (`promoteOnes`) produces a multiset $M_1$ with all elements $\ge 2$, $|M_1| = L(n)$, and $\sum_{k \in M_1} J_k = n$. For any competing multiset $M'$ with $|M'| = L(n)$ and $\sum_{k \in M'} J_k = n$, every $k \in M'$ satisfies $J_k \le n$, hence $k \le g(n)$ and $6^k \le 6^{g(n)}$, giving the uniform finite upper bound $\Phi(M') \le L(n) \cdot 6^{g(n)}$. A nonempty subset of $\{0, 1, \dots, L(n) \cdot 6^{g(n)}\}$ attains its maximum (`exists_max_of_bdd`), yielding a canonical representation of $n$. $\square$

**Lemma 4.2 (Hereditary Sub-Multiset Optimality — `C049.IsCanonical_of_add_left`).** *If $A + B$ is canonical, then $A$ is canonical.*

*Proof.* Clearly $\min(A) \ge \min(A + B) \ge 2$. If some $A'$ had $\sum_{k \in A'} J_k = \sum_{k \in A} J_k$ and $|A'| < |A|$, then $A' + B$ would represent $\sum_{k \in A+B} J_k$ in strictly fewer than $|A + B| = L\bigl(\sum_{k \in A+B} J_k\bigr)$ summands, a contradiction. Similarly, if some $A'$ with $\min(A') \ge 2$, $|A'| = |A|$, and $\sum_{k \in A'} J_k = \sum_{k \in A} J_k$ satisfied $\Phi(A') > \Phi(A)$, additivity $\Phi(A' + B) = \Phi(A') + \Phi(B) > \Phi(A) + \Phi(B) = \Phi(A + B)$ would contradict $\Phi$-maximality of $A + B$. $\square$

Consequently, **no canonical multiset $M$ can contain the left-hand side $S$ of any of `(E1)–(E6)`** (within the parameter ranges where the right-hand side $S'$ has indices $\ge 2$):
- `(E1)` ($k \ge 2$), `(E3)` ($t \ge 1$), `(E4)` ($t \ge 1$), and `(E5)` ($t \ge 1, u \ge 1$) strictly decrease cardinality (`IsCanonical_not_shorter`).
- `(E2)` ($t \ge 1$) preserves cardinality $2$ and strictly increases $\Phi$:
  $$\Phi(\{2t+2, 2\}) = 6 \cdot 6^{2t+1} + 36 > 2 \cdot 6^{2t+1} = \Phi(\{2t+1, 2t+1\}).$$
- `(E6)` ($t \ge 2, 2 \le u \le t$) preserves cardinality $5$, keeps $2u - 2 \ge 2$, and strictly increases $\Phi$:
  $$\Phi\bigl(\{2t+2, (2u-2)^4\}\bigr) = 36 \cdot 6^{2t} + 4 \cdot 6^{2u-2} > 5 \cdot 6^{2t} \ge 4 \cdot 6^{2t} + 6^{2u} = \Phi\bigl(\{2t^4, 2u\}\bigr).$$

---

## 5. The Two-Step Even-Barrier Induction and Proof of Theorems 1.1–1.2

The heart of the proof is the following sharp upper bound at odd index barriers $2K + 1$:

**Theorem 5.1 (Even-Barrier Sum Bound — `C049.canonical_sum_le_pred_even_jacobsthal`).** *For every integer $K \ge 1$ and every canonical multiset $M$ whose elements satisfy $2 \le k \le 2K + 1$,*
$$\sum_{k \in M} J_k \le J_{2K+2} - 1.$$

*Proof.* We induct on $K \ge 1$. Write $c_r$ for the multiplicity of $r$ in $M$.

**Base case ($K = 1$, support in $\{2, 3\}$, target $\le J_4 - 1 = 4$).**
- By `(E2)` at $t = 1$ ($\{3, 3\} \mapsto \{4, 2\}$), $c_3 \le 1$.
- By `(E3)` at $t = 1$ ($\{2, 2, 2\} \mapsto \{3\}$), $c_2 \le 2$.
- By `(E1)` at $k = 3$ ($\{3, 2, 2\} \mapsto \{4\}$), we cannot have both $c_3 \ge 1$ and $c_2 \ge 2$.
Hence $(c_3, c_2) \in \{(0,0), (0,1), (0,2), (1,0), (1,1)\}$, so $\sum_{k \in M} J_k = 3 c_3 + c_2 \le 3 + 1 = 4 = J_4 - 1$.

**Inductive step ($K \ge 2$, assuming the theorem holds for $K - 1$).** Decompose
$$M = \underbrace{\{2K+1, \dots, 2K+1\}}_{c_{2K+1}} + \underbrace{\{2K, \dots, 2K\}}_{c_{2K}} + R,$$
where every element of $R$ lies in $\{2, \dots, 2K - 1\} = \{2, \dots, 2(K-1) + 1\}$. By Lemma 4.2, $R$ is canonical, so the induction hypothesis gives $\sum_{r \in R} J_r \le J_{2K} - 1$. Also `(E2)` at $t = K$ forces $c_{2K+1} \le 1$.

- **Case 1 ($c_{2K+1} = 1$).** By `(E1)` at $k = 2K + 1$ ($J_{2K+1} + 2 J_{2K} = J_{2K+2}$), we must have $c_{2K} \le 1$. Therefore
  $$\sum_{k \in M} J_k \le J_{2K+1} + J_{2K} + (J_{2K} - 1) = (J_{2K+1} + 2 J_{2K}) - 1 = J_{2K+2} - 1.$$

- **Case 2 ($c_{2K+1} = 0$ and $c_{2K} \le 3$).** Using `(E4)` ($4 J_{2K} + 1 = J_{2K+2}$),
  $$\sum_{k \in M} J_k \le 3 J_{2K} + (J_{2K} - 1) = 4 J_{2K} - 1 = J_{2K+2} - 2 \le J_{2K+2} - 1.$$

- **Case 3 ($c_{2K+1} = 0$ and $c_{2K} \ge 4$).** First, $c_{2K} \ge 5$ is impossible by `(E6)` at $t = u = K$ ($5 J_{2K} = J_{2K+2} + 4 J_{2K-2}$, valid since $2K - 2 \ge 2$). Thus $c_{2K} = 4$. We claim $R = \emptyset$. Suppose toward a contradiction that some $r \in R$ exists, so $2 \le r \le 2K - 1$ and $\{2K, 2K, 2K, 2K, r\} \subseteq M$:
  - If $r = 2$, then $\{2K, 2K, 2K, 2K, 2\} \subseteq M$ contradicts `(E4)` ($5 \to 1$).
  - If $r \ge 4$ is even, write $r = 2u$ with $2 \le u \le K - 1$; then $\{2K^4, 2u\} \subseteq M$ contradicts `(E6)` ($5 \to 5$, strict $\Phi$-increase).
  - If $r$ is odd, write $r = 2u + 1$ with $1 \le u \le K - 1$; then $\{2K^4, 2u+1\} \subseteq M$ contradicts `(E5)` ($5 \to 3$).
  Every $r \in \{2, \dots, 2K - 1\}$ is ruled out, so $R = \emptyset$ and $\sum_{k \in M} J_k = 4 J_{2K} = J_{2K+2} - 1$. $\square$

*Note on sharpness.* The bound $J_{2K+2} - 1$ in Theorem 5.1 is **attained for every $K \ge 1$**: at $K = 1$ by $\{3, 2\}$ ($3 + 1 = 4 = J_4 - 1$), at $K = 2$ by $\{5, 4, 3, 2\}$ ($11 + 5 + 3 + 1 = 20 = J_6 - 1$), and for every $K \ge 3$ by $\{2K, 2K, 2K, 2K\}$ ($4 J_{2K} = J_{2K+2} - 1$, which are the nine four-equal-summand drop points $84, 340, 1364, \dots, 5{,}592{,}404 = J_{24} - 1$ observed empirically in `OEIS A372558`).

### 5.2 Proof of Theorems 1.2 and 1.1

Always $a(n) \le g(n)$ (`a_le_g`) directly from the index interval `Finset.Icc 1 (g n)`.

1. **Even $g(n)$ (Theorem 1.2 — `a_eq_g_of_even_g`).** Write $g(n) = 2t$.
   - If $t = 0$, $g(n) = 0$ and $a(n) \le 0$, so $a(n) = 0 = g(n)$.
   - If $t = 1$, $g(n) = 2$, so $n \ge J_2 = 1$. Let $M$ be canonical for $n$ (Lemma 4.1). Since $\sum_{k \in M} J_k = n \ge 1$, $M$ is nonempty; any $k \in M$ satisfies $2 \le k \le a(n) \le g(n) = 2$, forcing $a(n) = 2 = g(n)$.
   - If $t = K + 1 \ge 2$, then $g(n) = 2K + 2$ ($K \ge 1$) and $n \ge J_{2K+2}$. Let $M$ be canonical for $n$. If every $k \in M$ satisfied $k \le 2K + 1$, Theorem 5.1 would give $n \le J_{2K+2} - 1$, impossible. Thus some $k \in M$ satisfies $2K + 2 \le k \le a(n) \le g(n) = 2K + 2$, forcing $a(n) = g(n)$.

2. **Odd $g(n)$ (completing Theorem 1.1 — `a_eq_g_or_pred`).** Suppose $g(n) = 2t + 1$.
   - $t = 0$ ($g(n) = 1$) never occurs, because $J_1 \le n < J_2$ reads $1 \le n < 1$.
   - If $t = 1$ ($g(n) = 3$, i.e., $n \in \{3, 4\}$), let $M$ be canonical for $n \ge J_3 = 3$. Then $M$ is nonempty and any $k \in M$ satisfies $g(n) - 1 = 2 \le k \le a(n) \le 3 = g(n)$, so $a(n) \in \{2, 3\} = \{g(n) - 1, g(n)\}$.
   - If $t = K + 1 \ge 2$ ($g(n) = 2K + 3$, $K \ge 1$), then $n \ge J_{2K+3} \ge J_{2K+2} > J_{2K+2} - 1$. Let $M$ be canonical for $n$. By Theorem 5.1, $M$ cannot have support inside $\{2, \dots, 2K + 1\}$, so some $k \in M$ satisfies $g(n) - 1 = 2K + 2 \le k \le a(n) \le g(n)$, forcing $a(n) = g(n)$ or $a(n) = g(n) - 1$. $\square$

---

## 6. Structure of the Exception Set `OEIS A372558` and Scope Boundaries

### 6.1 Empirical Structure Explained by the Proof

Independent dynamic programming across $n = 0..5{,}592{,}405 = J_{24}$ ($64\times$ Karttunen's `b372556.txt` range $87{,}381 = J_{18}$) finds $5{,}568{,}287$ values with $a(n) = g(n)$, $24{,}118$ values with $a(n) = g(n) - 1$ (matching all $24{,}118$ terms of `b372558.txt` identically), and $0$ violations:

| Odd $g(n) = 2K + 1$ | Bucket $[J_g, J_{g+1} - 1]$ | Drop Count | Minimum Drop $n_{\min}$ | Maximum Drop $n_{\max}$ |
| ---: | :--- | ---: | :--- | :--- |
| $7$ | $[43, 84]$ | $2$ | $63 = J_7 + 20$ | $84 = J_8 - 1$ |
| $9$ | $[171, 340]$ | $6$ | $191 = J_9 + 20$ | $340 = J_{10} - 1$ |
| $11$ | $[683, 1364]$ | $18$ | $703 = J_{11} + 20$ | $1364 = J_{12} - 1$ |
| $13$ | $[2731, 5460]$ | $58$ | $2751 = J_{13} + 20$ | $5460 = J_{14} - 1$ |
| $15$ | $[10923, 21844]$ | $186$ | $10943 = J_{15} + 20$ | $21844 = J_{16} - 1$ |
| $17$ | $[43691, 87380]$ | $586$ | $43711 = J_{17} + 20$ | $87380 = J_{18} - 1$ |
| $19$ | $[174763, 349524]$ | $1{,}802$ | $174783 = J_{19} + 20$ | $349524 = J_{20} - 1$ |
| $21$ | $[699051, 1398100]$ | $5{,}418$ | $699071 = J_{21} + 20$ | $1398100 = J_{22} - 1$ |
| $23$ | $[2796203, 5592404]$ | $16{,}042$ | $2796223 = J_{23} + 20$ | $5592404 = J_{24} - 1$ |

Theorem 1.2 accounts for the complete absence of even-$g(n)$ drops. At odd $g(n) = 2K + 1 \ge 7$, $2 J_{2K} = J_{2K+1} - 1$ falls short of $J_{2K+1}$ by $1$; when all remaining summands are even indices $2s \ge 6$ (starting at $2 J_{2K} + J_6 = J_{2K+1} + 20$), borrowing $+1$ to form $J_{2K+1}$ forces splitting $J_{2s} - 1 = 4 J_{2s-2}$, increasing total summand count by $+2$.

### 6.2 Strength Delta and What This Paper Does Not Show

- **Strength delta vs. source (`delta_vs_source: NONE`):** Theorem 1.1 (`C049.a_eq_g_or_pred`) proves Antti Karttunen's May 10, 2024 conjecture (`OEIS A372556`, `%C` line 13) verbatim over all $n \in \mathbb{N}$ with zero domain restriction, weakening, or surrogate replacement, and Theorem 1.2 (`C049.a_eq_g_of_even_g`) strictly strengthens the even-$g(n)$ half.
- **What this paper does NOT show:**
  1. It does **not** address Karttunen's separate array-symmetry conjecture in `OEIS A372561` (`%C` May 10, 2024).
  2. It does **not** derive an exact closed-form counting recurrence for the per-bucket drop counts $(2, 6, 18, 58, 186, 586, 1802, 5418, 16042, \dots)$ in `OEIS A372558`, which is unnecessary for the two-value bound.

---

## 7. Lean 4 Formalization and Verification Record

### 7.1 Declaration Map (`MathProofs/SeamB/C049_A372556.lean`)

| Mathematical Item | Lean 4 Declaration | Status |
| :--- | :--- | :--- |
| Jacobsthal sequence $J_k$ (`A001045`) | `C049.J` | Computable `def`, `0` axioms |
| Greedy index $g(n) = \lfloor \log_2(3n+1) \rfloor$ (`A130249`) | `C049.g` | Computable `def`, `0` axioms |
| Minimal summand count $L(n)$ (`A372555`) | `C049.L` | Pinned `noncomputable def` (`Nat.find`) |
| Optimal largest index $a(n)$ (`A372556`) | `C049.a` | Pinned `noncomputable def` (`Finset.sup`) |
| Refutation of naive triage identity | `C049.triage_id2_false` | Proved (`∀ k ≥ 2`) |
| Six-identity carry system `(E1)–(E6)` | `C049.jacobsthal_E1` .. `C049.jacobsthal_E6` | Proved |
| Canonical existence (Step 12) | `C049.exists_canonical_min_rep` | Proved |
| Hereditary optimality (Step 13) | `C049.IsCanonical_of_add_left` | Proved |
| Even-barrier induction $I_K$ (Steps 14–16) | `C049.canonical_sum_le_pred_even_jacobsthal` | Proved |
| Parity refinement (`Even (g n) → a n = g n`) | `C049.a_eq_g_of_even_g` | Proved |
| **Main Theorem (`C049`)** | **`C049.a_eq_g_or_pred`** | **Proved (`∀ n : ℕ, a n = g n ∨ a n = g n - 1`)** |
| Verified computable DP mirror & equivalence | `C049.L_dp`, `C049.a_dp`, `C049.L_dp_eq_L`, `C049.a_dp_eq_a` | Computable `def`s + formal equality proofs |
| Kernel spot checks ($n = 0..4, 63, 84, 105$) & drop witness | `C049.spot_check_0` .. `C049.spot_check_105`, `C049.exists_a_eq_g_pred_lt` | Proved in kernel (`rfl` via `L_dp_eq_L` / `a_dp_eq_a`) |

### 7.2 Recorded Trust, Axiom, Non-Vacuity, and Provenance Audit

0. **Artifact source digests bound to toolchain pin (`leanprover/lean4:v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, base `master` `55016601a2825cba629405ada0748117ddb1cf72`):**
   - `MathProofs/SeamB/C049_A372556.lean` (`1,183` lines): `5e56274caf5153ad7699c9a85cf64c244ad1af4b846ea5a000f047e181139c56` (`0 diff chars` vs. `PIN-C049.md` v1).
   - `lakefile.toml` (`19` lines, `defaultTargets = ["mathproofs"]` preserved): `5a82a75a91dc597eccd9305c998dffaf6273956b9c0819f0c28cc86040316a21`.
   - `Mathproofs.lean` (`80` lines): `a3496ba3b37cc6001f523e01fff32f95b2920ffa1951df8b5e51bcc6b0f54205`.
   - Clean-slate full build (`rm -rf .lake/build && lake build`): exit `0` (`17,976` jobs; `0` errors, `0` sorries, `0` warnings on `MathProofs.SeamB.C049_A372556`; log SHA-256 `42d9c7877b1b0a7a513b29fbfad41615683fce10b3f9ff2b77cf505354ca0727`).
1. **Axiom footprint (`#print axioms`):**
   - `C049.J`, `C049.g`: depend on **no axioms**.
   - `C049.h_exists`: `[propext, Quot.sound]`.
   - `C049.L`, `C049.a`, `C049.a_eq_g_or_pred`, `C049.a_eq_g_of_even_g`, `C049.L_dp_eq_L`, `C049.a_dp_eq_a`, `C049.exists_a_eq_g_pred_lt`: `[propext, Classical.choice, Quot.sound]` (exact allowlist).
2. **Transitive kernel closure & lexical trust-escape screen:**
   - Comment/string-stripped lexical scan across the solution closure (`MathProofs/SeamB/C049_A372556.lean`, `Mathproofs.lean`, `Main.lean`): **`0` hits** (and `0` raw hits) for `sorry`, `admit`, `sorryAx`, `axiom`, `native_decide`, `ofReduceBool`, `implemented_by`, `unsafe`.
   - `Lean.MetaM` transitive constant-closure scan on `C049.a_eq_g_or_pred` (`438` constants) and `C049.a_dp_eq_a` (`605` constants): `sorryAx = false`, `Lean.ofReduceBool = false`, `Lean.ofReduceNat = false`, `Lean.trustCompiler = false`.
   - Fresh-kernel replay (`lake env leanchecker --fresh --verbose MathProofs.SeamB.C049_A372556`): **exit `0`**.
3. **Non-vacuity & spot checks (kernel vs. VM / b-file boundary stated explicitly):**
   - **Kernel-checked directly on `C049.g`, `C049.L`, `C049.a`** (rewriting via the formally proved theorems `L_dp_eq_L` and `a_dp_eq_a` and discharging by `rfl` in the Lean kernel): $n = 0, 1, 2, 3, 4, 63, 84, 105$, including $a(63) = 6 < 7 = g(63)$ (`exists_a_eq_g_pred_lt`).
   - **Verified via `#eval` VM execution on the formally proved-equivalent Lean functions `C049.L_dp` / `C049.a_dp` and independent Python DP cross-check against `b372556.txt` / `b372555.txt`** (not claimed as kernel `rfl` reductions): $n = 21{,}843$ ($g = 15, L = 7, a = 14$) and $n = 22{,}184$ ($g = 16, L = 8, a = 16$), plus $0$ mismatches across all $87{,}382$ rows ($n = 0..87{,}381$, containing $856$ `A372558` drops).
4. **Provenance & review status:**
   - Mathematical route repaired and scoped in `SCOPING-C049.md` (`carbon-c049-scoping-20261114`), target frozen in `PIN-C049.md` v1, Lean 4 formalization authored in `carbon-c049-proof-20261115` (`google-ai-ultra` pool).
   - Independent cross-pool hostile review status at initial draft PR opening: **`NOT YET RUN (PENDING)`**.

---

## References

1. Antti Karttunen, *OEIS Sequence A372556: $a(n) =$ largest number $k \le \mathrm{A130249}(n)$ for which $\mathrm{A372555}(n - \mathrm{A001045}(k)) = \mathrm{A372555}(n) - 1$* (authored May 7, 2024; conjecture comment `%C` line 13 dated May 10, 2024), and companion sequences `A001045`, `A130249`, `A265745`, `A372555`, `A372557`, `A372558`, The On-Line Encyclopedia of Integer Sequences, https://oeis.org/A372556.
2. L. Carlitz, R. Scoville, and V. E. Hoggatt, Jr., *Jacobsthal representation numbers*, Fibonacci Quarterly **10** (1972), no. 5, 499–530.
3. The mathlib Community, *The Lean Mathematical Library (`Mathlib4`)*, commit `d13f23b723b8a846827a245b89c10fc7d3f11612` (`v4.34.1`), 2026.
