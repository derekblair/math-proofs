# Primorial-Core Factorization and Pure-Rational Harmonic Bounds for Unitary and Squarefree Divisor Sums: Proof and Lean 4 Formalization of Karttunen's OEIS A401714 / A401715 Conjecture

**Preprint Draft (`PAPER-S010.md`) — 2026-11-16**  
**Repository / Module:** `derekblair/math-proofs` (`Mathproofs/SeamC/A401714.lean`, `namespace SeamC.A401714`, `1,888` lines, `SHA-256: a051ec44382571e5cc1054fd5878296c04b336296a706f0cfe57cd556fcc622e`)  
**Toolchain & Mathlib Pin:** `leanprover/lean4:v4.34.1` (`Lake 5.0.0-src+5045d00`), Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`  
**Target Contract:** `PIN-S010.md` v1 (`SHA-256: 09df4c64eaac72455a6db0f21db43ba57d8674bf8dd69e703d6a6c61fc385b77`, `delta_vs_source: NONE`)

---

## Abstract

For every integer $n \ge 1$, let $\operatorname{rad}(n) = \prod_{p \mid n} p$ (`OEIS A007947`) denote the squarefree kernel of $n$, let $A_{003557}(n) = n / \operatorname{rad}(n)$ be the powerful quotient of $n$, let $A_{053669}(n)$ be the least prime not dividing $n$, let $\sigma^*(n) = A_{034448}(n) = \sum_{d \mid n,\, \gcd(d, n/d) = 1} d$ be the sum of the unitary divisors of $n$, and let $\sigma_{\mathrm{sqf}}(n) = A_{048250}(n) = \sum_{d \mid n,\, \mu(d)^2 = 1} d$ be the sum of the squarefree divisors of $n$. On November 6, 2026, after refuting a stronger May 2026 characterization proposed by Anthony Browne at $n = 240$ and $n = 270$, Antti Karttunen posed the reciprocal inequality conjecture `OEIS A401714(n) ≤ A401715(n)` (`A401714` `%F` line 14; `A401715` `%F` line 15): for every integer $n \ge 1$, whenever $n / \operatorname{rad}(n) < A_{053669}(n)$, one has
$$\sigma^*(n) + \sigma_{\mathrm{sqf}}(n) \ge 2n.$$

We prove Karttunen's conjecture unconditionally for all $n \ge 1$ and provide a complete, zero-`sorry` Lean 4 formalization directly from the literal divisor-sum definitions. Our proof resolves two obstructions that defeat naive smooth-tail arguments: (1) the raw set $\{n \ge 1 : n / \operatorname{rad}(n) < A_{053669}(n) \le q_0\}$ is **infinite** even for $q_0 = 2$ or $q_0 = 7$ (containing $n = p$, $n = 4p$, and $n = 24s$ for arbitrarily large primes $p$ and coprime squarefree integers $s$), and (2) the unitary sum $\sigma^*(n)$ alone does **not** clear $2n$ at $q = A_{053669}(n) \in \{11, 13\}$ (failing at $n \in \{1260, 1680, 2100, 27720\}$; the exact unitary-only threshold is $q \ge 17$, with global minimum ratio $\sigma^*(c)/c = 288/143$ at $q = 17, m = 12$). To overcome both obstacles, we establish a **Primorial-Core / Squarefree-Cofactor Factorization**: under $m := n / \operatorname{rad}(n) < q := A_{053669}(n)$, every prime divisor $p > q$ of $n$ appears with exponent $v_p(n) = 1$, splitting $n = c \cdot s$ into a finite **primorial core** $c = m \cdot (q - 1)\#$ ($1 \le m < q$) and a coprime squarefree cofactor $s$ satisfying $\sigma^*(s) = \sigma_{\mathrm{sqf}}(s) \ge s$. We then close all primorial cores across three regimes—exact verification on the $35$ cores with $q \le 13$, subset-deletion prime-tail bounds for $\omega(m) \le 10$ ($q \ge 17$), and a pure-$\mathbb{Q}$ harmonic-squarefree, odd-prime telescoping, and Cauchy dyadic argument for $\omega(m) \ge 11$ ($q \ge 17$) that avoids Mertens' theorem, Bertrand's postulate, real logarithms, and `native_decide`.

---

## 1. Introduction and Genealogy of the Conjecture

### 1.1 Primary Sources (`OEIS A401714`, `OEIS A401715`, and Connected Sequences)

Let $[P] \in \{0, 1\}$ denote the Iverson bracket of a proposition $P$. On November 6, 2026, Antti Karttunen introduced the twin `{0,1}`-valued indicator sequences `OEIS A401714` (live revision `#12`, November 7, 2026 [1]) and `OEIS A401715` (live revision `#13`, November 7, 2026 [2]) on domain $n \ge 1$:
$$A_{401714}(n) := \bigl[A_{003557}(n) < A_{053669}(n)\bigr], \qquad A_{401715}(n) := \bigl[\sigma^*(n) + \sigma_{\mathrm{sqf}}(n) \ge 2n\bigr],$$
where the four underlying classical arithmetic functions (`%O 1`) are:
- $A_{007947}(n) = \operatorname{rad}(n) = \prod_{p \in \operatorname{primeFactors}(n)} p$, the largest squarefree divisor (squarefree kernel) of $n$, with $\operatorname{rad}(1) = 1$ [3];
- $A_{003557}(n) = n / \operatorname{rad}(n) = \prod_{p^e \parallel n} p^{e - 1}$, with $A_{003557}(1) = 1$ [4];
- $A_{053669}(n) = \min\{p \text{ prime} : p \nmid n\}$, the smallest prime not dividing $n$, with $A_{053669}(1) = 2$ [5];
- $A_{034448}(n) = \sigma^*(n) = \sum_{\substack{d \mid n \\ \gcd(d, n/d) = 1}} d$, the sum of the unitary divisors of $n$ [6, 8]; and
- $A_{048250}(n) = \sigma_{\mathrm{sqf}}(n) = \sum_{\substack{d \mid n \\ \operatorname{Squarefree}(d)}} d$, the sum of the squarefree divisors of $n$ [7].

Across $1 \le n \le 239$, the two indicator sequences agree identically (beginning `1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, ...`). At $n = 240 = 2^4 \cdot 3 \cdot 5$, however, $\operatorname{rad}(240) = 30$, $A_{003557}(240) = 8$, and $A_{053669}(240) = 7$, giving $A_{401714}(240) = [8 < 7] = 0$, whereas
$$\sigma^*(240) + \sigma_{\mathrm{sqf}}(240) = 408 + 72 = 480 = 2 \cdot 240 \implies A_{401715}(240) = 1.$$
Karttunen reciprocally conjectured on both entries (`A401714` `%F` line 14; `A401715` `%F` line 15):

> **Conjecture (Antti Karttunen, November 6, 2026).** *For every integer $n \ge 1$, $A_{401714}(n) \le A_{401715}(n)$; equivalently, whenever $n / \operatorname{rad}(n) < A_{053669}(n)$, one has $\sigma^*(n) + \sigma_{\mathrm{sqf}}(n) \ge 2n$.*

*Genealogy and Subsumed Conjectures.* Tracing the cross-reference constellation (`A388986`, `A393869`, `A393981`, `A363082`, `A389215`, `A389216`, `A325973`, `A325977`) reveals how this conjecture arose:
1. On May 15, 2026, Anthony Browne conjectured on `OEIS A388986` (`{k : \sigma^*(k) + \sigma_{\mathrm{sqf}}(k) < 2k}`, the zero-set of $A_{401715}$) that `A388986` coincides with $\{k : \exists j < k,\, \operatorname{rad}(k) \mid j \land \operatorname{rad}(j) \nmid k\} = \{k : A_{053669}(k) < A_{003557}(k)\} = A_{393869}$ (the zero-set of $A_{401714}$; note equality $A_{003557}(k) = A_{053669}(k)$ is impossible for $k \ge 1$ because every prime dividing $k / \operatorname{rad}(k)$ divides $k$, whereas $A_{053669}(k)$ does not).
2. On November 6, 2026, Karttunen refuted Browne's two-way equality via the counterexamples $k = 240$ ($\sigma^* + \sigma_{\mathrm{sqf}} = 480 = 2k$) and $k = 270 = 2 \cdot 3^3 \cdot 5$ ($\sigma^* + \sigma_{\mathrm{sqf}} = 504 + 72 = 576 > 540 = 2k$), and posed the one-way inclusion `A388986 ⊆ A393869`—the exact contrapositive of $A_{401714}(n) \le A_{401715}(n)$.
3. Proving $A_{401714}(n) \le A_{401715}(n)$ simultaneously settles `A388986 ⊆ A393869`, its support inclusion `A393981 ⊆ A389215`, and Karttunen's September 30, 2025 restricted sub-conjecture `A363082 ⊆ A389216` (`OEIS A363082` `%C` line 11; `OEIS A325977` `%C` line 12), which restricted the same inequality to numbers that are neither squarefree nor prime powers.
4. *Parity Exactness of `A325973`.* Lines 13–14 of `A401715` `%F` also express $A_{401715}(n)$ via $A_{325973}(n) = (\sigma^*(n) + \sigma_{\mathrm{sqf}}(n)) / 2 \ge n$ (with a harmless dummy-variable typo `k` on the RHS in the OEIS text). Because $\sigma^*(n) + \sigma_{\mathrm{sqf}}(n)$ is **even for every $n \ge 1$** (Theorem 1.3 below), division by $2$ in $A_{325973}(n)$ is exact over $\mathbb{Z}$ and $\mathbb{N}$ without rounding ambiguity.

### 1.2 Summary of Formalized Theorems

In `Mathproofs/SeamC/A401714.lean` (`namespace SeamC.A401714`), all helper sequences are defined directly from their primary OEIS `%N` specifications (literal divisor sums for `a034448` and `a048250`; `sInf`-guarded least non-dividing prime for `a053669`). We prove:

- **Theorem 1.1 (Canonical Indicator Inequality — `SeamC.A401714.a401714_le_a401715`).** *For every $n \in \mathbb{N}$ with $1 \le n$,*
  $$\mathrm{a401714}(n) \le \mathrm{a401715}(n).$$
- **Theorem 1.2 (Implication Form — `SeamC.A401714.a401714_imp_a401715`).** *For every $n \in \mathbb{N}$ with $1 \le n$, if $\mathrm{a003557}(n) < \mathrm{a053669}(n)$, then*
  $$2n \le \mathrm{a034448}(n) + \mathrm{a048250}(n).$$
- **Theorem 1.3 (Divisor-Sum Euler Products, Multiplicativity, & Parity Exactness — `a034448_eq_prod`, `a048250_eq_prod`, `a034448_mul_of_coprime`, `a048250_mul_of_coprime`, `even_a034448_add_a048250`).** *For every $n \ne 0$, $\mathrm{a034448}(n) = \prod_{p \in n.\mathrm{primeFactors}} (1 + p^{v_p(n)})$ and $\mathrm{a048250}(n) = \prod_{p \in n.\mathrm{primeFactors}} (1 + p)$; both functions are multiplicative on coprime positive integers; and $\mathrm{a034448}(n) + \mathrm{a048250}(n)$ is even for every $n \ge 1$.*
- **Theorem 1.4 (Primorial-Core Reduction — `primorial_core_reduction`).** *If $1 \le n$ and $m := \mathrm{a003557}(n) < q := \mathrm{a053669}(n)$, then $n = c \cdot s$ with $c = m \cdot (q - 1)\#$, $\gcd(c, s) = 1$, and $s$ squarefree, so $2c \le \mathrm{a034448}(c) + \mathrm{a048250}(c)$ implies $2n \le \mathrm{a034448}(n) + \mathrm{a048250}(n)$.*
- **Theorem 1.5 (Exact Unitary-Only Threshold $q \ge 17$ & Refutation at $q \in \{11, 13\}$ — `ustar_core_gt_two_of_ge_seventeen`, `refute_intake_q11_ustar_claim`).** *For every $q \ge 17$ and $1 \le m < q$, $2 m \cdot (q - 1)\# < \mathrm{a034448}(m \cdot (q - 1)\#)$; conversely, at $n = 1260$ ($q = 11, m = 6$) and $n = 27720$ ($q = 13, m = 12$), $\mathrm{a003557}(n) < \mathrm{a053669}(n)$ holds while $\mathrm{a034448}(n) < 2n < \mathrm{a034448}(n) + \mathrm{a048250}(n)$.*

---

## 2. Formal Specification and Why Two Naive Heuristics Fail

### 2.1 Literal Pinned Definitions (`PIN-S010.md` v1)

To ensure zero definitional shortcutting (`PIN-S010.md` fidelity note 3), `a034448` and `a048250` are defined in `Mathproofs/SeamC/A401714.lean` as literal sums over `n.divisors` rather than pre-packaged Euler products, and `a053669` is defined via `sInf` on `Set ℕ` (evaluating cleanly to `0` at `n = 0` since every prime divides `0` in `ℕ`, and to the least non-dividing prime for all `n ≥ 1`):

```lean
def rad (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p

def a003557 (n : ℕ) : ℕ :=
  n / rad n

noncomputable def a053669 (n : ℕ) : ℕ :=
  sInf {p : ℕ | Nat.Prime p ∧ ¬ p ∣ n}

def a034448 (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors with Nat.Coprime d (n / d), d

def a048250 (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors with Squarefree d, d

noncomputable def a401714 (n : ℕ) : ℕ :=
  if a003557 n < a053669 n then 1 else 0

def a401715 (n : ℕ) : ℕ :=
  if 2 * n ≤ a034448 n + a048250 n then 1 else 0
```

### 2.2 Why Naive Smooth-Tail and $q \ge 11$ Unitary-Only Sketches Fail

An appealing first heuristic is to observe that if $q = A_{053669}(n)$, then every prime $p < q$ divides $n$, suggesting that $\sigma^*(n) / n = \prod_{p^e \parallel n} (1 + p^{-e})$ should exceed $2$ once $q$ is moderately large (say $q \ge 11$, since $\frac{3}{2}\cdot\frac{4}{3}\cdot\frac{6}{5}\cdot\frac{8}{7} = \frac{96}{35} > 2$), leaving only "finitely many" integers with $q \le 7$. **Both halves of that heuristic are false:**

1. **Failure of $\sigma^*(n)/n \ge 2$ at $q = 11$ and $q = 13$.** Higher prime powers $p^e \parallel n$ ($e \ge 2$) shrink the factor $1 + p^{-1}$ down to $1 + p^{-e}$. At $q = 11$, the primorial $(11 - 1)\# = 210$ multiplied by $m \in \{6, 8, 10\} \subset \{1, \dots, 10\}$ yields three counterexamples to $\sigma^*(n) \ge 2n$, and at $q = 13$, $(13 - 1)\# = 2310$ with $m = 12$ yields a fourth:
   - $n = 1260 = 2^2 \cdot 3^2 \cdot 5 \cdot 7$ ($q = 11, m = 6$): $\sigma^*(1260)/1260 = \frac{5}{4}\cdot\frac{10}{9}\cdot\frac{6}{5}\cdot\frac{8}{7} = \frac{40}{21} \approx 1.9048 < 2$;
   - $n = 1680 = 2^4 \cdot 3 \cdot 5 \cdot 7$ ($q = 11, m = 8$): $\sigma^*(1680)/1680 = \frac{68}{35} \approx 1.9429 < 2$;
   - $n = 2100 = 2^2 \cdot 3 \cdot 5^2 \cdot 7$ ($q = 11, m = 10$): $\sigma^*(2100)/2100 = \frac{208}{105} \approx 1.9810 < 2$;
   - $n = 27720 = 2^3 \cdot 3^2 \cdot 5 \cdot 7 \cdot 11$ ($q = 13, m = 12$): $\sigma^*(27720)/27720 = \frac{144}{77} \approx 1.8701 < 2$.
   In all four cases, the squarefree divisor sum $\sigma_{\mathrm{sqf}}(n)$ rescues the combined inequality: e.g., at $n = 27720$, $\sigma^*(27720) + \sigma_{\mathrm{sqf}}(27720) = 51840 + 6912 = 58752 > 55440 = 2 \cdot 27720$ (`refute_intake_q11_ustar_claim`). Unitary divisors alone clear $2n$ across all $1 \le m < q$ only starting at **$q \ge 17$** (Theorem 1.5).

2. **Infinitude of the Raw Small-$q$ Set.** The condition $n / \operatorname{rad}(n) < A_{053669}(n)$ restricts prime *exponents* above $q$, **not** prime *factors* above $q$. For instance:
   - every odd prime $n = p$ has $n / \operatorname{rad}(n) = 1 < 2 = A_{053669}(p)$;
   - every $n = 4p$ ($p \ge 5$ prime) has $n / \operatorname{rad}(n) = 2 < 3 = A_{053669}(4p)$; and
   - every $n = 24s$ ($\gcd(s, 30) = 1$, $s$ squarefree) has $n / \operatorname{rad}(n) = 4 < 5 = A_{053669}(24s)$.
   Thus $\{n \ge 1 : n / \operatorname{rad}(n) < A_{053669}(n) \le 13\}$ is **infinite** and cannot be discharged by raw finite enumeration. Only after factoring out the $> q$ prime support and proving it is squarefree does each prime $q$ collapse to $q - 1$ finite primorial cores.

---

## 3. Euler Products, Parity, and the Primorial-Core Reduction (Steps 1–3)

### 3.1 Step 1 — Divisor-Sum Bijections, Multiplicativity, and Parity

Let $n \ge 1$ have prime factorization $n = \prod_{p \in P} p^{v_p(n)}$, where $P = n.\mathrm{primeFactors}$.

1. **Unitary divisor sum (`a034448_eq_prod`).** If $d \mid n$ satisfies $\gcd(d, n/d) = 1$, then no prime $p \in d.\mathrm{primeFactors}$ can divide $n/d$, forcing $v_p(d) = v_p(n)$ for every $p \mid d$. Conversely, for every subset $T \subseteq P$, setting $d_T = \prod_{p \in T} p^{v_p(n)}$ and $c_T = \prod_{p \in P \setminus T} p^{v_p(n)}$ gives $d_T c_T = n$ and $\gcd(d_T, c_T) = 1$ because $T$ and $P \setminus T$ are disjoint sets of primes. Thus $d \mapsto d.\mathrm{primeFactors}$ is a bijection onto $P.\mathrm{powerset}$, and expanding via `Finset.prod_one_add` yields
   $$\sigma^*(n) = \sum_{T \subseteq P} \prod_{p \in T} p^{v_p(n)} = \prod_{p \in P} \bigl(1 + p^{v_p(n)}\bigr).$$

2. **Squarefree divisor sum (`a048250_eq_prod`).** Similarly, $d \mid n$ is squarefree if and only if $d = \prod_{p \in T} p$ for a unique subset $T = d.\mathrm{primeFactors} \subseteq P$, giving
   $$\sigma_{\mathrm{sqf}}(n) = \sum_{T \subseteq P} \prod_{p \in T} p = \prod_{p \in P} (1 + p) = \sigma_1(\operatorname{rad}(n)).$$
   Disjointness of prime supports for $\gcd(a, b) = 1$ immediately implies multiplicativity of both $\sigma^*$ and $\sigma_{\mathrm{sqf}}$ (`a034448_mul_of_coprime`, `a048250_mul_of_coprime`). Moreover, whenever $s$ is squarefree, $v_p(s) = 1$ for every $p \in s.\mathrm{primeFactors}$, whence
   $$\sigma^*(s) = \sigma_{\mathrm{sqf}}(s) = \prod_{p \in s.\mathrm{primeFactors}} (1 + p) \ge \prod_{p \in s.\mathrm{primeFactors}} p = s.$$

3. **Always-Even Sum (`even_a034448_add_a048250`).** If $n \ge 1$ has any odd prime factor $p$, then $1 + p^{v_p(n)}$ and $1 + p$ are both even, so $\sigma^*(n)$ and $\sigma_{\mathrm{sqf}}(n)$ are both even. Otherwise $n.\mathrm{primeFactors} \subseteq \{2\}$: if $n = 1$, $\sigma^*(1) + \sigma_{\mathrm{sqf}}(1) = 1 + 1 = 2$; if $n = 2^e$ ($e \ge 1$), $\sigma^*(2^e) + \sigma_{\mathrm{sqf}}(2^e) = (1 + 2^e) + 3 = 2^e + 4$, which is again even.

### 3.2 Step 2 & Step 3 — Key Exponent Lemma and Primorial-Core Factorization

Since $A_{401714}(n), A_{401715}(n) \in \{0, 1\}$, $A_{401714}(n) \le A_{401715}(n)$ holds for a given $n \ge 1$ if and only if $m < q \implies 2n \le \sigma^*(n) + \sigma_{\mathrm{sqf}}(n)$, where $m = A_{003557}(n) = \prod_{p \in P} p^{v_p(n) - 1} \ge 1$ and $q = A_{053669}(n)$.

By `Nat.exists_infinite_primes (n + 1)`, there exists a prime $p \ge n + 1$ not dividing $n$, so $q = \inf\{p \text{ prime} : p \nmid n\}$ is prime, $q \nmid n$, and every prime $p < q$ divides $n$ (`a053669_spec`). Consequently,
$$\{p \in n.\mathrm{primeFactors} : p < q\} = \mathrm{primesLE}(q - 1).$$
Partition the prime-power factorization of $n$ at $q$:
$$c := \prod_{\substack{p \in P \\ p < q}} p^{v_p(n)}, \qquad s := \prod_{\substack{p \in P \\ p \not< q}} p^{v_p(n)}, \qquad n = c \cdot s, \quad \gcd(c, s) = 1.$$

> **Lemma 3.1 (Key Exponent Lemma — `factorization_eq_one_of_ge_a053669`).** *Assume $1 \le n$ and $m = A_{003557}(n) < q = A_{053669}(n)$. For every $p \in n.\mathrm{primeFactors}$ with $p \not< q$, one has $v_p(n) = 1$.*
>
> *Proof.* Suppose $v_p(n) \ge 2$. Then $p \mid p^{v_p(n) - 1} \mid \prod_{r \in P} r^{v_r(n) - 1} = m$. Since $m \ge 1$, this forces $p \le m < q$, contradicting $p \not< q$. As $p \in n.\mathrm{primeFactors}$ gives $v_p(n) \ge 1$, we have $v_p(n) = 1$. $\square$

By Lemma 3.1, $s = \prod_{p \in P,\, p \not< q} p$ is a product of distinct primes and hence **squarefree**, while $m$'s $> q$ factors all equal $p^0 = 1$, giving $m = \prod_{p < q} p^{v_p(n) - 1}$ and
$$c = \left(\prod_{p \le q - 1} p\right)\left(\prod_{p \le q - 1} p^{v_p(n) - 1}\right) = m \cdot (q - 1)\#.$$
Using multiplicativity of $\sigma^*$ and $\sigma_{\mathrm{sqf}}$ on $\gcd(c, s) = 1$ together with $\sigma^*(s) = \sigma_{\mathrm{sqf}}(s) \ge s$, we obtain (`primorial_core_reduction`):
$$\sigma^*(n) + \sigma_{\mathrm{sqf}}(n) = \bigl(\sigma^*(c) + \sigma_{\mathrm{sqf}}(c)\bigr) \cdot \sigma_{\mathrm{sqf}}(s) \ge \bigl(\sigma^*(c) + \sigma_{\mathrm{sqf}}(c)\bigr) \cdot s.$$
Thus $2c \le \sigma^*(c) + \sigma_{\mathrm{sqf}}(c)$ immediately implies $2n = 2cs \le \sigma^*(n) + \sigma_{\mathrm{sqf}}(n)$. Moreover, since $1 \le m < q$, every prime factor of $m$ is $\le q - 1$, so $c = m \cdot (q - 1)\#$ has prime support $\mathrm{primesLE}(q - 1)$ with exponents $v_p(c) = v_p(m) + 1$ (`primorial_core_euler_products`, `ustar_core_rat_eq`):
$$\frac{\sigma^*(c)}{c} = \prod_{p \le q - 1} \left(1 + \frac{1}{p^{v_p(m) + 1}}\right), \qquad \sigma_{\mathrm{sqf}}(c) = \prod_{p \le q - 1} (1 + p).$$

---

## 4. Three-Regime Closure on Primorial Cores (Steps 4–7)

It remains to prove $2c \le \sigma^*(c) + \sigma_{\mathrm{sqf}}(c)$ for every prime $q$ and every integer $1 \le m < q$, where $c = m \cdot (q - 1)\#$.

### 4.1 Regime I ($q \le 13$): Exact Verification of All `35` Finite Cores

For $q \in \{2, 3, 5, 7, 11, 13\}$, there are $(2 - 1) + (3 - 1) + (5 - 1) + (7 - 1) + (11 - 1) + (13 - 1) = 35$ primorial cores $c = m \cdot (q - 1)\#$:

| Prime $q$ | $(q - 1)\#$ | Range of $m$ | Cores | Min $\sigma^*(c)/c$ | Min $(\sigma^*(c) + \sigma_{\mathrm{sqf}}(c))/c$ | Equalities ($= 2$) |
| ---: | ---: | :---: | ---: | :---: | :---: | :--- |
| $2$ | $1$ | $1$ | $1$ | $1$ ($m = 1$) | **$2$** ($c = 1$) | $m = 1$ ($1 + 1 = 2$) |
| $3$ | $2$ | $1..2$ | $2$ | $5/4$ ($m = 2$) | **$2$** ($c = 4$) | $m = 2$ ($5 + 3 = 8$) |
| $5$ | $6$ | $1..4$ | $4$ | $3/2$ ($m = 4$) | **$2$** ($c = 24$) | $m = 4$ ($36 + 12 = 48$) |
| $7$ | $30$ | $1..6$ | $6$ | $5/3$ ($m = 6$) | $31/15 > 2$ | none |
| $11$ | $210$ | $1..10$ | $10$ | $40/21$ ($m = 6$) | $1184/525 > 2$ | none |
| $13$ | $2310$ | $1..12$ | $12$ | $144/77$ ($m = 12$) | $816/385 > 2$ | none |

In Lean (`regime_one_core_bound`), `primorial_core_euler_products` rewrites all $35$ cores to explicit `0`-to-`5`-factor integer products via structural `ordPow`, closing every $q \le 13$ case cleanly (`3` equalities at $c \in \{1, 4, 24\}$, `32` strict inequalities).

### 4.2 Structural Prime-Set Bounds (`p ↦ (p + 1) / 2`)

For $q \ge 17$, we prove the stronger strict unitary-only bound $2c < \sigma^*(c)$ (`ustar_core_gt_two_of_ge_seventeen`). Let $B := m.\mathrm{primeFactors} \subseteq \mathrm{primesLE}(q - 1)$ and $k := |B|$. When $m \ge 2$ ($k \ge 1$), every $p \in B$ satisfies $1 + p^{-(v_p(m)+1)} > 1$, while every $p \in \mathrm{primesLE}(q - 1) \setminus B$ has $v_p(m) = 0$, giving (`ustar_core_rat_gt_sdiff`):
$$\frac{\sigma^*(c)}{c} > \prod_{p \in \mathrm{primesLE}(q - 1) \setminus B} \left(1 + \frac{1}{p}\right).$$

To control $|B| = k$ without sorting lists or invoking composite tables, consider the map $g(p) = (p + 1) / 2$ on primes (`two_mul_card_sub_one_le_max_primes`): $g(2) = 1$, while on odd primes $p = 2t - 1 \ge 3$ one has $g(p) = t \ge 2$. Thus $g$ is injective on any prime set $B$ and maps $B$ into $\{1, \dots, (p_{\max} + 1)/2\}$ where $p_{\max} = \max B$, yielding $|B| \le (p_{\max} + 1)/2$ and hence
$$p_{\max} \ge 2|B| - 1.$$
Peeling off $p_{\max}$ by induction on $k = |B| \ge 1$ (`prod_primes_ge_oddProd`, `sq_prod_one_add_inv_primes_le`) immediately yields both key estimates on $B$:
1. **Odd-product lower bound:** $\displaystyle m \ge \operatorname{rad}(m) = \prod_{p \in B} p \ge 2 \prod_{j = 1}^{k - 1} (2j + 1) =: \mathrm{oddProd}(k - 1)$;
2. **Telescoping upper bound:** using $p_{\max} \ge 2d + 3$ at step $|B| = d + 2$ ($d \ge 0$) and $(d + 1)(2d + 4)^2 = 4d^3 + 20d^2 + 32d + 16 \le 4d^3 + 20d^2 + 33d + 18 = (d + 2)(2d + 3)^2$,
   $$\left(\prod_{p \in B} \left(1 + \frac{1}{p}\right)\right)^2 \le \frac{9}{4} k.$$

### 4.3 Regime II ($q \ge 17$, $k = \omega(m) \le 10$): Subset-Deletion Prime-Tail & Small-$m$ Bounds

1. **Small-$m$ Closure (`1 ≤ m ≤ 78` — `small_m_ustar_gt_two`).** Whenever $1 \le m \le 78$ and $q \ge 17$ with $m < q$, we have $\max(13, m) \le q - 1$. Hence the explicit prefix $P_m := \{p \in \mathrm{primes}_{21} : p \le \max(13, m)\} \subseteq \mathrm{primesLE}(q - 1)$, where $\mathrm{primes}_{21} = [2, 3, \dots, 73]$. Because discarded primes $> \max(13, m)$ satisfy $1 + p^{-(v_p(m)+1)} > 1$,
   $$\frac{\sigma^*(c)}{c} \ge \prod_{p \in P_m} \left(1 + \frac{1}{p^{v_p(m) + 1}}\right) = \frac{\prod_{p \in P_m} (1 + p^{v_p(m)+1})}{\prod_{p \in P_m} p^{v_p(m)+1}} > 2$$
   across all $78$ integers $1 \le m \le 78$ (attaining minimum $\frac{288}{143} \approx 2.01399$ at $m = 12, P_{12} = \{2, 3, 5, 7, 11, 13\}$). This single lemma uniformly closes $k = 0$ ($m = 1$), all $17 \le q \le 79$, all $12$ residual $k = 2$ values ($m \le 30$), and all $5$ residual $k = 3$ values ($m \in \{30, 42, 60, 66, 70\}$).

2. **Subset-Deletion Prime-Tail Bound (`m ≥ 79`, `1 ≤ k ≤ 10` — `subset_deletion_prod_ge_tail`, `regime_two_large_m_ustar_gt_two`).** Suppose $A, T \subset \mathbb{N}_+$ are disjoint finite sets with $A$ nonempty, $\max A \le \min T$, $A \cup T \subseteq P = \mathrm{primesLE}(q - 1)$, and $|B| \le |A|$. Writing $C = (A \cup T) \cap B$ and $a_{\max} = \max A$, we have $|C \setminus A| \le |A \setminus C|$, $1 + 1/x \le 1 + 1/a_{\max}$ on $C \setminus A \subseteq T$, and $1 + 1/a_{\max} \le 1 + 1/y$ on $A \setminus C \subseteq A$, so
   $$\prod_{x \in C \setminus A} \left(1 + \frac{1}{x}\right) \le \left(1 + \frac{1}{a_{\max}}\right)^{|C \setminus A|} \le \left(1 + \frac{1}{a_{\max}}\right)^{|A \setminus C|} \le \prod_{y \in A \setminus C} \left(1 + \frac{1}{y}\right).$$
   Multiplying by $\prod_{z \in C \cap A} (1 + 1/z)$ gives $\prod_{x \in C} (1 + 1/x) \le \prod_{y \in A} (1 + 1/y)$, whence cancelling $\prod_{y \in A} (1 + 1/y) > 0$ from $\prod_{A \cup T} = \prod_A \prod_T = \prod_C \prod_{(A \cup T) \setminus C}$ yields
   $$\prod_{p \in P \setminus B} \left(1 + \frac{1}{p}\right) \ge \prod_{p \in (A \cup T) \setminus C} \left(1 + \frac{1}{p}\right) \ge \prod_{t \in T} \left(1 + \frac{1}{t}\right).$$
   Taking $A \cup T$ to be the first $N_k \in \{6, 11, 21, 35, 51, 73, 98, 130, 167, 204\}$ primes from `primes204` (`2` through `1249`) with $|A| = k$ and $T$ the remaining $N_k - k$ primes:
   - For $k \in \{1, 2, 3\}$, $\max(A \cup T) \in \{13, 31, 73\} \le 79 \le m \le q - 1$;
   - For $4 \le k \le 10$, $\mathrm{oddProd}(k - 1) \in \{210, 1890, 20790, 270270, 4054050, 68918850, 1309458150\}$ automatically exceeds $\max(A \cup T) \in \{149, 233, 367, 521, 733, 991, 1249\}$, so $A \cup T \subseteq \mathrm{primesLE}(q - 1)$ with **zero** residual $m$-cases; and
   - In every case $1 \le k \le 10$, clearing denominators to $\mathbb{N}$ certifies $\prod_{t \in T} (t + 1) > 2 \prod_{t \in T} t$, i.e., $\prod_{t \in T} (1 + 1/t) > 2$.

### 4.4 Regime III ($q \ge 17$, $k = \omega(m) \ge 11$): Pure-$\mathbb{Q}$ Harmonic-Squarefree Closure

For $k \ge 11$, we dispense with finite prime tables entirely and work over $\mathbb{Q}$ (`regime_three_ustar_gt_two`):

1. **Harmonic-Squarefree Cover (`harm_lt_zeta2_mul_primorial_prod`).** Let $N = q - 1 \ge 16$. Every integer $1 \le j \le N$ writes via `Nat.sq_mul_squarefree_of_pos` as $j = b_j^2 a_j$ with $a_j, b_j \ge 1$ and $a_j$ squarefree. Since $a_j \le j \le N$, `Squarefree.dvd_primorial` and `primorial_dvd_primorial` give $a_j \mid a_j\# \mid N\#$; moreover, $j \mapsto (a_j, b_j)$ is injective because $b_j^2 a_j = j$ reconstructs $j$. Summing reciprocals over $\mathbb{Q}$ and using $\sum_{b=1}^N b^{-2} \le \frac{61}{36} - \frac{1}{N} < \frac{61}{36}$ (`sum_inv_sq_lt`, by telescoping $b^{-2} \le \frac{1}{b-1} - \frac{1}{b}$ for $b \ge 4$ above $1 + \frac{1}{4} + \frac{1}{9} = \frac{49}{36}$) yields
   $$H_{q - 1} := \sum_{j = 1}^{q - 1} \frac{1}{j} \le \left(\sum_{a \mid (q - 1)\#} \frac{1}{a}\right)\left(\sum_{b = 1}^{q - 1} \frac{1}{b^2}\right) < \frac{61}{36} \prod_{p \le q - 1} \left(1 + \frac{1}{p}\right).$$

2. **Cauchy Dyadic Lower Bound (`harm_two_pow_ge`, `oddProd_ge_two_pow`).** At $k = 11$, $\mathrm{oddProd}(10) = 27{,}498{,}621{,}150 > 2^{34} = 17{,}179{,}869{,}184$, and each step $k \mapsto k + 1$ multiplies by $2k + 1 \ge 23 > 2^4$, giving $q - 1 \ge m \ge \mathrm{oddProd}(k - 1) \ge 2^{34 + 4(k - 11)}$. By Cauchy dyadic grouping $H_{2^L} \ge 1 + L / 2$,
   $$H_{q - 1} \ge 1 + \frac{34 + 4(k - 11)}{2} = 18 + 2(k - 11) = 2k - 4.$$

3. **Final Ratio Closure.** Combining Steps 1–2 with $\left(\prod_{p \in B} (1 + 1/p)\right)^2 \le \frac{9}{4} k$ gives
   $$\left(\frac{\sigma^*(c)}{c}\right)^2 > \left(\prod_{p \in \mathrm{primesLE}(q - 1) \setminus B} \left(1 + \frac{1}{p}\right)\right)^2 > \frac{\bigl(\frac{36}{61}(2k - 4)\bigr)^2}{\frac{9}{4} k} = \frac{576 (2k - 4)^2}{3721 k} = \frac{2304 (k - 2)^2}{3721 k}.$$
   *(Algebraic note: `SCOPING-S010.md` §2.2 L203 wrote $576(k+7)^2/(3721k)$ by simplifying $18 + 2(k - 11)$ at $k = 11$ without distributing the factor $2$ onto $k - 11$; both expressions evaluate to $\frac{186624}{40931} \approx 4.5595 > 4$ at $k = 11$, and the exact expression $\frac{2304(k - 2)^2}{3721 k}$ grows four times faster for $k > 11$.)* Writing $k = 11 + d$ ($d \ge 0$), clearing denominators reduces $4 < \frac{576(2k - 4)^2}{3721 k}$ to
   $$576(18 + 2d)^2 - 4 \cdot 3721 (11 + d) = 22{,}900 + 26{,}588 d + 2{,}304 d^2 > 0,$$
   establishing $\sigma^*(c) > 2c$ for all $k \ge 11$ and completing the proof of Theorems 1.1 and 1.2.

---

## 5. Scope, Strength Delta, and Verification Record

### 5.1 Strength Delta and Open Questions ("What This Does Not Show")

- **Strength Delta vs Source:** **`NONE`**. Theorems 1.1 and 1.2 establish Karttunen's exact published conjecture on `OEIS A401714` and `OEIS A401715` over the full `%O 1` domain $n \ge 1$, with all helper functions defined directly from their primary `%N` definitions.
- **What This Paper Does *Not* Show:**
  1. When $A_{003557}(n) > A_{053669}(n)$ (`A401714(n) = 0`), the difference $A_{325977}(n) = \frac{1}{2}(\sigma^*(n) + \sigma_{\mathrm{sqf}}(n)) - n$ takes both negative values (`A388986`: $8, 9, 16, 25, 27, \dots$) and nonnegative values (`240, 270, 280, 294, 315, \dots`). Characterizing the exact overflow set $\{n : A_{401714}(n) = 0 \land A_{401715}(n) = 1\}$ (`A389215 \ A393981`) remains a separate question.
  2. Our proof shows that within the support $A_{401714}(n) = 1$, exact equality $\sigma^*(n) + \sigma_{\mathrm{sqf}}(n) = 2n$ occurs **only** at $n \in \{1, 4, 24\}$ (since $s > 1$ squarefree forces $\sigma_{\mathrm{sqf}}(s) \ge 1 + s > s$, and every core outside $\{(2, 1), (3, 2), (5, 4)\}$ satisfies $\sigma^*(c) + \sigma_{\mathrm{sqf}}(c) > 2c$). Outside $A_{401714}(n) = 1$, `OEIS A325963` records two additional equalities $n = 240$ and $n = 349{,}440 = 2^8 \cdot 3 \cdot 5 \cdot 7 \cdot 13$ ($690{,}816 + 8{,}064 = 698{,}880 = 2 \cdot 349{,}440$, verified in `boundary_and_equality_spot_checks`) with no others below $10^{12}$; whether `A325963` is finite is an open problem analogous to the unitary perfect number conjecture.

### 5.2 Computational and Formal Verification Summary

1. **Bounded Independent Verification:** Checked `0` mismatches against all `105` printed `%S/%T/%U` terms on `A401714` and `A401715` (`808` printed terms across $9$ sequences and `131,074` b-file terms through $n = 65{,}537$ during scoping), `0` violations and `0` odd values of $\sigma^*(n) + \sigma_{\mathrm{sqf}}(n)$ across $1 \le n \le 2{,}000{,}000$ (`27,087` strict `<` cases starting at $n = 240$; exact equalities $\{1, 4, 24, 240, 349440\}$), and `0` violations across `100,000` primorial multiples and `76,967` primorial cores ($q \le 1{,}009$).
2. **Lean 4 Kernel & Trust-Gate Audit (`Mathproofs/SeamC/A401714.lean`):**
   - Clean-slate `rm -rf .lake/build && lake build`: exit `0`, `0` errors, `0` `sorry`s, `0` linter warnings.
   - Fresh kernel replay `leanchecker --fresh Mathproofs.SeamC.A401714`: exit `0`.
   - `#print axioms` on `a401714_le_a401715`, `a401714_imp_a401715`, and all $7$ pinned definitions: `[propext, Classical.choice, Quot.sound]` only.
   - Comment- and string-stripped lexical trust-escape screen across the import closure: `0` active hits on `sorry`, `admit`, `sorryAx`, `axiom`, `native_decide`, `ofReduceBool`, `implemented_by`, `unsafe`.
   - Kernel non-vacuity theorems (`oeis_a401714_1_to_105`, `oeis_a401715_1_to_105`, `boundary_and_equality_spot_checks`, `refute_intake_q11_ustar_claim`): proved via formally verified computable mirrors (`a401714_eq_smallCompute`, `a401715_eq_compute`), matching all `105` live OEIS terms and boundary cases $n \in \{1, 4, 8, 9, 24, 240, 270, 1260, 27720, 349440\}$.

---

## References

1. A. Karttunen, Sequence `A401714` in *The On-Line Encyclopedia of Integer Sequences* (`https://oeis.org/A401714`), Nov. 6, 2026 (rev. `#12`, Nov. 7, 2026).
2. A. Karttunen, Sequence `A401715` in *The On-Line Encyclopedia of Integer Sequences* (`https://oeis.org/A401715`), Nov. 6, 2026 (rev. `#13`, Nov. 7, 2026); cf. connected entries `A388986`, `A393869`, `A393981`, `A363082`, `A389215`, `A389216`, `A325963`, `A325973`, `A325977`.
3. N. J. A. Sloane, Sequence `A007947` (largest squarefree number dividing $n$: squarefree kernel $\operatorname{rad}(n)$) in *The On-Line Encyclopedia of Integer Sequences* (`https://oeis.org/A007947`).
4. N. J. A. Sloane, Sequence `A003557` ($n$ divided by largest squarefree divisor of $n$) in *The On-Line Encyclopedia of Integer Sequences* (`https://oeis.org/A003557`).
5. R. Stephan and N. J. A. Sloane, Sequence `A053669` (smallest prime not dividing $n$) in *The On-Line Encyclopedia of Integer Sequences* (`https://oeis.org/A053669`).
6. N. J. A. Sloane, Sequence `A034448` ($\operatorname{usigma}(n)$, sum of unitary divisors of $n$) in *The On-Line Encyclopedia of Integer Sequences* (`https://oeis.org/A034448`).
7. L. Tóth and N. J. A. Sloane, Sequence `A048250` (sum of squarefree divisors of $n$) in *The On-Line Encyclopedia of Integer Sequences* (`https://oeis.org/A048250`).
8. E. Cohen, "Arithmetical functions associated with the unitary divisors of an integer," *Mathematische Zeitschrift*, vol. 74, pp. 66–80, 1960.
9. The mathlib Community, "The Lean Mathematical Library," in *Proc. 9th ACM SIGPLAN Int. Conf. Certified Programs and Proofs (CPP)*, 2020 (`leanprover-community/mathlib4`, rev. `d13f23b723b8a846827a245b89c10fc7d3f11612`).
