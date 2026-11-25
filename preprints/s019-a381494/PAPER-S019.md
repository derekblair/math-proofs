# Discrete Radix Periodicity and Finite-Field Minimal Polynomials: Proof and Lean 4 Formalization of R. J. Mathar's OEIS A381494 = A218358 Conjecture

**Preprint Draft (`PAPER-S019.md`) — 2026-11-16**  
**Repository / Module:** `derekblair/math-proofs` (`SeamC/A381494.lean`, `namespace SeamC.A381494`, `1,017` lines, `SHA-256: ca7196659af75049e0dfe9e99ca8b716a6db0b40cdc36460d7c1890553c961bf`)  
**Toolchain & Mathlib Pin:** `leanprover/lean4:v4.34.1` (`Lake 5.0.0-src+5045d00`), Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`  
**Target Contract:** `PIN-S019.md` v1 (`SHA-256: cb886cb3db98808363e93d9a882cd649c3dbce132015afb8f67bbadb7330c663`, `delta_vs_source: NONE`)

---

## Abstract

For every integer $n \ge 0$, let $A_{381494}(n)$ (`OEIS A381494`, introduced by Erich Friedman on February 25, 2025) denote the smallest positive integer $m$ whose reciprocal $1/m$ has eventual post-radix period length $n$ in base $7$ (with terminating expansions assigned period length $0$). Independently, for every integer $n \ge 1$, let $A_{218358}(n)$ (`OEIS A218358`, introduced by Alois P. Heinz on October 27, 2012) denote the minimal polynomial order $\operatorname{ord}(f) = \min\{e \ge 1 : f(X) \mid (X^e - 1)\}$ over all degree-$n$ irreducible polynomials $f \in \mathbb{F}_7[X]$ with $f(0) \ne 0$. On March 3, 2025, R. J. Mathar conjectured (`OEIS A381494` `%F` line 14) that for every integer $n \ge 2$,
$$A_{381494}(n) \;=\; A_{218358}(n).$$

We prove Mathar's conjecture unconditionally for all $n \ge 2$—together with its sharp boundary behavior at $n = 0, 1$ and the Zsigmondy-exception base case $A_{381494}(2) = A_{218358}(2) = 4$—and provide a complete, zero-`sorry` Lean 4 formalization directly between the two primary `%N` definitions. We also clarify and avoid two structural traps in formalizing this identity: (1) defining either sequence via the unproved divisor-scan formulas in `A381494` `%C` and `A218358` `%F` (`min(M(n))`) is forbidden because those two formulas define the identical set difference on $\mathbb{N}$ and would reduce the theorem to a definitional tautology bypassing both base-$7$ expansions and $\mathbb{F}_7[X]$ polynomials; and (2) routing through integer cyclotomic polynomial values $d \mid \Phi_n(7)$ is mathematically false in general, failing first at $n = 3$ ($a(3) = 9 \nmid 57 = \Phi_3(7)$), becoming coprime at $n = 6$ ($\gcd(36, 43) = 1$), and failing at $21$ of the $49$ indices $2 \le n \le 50$ ($32$ of $79$ in $2 \le n \le 80$). Instead, we establish a cyclotomic-free, Zsigmondy-free, and real-analysis-free five-step bridge through the internal primitive-divisor set $S(n) = \{d > 1 : d \mid (7^n - 1) \land \forall\, 1 \le k < n,\, d \nmid (7^k - 1)\}$, pairing a subtraction-free discrete remainder-block recursion and $\mathbb{Z}$-boundedness cancellation on base-$7$ digits with `AdjoinRoot` Frobenius root-counting and `GaloisField 7 n` cyclic-unit realization via the intermediate-field dimension tower law.

---

## 1. Introduction and Primary Sources

### 1.1 The Two OEIS Sequences and R. J. Mathar's Conjecture

On October 27, 2012, Alois P. Heinz introduced sequence `OEIS A218358` (`%O 1,2`, live revision `#17`, February 16, 2025 [2]; `430`-term b-file by Max Alekseyev [3]) with primary `%N` definition:

> **`%N A218358`** *Minimal order of degree-$n$ irreducible polynomials over $\mathrm{GF}(7)$.*

Here, following Lidl and Niederreiter [5, Def. 3.2, p. 84], the *order* (or *period* / *exponent*) of a nonzero polynomial $f \in \mathbb{F}_q[X]$ satisfying $f(0) \ne 0$ is the least positive integer $e \ge 1$ such that $f(X)$ divides $X^e - 1$ in $\mathbb{F}_q[X]$ (at $n = 1$, the single zero-constant monic linear polynomial $f(X) = X$ divides no $X^e - 1$ and is excluded by $f(0) \ne 0$, whereas for all $n \ge 2$ every degree-$n$ irreducible automatically satisfies $f(0) \ne 0$). Its initial values for $n = 1..10$ are:
$$A_{218358}(1..10) \;=\; [1,\; 4,\; 9,\; 5,\; 2801,\; 36,\; 29,\; 64,\; 27,\; 11].$$

More than twelve years later, on February 25, 2025, Erich Friedman introduced sequence `OEIS A381494` (`%O 0,2`, live revision `#23`, March 2, 2026 [1]; `127`-term b-file for $n = 0..126$ by Robert Israel [4]) alongside base-$9$ and base-$8$ siblings `A381370` and `A381493`, with primary `%N` definition:

> **`%N A381494`** *Smallest number with reciprocal of period length $n$ in base $7$.*

For a positive integer $m \ge 1$, the $k$-th base-$7$ digit of $1/m$ after the radix point ($k \ge 1$) is the integer $d_k(m) = \lfloor 7^k / m \rfloor \bmod 7 \in \{0, \dots, 6\}$. Under the standard OEIS convention shared across `A003060` (base $10$), `A381370` (base $9$), `A381493` (base $8$), and `A381494` (base $7$):
- Terminating base-$7$ expansions ($d_k(m) = 0$ for all sufficiently large $k$, occurring precisely at powers $m = 7^v$) are assigned period length $0$, so $A_{381494}(0) = 1$ ($1/1 = 1.000\ldots_7$).
- Non-terminating expansions are assigned period length equal to their minimal positive eventual period $n \ge 1$ (permitting mixed-periodic preperiods when $7 \mid m$). At $n = 1$, since $m = 1$ terminates, the smallest denominator with period length $1$ is $m = 2$ ($1/2 = 0.333\ldots_7$), giving $A_{381494}(1) = 2$. For $n = 0..10$, the live sequence begins:
$$A_{381494}(0..10) \;=\; [1,\; 2,\; 4,\; 9,\; 5,\; 2801,\; 36,\; 29,\; 64,\; 27,\; 11].$$

Observing the agreement from $n = 2$ onward, R. J. Mathar posed the following conjecture on March 3, 2025 (`OEIS A381494` `%F` line 14 [1]):

> **Conjecture (R. J. Mathar, March 3, 2025).** *For every integer $n \ge 2$, $A_{381494}(n) = A_{218358}(n)$.*

Notice that Mathar's domain guard $n \ge 2$ is **sharp**:
1. At $n = 0$, $A_{381494}(0) = 1$, whereas $A_{218358}$ is undefined at $n = 0$ (`%O 1,2`, as constants in $\mathbb{F}_7[X]$ are units or zero, never irreducible).
2. At $n = 1$, $A_{381494}(1) = 2$ because $m = 1$ terminates (period $0$), whereas in $\mathbb{F}_7[X]$ the monic linear polynomial $f(X) = X - 1$ is irreducible of degree $1$ with $f(0) = -1 \ne 0$ and divides $X^1 - 1$, yielding $A_{218358}(1) = 1 \ne 2 = A_{381494}(1)$.

Moreover, the very first in-domain index $n = 2$ exhibits a classic arithmetic subtlety: because $7 = 2^3 - 1$ is a Mersenne prime, $(b, n) = (7, 2)$ is the **Zsigmondy prime exception** [7]. Every prime factor of $7^2 - 1 = 48 = 2^4 \cdot 3$ already divides $7^1 - 1 = 6$, so $7^2 - 1$ possesses **no prime** primitive divisor (`OEIS A379640(2) = 1`). Nevertheless, composite prime powers rescue primitive divisibility: $S(2) = \{4, 8, 12, 16, 24, 48\}$ has minimum $4$, matching both $1/4 = 0.1515\ldots_7$ (period $2$) and $f(X) = X^2 + 1 \in \mathbb{F}_7[X]$ (irreducible since $-1 \equiv 6$ is a quadratic nonresidue modulo $7$, dividing $X^4 - 1 = (X^2 - 1)(X^2 + 1)$ of minimal order $4$). Any proof valid for all $n \ge 2$ must therefore treat composite primitive divisors uniformly without invoking Zsigmondy's theorem.

### 1.2 Summary of Formalized Results

In `SeamC/A381494.lean` (`namespace SeamC.A381494`), both sequences are formalized verbatim from their primary `%N` definitions (`base7LeastPeriodDenominator` via the exact integer post-radix digit sequence `base7RecipDigit m k := (7 ^ k / m) % 7`, and `minIrredOrder` via `polyOrder` over `Polynomial (ZMod 7)`). We prove:

- **Theorem 1.1 (Main Identity — `SeamC.A381494.base7LeastPeriodDenominator_eq_minIrredOrder`).** *For every $n \in \mathbb{N}$ with $2 \le n$,*
  $$\mathrm{base7LeastPeriodDenominator}(n) \;=\; \mathrm{minIrredOrder}(n).$$
- **Theorem 1.2 (Base Calibration — `SeamC.A381494.base7LeastPeriodDenominator_two`, `minIrredOrder_two`).**
  $$\mathrm{base7LeastPeriodDenominator}(2) \;=\; \mathrm{minIrredOrder}(2) \;=\; 4.$$
- **Theorem 1.3 (Sharp Boundary Behavior & Automatic Constant-Term Guard — `base7LeastPeriodDenominator_zero`, `sharp_guard_at_one`, `irred_coeff_zero_ne_zero_of_two_le`).** *At $n = 0$ and $n = 1$, $\mathrm{base7LeastPeriodDenominator}(0) = 1$, $\mathrm{base7LeastPeriodDenominator}(1) = 2$, and $\mathrm{minIrredOrder}(1) = 1$ ($2 \ne 1$); furthermore, for every irreducible $f \in \mathbb{F}_7[X]$ with $\deg f \ge 2$, $f(0) \ne 0$ holds automatically.*
- **Theorem 1.4 (`O(\sqrt{7^n - 1})` Computable Mirror & Cyclotomic Refutation — `base7LeastPeriodDenominator_eq_compute`, `minIrredOrder_eq_compute`, `oeis_spot_checks_2_to_10`, `refute_cyclotomic_divisor_shortcut`).** *Both pinned sequences agree with the total structural divisor-pair algorithm `a381494Compute`, certifying the live OEIS terms `[4, 9, 5, 2801, 36, 29, 64, 27, 11]` for $n = 2..10$ in the Lean kernel (without `native_decide`) and refuting $a(n) \mid \Phi_n(7)$ at $n = 3$ ($9 \nmid 57$) and $n = 6$ ($\gcd(36, 43) = 1$).*

---

## 2. Formal Specification and Two Structural Traps

### 2.1 Literal Pinned Definitions (`PIN-S019.md` v1)

```lean
def base7RecipDigit (m k : ℕ) : ℕ :=
  (7 ^ k / m) % 7

def HasBase7RecipPeriodLen (m n : ℕ) : Prop :=
  1 ≤ m ∧
    ((n = 0 ∧ ∃ K ≥ 1, ∀ k ≥ K, base7RecipDigit m k = 0) ∨
      (1 ≤ n ∧
        (¬ ∃ K ≥ 1, ∀ k ≥ K, base7RecipDigit m k = 0) ∧
        (∃ K ≥ 1, ∀ k ≥ K, base7RecipDigit m (k + n) = base7RecipDigit m k) ∧
        (∀ p : ℕ, 1 ≤ p → p < n →
          ¬ ∃ K ≥ 1, ∀ k ≥ K, base7RecipDigit m (k + p) = base7RecipDigit m k)))

noncomputable def base7LeastPeriodDenominator (n : ℕ) : ℕ :=
  sInf { m : ℕ | HasBase7RecipPeriodLen m n }

noncomputable def polyOrder (f : Polynomial (ZMod 7)) : ℕ :=
  sInf { e : ℕ | 1 ≤ e ∧ f ∣ (Polynomial.X ^ e - 1) }

noncomputable def minIrredOrder (n : ℕ) : ℕ :=
  sInf { d : ℕ | ∃ f : Polynomial (ZMod 7),
    f.Monic ∧ Irreducible f ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0 ∧ d = polyOrder f }
```

Note that restricting `minIrredOrder` to monic polynomials loses no generality: over the field $\mathbb{F}_7 = \mathrm{ZMod}\ 7$, every nonzero polynomial $g$ is unit-associate to the unique monic polynomial $f = c^{-1} g$ ($c = \operatorname{leadingCoeff}(g) \in \mathbb{F}_7^\times$), and scaling by $c^{-1} \in \mathbb{F}_7^\times$ preserves `Irreducible`, `natDegree`, `coeff 0 ≠ 0`, and divisibility into $X^e - 1$.

### 2.2 Trap 1: Why `min(M(n))` Divisor-Scan Definientia Are Forbidden

Both OEIS entries contain unproved secondary comments/formulas expressing $a(n)$ as a primitive-divisor scan:
- `A381494` `%C` (line 11): *"For $n > 1$, $a(n)$ is the smallest positive $d$ such that $d$ divides $7^n - 1$ and does not divide any of $7^k - 1$ for $0 < k < n$."*
- `A218358` `%F` (line 15): *"a(n) = min(M(n)) with M(n) = {d : d|(7^n-1)} \ U(n-1) and U(n) = M(n) union U(n-1) for n>0, U(0) = {}."*

By induction on $n \ge 1$, $U(n - 1) = \bigcup_{k = 1}^{n - 1} \{d : d \mid (7^k - 1)\}$. Since $1 \mid (7^1 - 1) = 6$, we have $1 \in U(n - 1)$ for every $n \ge 2$. Therefore, for all $n \ge 2$, the set $M(n)$ in `A218358` `%F` and the set in `A381494` `%C` are **literally the same subset of $\mathbb{N}$**. Neither OEIS record proves that its `%N` object equals this divisor scan. Formalizing either sequence by its divisor-scan formula would erase the mathematical content of Mathar's conjecture, collapsing it into a trivial set-theory exercise without ever touching base-$7$ digits or polynomials over $\mathbb{F}_7$. Our formalization therefore forbids divisor-scan shortcuts in the exported definitions and proves **both** halves of the bridge from scratch through an internal (`private`) primitive-divisor predicate.

### 2.3 Trap 2: Refutation of the Integer Cyclotomic-Divisor Shortcut `d ∣ Φ_n(7)`

Because $7^n - 1 = \prod_{e \mid n} \Phi_e(7)$, it is tempting to conflate *"primitive divisors of $7^n - 1$"* with *"divisors $d > 1$ of the $n$-th cyclotomic polynomial value $\Phi_n(7)$ not dividing $7^k - 1$ for $k < n$"*. **That integer cyclotomic-divisor condition is false in general:**

1. **Prime-power lifting across shared prime factors ($n = 3$):** We have $7^1 - 1 = \Phi_1(7) = 6 = 2 \cdot 3$ and $\Phi_3(7) = 7^2 + 7 + 1 = 57 = 3 \cdot 19$, so $7^3 - 1 = 342 = 2 \cdot 3^2 \cdot 19$. Here $S(3) = \{9, 18, 19, 38, 57, 114, 171, 342\}$ has minimum $a(3) = 9$ ($1/9 = 0.053053\ldots_7$; over $\mathbb{F}_7[X]$, $\Phi_9(X) = X^6 + X^3 + 1 \equiv (X^3 + 2)(X^3 + 4) \pmod 7$ yields two cubic irreducibles of order $9$), yet **$9 \nmid 57 = \Phi_3(7)$** ($\gcd(9, 57) = 3$).
2. **Pure $\operatorname{lcm}$-order combinations coprime to $\Phi_n(7)$ ($n = 6$):** Whenever $n$ has proper divisors $e_1, e_2 < n$ with $\operatorname{lcm}(e_1, e_2) = n$, multiplying $d_1 \in S(e_1)$ and $d_2 \in S(e_2)$ with $\gcd(d_1, d_2) = 1$ yields $d_1 d_2 \in S(n)$ using **zero** prime factors from $\Phi_n(7)$. At $n = 6$, $4 \in S(2)$ and $9 \in S(3)$ give $a(6) = 36 \in S(6)$, which is **coprime** to $\Phi_6(7) = 7^2 - 7 + 1 = 43$ ($\gcd(36, 43) = 1$). Similarly, at $n = 50$, $4 \in S(2)$ and $2551 \in S(25)$ give $a(50) = 10204$ with $\gcd(10204, \Phi_{50}(7)) = 1$.
3. **Quantitative frequency:** Across $2 \le n \le 50$, $a(n) \mid \Phi_n(7)$ fails at **$21$ of $49$ indices** (`n = 3, 6, 8, 9, 18, 20, 21, 27, 28, 30, 32, 34, 35, 36, 38, 42, 44, 45, 46, 48, 50`), with $\gcd(a(n), \Phi_n(7)) = 1$ at **$15$ of $49$ indices**; extending to $2 \le n \le 80$ yields **$32$ failures**.

Over $\mathbb{F}_7[X]$, the cyclotomic polynomial genuinely associated with an order $d \in S(n)$ is the **$d$-th** cyclotomic polynomial $\Phi_d(X) \bmod 7$ (which splits into $\varphi(d)/n$ monic irreducibles of degree $\operatorname{ord}_d(7) = n$ [5, Thm. 2.47]), **not** $\Phi_n(7)$. Better still, as shown in Section 4, routing through `AdjoinRoot` and `GaloisField 7 n` avoids cyclotomic polynomials completely.

---

## 3. Discrete Base-7 Reciprocal Periods (Steps 1–2)

### 3.1 Step 1 — The Primitive-Divisor Set $S(n)$

For $n \ge 1$, define the primitive-divisor set of $7^n - 1$:
$$S(n) \;:=\; \bigl\{\, d \in \mathbb{N} \;:\; 1 < d \;\land\; d \mid (7^n - 1) \;\land\; \forall k \in \{1, \dots, n - 1\},\; d \nmid (7^k - 1) \,\bigr\}.$$

> **Lemma 3.1 (`self_mem_primitiveDivisors7`, `coprime_seven_of_dvd_seven_pow_sub_one`).** *For every $n \ge 1$, $7^n - 1 \in S(n)$, so $S(n)$ is nonempty with well-defined minimum $d_{\min}(n) := \inf S(n) \in [2, 7^n - 1]$. Moreover, every $d \mid (7^n - 1)$ satisfies $\gcd(d, 7) = 1$.*
>
> *Proof.* Since $n \ge 1$, $7^n \ge 7 > 2$, so $1 < 7^n - 1$ and $(7^n - 1) \mid (7^n - 1)$. For $1 \le k < n$, strict monotonicity of $7^{(\cdot)}$ gives $0 < 7^k - 1 < 7^n - 1$, preventing $(7^n - 1) \mid (7^k - 1)$. Finally, if $7 \mid d \mid (7^n - 1)$, then since $7 \mid 7^n$, $7$ divides $7^n - (7^n - 1) = 1$, a contradiction; since $7$ is prime, $\gcd(d, 7) = 1$. $\square$

### 3.2 Step 2 — Subtraction-Free Remainder-Block Recursion and $\mathbb{Z}$-Boundedness Cancellation

To characterize `HasBase7RecipPeriodLen m n` without real numbers or convergent geometric series, we first factor out powers of $7$. By strong induction (`exists_seven_pow_mul_coprime`), every $m \ge 1$ writes as $m = 7^v m'$ with $v \ge 0$, $m' \ge 1$, and $\gcd(m', 7) = 1$. Because
$$d_{v + j}(7^v m') \;=\; \left\lfloor \frac{7^{v + j}}{7^v m'} \right\rfloor \bmod 7 \;=\; \left\lfloor \frac{7^j}{m'} \right\rfloor \bmod 7 \;=\; d_j(m') \qquad (\forall j \ge 1),$$
the sequence $(d_k(7^v m'))_{k \ge 1}$ is simply $(d_j(m'))_{j \ge 1}$ shifted by $v$ preperiod digits (`base7RecipDigit_seven_pow_mul`). Consequently, eventual termination and eventual periodicity of period $p$ are invariant under multiplying by $7^v$, giving (`hasBase7RecipPeriodLen_seven_pow_mul_iff`):
$$\mathrm{HasBase7RecipPeriodLen}(7^v m', n) \;\iff\; \mathrm{HasBase7RecipPeriodLen}(m', n) \qquad (\forall v, n \in \mathbb{N},\; m' \ge 1).$$

Next, for any $m, k \in \mathbb{N}$, let $Q = \lfloor 7^{k+1} / m \rfloor$. Since $Q / 7 = \lfloor 7^{k+1} / (7m) \rfloor = \lfloor 7^k / m \rfloor$ and $Q \bmod 7 = d_{k+1}(m)$, Euclidean division $Q = 7(Q / 7) + (Q \bmod 7)$ gives the exact one-step quotient identity (`seven_pow_div_step`):
$$\lfloor 7^{k + 1} / m \rfloor \;=\; 7 \lfloor 7^k / m \rfloor + d_{k + 1}(m).$$
Defining the $P$-digit block $B(m, K, P)$ recursively by $B(m, K, 0) = 0$ and $B(m, K, P + 1) = 7 B(m, K, P) + d_{K + P + 1}(m)$, induction on $P \ge 0$ yields $B(m, K, P) < 7^P$ (`digitBlock_lt_pow`), $\lfloor 7^{K+P} / m \rfloor = 7^P \lfloor 7^K / m \rfloor + B(m, K, P)$ (`digitBlock_div_eq`), and—after multiplying by $m$ and cancelling $m \cdot 7^P \lfloor 7^K / m \rfloor$ from $7^{K+P} = 7^P(m \lfloor 7^K / m \rfloor + (7^K \bmod m))$—the **subtraction-free remainder-block identity** (`rem_block_identity`):
$$7^P (7^K \bmod m) \;=\; m \cdot B(m, K, P) + (7^{K + P} \bmod m) \qquad (\forall m, K, P \in \mathbb{N}).$$

For $m' \ge 1$ with $\gcd(m', 7) = 1$, this single equation governs all three clauses of `HasBase7RecipPeriodLen`:

1. **Termination iff $m' = 1$ (`terminates_one`, `not_terminates_of_gt_one_coprime`).** At $m' = 1$, $d_k(1) = 7^k \bmod 7 = 0$ for all $k \ge 1$. Conversely, if $m' > 1$ with $\gcd(m', 7) = 1$ terminated after $K \ge 1$, then $B(m', K, m') = 0$, so $7^{m'} (7^K \bmod m') = 7^{K + m'} \bmod m' < m'$. Since $\gcd(m', 7^K) = 1$ and $m' > 1$, we have $7^K \bmod m' \ge 1$, contradicting $m' < 7^{m'} \le 7^{m'}(7^K \bmod m')$.
2. **Forward Periodicity (`eventualPeriod_of_dvd_seven_pow_sub_one`).** If $m' \mid (7^P - 1)$, write $7^P = m' c + 1$. Then for every $k \ge 1$, $7^{k + P} = 7^k + (7^k c) m'$, so $\lfloor 7^{k+P} / m' \rfloor = \lfloor 7^k / m' \rfloor + 7^k c$. Because $k \ge 1$ implies $7 \mid 7^k c$, reducing modulo $7$ gives $d_{k + P}(m') = d_k(m')$ immediately from $K = 1$.
3. **Converse Periodicity via $\mathbb{Z}$-Boundedness Cancellation (`dvd_seven_pow_sub_one_of_eventualPeriod`).** Suppose $d_{k + P}(m') = d_k(m')$ for all $k \ge K$ ($K, P \ge 1$). Then $B_s := B(m', K + sP, P)$ equals a constant $B = B(m', K, P) < Q := 7^P$ for every $s \ge 0$, and $r_s := 7^{K + sP} \bmod m' < m'$ satisfies $Q r_s = m' B + r_{s + 1}$. Setting $\Delta := (Q - 1) r_0 - m' B \in \mathbb{Z}$, induction on $s \ge 0$ gives:
   $$Q^s \Delta \;=\; (Q - 1) r_s - m' B \qquad (\forall s \ge 0),$$
   since $Q\bigl((Q - 1) r_s - m' B\bigr) - \bigl((Q - 1) r_{s+1} - m' B\bigr) = (Q - 1)(Q r_s - m' B - r_{s+1}) = 0$. At $s = m' + 1$, $Q > 1$ implies $m' < Q^{m'}$ and hence $m' Q < Q^{m' + 1}$. Because $0 \le r_{m'+1} < m'$ and $0 \le B < Q$, the right-hand side satisfies
   $$-Q^{m' + 1} \;<\; -m' Q \;<\; (Q - 1) r_{m' + 1} - m' B \;<\; m' Q \;<\; Q^{m' + 1},$$
   forcing $\Delta = 0$. Thus $(7^P - 1)(7^K \bmod m') = m' B$ in $\mathbb{N}$, whence $m' \mid (7^P - 1) \cdot 7^K$. By $\gcd(m', 7^K) = 1$, Euclid's lemma yields $m' \mid (7^P - 1)$.

Combining (1)–(3), for $n \ge 1$ and $\gcd(m', 7) = 1$, $\mathrm{HasBase7RecipPeriodLen}(m', n) \iff m' \in S(n)$ (`hasBase7RecipPeriodLen_iff_primitiveDivisor_of_coprime`). Since $d_{\min}(n) \in S(n)$ is coprime to $7$, $m = d_{\min}(n)$ achieves period length $n$; conversely, any $m = 7^v m'$ with period length $n$ has $m' \in S(n)$ and therefore $d_{\min}(n) \le m' \le 7^v m' = m$. Taking $\inf$ establishes **Half 1** (`base7LeastPeriodDenominator_eq_minPrimDiv7`):
$$\mathrm{base7LeastPeriodDenominator}(n) \;=\; d_{\min}(n) \qquad (\forall n \ge 1).$$

---

## 4. Finite-Field Irreducible Polynomial Orders (Steps 3–5)

### 4.1 Step 3 — Forward Inclusion via `AdjoinRoot` and Frobenius Root-Counting

> **Proposition 4.1 (`polyOrder_mem_primitiveDivisors7`).** *Let $n \ge 2$ and let $f \in (\mathrm{ZMod}\ 7)[X]$ be monic and irreducible with $f.\mathrm{natDegree} = n$. Then $\operatorname{polyOrder}(f) \in S(n)$.*

*Proof.* Since $\mathrm{ZMod}\ 7$ is a field (`Fact (Nat.Prime 7)`) and $f$ is irreducible, the quotient ring $K := \mathrm{AdjoinRoot}\ f = (\mathrm{ZMod}\ 7)[X]/(f)$ is a field (`AdjoinRoot.instField`) of characteristic $7$. By `AdjoinRoot.powerBasis`, $1, \alpha, \dots, \alpha^{n-1}$ (where $\alpha := \mathrm{AdjoinRoot.root}\ f$) is a $(\mathrm{ZMod}\ 7)$-basis of $K$, giving a linear equivalence $K \simeq (\mathrm{Fin}\ n \to \mathrm{ZMod}\ 7)$ and hence $|K| = 7^n$ and $|K^\times| = 7^n - 1$.

1. **Nonvanishing and unit order:** For any $e \in \mathbb{N}$, `AdjoinRoot.mk_eq_zero` gives $f \mid (X^e - 1) \iff \alpha^e - 1 = 0 \iff \alpha^e = 1$. If $\alpha = 0$, then $f \mid X$, forcing $\deg f \le 1 < 2 \le n$, a contradiction. Thus $\alpha$ lifts to a unit $u \in K^\times$ of finite multiplicative order $d := \operatorname{orderOf}(\alpha) = \operatorname{orderOf}(u) \ge 1$. By Lagrange's theorem (`orderOf_dvd_natCard`), $d \mid |K^\times| = 7^n - 1$. Moreover, $\alpha^e = 1 \iff d \mid e$, so $d \in \{e \ge 1 : f \mid (X^e - 1)\}$ is the least element of that set, i.e., $\operatorname{polyOrder}(f) = d$.
2. **Strict bound $d > 1$:** If $d = 1$, then $\alpha = 1$, so $f \mid (X - 1)$, forcing $\deg f \le 1 < n$, a contradiction.
3. **Primitive divisibility via $k$-fold Frobenius root counting:** Suppose $d \mid (7^k - 1)$ for some $1 \le k < n$. Then $\alpha^{7^k - 1} = 1$, and multiplying by $\alpha$ yields $\alpha^{7^k} = \alpha$. For every polynomial $g \in (\mathrm{ZMod}\ 7)[X]$, structural induction on $g$ (`Polynomial.induction_on`) shows $(\mathrm{mk}\ f\ g)^{7^k} = \mathrm{mk}\ f\ g$: scalars $c \in \mathrm{ZMod}\ 7$ satisfy $c^{7^k} = c$ (`ZMod.pow_card_pow`), sums satisfy $(x + y)^{7^k} = x^{7^k} + y^{7^k}$ in characteristic $7$ (`add_pow_char_pow`), and monomial multiplication by $X$ maps to multiplication by $\alpha$ (`(x\alpha)^{7^k} = x^{7^k}\alpha^{7^k} = x\alpha$). Because $\mathrm{mk}\ f$ is surjective (`AdjoinRoot.induction_on`), **every** element $z \in K$ satisfies $z^{7^k} = z$. Consequently, all $7^n$ elements of $K$ are roots of $P(Y) := Y^{7^k} - Y \in K[Y]$. Since $7^k \ge 7 > 1$, the coefficient of $Y^{7^k}$ in $P$ is $1 \ne 0$, so $P \ne 0$ and $\deg P \le 7^k$. By `Polynomial.card_roots'`, $7^n = |K| \le |P.\mathrm{roots}| \le \deg P \le 7^k$, contradicting $7^k < 7^n$ for $k < n$. Thus $d \in S(n)$. $\square$

### 4.2 Step 4 — Converse Realization via `GaloisField 7 n` and the Dimension Tower Law

> **Proposition 4.2 (`exists_irred_of_primitiveDivisor7`).** *Let $n \ge 2$ and $d \in S(n)$. There exists a monic irreducible polynomial $f \in (\mathrm{ZMod}\ 7)[X]$ with $f.\mathrm{natDegree} = n$, $f.\mathrm{coeff}\ 0 \ne 0$, and $\operatorname{polyOrder}(f) = d$.*

*Proof.* Let $E := \mathrm{GaloisField}\ 7\ n$, the splitting field of $X^{7^n} - X$ over $\mathrm{ZMod}\ 7$. For $n \ge 2$ ($n \ne 0$), `GaloisField.card` and `GaloisField.finrank` give $|E| = 7^n$ and $\dim_{\mathrm{ZMod}\ 7} E = n$, so $|E^\times| = 7^n - 1$.

1. **Constructing $\alpha \in E$ of exact multiplicative order $d$:** Since the finite group $E^\times$ of units of a field is cyclic (`IsCyclic.exists_ofOrder_eq_natCard`), choose a generator $g \in E^\times$ with $\operatorname{orderOf}(g) = 7^n - 1 > 0$. Because $d \mid (7^n - 1) = \operatorname{orderOf}(g)$, setting $u := g^{\operatorname{orderOf}(g)/d} \in E^\times$ and $\alpha := (u : E) \ne 0$ gives $\operatorname{orderOf}(\alpha) = \operatorname{orderOf}(u) = d$ (`orderOf_pow_orderOf_div`, `orderOf_units`).
2. **Minimal polynomial and polynomial order:** Because $E$ is finite-dimensional over $\mathrm{ZMod}\ 7$, $\alpha$ is integral over $\mathrm{ZMod}\ 7$ (`Algebra.IsIntegral.isIntegral`), so $f := \mathrm{minpoly}\ (\mathrm{ZMod}\ 7)\ \alpha$ is monic (`minpoly.monic`) and irreducible (`minpoly.irreducible`). For every $e \in \mathbb{N}$, `minpoly.dvd_iff` gives
   $$f \mid (X^e - 1) \;\iff\; \mathrm{aeval}\ \alpha\ (X^e - 1) = 0 \;\iff\; \alpha^e = 1 \;\iff\; d \mid e.$$
   Since $d > 1$, the least $e \ge 1$ divisible by $d$ is $d$ itself, proving $\operatorname{polyOrder}(f) = d$. Evaluating $X^d - 1 = f(X) q(X)$ at $0 \in \mathrm{ZMod}\ 7$ gives $-1 = f(0) q(0)$ (since $d > 1 \implies 0^d = 0$), so $f.\mathrm{coeff}\ 0 = f(0) \ne 0$.
3. **Exact degree $\deg f = n$ via intermediate-field tower law:** Let $F_\alpha := (\mathrm{ZMod}\ 7)\langle\alpha\rangle = \mathrm{IntermediateField.adjoin}\ (\mathrm{ZMod}\ 7)\ \{\alpha\} \subseteq E$, and set $k := f.\mathrm{natDegree} \ge 1$ (`minpoly.natDegree_pos`). By `IntermediateField.adjoin.finrank` and `Module.finrank_mul_finrank`,
   $$\dim_{\mathrm{ZMod}\ 7} F_\alpha = k, \qquad k \cdot \dim_{F_\alpha} E = \dim_{\mathrm{ZMod}\ 7} E = n,$$
   so $1 \le k \le n$ and $|F_\alpha| = 7^k$ (`FiniteField.pow_finrank_eq_natCard`), whence $|F_\alpha^\times| = 7^k - 1$. Since $\alpha \in F_\alpha \setminus \{0\}$ lifts to a unit $u_F \in F_\alpha^\times$ whose multiplicative order is preserved under the injective inclusion $F_\alpha \hookrightarrow E$ (`orderOf_injective`), Lagrange's theorem in $F_\alpha^\times$ yields $d = \operatorname{orderOf}(u_F) \mid (7^k - 1)$. Because $d \in S(n)$ forbids $d \mid (7^k - 1)$ for all $1 \le k < n$, we conclude $k = n$. $\square$

### 4.3 Step 5 — Synthesis and Base Calibration

Combining Propositions 4.1 and 4.2 shows that for every $n \ge 2$, the set of orders of monic degree-$n$ irreducible polynomials over $\mathbb{F}_7$ (`OEIS A212486` row $n$) equals $S(n)$ identically, so taking $\inf$ gives **Half 2** (`minIrredOrder_eq_minPrimDiv7`):
$$\mathrm{minIrredOrder}(n) \;=\; d_{\min}(n) \qquad (\forall n \ge 2).$$
Equating Half 1 and Half 2 proves Theorem 1.1 (`base7LeastPeriodDenominator_eq_minIrredOrder`) for all $n \ge 2$ with zero finite casework tail. At $n = 2$, $4 > 1$, $4 \mid 48 = 7^2 - 1$, and $4 \nmid 6 = 7^1 - 1$, while $d = 2, 3$ both divide $6$, proving $d_{\min}(2) = 4$ and establishing Theorem 1.2 (`base7LeastPeriodDenominator_two`).

---

## 5. Strength Delta, Scope, and Verification Record

### 5.1 Strength Delta and Open Questions ("What This Paper Does Not Show")

- **Strength Delta vs Source:** **`NONE`**. Theorems 1.1 and 1.2 establish R. J. Mathar's exact March 3, 2025 conjecture on `OEIS A381494` over its full sharp domain $n \ge 2$, formalizing both sequences directly from their primary OEIS `%N` specifications.
- **What This Paper Does *Not* Show:**
  1. *Prime vs prime-power vs composite bases:* Our proof exploits the fact that the radix $b = 7$ is prime, so $\mathrm{ZMod}\ 7$ is the prime field $\mathbb{F}_7$. For a prime power $b = p^r$ ($r \ge 2$, e.g. $b = 8$ in `A381493` or $b = 9$ in `A381370`), $\mathbb{F}_{p^r}$ is not $\mathbb{Z}/b\mathbb{Z}$ (`GaloisField p r` vs `ZMod (p^r)`), though both sequences still share the common primitive-divisor set of $b^n - 1$; for non-prime-power composite bases such as $b = 10$ (`OEIS A003060`), no finite field $\mathrm{GF}(10)$ exists at all, so the reciprocal-period sequence has no irreducible-polynomial counterpart.
  2. *Distribution of composite vs prime minima:* While Zsigmondy's theorem guarantees at least one *prime* primitive divisor of $7^n - 1$ for every $n \ge 3$ (`OEIS A379640(n) > 1`), the *minimal* primitive divisor $A_{381494}(n)$ is frequently composite (e.g., $n = 2, 3, 6, 8, 9, 18, 20, 21, \dots$), whenever a product of prime-power or lower-order factors beats the smallest Zsigmondy prime. Characterizing the asymptotic density of indices $n$ for which $A_{381494}(n)$ is prime (`A381494(n) = A379640(n)`) remains an open analytic number theory question.

### 5.2 Computational and Formal Verification Summary

1. **Independent First-Hand Recomputation (`recompute_s019.py`, `TOTAL_RECOMPUTE_FAILURES=0`):**
   - Verified `0` mismatches across all `51` printed terms of `A381494` ($n = 0..50$), all `47` printed terms of `A218358` ($n = 1..47$), and the full `125`-term b-file overlap $n = 2..126$ (`b381494.txt` vs `b218358.txt`).
   - Verified direct remainder-cycle base-$7$ digit period lengths across $m = 1..3500$ ($n = 0..12, 14, 15$), exhaustive Rabin-certified $\mathbb{F}_7[X]$ monic irreducible order sets for $n = 1..5$ (`4,087` irreducibles; `23,625` through $n = 6$ during scoping), multiplicative order $\operatorname{ord}_{a(n)}(7) = n$ across all `429` b-file rows $n = 2..430$ of `b218358.txt`, and `21` failures (`15` coprime) of $a(n) \mid \Phi_n(7)$ in $n = 2..50$ (`32` in $n = 2..80$).
2. **Lean 4 Kernel & Trust-Gate Audit (`SeamC/A381494.lean`):**
   - Clean-slate `rm -rf .lake/build && lake build`: exit `0`, `0` errors, `0` `sorry`s, `0` warnings on `SeamC.A381494`.
   - Fresh kernel replay `lake env leanchecker --fresh SeamC.A381494`: exit `0`.
   - `#print axioms` on `base7LeastPeriodDenominator_two`, `base7LeastPeriodDenominator_eq_minIrredOrder`, all `5` pinned definitions, and all `11` supporting public theorems: subsets of `[propext, Classical.choice, Quot.sound]` only.
   - Fidelity audit vs Step 0 staged contract (`6a3d01541fd77dfca7aeb2d2887e9937b9756aca`): `TOTAL_FIDELITY_DIFF_CHARS=0`.
   - Comment- and string-stripped lexical trust-escape screen across the repo import closure: `0` active hits on `sorry`, `admit`, `sorryAx`, `axiom`, `native_decide`, `ofReduceBool`, `implemented_by`, `unsafe`.
   - Non-vacuity computation boundary: because `base7LeastPeriodDenominator` and `minIrredOrder` are `sInf` over infinite sets (`noncomputable`), direct raw `rfl` on those symbols is blocked by `sInf`; we prove literal `rfl` on `base7RecipDigit` (`base7RecipDigit_literal_examples`), prove exact boundary theorems on the unrewritten pinned functions (`base7LeastPeriodDenominator_zero`, `sharp_guard_at_one`), and prove formal equivalence to the total `O(\sqrt{7^n - 1})` structural mirror `a381494Compute` (`base7LeastPeriodDenominator_eq_compute`, `minIrredOrder_eq_compute`), certifying `n = 2..10` (`oeis_spot_checks_2_to_10`) and the cyclotomic counterexamples $n = 3, 6$ (`refute_cyclotomic_divisor_shortcut`) via standard kernel `decide`.

---

## References

1. E. Friedman, Sequence `A381494` (Smallest number with reciprocal of period length $n$ in base $7$; conjecture in `%F` by R. J. Mathar, Mar. 3, 2025) in *The On-Line Encyclopedia of Integer Sequences* (`https://oeis.org/A381494`), Feb. 25, 2025 (rev. `#23`, Mar. 2, 2026); cf. `A381370`, `A381493`, `A379640`, `A003060`.
2. A. P. Heinz, Sequence `A218358` (Minimal order of degree-$n$ irreducible polynomials over $\mathrm{GF}(7)$) in *The On-Line Encyclopedia of Integer Sequences* (`https://oeis.org/A218358`), Oct. 27, 2012 (rev. `#17`, Feb. 16, 2025); cf. `A212486`, `A213224`, `A059889`.
3. M. Alekseyev, Table of $n, A_{218358}(n)$ for $n = 1..430$ (`https://oeis.org/A218358/b218358.txt`).
4. R. Israel, Table of $n, A_{381494}(n)$ for $n = 0..126$ (`https://oeis.org/A381494/b381494.txt`), Mar. 1, 2026.
5. R. Lidl and H. Niederreiter, *Finite Fields*, 2nd ed., Encyclopedia of Mathematics and its Applications, vol. 20, Cambridge University Press, 1997 (Def. 3.2, Thm. 2.47, Thm. 3.3, Thm. 3.5, and Table C, pp. 560–562).
6. J. Brillhart, D. H. Lehmer, J. L. Selfridge, B. Tuckerman, and S. S. Wagstaff, Jr., *Factorizations of $b^n \pm 1$, $b = 2, 3, 5, 6, 7, 10, 11, 12$ up to High Powers*, Contemporary Mathematics, vol. 22, 2nd ed., American Mathematical Society, 1985.
7. K. Zsigmondy, "Zur Theorie der Potenzreste," *Monatshefte für Mathematik und Physik*, vol. 3, pp. 265–284, 1892.
8. The mathlib Community, "The Lean Mathematical Library," in *Proc. 9th ACM SIGPLAN Int. Conf. Certified Programs and Proofs (CPP)*, 2020 (`leanprover-community/mathlib4`, rev. `d13f23b723b8a846827a245b89c10fc7d3f11612`).
