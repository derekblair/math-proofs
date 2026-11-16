# Strict Prefix Records in the Numerators of the Dirichlet Square Root of the Unitary Divisor Function: Proof and Lean 4 Formalization of Karttunen's OEIS A317933 Conjecture

**Preprint Draft (`PAPER-C047.md`) — 2026-11-16**  
**Repository / Module:** `derekblair/math-proofs` (`Mathproofs/A317933Records.lean`, `namespace Mathproofs.A317933Records`)  
**Toolchain & Mathlib Pin:** `leanprover/lean4:v4.34.1` (`commit 5045d0056413266e57c625dcd7c365b10e377c52`), Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`  
**Target Contract:** `PIN-C047.md` v1 (`SHA-256: c13956fdd67544a869909bd6e953e39fd9ef3ab222882982881a52aab50f9a31`, `delta_vs_source: NONE`)

---

## Abstract

Let $u(n) = 2^{\omega(n)}$ (`OEIS A034444`, the number of unitary divisors of $n \ge 1$, where $\omega(n)$ counts distinct prime factors of $n$), let $f : \mathbb{N} \to \mathbb{Q}$ be the unique arithmetic function satisfying $f(1) = 1$ and the Dirichlet self-convolution equation $(f * f)(n) = \sum_{d \mid n} f(d) f(n/d) = u(n)$ for all $n \ge 1$ (`f 0 = 0`), and let $a(n) = \operatorname{num}(f(n)) \in \mathbb{Z}$ (`OEIS A317933`) denote the reduced numerator of $f(n)$. On August 12, 2018, Antti Karttunen observed empirically in `OEIS A317933` (`%C` line 13) that *"Records seem to be A001790, occurring at A000302 (apart from 4),"* where $\operatorname{A001790}(k) = \operatorname{num}\!\bigl(\binom{2k}{k} / 4^k\bigr) = \binom{2k}{k} / 2^{s_2(k)}$ is the odd part of the central binomial coefficient ($s_2(k)$ denoting the binary digit sum of $k$) and $\operatorname{A000302}(k) = 4^k$.

We prove Karttunen's conjecture unconditionally across all $n \ge 1$ directly from the Dirichlet convolution equation $f * f = u$, without assuming any external closed form and without power-series square roots or real-analytic estimates. First, a finite sum-reversal proof of $\sum_{i=0}^m \binom{2i}{i}\binom{2(m-i)}{m-i} = 4^m$ and parity-split prime-power evaluation establish existence, uniqueness, and multiplicativity of $f$, giving $f(p^e) = \binom{2\lfloor e/2 \rfloor}{\lfloor e/2 \rfloor} / 4^{\lfloor e/2 \rfloor}$. Second, Legendre's 2-adic valuation formula proves $v_2\bigl(\binom{2m}{m}\bigr) = s_2(m)$, so $\operatorname{A001790}(m)$ is odd and no cross-prime numerator-denominator cancellation occurs in $f(n) = \prod_{p^e \parallel n} f(p^e)$, yielding both $\operatorname{num}\!\bigl(\binom{2k}{k}/4^k\bigr) = \operatorname{A001790}(k)$ and Amiram Eldar's November 1, 2026 formula $a(p^e) = \operatorname{A001790}(\lfloor e/2 \rfloor)$ from first principles. Third, replacing a naive crude bound $\operatorname{A001790}(m_1) \le \binom{2m_1}{m_1}/2$—which we prove false at $k = 31, m_1 = 29, m_2 = 1$—we establish exact supermultiplicativity $\operatorname{A001790}(x)\operatorname{A001790}(y) \le \operatorname{A001790}(x + y)$ via Vandermonde's identity and binary digit-sum subadditivity, paired with the prime-square bound $4^{M(n)} \le n$ for $M(n) = \sum_{p \mid n} \lfloor v_p(n)/2 \rfloor$. This closes both directions of the strict prefix-record characterization: $\operatorname{isStrictRecord}(a, n)$ holds if and only if $n = 1$ or $n = 4^k$ with $k \ge 2$ (suppressing the tied value $a(4) = \operatorname{A001790}(1) = 1 = a(1)$), with values $a(1) = \operatorname{A001790}(0)$ and $a(4^k) = \operatorname{A001790}(k)$ for $k \ge 2$. Every step, refutation witness, computable mirror, and non-vacuity check is formalized and machine-verified in Lean 4 (`v4.34.1` / Mathlib `d13f23b7...`) with zero `sorry`s, zero custom axioms, and zero trust escapes.

---

## 1. Introduction and Primary-Source Context

### 1.1 Rational Dirichlet Square Roots and `OEIS A317933`

In the ring of rational-valued arithmetic functions $(\mathcal{A}(\mathbb{Q}), +, *)$ equipped with Dirichlet convolution
$$(g * h)(n) := \sum_{d_1 d_2 = n} g(d_1)\,h(d_2) \qquad (n \ge 1),$$
every function $u \in \mathcal{A}(\mathbb{Q})$ with $u(1) = 1$ admits a unique normalized Dirichlet square root $f \in \mathcal{A}(\mathbb{Q})$ satisfying $f(1) = 1$ and $f * f = u$, determined recursively for $n \ge 2$ by
$$f(n) = \frac{1}{2}\Biggl(u(n) - \sum_{\substack{d \mid n \\ 1 < d < n}} f(d)\,f(n/d)\Biggr).$$
When $u$ is the constant-one function $\zeta(n) = 1$ (corresponding to the formal Dirichlet series $\zeta(s)^{1/2}$), the reduced numerators and denominators of $f(n)$ form the classical sequences `OEIS A046643` and `OEIS A046644`.

On August 12, 2018, Antti Karttunen introduced `OEIS A317933` (and denominator companion `OEIS A317934`) by taking $u(n) = \operatorname{A034444}(n) = 2^{\omega(n)}$, the number of unitary divisors $d \mid n$ with $\gcd(d, n/d) = 1$ [1]. Karttunen recorded two structural questions in the comments of `OEIS A317933`:
1. whether $a(n) = \operatorname{num}(f(n))$ is nonnegative for all $n \ge 1$ (`%C` line 12, answered affirmatively via the local formula added by Amiram Eldar on November 1, 2026); and
2. the record-value and record-position conjecture (`%C` line 13 [1]):

> **Conjecture (Karttunen, August 12, 2018; `OEIS A317933`, `%C` line 13).** *"Records seem to be A001790, occurring at A000302 (apart from 4)."*

Here `OEIS A000302` is the sequence of powers of four $4^k$ ($k \ge 0$: $1, 4, 16, 64, 256, 1024, \dots$), and `OEIS A001790` ($k \ge 0$: $1, 1, 3, 5, 35, 63, 231, 429, 6435, \dots$) is the sequence of reduced numerators of $\binom{2k}{k} / 4^k$, equivalently the odd part $\binom{2k}{k} / 2^{s_2(k)}$ of the central binomial coefficient $B_k := \binom{2k}{k}$. On November 1, 2026 (`#21`), Amiram Eldar added the multiplicative formula $a(p^e) = \operatorname{A001790}(\lfloor e/2 \rfloor)$ on `%F` line 18 without citing a proof, while `%C` line 13 remained open (`"seem"`).

### 1.2 Main Results

Starting exclusively from the Dirichlet convolution specification $f(1) = 1 \wedge f * f = u$ (`PIN-C047.md` v1), we prove Karttunen's conjecture in full generality together with all foundational bridges:

- **Theorem 1.1 (Existence and Uniqueness — `Mathproofs.A317933Records.f_existsUnique`).** *There exists a unique arithmetic function $f : \operatorname{ArithmeticFunction} \mathbb{Q}$ satisfying $f(1) = 1$ and $f * f = u$. Moreover, $f$ coincides across all $n \in \mathbb{N}$ with the explicit computable multiplicative function*
  $$g(n) = \prod_{p \in n.\mathrm{primeFactors}} \frac{\binom{2\lfloor v_p(n)/2 \rfloor}{\lfloor v_p(n)/2 \rfloor}}{4^{\lfloor v_p(n)/2 \rfloor}} \qquad (n \ge 1,\ g(0) = 0).$$
- **Theorem 1.2 (`A001790` Rational-Numerator Equivalence — `Mathproofs.A317933Records.A001790_eq_num`).** *For every $k \in \mathbb{N}$, the reduced rational numerator of $\binom{2k}{k} / 4^k$ equals $\operatorname{A001790}(k) := \binom{2k}{k} / 2^{s_2(k)}$, where $s_2(k) = (\mathrm{Nat.digits}\ 2\ k).\mathrm{sum}$ is the base-$2$ digit sum of $k$.*
- **Theorem 1.3 (Multiplicative Numerator Formula — `a_eq_prod_A001790`, `a_prime_pow`).** *For every $n \ge 1$, zero cross-prime cancellation occurs in the rational product for $f(n)$, so*
  $$a(n) = \prod_{p \in n.\mathrm{primeFactors}} \operatorname{A001790}\!\bigl(\lfloor v_p(n)/2 \rfloor\bigr) \ge 1,$$
  *and in particular $a(p^e) = \operatorname{A001790}(\lfloor e/2 \rfloor)$ for every prime $p$ and exponent $e \ge 0$.*
- **Theorem 1.4 (Main Record Characterization — `Mathproofs.A317933Records.a317933_records`).** *Let $\operatorname{isStrictRecord}(\mathrm{seq}, n) :\Leftrightarrow 1 \le n \wedge \forall m,\ 1 \le m < n \implies \mathrm{seq}(m) < \mathrm{seq}(n)$. Then:*
  1. *For all $n \in \mathbb{N}$, $\operatorname{isStrictRecord}(a, n) \iff \bigl(n = 1 \vee \exists k \ge 2,\ n = 4^k\bigr)$.*
  2. *$a(1) = \operatorname{A001790}(0) = 1$, and for all $k \ge 2$, $a(4^k) = \operatorname{A001790}(k)$.*

---

## 2. Formal Specification and Convention Audit

In Lean 4 (`Mathproofs/A317933Records.lean`, `namespace Mathproofs.A317933Records`), the five pinned definitions of `PIN-C047.md` v1 are:

```lean
def u : ArithmeticFunction ℚ :=
  ⟨fun n => if n = 0 then 0 else (2 : ℚ) ^ n.primeFactors.card, by simp⟩

noncomputable def f : ArithmeticFunction ℚ :=
  open Classical in
  if h : ∃ g : ArithmeticFunction ℚ, g 1 = 1 ∧ g * g = u then Classical.choose h else 0

noncomputable def a (n : ℕ) : ℤ := (f n).num

def A001790 (k : ℕ) : ℕ := Nat.choose (2 * k) k / 2 ^ (Nat.digits 2 k).sum

def isStrictRecord (seq : ℕ → ℤ) (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ m : ℕ, 1 ≤ m → m < n → seq m < seq n
```

Four design and fidelity invariants govern this specification (`delta_vs_source: NONE`):

1. **First-principles definition of $f$ (`f_existsUnique`).** Rather than defining $a(n)$ from Eldar's unproved November 1, 2026 `%F` formula, $f$ is selected directly from $\{g : \operatorname{ArithmeticFunction} \mathbb{Q} \mid g(1) = 1 \wedge g * g = u\}$ via `Classical.choose`. Proving `f_existsUnique` certifies that the `if h : ...` branch is inhabited and uniquely determined, matching Karttunen's `%N` description and `%F` line 16 recurrence (`f(1) = 1` selects $+f$ over $-f$).
2. **Strict 1-based prefix records forced by the fifteen leading `1`s and `"apart from 4"`.** `OEIS A317933` has offset `%O A317933 1,16` and begins with fifteen consecutive ones (`a(1) = a(2) = \dots = a(15) = 1`, proved algebraically in `a_eq_one_of_lt_sixteen`), followed by $a(16) = 3$. Under weak prefix maxima ($\le$), every integer $n \in \{1, 2, \dots, 15\}$ would be a record, contradicting *"occurring at A000302 (apart from 4)"*. Under strict 1-based prefix maxima (`isStrictRecord`), $n = 1$ ($a(1) = 1 = \operatorname{A001790}(0)$) is the initial record, $n = 4 = 4^1$ has $a(4) = \operatorname{A001790}(1) = 1 = a(1)$ and is suppressed by the tie (`guard_exclusions`), $n = 0$ is excluded on both sides of the equivalence (`1 ≤ 0` vs. $4^k \ge 1$), and the subsequent records occur at $4^k$ ($k \ge 2$) with values $\operatorname{A001790}(k)$.
3. **Mathlib `v4.34.1` binary Hamming weight (`Trap #2`: non-existence of `Nat.popCount`).** An initial triage sketch wrote `Nat.popCount k`, which **does not exist** in Lean 4 `v4.34.1` core, Batteries, or Mathlib (only fixed-width `BitVec.popcount` exists). Mathlib's canonical base-$2$ Hamming weight in Legendre's formula `Nat.sub_one_mul_factorization_factorial` (`Mathlib.Data.Nat.Choose.Factorization`) is `(Nat.digits 2 k).sum` (`Mathlib.Data.Nat.Digits.Defs`). Pinning Theorem 1.2 (`A001790_eq_num`) certifies inside Lean's kernel that `A001790 k` equals the reduced rational numerator of $\binom{2k}{k}/4^k$ (`OEIS A001790`, `%F` line 61).
4. **Canonical reduced rational numerator (`Rat.num`).** For $q \in \mathbb{Q}$, `q.num : ℤ` and `q.den : ℕ` satisfy `0 < q.den`, `Nat.Coprime q.num.natAbs q.den`, and $q = q.\mathrm{num} / q.\mathrm{den}$, matching PARI `numerator(q)` and Mathematica `Numerator[q]`.

---

## 3. Why Naive Crude-Bound Sketches Fail (`Trap #1` at $k = 31$)

Before scoping (`SCOPING-C047.md` §2.1), a preliminary heuristic (`TRIAGE-SEAMB.md` §3.4) proposed bounding competing prime-square products $m = 2^{2 m_1} 3^{2 m_2} \cdots < 4^k$ by:
1. replacing $\operatorname{A001790}(m_1) = \binom{2m_1}{m_1} / 2^{s_2(m_1)}$ with the crude upper bound $\binom{2m_1}{m_1} / 2$ (using $s_2(m_1) \ge 1$ for $m_1 \ge 1$); and
2. arguing from $4^{m_1} \cdot 9^{m_2} < 4^k$, i.e., $m_1 + (\log_4 9)\,m_2 \approx m_1 + 1.585\,m_2 < k$, that the exponential slack $4^{k - m_1}$ absorbs the denominator penalty $2^{s_2(k)}$ in $\operatorname{A001790}(k) = \binom{2k}{k} / 2^{s_2(k)}$.

**This literal intermediate inequality is false.** Consider $k = 31 = 2^5 - 1$, $m_1 = 29$, and $m_2 = 1$ (corresponding to $n = 4^{29} \cdot 9^1$):
- The domain condition holds: $4^{29} \cdot 9 < 4^{29} \cdot 16 = 4^{31}$.
- Since $29 = (11101)_2$ has $s_2(29) = 4$ while $31 = (11111)_2$ has $s_2(31) = 5$, discarding $2^{s_2(29) - 1} = 2^3 = 8$ in the crude bound $\binom{58}{29}/2$ forfeits a factor of $8$, whereas stepping two central binomial indices from $29$ to $31$ gains less than $4^2 = 16$ relative to $2^{s_2(31)} = 32$:
  $$\frac{\binom{58}{29}}{2} \cdot \operatorname{A001790}(1) = 15{,}033{,}633{,}249{,}770{,}520 \;>\; 14{,}544{,}636{,}039{,}226{,}909 = \frac{\binom{62}{31}}{32} = \operatorname{A001790}(31).$$

We certify this refutation directly inside Lean's kernel (`triage_step2_bound_false_at_31`). By contrast, retaining the exact 2-adic valuation $2^{s_2(m_1)}$ via supermultiplicativity (Lemma 5.2 below) gives
$$\operatorname{A001790}(29) \cdot \operatorname{A001790}(1) = 1{,}879{,}204{,}156{,}221{,}315 \;\le\; \operatorname{A001790}(30) = 7{,}391{,}536{,}347{,}803{,}839 \;<\; \operatorname{A001790}(31),$$
eliminating both the false inequality and any dependence on real-valued `Real.log` bounds.

---

## 4. Dirichlet Square-Root Structure and the `Rat.num` Bridge (Steps D1–D4)

Write $B_m := \binom{2m}{m}$ (`Nat.centralBinom m`) and $s_2(m) := (\mathrm{Nat.digits}\ 2\ m).\mathrm{sum}$.

### 4.1 Step D1: Uniqueness via Strong Induction (`dirichlet_sqrt_unique`)

**Lemma 4.1.** *If $h_1, h_2 \in \mathcal{A}(\mathbb{Q})$ satisfy $h_i(1) = 1$ and $h_i * h_i = u$, then $h_1 = h_2$.*

*Proof.* We induct strongly on $n \in \mathbb{N}$. At $n = 0$, $h_1(0) = 0 = h_2(0)$ by definition of `ArithmeticFunction`; at $n = 1$, $h_1(1) = 1 = h_2(1)$. For $n \ge 2$, the pairs $(1, n)$ and $(n, 1)$ are distinct elements of `Nat.divisorsAntidiagonal n`, and every remaining pair $(d_1, d_2) \in \mathrm{divisorsAntidiagonal}(n) \setminus \{(1, n), (n, 1)\}$ satisfies $d_1 d_2 = n$ with $1 < d_1 < n$ and $1 < d_2 < n$. Expanding $(h_i * h_i)(n)$ (`dirichlet_sqrt_apply_ge_two`) gives
$$u(n) = 2 h_i(n) + \sum_{\substack{d_1 d_2 = n \\ (d_1, d_2) \notin \{(1, n), (n, 1)\}}} h_i(d_1)\,h_i(d_2).$$
By the strong induction hypothesis on $d_1, d_2 < n$, the interior sums for $h_1$ and $h_2$ are equal, so $2 h_1(n) = 2 h_2(n)$ in $\mathbb{Q}$, whence $h_1(n) = h_2(n)$. $\square$

### 4.2 Step D2: Power-Series-Free Central-Binomial Convolution and Multiplicative Witness `g`

Heuristically, on a prime power $p^e$, $u(1) = 1$ and $u(p^e) = 2$ ($e \ge 1$) have ordinary generating series
$$\sum_{e \ge 0} u(p^e) X^e = 1 + \frac{2X}{1 - X} = \frac{1 + X}{1 - X} = \left(\frac{1 + X}{\sqrt{1 - X^2}}\right)^{\!2} = \left(\sum_{e \ge 0} \frac{B_{\lfloor e/2 \rfloor}}{4^{\lfloor e/2 \rfloor}} X^e\right)^{\!2}.$$
Rather than importing formal power-series fractional exponents into Lean, we prove the underlying finite convolution directly in $\mathbb{N}$:

**Lemma 4.2 (`centralBinom_conv`).** *For every $m \in \mathbb{N}$, $\operatorname{cbConv}(m) := \sum_{i=0}^m B_i B_{m-i} = 4^m$.*

*Proof.* At $m = 0$, $B_0^2 = 1 = 4^0$. For the inductive step $m \to m + 1$, reversing $k \mapsto m + 1 - k$ (`Finset.sum_range_reflect`) in $\sum_{k=0}^{m+1} k B_k B_{m+1-k}$ and adding the sum to its reversal yields
$$(m + 1)\operatorname{cbConv}(m + 1) = \sum_{k=0}^{m+1} \bigl((m + 1 - k) + k\bigr) B_k B_{m+1-k} = 2 \sum_{k=0}^{m+1} k B_k B_{m+1-k}.$$
Dropping the $k = 0$ zero term (`Finset.sum_range_succ'`), reindexing $k = j + 1$ ($0 \le j \le m$), and applying $(j + 1) B_{j+1} = 2(2j + 1) B_j$ (`Nat.succ_mul_centralBinom_succ`) gives
$$\sum_{k=0}^{m+1} k B_k B_{m+1-k} = 2 \sum_{j=0}^m (2j + 1) B_j B_{m-j}.$$
Reversing $j \mapsto m - j$ once more gives $2 \sum_{j=0}^m (2j + 1) B_j B_{m-j} = \sum_{j=0}^m \bigl((2(m - j) + 1) + (2j + 1)\bigr) B_j B_{m-j} = 2(m + 1)\operatorname{cbConv}(m)$. Combining these identities yields $(m + 1)\operatorname{cbConv}(m + 1) = (m + 1)\bigl(4\operatorname{cbConv}(m)\bigr)$; canceling $m + 1 > 0$ gives $\operatorname{cbConv}(m + 1) = 4 \cdot 4^m = 4^{m+1}$. $\square$

**Lemma 4.3 (`g_isMultiplicative`, `g_mul_self_eq_u`, `g_eq_f`).** *Define $\ell(e) := B_{\lfloor e/2 \rfloor} / 4^{\lfloor e/2 \rfloor} \in \mathbb{Q}$ and $g(n) := \prod_{p \in n.\mathrm{primeFactors}} \ell(v_p(n))$ for $n \ge 1$ ($g(0) = 0$). Then $g$ is multiplicative, $g(1) = 1$, $g * g = u$, and $g = f$.*

*Proof.* For coprime $x, y \ge 1$, $(xy).\mathrm{primeFactors} = x.\mathrm{primeFactors} \sqcup y.\mathrm{primeFactors}$ and $v_p(xy)$ restricts to $v_p(x)$ on $x.\mathrm{primeFactors}$ and $v_p(y)$ on $y.\mathrm{primeFactors}$, proving `g.IsMultiplicative` (and similarly `u.IsMultiplicative`). Thus $g * g$ is multiplicative (`IsMultiplicative.mul`), so by `IsMultiplicative.eq_iff_eq_on_prime_powers` it suffices to check $(g * g)(p^e) = u(p^e)$ for prime $p$ and $e \ge 0$. At $e = 0$, both equal $1$. For $e \ge 1$, $u(p^e) = 2$, while `Nat.sum_divisorsAntidiagonal` and `Nat.sum_divisors_prime_pow` reduce $(g * g)(p^e)$ to $\sum_{j=0}^e \ell(j)\ell(e - j)$ (`localFactor_conv_eq_two`), paired via $\sum_{j=0}^{2m+1} h(j) = \sum_{i=0}^m \bigl(h(2i) + h(2i+1)\bigr)$ (`sum_range_pair`):
- If $e = 2m + 1$, both $j = 2i$ ($e - j = 2(m - i) + 1$) and $j = 2i + 1$ ($e - j = 2(m - i)$) contribute $\frac{B_i}{4^i}\frac{B_{m-i}}{4^{m-i}}$, summing by Lemma 4.2 to $2 \cdot \frac{\operatorname{cbConv}(m)}{4^m} = 2$.
- If $e = 2(m + 1)$, the even indices $j = 2i$ ($0 \le i \le m + 1$) sum to $\frac{\operatorname{cbConv}(m+1)}{4^{m+1}} = 1$ and the odd indices $j = 2i + 1$ ($0 \le i \le m$, $e - j = 2(m - i) + 1$) sum to $\frac{\operatorname{cbConv}(m)}{4^m} = 1$, totaling $1 + 1 = 2$.

Thus $g(1) = 1 \wedge g * g = u$, witnessing existence in `def f`, and Lemma 4.1 gives $g = f$ (`f_existsUnique`). $\square$

### 4.3 Steps D3–D4: 2-adic Valuation of $B_m$ and the `Rat.num` No-Cancellation Bridge

**Lemma 4.4 (`centralBinom_factorization_two`, `A001790_coprime_two`).** *For every $m \in \mathbb{N}$, $v_2(B_m) = s_2(m)$, $B_m = 2^{s_2(m)} \operatorname{A001790}(m)$, and $\gcd(\operatorname{A001790}(m), 2) = 1$.*

*Proof.* By `Nat.digit_sum_le`, $s_2(n) \le n$, so Mathlib's Legendre formula `Nat.sub_one_mul_factorization_factorial Nat.prime_two` (`v_2(n!) = n - s_2(n)`) rearranges without truncated-subtraction loss to $v_2(n!) + s_2(n) = n$ (`fact_two_add_s2`). Also $s_2(2m) = s_2(m)$ (`Nat.digits_base_mul` for $m > 0$). Applying $v_2$ to $B_m \cdot m! \cdot m! = (2m)!$ gives
$$v_2(B_m) + 2(m - s_2(m)) = 2m - s_2(2m) = 2m - s_2(m) \implies v_2(B_m) = s_2(m).$$
Hence $2^{s_2(m)} \mid B_m$, $2^{s_2(m)} \operatorname{A001790}(m) = B_m$, and $v_2(\operatorname{A001790}(m)) = v_2(B_m) - s_2(m) = 0$, so $2 \nmid \operatorname{A001790}(m)$ (`A001790_odd`). $\square$

**Proof of Theorems 1.2 and 1.3 (`A001790_eq_num`, `a_eq_prod_A001790`, `a_prime_pow`).** Since $s_2(m) \le m \le 2m$, Lemma 4.4 gives in $\mathbb{Q}$:
$$\ell(e) = \frac{B_m}{4^m} = \frac{2^{s_2(m)} \operatorname{A001790}(m)}{2^{s_2(m)} \cdot 2^{2m - s_2(m)}} = \frac{\operatorname{A001790}(m)}{2^{2m - s_2(m)}} \qquad (m := \lfloor e/2 \rfloor).$$
For any $N, d \in \mathbb{N}$ with $\gcd(N, 2) = 1$, $\gcd(N, 2^d) = 1$ (`Nat.Coprime.pow_right`) and $2^d > 0$, so `Rat.num_div_eq_of_coprime` yields $\operatorname{num}(N / 2^d) = N$ (`num_nat_div_two_pow`).
- Applying this to a single factor $\ell(2k) = B_k / 4^k$ immediately proves Theorem 1.2 (`A001790_eq_num`).
- For any $n \ge 1$, writing $m_p := \lfloor v_p(n)/2 \rfloor$, Lemma 4.3 and `Finset.prod_div_distrib` give
  $$f(n) = g(n) = \frac{\prod_{p \in n.\mathrm{primeFactors}} \operatorname{A001790}(m_p)}{2^{\sum_{p \in n.\mathrm{primeFactors}} (2 m_p - s_2(m_p))}}.$$
  Because each factor $\operatorname{A001790}(m_p)$ is coprime to $2$, their finite product $N(n) = \prod_p \operatorname{A001790}(m_p)$ is also coprime to $2$ (`Nat.Coprime.prod_left`)—so **zero cross-prime cancellation occurs** between any prime's numerator and another prime's power-of-$2$ denominator. Applying `num_nat_div_two_pow` yields $a(n) = N(n)$ (`a_eq_prod_A001790`), and specializing to $n = p^e$ yields $a(p^e) = \operatorname{A001790}(\lfloor e/2 \rfloor)$ (`a_prime_pow`). $\square$

---

## 5. Exact Supermultiplicativity, Dominance at $4^k$, and Proof of Theorem 1.4 (Steps D5–D8)

### 5.1 Steps D5–D6: Digit-Sum Subadditivity, Monotonicity, and Supermultiplicativity

**Lemma 5.1 (`s2_add_le`, `A001790_strictMono_from_one`, `A001790_mono`).** *For all $x, y \in \mathbb{N}$, $s_2(x + y) \le s_2(x) + s_2(y)$. Moreover, $\operatorname{A001790}(0) = \operatorname{A001790}(1) = 1$ and $\operatorname{A001790}(k) < \operatorname{A001790}(k + 1)$ for all $k \ge 1$.*

*Proof.* Applying $v_2$ to $\binom{x+y}{x} x!\,y! = (x + y)!$ gives $v_2\bigl(\binom{x+y}{x}\bigr) + (x - s_2(x)) + (y - s_2(y)) = x + y - s_2(x + y)$, whence $s_2(x + y) = s_2(x) + s_2(y) - v_2\bigl(\binom{x+y}{x}\bigr) \le s_2(x) + s_2(y)$. In particular, $s_2(k + 1) \le s_2(k) + 1$, so $2^{s_2(k+1)} \le 2 \cdot 2^{s_2(k)}$. Substituting $B_j = 2^{s_2(j)} \operatorname{A001790}(j)$ into $(k + 1) B_{k+1} = 2(2k + 1) B_k$ for $k \ge 1$ (`k + 1 < 2k + 1`, $\operatorname{A001790}(k) \ge 1$) yields
$$(k + 1) 2^{s_2(k+1)} \operatorname{A001790}(k) < (2k + 1) 2^{s_2(k+1)} \operatorname{A001790}(k) \le (2k + 1)(2 \cdot 2^{s_2(k)}) \operatorname{A001790}(k) = (k + 1) 2^{s_2(k+1)} \operatorname{A001790}(k + 1).$$
Canceling $(k + 1) 2^{s_2(k+1)} > 0$ gives $\operatorname{A001790}(k) < \operatorname{A001790}(k + 1)$. $\square$

**Lemma 5.2 (`A001790_supermult`, `prod_A001790_le`).** *For all $x, y \in \mathbb{N}$,*
$$\operatorname{A001790}(x) \cdot \operatorname{A001790}(y) \le \operatorname{A001790}(x + y),$$
*and for any finite family $(w_i)_{i \in I}$ in $\mathbb{N}$, $\prod_{i \in I} \operatorname{A001790}(w_i) \le \operatorname{A001790}\bigl(\sum_{i \in I} w_i\bigr)$.*

*Proof.* By Vandermonde's identity (`Nat.add_choose_eq`),
$$B_{x+y} = \binom{2x + 2y}{x + y} = \sum_{i + j = x + y} \binom{2x}{i}\binom{2y}{j} \ge \binom{2x}{x}\binom{2y}{y} = B_x B_y$$
(`Finset.single_le_sum` at $(x, y) \in \mathrm{antidiagonal}(x + y)$). Using $B_z = 2^{s_2(z)}\operatorname{A001790}(z)$ and $2^{s_2(x+y)} \le 2^{s_2(x)+s_2(y)}$ (Lemma 5.1),
$$2^{s_2(x)+s_2(y)} \operatorname{A001790}(x)\operatorname{A001790}(y) = B_x B_y \le B_{x+y} = 2^{s_2(x+y)} \operatorname{A001790}(x + y) \le 2^{s_2(x)+s_2(y)} \operatorname{A001790}(x + y).$$
Canceling $2^{s_2(x)+s_2(y)} > 0$ proves the two-factor inequality, and induction over `Finset` extends it to finite products. $\square$

### 5.2 Steps D7–D8: Exponent-Sum Dominance and Proof of Theorem 1.4

For $n \ge 1$, set $M(n) := \sum_{p \in n.\mathrm{primeFactors}} \lfloor v_p(n)/2 \rfloor$.

**Lemma 5.3 (`four_pow_M_le`, `four_pow_M_eq_self_iff`, `a_le_A001790_M`).** *For every $n \ge 1$, $4^{M(n)} \le n$ (with equality if and only if $n = 4^k$ for some $k \in \mathbb{N}$), and $a(n) \le \operatorname{A001790}(M(n))$.*

*Proof.* Every prime $p \in n.\mathrm{primeFactors}$ satisfies $p \ge 2$, so $4 \le p^2$ and $4^{\lfloor v_p(n)/2 \rfloor} \le p^{2\lfloor v_p(n)/2 \rfloor} \le p^{v_p(n)}$. Multiplying over $p \in n.\mathrm{primeFactors}$ (`Nat.prod_factorization_pow_eq_self`) gives $4^{M(n)} \le n$. Moreover, $M(4^k) = M(2^{2k}) = \lfloor 2k/2 \rfloor = k$ (`M_four_pow`), so $4^{M(n)} = n \iff \exists k,\ n = 4^k$. Combining Theorem 1.3 with Lemma 5.2 yields $a(n) = \prod_p \operatorname{A001790}(\lfloor v_p(n)/2 \rfloor) \le \operatorname{A001790}(M(n))$. $\square$

**Proof of Theorem 1.4 (`a317933_records`).**
- *Values at $1$ and $4^k$ (`a_one_eq_A001790_zero`, `a_four_pow`):* At $n = 1$, $f(1) = 1 \implies a(1) = 1 = \operatorname{A001790}(0)$. For any $k \in \mathbb{N}$, $4^k = 2^{2k}$, so Theorem 1.3 gives $a(4^k) = a(2^{2k}) = \operatorname{A001790}(k)$.
- *Sufficiency $(\Leftarrow)$:* At $n = 1$, $1 \le 1$ and no $m$ satisfies $1 \le m < 1$, so `isStrictRecord a 1` holds vacuously. If $n = 4^k$ with $k \ge 2$, then $1 \le 4^k$, and for any $m$ with $1 \le m < 4^k$, Lemma 5.3 gives $4^{M(m)} \le m < 4^k$, so $M(m) \le k - 1$. Since $k - 1 \ge 1$, Lemma 5.1 gives $\operatorname{A001790}(M(m)) \le \operatorname{A001790}(k - 1) < \operatorname{A001790}(k)$, whence $a(m) \le \operatorname{A001790}(M(m)) < \operatorname{A001790}(k) = a(4^k)$.
- *Necessity $(\Rightarrow)$:* Suppose `isStrictRecord a n` holds, so $n \ge 1$. If $n = 1$, we are done. Otherwise $n \ge 2$:
  - If $M(n) \le 1$, then $a(n) \le \operatorname{A001790}(M(n)) \le \operatorname{A001790}(1) = 1 = a(1)$, contradicting $a(1) < a(n)$ at $m = 1 < n$ (in particular ruling out $n = 4 = 4^1$, where $M(4) = 1$).
  - If $M(n) \ge 2$ and $n \ne 4^{M(n)}$, Lemma 5.3 gives $1 \le 4^{M(n)} < n$ while $a(n) \le \operatorname{A001790}(M(n)) = a(4^{M(n)})$, contradicting $a(4^{M(n)}) < a(n)$ at $m = 4^{M(n)} < n$. Thus $n = 4^{M(n)}$ with $k := M(n) \ge 2$. $\square$

*Corollary (`a_eq_one_of_lt_sixteen`).* For every $1 \le n \le 15$, $4^{M(n)} \le n < 4^2$ forces $M(n) \le 1$, so $1 \le a(n) \le \operatorname{A001790}(1) = 1$, immediately accounting for the fifteen leading ones of `OEIS A317933`.

---

## 6. Strength Delta and What This Paper Does Not Show

- **Strength delta vs. published source (`delta_vs_source: NONE`):** Theorems 1.1–1.4 prove the strongest published form of Karttunen's `OEIS A317933` `%C` line 13 assertion (`#21 Nov 01 2026`) across all $n \in \mathbb{N}$ with zero domain restriction, exponent loss, or auxiliary hypothesis—deriving both the record-position equivalence and the record values directly from $f(1) = 1 \wedge f * f = u$, while certifying `A001790_eq_num` and Eldar's `%F` line 18 formula as proved theorems.
- **What this paper does NOT show:**
  1. It does **not** prove Vaclav Kotesovec's analytic mean-value asymptotic $\sum_{k=1}^n f(k) \sim \frac{\sqrt{6}}{\pi} n$ (`OEIS A317933`, `%F` line 17, May 10, 2025).
  2. It does **not** formalize record theorems for the companion $\zeta(s)^{1/2}$ numerator sequence `OEIS A046643` (where $f_{\zeta}(p^e) = \binom{2e}{e}/4^e$ has $\lfloor e \rfloor$ in place of $\lfloor e/2 \rfloor$, shifting records to powers of $2$ rather than powers of $4$).
  3. Following `PIN-C047.md` v1 (`fidelity_notes` §5), $u(n)$ is defined as $2^{\omega(n)}$ (`2 ^ n.primeFactors.card`, matching Karttunen's `A034444(n) = (2^omega(n))` on `%o` line 21 and `A034444` `%F` line 44); this module does not add an unpinned companion lemma equating $2^{\omega(n)}$ with the literal filter cardinality `#\{d \in n.\mathrm{divisors} \mid \gcd(d, n/d) = 1\}`.

---

## 7. Lean 4 Formalization and Verification Record

### 7.1 Declaration Map (`Mathproofs/A317933Records.lean`)

| Mathematical Item | Lean 4 Declaration (`Mathproofs.A317933Records.*`) | Status |
| :--- | :--- | :--- |
| Unitary-divisor count $u(n) = 2^{\omega(n)}$ (`A034444`) | `u` | Pinned computable `def` |
| Canonical Dirichlet square root $f$ (`f 1 = 1 ∧ f * f = u`) | `f` | Pinned `noncomputable def` (`Classical.choose`) |
| Reduced rational numerator $a(n) = (f(n)).\mathrm{num}$ (`A317933`) | `a` | Pinned `noncomputable def` |
| Odd part of central binomial $\binom{2k}{k}/2^{s_2(k)}$ (`A001790`) | `A001790` | Pinned computable `def` |
| Strict 1-based prefix-record predicate | `isStrictRecord` | Pinned `def` (`0` axioms) |
| Step D1 uniqueness of Dirichlet square root | `dirichlet_sqrt_unique` | Proved |
| Step D2a finite convolution $\sum_{i=0}^m B_i B_{m-i} = 4^m$ | `centralBinom_conv` | Proved |
| Step D2b computable multiplicative witness $g$ & $g = f$ | `g`, `g_isMultiplicative`, `g_mul_self_eq_u`, `g_eq_f` | Computable `def` + proved |
| Step D3 2-adic valuation $v_2(B_m) = s_2(m)$ & oddness | `centralBinom_factorization_two`, `A001790_coprime_two`, `A001790_odd` | Proved |
| Step D4 `Rat.num` bridge & Eldar's prime-power formula | `a_eq_prod_A001790`, `a_prime_pow` | Proved |
| Steps D5–D6 monotonicity & supermultiplicativity | `s2_add_le`, `A001790_strictMono_from_one`, `A001790_supermult` | Proved |
| Trap #1 refutation witness at $k = 31, m_1 = 29, m_2 = 1$ | `triage_step2_bound_false_at_31` | Proved in kernel (`decide`) |
| Step D7 dominance $4^{M(n)} \le n$ & leading 15 ones | `four_pow_M_le`, `four_pow_M_eq_self_iff`, `one_le_a`, `a_eq_one_of_lt_sixteen` | Proved |
| **Pinned Theorem 1 (`f_existsUnique`)** | **`f_existsUnique`** | **Proved** |
| **Pinned Theorem 2 (`A001790_eq_num`)** | **`A001790_eq_num`** | **Proved** |
| **Pinned Theorem 3 (`a317933_records`)** | **`a317933_records`** | **Proved** |
| Computable mirror & kernel spot / guard checks | `a_mirror`, `a_mirror_eq_a`, `a_spot_checks`, `guard_exclusions` | Computable `def` + kernel-proved |

### 7.2 Recorded Trust, Axiom, Non-Vacuity, and Provenance Audit

0. **Artifact source digests bound to toolchain pin (`leanprover/lean4:v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, base `master` `2d8267e1f5e7543e2915d8ed4aee8ae917531882`):**
   - `Mathproofs/A317933Records.lean` (`814` lines): `32358f5814efb4138b2ef5f32b3373189315d461809b3db4309153f9ac419e94` (`0 diff chars` vs. `PIN-C047.md` v1 across all 5 definitions and 3 theorem signatures).
   - `Mathproofs.lean` (`81` lines, adds `import Mathproofs.A317933Records`): `ecc22863de78c6d9df713a43cc122e2e55550a247ca04d0f919f108df172b158`.
   - `lakefile.toml` (`19` lines, unchanged): `5a82a75a91dc597eccd9305c998dffaf6273956b9c0819f0c28cc86040316a21`.
   - Clean-slate full build (`rm -rf .lake/build && lake build`): exit `0` (`17,978` jobs; `0` errors, `0` sorries, `0` warnings on `Mathproofs.A317933Records`; log SHA-256 `def37675715244cf432abd4c84da4304a5432671d8cddde138d7bc394fab743b`).
1. **Axiom footprint (`#print axioms`):**
   - `Mathproofs.A317933Records.isStrictRecord`: depends on **no axioms**.
   - `Mathproofs.A317933Records.u`, `f`, `a`, `A001790`, `f_existsUnique`, `A001790_eq_num`, `a317933_records`, and all supporting declarations (`g`, `g_eq_f`, `a_mirror`, `a_mirror_eq_a`, `a_spot_checks`, `guard_exclusions`, `triage_step2_bound_false_at_31`): `[propext, Classical.choice, Quot.sound]` (exact allowlist).
2. **Transitive kernel closure & lexical trust-escape screen:**
   - Comment/string-stripped lexical scan across the local import closure (`Mathproofs/A317933Records.lean`, `Mathproofs.lean`, `Main.lean`): **`0` active hits** (and `0` raw hits) for `sorry`, `admit`, `sorryAx`, `axiom`, `native_decide`, `ofReduceBool`, `implemented_by`, `unsafe`.
   - Transitive `Lean.CoreM` constant-closure audit across `10,136` reachable constants: `DISALLOWED_AXIOMS = []`, `sorryAx = false`, `Lean.ofReduceBool = false`, `Lean.ofReduceNat = false`, `Lean.trustCompiler = false`.
   - Fresh-kernel replay (`lake env leanchecker --fresh --verbose Mathproofs.A317933Records`): **exit `0`**.
3. **Non-vacuity & spot checks (kernel vs. VM / b-file boundary stated explicitly):**
   - **Proved in the Lean kernel directly on the pinned `a` and `isStrictRecord`:** `a_spot_checks` (`a 1 = 1`, `a 2 = 1`, `a 3 = 1`, `a 4 = 1`, `a 5 = 1`, `a 16 = 3`, `a 64 = 5`, `a 256 = 35`, `a 1024 = 63`, `a 4096 = 231`), `a_eq_one_of_lt_sixteen` (`∀ n, 1 ≤ n → n < 16 → a n = 1`), and `guard_exclusions` (`¬ isStrictRecord a 0`, `¬ isStrictRecord a 2`, `¬ isStrictRecord a 3`, `¬ isStrictRecord a 4`, `¬ isStrictRecord a 5`, `a 4 = a 1`).
   - **Evaluated via Lean VM `#eval` on the computable mirror `a_mirror n = (g n).num`** (formally proved equal to `a n` for all $n \in \mathbb{N}$ by `a_mirror_eq_a`; `f` itself is `noncomputable` via `Classical.choose`) **and independent Python cross-checks** (not claimed as kernel `rfl` reductions): `0` mismatches across all `105` live `%S/%T/%U` terms (`n = 1..105`, `#eval`), `0` mismatches across `n = 1..500` against Karttunen's `b317933.txt` (`#eval`), `0` mismatches across `n = 1..8,192` from the rational Dirichlet recurrence (`recompute_c047_independent.py`), and `0` mismatches across all `65,537` rows of `b317933.txt`.
4. **Provenance & crossed-review status:**
   - High-level two-step concept from `TRIAGE-SEAMB.md` §3.4; repaired power-series-free, logarithm-free chain `D1–D8` (including `Trap #1` at $k = 31$ and `Trap #2` on `Nat.popCount`) derived in `SCOPING-C047.md` (`carbon-c047-scoping-20261114`), target frozen in `PIN-C047.md` v1; Lean 4 formalization authored in `carbon-c047-proof-20261116` (`nibbles`, `gemini-4-carbon-high`, `google-ai-ultra` pool).
   - Independent review status at draft PR opening: **`NOT YET RUN (PENDING)`** — awaiting crossed review by a fresh Gemini 4 Carbon High session disjoint from this author session, on a different machine where possible (session-level independence, per Derek's 2026-11-10 order).

---

## References

1. Antti Karttunen, *OEIS Sequence A317933: Numerators of rational valued sequence whose Dirichlet convolution with itself yields A034444 (number of unitary divisors of n)* (authored August 12, 2018; revision `#21` November 1, 2026, with formula contributions by Vaclav Kotesovec and Amiram Eldar), and companion sequences `A000302`, `A001790`, `A034444`, `A046643`, `A046644`, `A317934`, The On-Line Encyclopedia of Integer Sequences, https://oeis.org/A317933.
2. Ernst Kummer, *Über die Ergänzungssätze zu den allgemeinen Reciprocitätsgesetzen*, Journal für die reine und angewandte Mathematik **44** (1852), 93–146.
3. The mathlib Community, *The Lean Mathematical Library (`Mathlib4`)*, commit `d13f23b723b8a846827a245b89c10fc7d3f11612` (`v4.34.1`), 2026.
