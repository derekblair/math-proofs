# Formal Rogers–Fine Telescoping and Shift-and-Cancel Invariance for the Generalized Pentagonal False-Theta Series: Proof and Lean 4 Formalization of Peter Bala's OEIS A203568 Polynomial Family (`C037`)

**Preprint Draft (`PAPER-C037.md`) — 2026-11-16**  
**Repository / Module:** `derekblair/math-proofs` (`Mathproofs/A203568RogersFineFamily.lean`, `namespace Mathproofs.A203568RogersFineFamily`)  
**Toolchain & Mathlib Pin:** `leanprover/lean4:v4.34.1` (`commit 5045d0056413266e57c625dcd7c365b10e377c52`), Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`  
**Target Contract:** `PIN-C037.md` v1 (`SHA-256: 3f77fb26f6ca9bf3765856099f999fde66788dd49e17fb646d0a4494e66dcb22`, `delta_vs_source: NONE`)

---

## Abstract

Let $A(x) = \sum_{n \ge 0} a(n) x^n \in \mathbb{Z}\llbracket x \rrbracket$ be the ordinary generating function of `OEIS A203568` (Michael Somos, January 3, 2012), defined combinatorially by $a(n) = A026837(n) - A026838(n)$ as the number of partitions of $n$ into distinct parts with greatest part odd minus the number with greatest part even ($a(0) = 0$), and equal by Fine's partition theorem to the generalized pentagonal false-theta series $\sum_{k \in \mathbb{Z}} \operatorname{sign}(k)\, x^{k(3k-1)/2} = \sum_{k \ge 1} x^{k(3k-1)/2}(1 - x^k)$. On February 11, 2021, Peter Bala conjectured (`OEIS A203568`, `%F` lines 24–26) that $A(x) = \sum_{n \ge 1} (-1)^{n+1} x^{2n-1} / \prod_{k=1}^n (1 + x^{2k-1})$ (`C036`) and, more generally, that for every integer $N \ge 1$,
$$A(x) = \left(\prod_{j=1}^{N-1} \frac{1}{1 + x^{2j}}\right)\!\left(P(N, x) + \sum_{n \ge 1} \frac{(-1)^{n+N} x^{2Nn - N}}{\prod_{k=1}^n (1 + x^{2k-1})}\right)$$
for a polynomial $P(N, x) \in \mathbb{Z}[x]$ of exact degree $N^2 - N - 1$ when $N > 1$, recording $P(1, x) = 0$, $P(2, x) = x$, $P(3, x) = x - x^2 + x^5$, and $P(4, x) = x - x^2 + x^3 + x^5 + x^7 - x^8 + x^{11}$ empirically (`C037`).

We give a self-contained algebraic proof in $\mathbb{Z}[x]$ and $\mathbb{Z}\llbracket x \rrbracket$—using zero Laurent series, zero analytic limits, and zero external monograph axioms—together with a complete Lean 4 formalization of `C037` in both Bala's verbatim existential form and a strengthened unique/explicit form. Specifically, we construct $P(N, x)$ explicitly via the two-term recurrence $P(1, x) = 0$, $P(N + 1, x) = (1 + x^{2N}) P(N, x) + (-1)^{N+1} x^N$, yielding the closed form
$$P(N, x) = \sum_{m=1}^{N-1} (-1)^{m+1} x^m \prod_{j=m+1}^{N-1} (1 + x^{2j}),$$
and prove that $P(N, x)$ is monic of exact degree $N^2 - N - 1$ for every $N > 1$ and is the **unique** polynomial in $\mathbb{Z}[x]$ satisfying Bala's identity for each $N \ge 1$. Along the way we prove Fine's partition theorem directly from `Nat.Partition.distincts`, establish the $N = 1$ base case (`C036`) via a parameter-corrected positive-valuation Rogers–Fine telescoping ($q = x^2, \alpha = 0, \beta = -x^3, \tau = -x^2$) in $\mathbb{Z}\llbracket x \rrbracket$ where clearing the unit $(1 + x^{2M+2})$ avoids infinite double-sum Fubini swaps, prove that $P(5, x)$ is the first member with a coefficient outside $\{-1, 0, +1\}$ ($[x^{11}] P(5, x) = 2$), and verify decoupled constructive mirrors against all printed OEIS terms in Lean's kernel.

---

## 1. Introduction and Primary-Source Context

### 1.1 The Generalized Pentagonal False-Theta Series `OEIS A203568` and Peter Bala's Conjecture

Euler's pentagonal number theorem expands $\prod_{m \ge 1} (1 - x^m) = \sum_{k \in \mathbb{Z}} (-1)^k x^{k(3k-1)/2}$, weighting generalized pentagonal exponents $\omega(k) := k(3k - 1)/2$ by the parity sign $(-1)^k$. Replacing $(-1)^k$ by the chamber sign $\operatorname{sign}(k) \in \{-1, 0, +1\}$ produces the order-$3/2$ *false theta series* (`OEIS A203568` [1], offset $0$, $a(0) = 0$; companion `OEIS A143062` [2] has generating function $1 - A(x)$):
$$A(x) = \sum_{k \in \mathbb{Z}} \operatorname{sign}(k)\, x^{k(3k-1)/2} = \sum_{k=1}^{\infty} x^{k(3k-1)/2}(1 - x^k) = x - x^2 + x^5 - x^7 + x^{12} - x^{15} + x^{22} - x^{26} + \cdots.$$
In `OEIS A203568` (`%N`), Michael Somos defines $a(n)$ combinatorially via its primary partition decomposition
$$a(n) := A026837(n) - A026838(n) \qquad (n \ge 0),$$
where `A026837(n)` [3] counts partitions of $n$ into distinct parts whose greatest part is odd and `A026838(n)` [4] counts partitions of $n$ into distinct parts whose greatest part is even (both evaluating to $0$ at $n = 0$ because the unique empty partition of $0$ has no parts). The equality of this partition difference with the false-theta series $A(x)$ is a classical theorem of Nathan Fine (see Pak [5]).

On February 11, 2021, Peter Bala contributed a formula block to `OEIS A203568` (`%F` lines 20–26, live revision `#52` dated February 18, 2021 [1]) concluding with two open-labeled conjectures (`C036` and `C037`):

> **Conjecture (`C036` and `C037`, Peter Bala, Feb 11 2021 [1]).**
> - *(`C036`, line 24): Conjectural g.f.:*
>   $$A(x) = \sum_{n \ge 1} \frac{(-1)^{n+1} x^{2n-1}}{\prod_{k=1}^n (1 + x^{2k-1})} = x - x^2 + x^5 - x^7 + x^{12} - x^{15} + - \cdots.$$
> - *(`C037`, lines 25–26): More generally, for positive integer $N$, we appear to have the identity*
>   $$A(x) = \left(\prod_{j=1}^{N-1} \frac{1}{1 + x^{2j}}\right)\!\left(P(N, x) + \sum_{n \ge 1} \frac{(-1)^{n+N} x^{2Nn - N}}{\prod_{k=1}^n (1 + x^{2k-1})}\right),$$
>   *where $P(N, x)$ is a polynomial in $x$ of degree $N^2 - N - 1$ for $N > 1$, with the first few values given empirically by $P(1, x) = 0$, $P(2, x) = x$, $P(3, x) = x - x^2 + x^5$, and $P(4, x) = x - x^2 + x^3 + x^5 + x^7 - x^8 + x^{11}$. Cf. `A186424`.*

Notice that in Bala's published note, $P(N, x)$ is **purely existential** beyond $N = 4$: neither a closed form nor a recurrence for $P(N, x)$ appears in `A203568` or in any cross-referenced OEIS entry.

### 1.2 Prior-Art Boundary (`C037` vs. `C036`) and Adjacent OEIS Slips

A systematic literature audit (`SCOPING-C037.md` §3; 29 logged queries across OEIS, arXiv, OpenAlex, Zenodo, and general web search) delineates the exact novelty boundary of this work:

1. **Novelty boundary between `C036` ($N = 1$) and `C037` ($N \ge 1$ family):**
   - For the $N = 1$ identity `C036`, Bala himself notes on line 21 of `A203568` that pairwise grouping of Somos's 2015 series ($\sum_{m \ge 1} (-1)^{m+1} x^{m(m+1)/2} / (-x; x)_m$, originally due to Rogers, 1917 [6, Eq. 5.0.1]) gives Ramanujan's *Lost Notebook* **Entry 9.4.4** [6, §5.0, Eq. 5.0.3]:
     $$A(x) = \sum_{n=1}^{\infty} \frac{x^{n(2n-1)}}{\prod_{j=1}^{2n} (1 + x^j)}.$$
     Once reindexed by $n = m + 1$ with $\frac{x}{1+x}$ factored out, transforming `C036` into Entry 9.4.4 is a one-step specialization of the classical Rogers–Fine identity (`arXiv:2606.11011v1` §4.1 [7]; `arXiv:1604.04028v1` §4.2 [8]). Accordingly, **standalone `C036` is treated conservatively as a classical corollary (novelty-doubtful)** and is proved here strictly as the self-contained $N = 1$ base case of `C037`, never claimed as a standalone contribution.
   - By contrast, across all 29 literature and preprint searches (including Zenodo deposits where proofs of other Bala OEIS conjectures appear), **zero works** prove Bala's published $N$-parameterized conjecture `C037`, or pin the explicit recurrence, closed form, monicity, exact quadratic degree $N^2 - N - 1$, or uniqueness of $P(N, x)$ (`UNPROVED` prior-art status). The contribution of this paper is therefore framed modestly: a first written and machine-checked proof of Bala's published `OEIS A203568` conjecture `C037`, together with the explicit construction and uniqueness of its polynomial family $P(N, x)$.
   - **Closed-access discipline:** Closed-access monographs and paywalled articles (Andrews & Berndt, *Ramanujan's Lost Notebook, Part I*, 2005; Fine, *Basic Hypergeometric Series and Applications*, 1988; Andrews, *Math. Mag.* 1983; Berndt, Kim, & Yee, *JCTA* 2010) were neither accessed nor cited as unproved lemmas; every step below is proved unconditionally from scratch in $\mathbb{Z}\llbracket x \rrbracket$.

2. **Two adjacent OEIS slips that do NOT affect `C037`:**
   - **`OEIS A143062` line 30 (`n >= 0` typo):** Seven days before his `A203568` note, Bala posted on `A143062` (Feb 4, 2021) the conjectural formula $1 + \sum_{n \ge 0} (-1)^n x^{2n-1} / \prod_{k=1}^n (1 + x^{2k-1})$, whose $n = 0$ summand is the Laurent pole $x^{-1} \notin \mathbb{Z}\llbracket x \rrbracket$. Bala corrected the lower limit to $n \ge 1$ when posting `C036` and `C037` on `A203568` on Feb 11, 2021.
   - **`OEIS A186424` (`"Cf. A186424"`, $N = 0$ constant-term discrepancy):** Two days after `A203568`, Bala posted an analogous $N$-family conjecture (Feb 13, 2021) on `A186424` for a *different* series ($1 - x - x^3 + x^{11} + x^{17} - \cdots$, with polynomial degree $N^2 - 1$). Changing $\sum_{n \ge 0}$ to $\sum_{n \ge 1}$ there while writing $P_{A186424}(0, x) = 0$ introduced a constant-term slip at $N = 0$ (the true polynomial at $N = 0$ is $Q_0(x) = 1$, matching Bala's $P(1)..P(4)$ for $N \ge 1$). Entry `A186424` is **not** a dependency of `C037`, and `C037` on `A203568` ($N \ge 1$) has **zero** index or constant-term discrepancies.

### 1.3 Summary of Main Results

In `Mathproofs/A203568RogersFineFamily.lean` (`namespace Mathproofs.A203568RogersFineFamily`), we formalize and prove:

- **Theorem 1.1 (Fine's Partition Theorem — `a203568_eq_pentagonal`).** *For every $n \in \mathbb{N}$,*
  $$a203568(n) = \begin{cases} \operatorname{sign}(k) & \text{if } n = \frac{k(3k-1)}{2} \text{ for some } k \in \mathbb{Z}, \\ 0 & \text{otherwise.} \end{cases}$$
- **Theorem 1.2 (Explicit Polynomial Family, Closed Form, Degree, and Monicity — `c037Poly_closed_form`, `c037Poly_empirical_values`, `c037Poly_degree_and_monic`).** *Let $P(N, X) \in \mathbb{Z}[X]$ (`c037Poly N`) be defined by $P(0, X) = P(1, X) = 0$ and $P(N + 1, X) = (1 + X^{2N}) P(N, X) + (-1)^{N+1} X^N$ for $N \ge 1$. Then for all $N \ge 1$,*
  $$P(N, X) = \sum_{m=1}^{N-1} (-1)^{m+1} X^m \prod_{j=m+1}^{N-1} (1 + X^{2j}),$$
  *$P(1, X)..P(4, X)$ match Bala's four empirical polynomials verbatim, and for every $N > 1$, $P(N, X)$ is monic of exact `WithBot ℕ` degree $\deg P(N, X) = N^2 - N - 1$.*
- **Theorem 1.3 ($N = 1$ Base Case `C036` — `c036_a203568_gf`).** *In $\mathbb{Z}\llbracket X \rrbracket$ equipped with the product (`WithPiTopology`) topology over discrete $\mathbb{Z}$,*
  $$\operatorname{HasSum}\!\left(m \mapsto (-1)^{m+2} X^{2m+1} \left(\prod_{k=1}^{m+1} (1 + X^{2k-1})\right)^{\!-1},\; A(X)\right).$$
- **Theorem 1.4 (Explicit, Unique, and Existential `C037` Family — `c037_a203568_family_explicit`, `c037_a203568_family`, `c037_a203568_family_exists`).** *For every integer $N \ge 1$, there exists a **unique** polynomial $P \in \mathbb{Z}[X]$—namely $P = P(N, X)$—such that $(N = 1 \implies P = 0)$, $(1 < N \implies \deg P = N^2 - N - 1)$, and*
  $$A(X) = \left(\prod_{j=1}^{N-1} (1 + X^{2j})\right)^{\!-1} \bigl(P(X) + S_N(X)\bigr),$$
  *where $\operatorname{HasSum}\!\left(m \mapsto (-1)^{m+1+N} X^{2N(m+1) - N} \left(\prod_{k=1}^{m+1} (1 + X^{2k-1})\right)^{\!-1},\; S_N(X)\right)$ in $\mathbb{Z}\llbracket X \rrbracket$. Note that uniqueness actually holds unconditionally in $\mathbb{Z}[X]$ even without the degree hypothesis.*

---

## 2. Formal Specification in $\mathbb{Z}\llbracket X \rrbracket$ and $\mathbb{Z}[X]$

To eliminate every standard formalization pitfall (junk field division `0⁻¹ = 0`, junk `tsum = 0` on non-summable families, and `natDegree 0 = 0` conflating $P = 0$ with nonzero constants), `PIN-C037.md` v1 encodes all definitions directly over `Nat.Partition`, `ℤ[X]`, and `ℤ⟦X⟧` (`PowerSeries ℤ`):

```lean
def a026837 (n : ℕ) : ℕ :=
  ((Nat.Partition.distincts n).filter
    (fun p ↦ ∃ m ∈ p.parts, Odd m ∧ ∀ x ∈ p.parts, x ≤ m)).card

def a026838 (n : ℕ) : ℕ :=
  ((Nat.Partition.distincts n).filter
    (fun p ↦ ∃ m ∈ p.parts, Even m ∧ ∀ x ∈ p.parts, x ≤ m)).card

def a203568 (n : ℕ) : ℤ :=
  (a026837 n : ℤ) - (a026838 n : ℤ)

def a203568Series : ℤ⟦X⟧ :=
  PowerSeries.mk a203568

def c037Poly : ℕ → ℤ[X]
  | 0 => 0
  | 1 => 0
  | N + 2 =>
      (1 + Polynomial.X ^ (2 * (N + 1))) * c037Poly (N + 1) +
        (-1) ^ (N + 2) * Polynomial.X ^ (N + 1)
```

Four design invariants govern the formalization:
1. **Unit reciprocals in `ℤ⟦X⟧` (`no junk division`):** Every denominator product $\prod_{j=1}^{N-1} (1 + X^{2j})$ and $\prod_{k=1}^{m+1} (1 + X^{2k-1})$ has constant coefficient $1 \in \mathbb{Z}^\times$ and is inverted exclusively via `PowerSeries.invOfUnit φ (1 : ℤˣ)` (`Mathlib.RingTheory.PowerSeries.Inverse`), satisfying $\varphi \cdot \operatorname{invOfUnit}(\varphi, 1) = 1$ in `ℤ⟦X⟧`.
2. **Locally finite infinite sums (`no tsum = 0 trap`):** Infinite sums over $n \ge 1$ are reindexed by $m \in \mathbb{N}$ ($n = m + 1$) and stated as `HasSum` propositions under `PowerSeries.WithPiTopology` (`Mathlib.RingTheory.PowerSeries.PiTopology`) with discrete topology on $\mathbb{Z}$. By `PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff`, `HasSum f S` holds in $\mathbb{Z}\llbracket X \rrbracket$ if and only if for every degree $d \in \mathbb{N}$, `[X^d] (f m)` has finite support in $m$ and sums to `[X^d] S`.
3. **Exact `WithBot ℕ` polynomial degree (`no natDegree 0 = 0 trap`):** Degree is stated via `Polynomial.degree : ℤ[X] → WithBot ℕ`. At $N = 1$, $P(1, X) = 0$ has exact degree $\bot \in \operatorname{WithBot}\;\mathbb{N}$ (matching Bala's explicit guard $N > 1$ on $N^2 - N - 1$, since $1^2 - 1 - 1 = -1$), and $\prod_{j \in \mathrm{Icc}\; 1\; 0} (1 + X^{2j}) = 1$, so `C037` at $N = 1$ reduces syntactically to `C036`. For $N > 1$, $N^2 - N - 1 \ge 1$ in $\mathbb{N}$ without truncation underflow.
4. **Universal telescoping principle (`hasSum_of_sub_eq_and_coeff_zero`):** Steps 0, Link 1, and Link 3 all share a single 21-line formal telescoping lemma in `ℤ⟦X⟧` (lines 172–192): if a remainder sequence $(R_M)_{M \ge 0}$ in $\mathbb{Z}\llbracket X \rrbracket$ satisfies $R_M - R_{M+1} = t(M)$ for all $M \ge 0$ and $[X^d] R_M = 0$ for all $d < M$, then $\operatorname{HasSum}(t, R_0)$. Indeed, for every degree $d \in \mathbb{N}$ and every $M \ge d + 1$, both $[X^d] R_M$ and $[X^d] R_{M+1}$ vanish, so $[X^d] t(M) = 0$; hence `hasSum_sum_of_ne_finset_zero` reduces the sum at degree $d$ to `Finset.range (d + 1)`, where telescoping (`Finset.sum_range_sub'`) gives $\sum_{M=0}^{d} [X^d] t(M) = [X^d] R_0 - [X^d] R_{d+1} = [X^d] R_0$ without touching `ENat` valuation limits.

---

## 3. Step 0: Fine's Partition Theorem from `Nat.Partition.distincts`

### 3.1 Partition Decomposition by Greatest Part

Fix $n \in \mathbb{N}$. At $n = 0$, the unique partition $p \in \mathrm{distincts}(0)$ has $p.\mathrm{parts} = \emptyset$, so neither `∃ m ∈ p.parts, Odd m ∧ ...` nor `∃ m ∈ p.parts, Even m ∧ ...` holds; hence `a026837 0 = a026838 0 = 0` and `a203568 0 = 0`.

For $n \ge 1$, every partition $p \in \mathrm{distincts}(n)$ has nonempty nodup positive multiset `p.parts`, hence a unique greatest part $m = k + 1 \in \{1, \dots, n\}$ ($0 \le k < n$). Erasing $k + 1$ from `p.parts.toFinset` defines an explicit bijection (`maxPartDistincts_card_eq_subsetSum`, proved via `Finset.card_bij`) between:
$$\mathcal{M}(n, k + 1) := \bigl\{p \in \mathrm{distincts}(n) \;\big|\; k + 1 \in p.\mathrm{parts} \land \forall x \in p.\mathrm{parts},\; x \le k + 1\bigr\}$$
and the subset-sum family
$$\mathcal{S}(k, n - (k + 1)) := \Bigl\{s \subseteq \{1, \dots, k\} \;\Big|\; \sum_{j \in s} j = n - (k + 1)\Bigr\}.$$
On the algebra side, expanding $\prod_{j=1}^k (1 + X^j) = \sum_{s \subseteq \{1, \dots, k\}} X^{\sum_{j \in s} j}$ via `Finset.prod_one_add` and applying `maxPartDistincts_card_eq_subsetSum` shows $[X^n]\bigl(X^{k+1}\prod_{j=1}^k (1 + X^j)\bigr) = \#\mathcal{M}(n, k + 1)$ (`coeff_X_pow_mul_prod_range`, equal to $\#\mathcal{S}(k, n - (k + 1))$ for $k + 1 \le n$ and $0$ otherwise). Because $k + 1$ is odd if and only if $k$ is even (`(-1)^k = +1` for odd $k + 1$ and `-1` for even $k + 1$), summing over $k \ge 0$ yields the formal generating-function identity (`hasSum_distincts_a203568Series`):
$$A(X) = \sum_{k=0}^{\infty} (-1)^k X^{k+1} \prod_{j=1}^k (1 + X^j).$$

### 3.2 Telescoping to the Generalized Pentagonal Series

Following the algebraic spine of Mathlib's `Combinatorics/Enumerative/Pentagonal/Ring.lean`, Lean §3 skips defining an unshifted auxiliary series and works directly with the shifted remainder `step0Rem k` ($R_k^{\mathrm{pent}}(X) \in \mathbb{Z}\llbracket X \rrbracket$, $k \ge 0$), defined as the formal sum of
$$a_k(m) := (-1)^m X^{\omega(k+1) + (k+1)m} \prod_{i=0}^{m-1} \bigl(1 + X^{k+1+i}\bigr) \qquad (\omega(k+1) = (k+1)(3k+2)/2).$$
At $k = 0$, $\omega(1) = 1$, so $a_0(m)$ coincides term-by-term with the summand in `hasSum_distincts_a203568Series`, giving $R_0^{\mathrm{pent}}(X) = A(X)$ (`step0Rem_zero_eq_a203568Series`). To compare $R_k^{\mathrm{pent}}(X)$ with $R_{k+1}^{\mathrm{pent}}(X)$, introduce the inner telescoping sequence (`step0Aux`)
$$u_k(r) := (-1)^r X^{\omega(k+1) + (k+1)(r+2)} \prod_{i=0}^{r-1} \bigl(1 + X^{k+2+i}\bigr) \qquad (r \ge 0).$$
In $a_k(r + 2)$, factoring out both ends of $\prod_{i=0}^{r+1}(1 + X^{k+1+i}) = (1 + X^{k+1})\bigl(\prod_{i=0}^{r-1}(1 + X^{k+2+i})\bigr)(1 + X^{k+2+r})$ and expanding $(1 + X^{k+1})(1 + X^{k+2+r}) = 1 + X^{k+2+r} + X^{k+1}(1 + X^{k+2+r})$ splits $a_k(r + 2)$ into three pieces:
- the $1$ term, which equals $u_k(r)$;
- the $X^{k+2+r}$ term, whose exponent satisfies $\omega(k+1) + (k+1)(r+2) + (k+2+r) = \omega(k+2) + (k+2)r$ (using $\omega(k+1) + (3k+4) = \omega(k+2)$), reproducing $a_{k+1}(r)$ identically; and
- the $X^{k+1}(1 + X^{k+2+r})$ term, which carries exponent $\omega(k+1) + (k+1)(r+3)$, extends the product to $r + 1$ factors, and has sign $(-1)^r = -(-1)^{r+1}$, equalling $-u_k(r + 1)$.

Rearranging yields the exact inner telescoping identity (`step0_telescoping_term`):
$$a_k(r + 2) - a_{k+1}(r) = u_k(r) - u_k(r + 1) \qquad (\forall k, r \ge 0).$$
Applying `hasSum_of_sub_eq_and_coeff_zero` in $r$ sums $a_k(r + 2) - a_{k+1}(r)$ to $u_k(0) = X^{\omega(k+1) + 2(k+1)}$. On the other hand, peeling off $m = 0$ and $m = 1$ from $R_k^{\mathrm{pent}}(X)$ shows that the same series sums to $R_k^{\mathrm{pent}}(X) - a_k(0) - a_k(1) - R_{k+1}^{\mathrm{pent}}(X)$. By uniqueness of `HasSum` limits, and because $a_k(0) = X^{\omega(k+1)}$ while $a_k(1) = -X^{\omega(k+1)+(k+1)}(1 + X^{k+1}) = -X^{\omega(-(k+1))} - u_k(0)$ (using $\omega(k+1) + (k+1) = \omega(-(k+1))$), the $u_k(0)$ terms cancel to give (`step0Rem_sub_succ`):
$$R_k^{\mathrm{pent}}(X) - R_{k+1}^{\mathrm{pent}}(X) = X^{\omega(k+1)} - X^{\omega(-(k+1))}, \qquad [X^d] R_k^{\mathrm{pent}}(X) = 0 \text{ for } d < k.$$
Applying our universal telescoping lemma gives $A(X) = R_0^{\mathrm{pent}}(X) = \sum_{k=0}^\infty \bigl(X^{\omega(k+1)} - X^{\omega(-(k+1))}\bigr)$ (`hasSum_pentagonal_a203568Series`). Extracting $[X^n]$ and using `pentagonal_injective` proves Theorem 1.1 (`a203568_eq_pentagonal`). $\square$

---

## 4. Links 1 and 2: From Pentagonal False-Theta Series to Ramanujan's Entry 9.4.4

### 4.1 Link 1: Formal Remainder Proof of Somos's Alternating Series

For every $M, r \in \mathbb{N}$, put $E(M, r) := \frac{(M+r)(M+r+1)}{2} + M^2 + Mr$ and define in $\mathbb{Z}\llbracket X \rrbracket$:
$$\mathcal{L}_M(X) := \sum_{r=0}^{\infty} (-1)^r X^{E(M, r)} \left(\prod_{j=M+1}^{M+r} (1 + X^j)\right)^{\!-1}.$$
Every summand of $\mathcal{L}_M$ has valuation $\ge E(M, r) \ge E(M, 0) = \frac{M(3M+1)}{2} = \omega(-M)$, so $[X^d] \mathcal{L}_M = 0$ for all $M > d$. At $M = 0$, $E(0, r) = r(r+1)/2$, so separating $r = 0$ gives $\mathcal{L}_0(X) = 1 - S_{\mathrm{Somos}}(X)$, where
$$S_{\mathrm{Somos}}(X) := \sum_{m=1}^{\infty} (-1)^{m+1} X^{m(m+1)/2} \left(\prod_{j=1}^m (1 + X^j)\right)^{\!-1}.$$
Using the exact integer exponent identities $E(M + 1, s) = E(M, s + 1) + M + s + 1$ and $E(M, u + 1) = E(M, u) + 2M + u + 1$, multiply each $s$-th summand of $\mathcal{L}_{M+1}$ by $(1 + X^{M+1})(1 + X^{M+1})^{-1}$ to restore the $j = M + 1$ denominator factor:
$$\mathcal{L}_{M+1}(X) = \sum_{s=0}^{\infty} \frac{(-1)^s X^{E(M, s+1) + (M+s+1)}}{\prod_{j=M+1}^{M+s+1} (1 + X^j)} + \sum_{s=0}^{\infty} \frac{(-1)^s X^{E(M, s+1) + (2M+s+2)}}{\prod_{j=M+1}^{M+s+1} (1 + X^j)}.$$
Subtracting the first sum of $\mathcal{L}_{M+1}(X)$ from the $r = s + 1 \ge 1$ tail of $\mathcal{L}_M(X)$ (in computing $\mathcal{L}_M(X) - \mathcal{L}_{M+1}(X)$) produces numerator $(-1)^{s+1} X^{E(M, s+1)}(1 + X^{M+s+1})$, cancelling the top denominator factor $(1 + X^{M+s+1})$ to leave $\sum_{s=0}^\infty (-1)^{s+1} X^{E(M, s+1)} / \prod_{j=M+1}^{M+s} (1 + X^j)$. Since $E(M, 0) = M(3M+1)/2 = \omega(-M)$ and $E(M, 1) = \frac{(M+1)(M+2)}{2} + M^2 + M = \frac{3M^2 + 5M + 2}{2} = \omega(M+1)$, its $s = 0$ term is $-X^{E(M, 1)} = -X^{\omega(M+1)}$ and its $s = u + 1 \ge 1$ tail cancels the negated second sum of $\mathcal{L}_{M+1}(X)$ term-by-term (formalized via the inner telescoping identity `link1_telescoping_term`), leaving (`link1Rem_sub_succ`):
$$\mathcal{L}_M(X) - \mathcal{L}_{M+1}(X) = X^{E(M, 0)} - X^{E(M, 1)} = X^{\omega(-M)} - X^{\omega(M+1)}.$$
Telescoping over $M \ge 0$: the $M = 0$ term is $X^0 - X^{\omega(1)} = 1 - X$, and for $M \ge 1$ the terms rearrange via $(1 - X^{\omega(1)}) + \sum_{M=1}^\infty (X^{\omega(-M)} - X^{\omega(M+1)}) = 1 - \sum_{k=1}^\infty (X^{\omega(k)} - X^{\omega(-k)}) = 1 - A(X)$. Thus $1 - S_{\mathrm{Somos}}(X) = \mathcal{L}_0(X) = 1 - A(X)$, proving $S_{\mathrm{Somos}}(X) = A(X)$ (`hasSum_somos_a203568Series`).

### 4.2 Link 2: Pairwise Grouping to Entry 9.4.4

For any locally finite sequence $(g_r)_{r \ge 0}$ in $\mathbb{Z}\llbracket X \rrbracket$, constructing the even-indexed and odd-indexed formal sums separately and combining them via Mathlib's `HasSum.even_add_odd` and `HasSum.add` gives $\sum_{r=0}^\infty g_r = \sum_{m=0}^\infty (g_{2m} + g_{2m+1})$. Applying this to Somos's series ($n = m + 1 \ge 1$, pairing indices $2m + 1$ and $2m + 2$):
$$\frac{X^{(2m+1)(m+1)}}{\prod_{j=1}^{2m+1} (1 + X^j)} - \frac{X^{(m+1)(2m+3)}}{\prod_{j=1}^{2m+2} (1 + X^j)} = \frac{X^{(m+1)(2m+1)}(1 + X^{2m+2}) - X^{(m+1)(2m+3)}}{\prod_{j=1}^{2m+2} (1 + X^j)} = \frac{X^{(m+1)(2m+1)}}{\prod_{j=1}^{2m+2} (1 + X^j)}.$$
Writing $n = m + 1 \ge 1$ establishes Ramanujan's Entry 9.4.4 in $\mathbb{Z}\llbracket X \rrbracket$ (`hasSum_entry944_a203568Series`):
$$A(X) = \sum_{n=1}^{\infty} \frac{X^{n(2n-1)}}{\prod_{j=1}^{2n} (1 + X^j)}.$$

---

## 5. Link 3: Parameter-Corrected Rogers–Fine Telescoping in $\mathbb{Z}\llbracket X \rrbracket$ (`C036`)

### 5.1 Refutation of the Literal `b = -x^(-1)` Parameter and Positive-Valuation Correction

In `TRIAGE-SEAMB.md` (lines 54, 349), `C036` was sketched as specializing the Rogers–Fine identity at $q \mapsto x^2$, $a = 0$, $b = -x^{-1}$, $t = -x^2$. Testing that specialization directly reveals an index-shift discrepancy in both standard conventions:
1. In the $(\alpha; q)_n / (\beta; q)_n$ convention (`arXiv:2606.11011v1` §4.1, $\sum_{n \ge 0} \frac{(\alpha; q)_n}{(\beta; q)_n} \tau^n$), setting $\beta = -x^{-1}$ introduces the negative-valuation factor $(1 + x^{-1}) = \frac{1+x}{x}$ at $k = 0$, exiting $\mathbb{Z}\llbracket x \rrbracket$ and yielding $1 - \frac{x^3}{1+x} + \frac{x^5}{(1+x)^2} - \cdots \ne 1 - S_1(x)$.
2. In Fine's shifted $(aq; q)_n / (bq; q)_n$ convention ($\beta = bq$), setting $q = x^2, a = 0, b = -x^{-1}, t = -x^2$ gives $\beta = bq = -x$ and $(bq; q)_n = \prod_{k=1}^n (1 + x^{2k-1})$, **but** the numerator is $t^n = (-1)^n x^{2n}$ rather than $(-1)^{n+1} x^{2n-1}$, producing
   $$\sum_{n=0}^{\infty} \frac{(-1)^n x^{2n}}{\prod_{k=1}^n (1 + x^{2k-1})} = 1 - x S_1(x) = \sum_{n=0}^{\infty} \frac{x^{n(2n+1)}}{(-x; x)_{2n}(1 + x^{2n+2})},$$
   which carries a spurious factor of $x$ and skips $(1 + x^{2n+1})$.

**Corrected positive-valuation specialization:** Reindex $S_1(X) = \sum_{n \ge 1} (-1)^{n+1} X^{2n-1} / \prod_{k=1}^n (1 + X^{2k-1})$ by $n = m + 1$ ($m \ge 0$) and factor out $\frac{X}{1+X}$:
$$S_1(X) = X (1 + X)^{-1} \sum_{m=0}^{\infty} (-X^2)^m \left(\prod_{k=1}^m \bigl(1 + X^{2k+1}\bigr)\right)^{\!-1}.$$
Now specialize the $\alpha = 0$ Rogers–Fine identity at
$$q = X^2, \qquad \alpha = 0, \qquad \beta = -X^3 \quad (b = \beta / q = -X), \qquad \tau = -X^2.$$
Every parameter lies strictly inside $X\mathbb{Z}[X]$—**zero negative powers of $X$ and zero Laurent series occur anywhere**.

### 5.2 Unit-Clearing Remainder Proof Eliminating Double-Sum Fubini

In `SCOPING-C037.md` §5.2, justifying the infinite double-sum Fubini interchange $\sum_{k > M} \sum_{j=M}^{k-1} \leftrightarrow \sum_{j \ge M} \sum_{k > j}$ in the Rogers–Fine remainder identity was identified as the hardest technical bottleneck of the proof. In our Lean 4 formalization (`Section 5` of `Mathproofs/A203568RogersFineFamily.lean`), we bypass infinite double sums *completely* by a unit-clearing observation!

For each $M \ge 0$, since $\beta^M \tau^{M+r} = (-X^3)^M (-X^2)^{M+r} = (-1)^{2M+r} X^{3M + 2M + 2r} = (-1)^r X^{5M + 2r}$, define the concrete positive-valuation remainder in $\mathbb{Z}\llbracket X \rrbracket$:
$$\mathcal{R}_M(X) := \sum_{r=0}^{\infty} (-1)^r X^{2M^2 + 3M + (2M+2)r} \cdot U_{\mathrm{odd}}(M + r)^{-1} \cdot U_{\mathrm{even}}(M)^{-1},$$
where $U_{\mathrm{odd}}(k) := \prod_{i=1}^k (1 + X^{2i+1})$ and $U_{\mathrm{even}}(M) := \prod_{i=1}^M (1 + X^{2i})$. Note two immediate facts:
1. At $M = 0$, $2M^2 + 3M + (2M+2)r = 2r$ and $U_{\mathrm{even}}(0) = 1$, so $X(1 + X)^{-1} \mathcal{R}_0(X) = S_1(X)$.
2. Every summand of $\mathcal{R}_M(X)$ has valuation $\ge 2M^2 + 3M \ge M$, so $[X^d] \mathcal{R}_M(X) = 0$ whenever $d < 2M^2 + 3M$—in particular for all $d < M$, which is the simpler sufficient hypothesis formalized in `rfRem_coeff_zero`.

To prove $\mathcal{R}_M(X) - \mathcal{R}_{M+1}(X) = X^{2M^2 + 3M} U_{\mathrm{odd}}(M)^{-1} U_{\mathrm{even}}(M + 1)^{-1}$, multiply the target equation by the unit $1 - \tau q^M = 1 + X^{2M+2}$. Because $U_{\mathrm{even}}(M + 1) = (1 + X^{2M+2}) U_{\mathrm{even}}(M)$, multiplying $\mathcal{R}_{M+1}(X)$ by $(1 + X^{2M+2})$ cancels the newly adjoined $(1 + X^{2M+2})$ factor from $U_{\mathrm{even}}(M + 1)^{-1}$, leaving the **same** even-product inverse $U_{\mathrm{even}}(M)^{-1}$ on all terms:
$$(1 + X^{2M+2})\bigl(\mathcal{R}_M(X) - \mathcal{R}_{M+1}(X)\bigr) = \bigl(1 + X^{2M+2}\bigr) \mathcal{R}_M(X) - \sum_{s=0}^{\infty} (-1)^s X^{E_{\mathrm{RF}}(M+1, s)} U_{\mathrm{odd}}(M + 1 + s)^{-1} U_{\mathrm{even}}(M)^{-1},$$
where $E_{\mathrm{RF}}(M, r) := 2M^2 + 3M + (2M+2)r$. Now split $1 \cdot \mathcal{R}_M(X)$ into its $r = 0$ summand $u_0(M) := X^{2M^2 + 3M} U_{\mathrm{odd}}(M)^{-1} U_{\mathrm{even}}(M)^{-1}$ plus its $r = s + 1$ tail ($s \ge 0$), and promote $U_{\mathrm{odd}}(M + s)^{-1}$ in $X^{2M+2} \mathcal{R}_M(X)$ to $(1 + X^{2M+2s+3}) U_{\mathrm{odd}}(M + s + 1)^{-1}$. Every $s \ge 0$ summand across:
- the $r = s + 1$ tail of $1 \cdot \mathcal{R}_M(X)$,
- the full $s \ge 0$ series of $X^{2M+2} \mathcal{R}_M(X)$, and
- the full $s \ge 0$ series of $-(1 + X^{2M+2}) \mathcal{R}_{M+1}(X)$

now shares the common denominator factor $U_{\mathrm{odd}}(M + 1 + s)^{-1} U_{\mathrm{even}}(M)^{-1}$, and at each $s \ge 0$ their numerators sum identically to zero by a one-line polynomial `ring` identity (`rf_term_identity`):
$$(-1)^{s+1} X^{E_{\mathrm{RF}}(M, s+1)} + X^{2M+2} (-1)^s X^{E_{\mathrm{RF}}(M, s)}\bigl(1 + X^{2M+2s+3}\bigr) - (-1)^s X^{E_{\mathrm{RF}}(M+1, s)} = 0.$$
Thus $(1 + X^{2M+2})(\mathcal{R}_M(X) - \mathcal{R}_{M+1}(X)) = u_0(M) = X^{2M^2 + 3M} U_{\mathrm{odd}}(M)^{-1} U_{\mathrm{even}}(M)^{-1}$. Multiplying both sides by $(1 + X^{2M+2})^{-1}$ immediately gives (`rfRem_sub_succ`):
$$\mathcal{R}_M(X) - \mathcal{R}_{M+1}(X) = X^{2M^2 + 3M} U_{\mathrm{odd}}(M)^{-1} U_{\mathrm{even}}(M + 1)^{-1}.$$

Applying the universal telescoping lemma yields $\mathcal{R}_0(X) = \sum_{m=0}^\infty X^{2m^2 + 3m} U_{\mathrm{odd}}(m)^{-1} U_{\mathrm{even}}(m + 1)^{-1}$. Multiplying by $X(1 + X)^{-1}$ merges $(1 + X)$ with $U_{\mathrm{odd}}(m)$ into $\prod_{k=1}^{m+1} (1 + X^{2k-1})$, combines $X \cdot X^{2m^2 + 3m} = X^{(m+1)(2m+1)}$, and merges the odd and even factorials via the parity partition of $\{1, \dots, 2m+2\}$ (`odd_even_prod_eq_link1Prod`) into $\prod_{j=1}^{2m+2} (1 + X^j)$. By uniqueness of `HasSum` limits against Link 2 (`hasSum_entry944_a203568Series`), $S_1(X) = A(X)$, completing Theorem 1.3 (`c036_a203568_gf`). $\square$

---

## 6. Link 4: Shift-and-Cancel Induction, Quadratic Degree, Monicity, Uniqueness, and the $P(5, X)$ Collision (`C037`)

### 6.1 The Shift-and-Cancel Identity for $S_N(X)$

For each integer $N \ge 1$, let $S_N(X) \in \mathbb{Z}\llbracket X \rrbracket$ (`c037Tail N`) be the unique formal sum of
$$m \longmapsto (-1)^{m+1+N} X^{2N(m+1) - N} \left(\prod_{k=1}^{m+1} (1 + X^{2k-1})\right)^{\!-1}.$$
Subtracting $S_{N+1}(X)$ from $S_N(X)$ (equivalently, adding $-S_{N+1}(X)$ to $S_N(X)$) combines the $m$-th numerators into
$$(-1)^{m+1+N} X^{N(2m+1)} - (-1)^{m+2+N} X^{(N+1)(2m+1)} = (-1)^{m+1+N} X^{N(2m+1)} \bigl(1 + X^{2m+1}\bigr).$$
Cancelling the top odd factor $(1 + X^{2m+1})$ (`k = m + 1`) from $\prod_{k=1}^{m+1} (1 + X^{2k-1})$ leaves:
- at $m = 0$: $(-1)^{N+1} X^N \cdot 1^{-1} = (-1)^{N+1} X^N$;
- at $m = r + 1 \ge 1$: $(-1)^{r+2+N} X^{N(2r+3)} / \prod_{k=1}^{r+1} (1 + X^{2k-1}) = -X^{2N} \cdot \bigl(\text{$r$-th summand of } S_N(X)\bigr)$.

Rearranging gives the fundamental shift-and-cancel identity (`c037_shift_cancel`):
$$\bigl(1 + X^{2N}\bigr) S_N(X) = (-1)^{N+1} X^N + S_{N+1}(X) \qquad (\forall N \ge 1).$$

### 6.2 Invariance of $\prod_{j=1}^{N-1} (1 + X^{2j}) A(X) = P(N, X) + S_N(X)$

By definition of `c037Poly`, $P(1, X) = 0$ and $P(N + 1, X) = (1 + X^{2N}) P(N, X) + (-1)^{N+1} X^N$ for $N \ge 1$. Let $E_N(X) := \prod_{j=1}^{N-1} (1 + X^{2j})$. We prove $E_N(X) A(X) = P(N, X) + S_N(X)$ (`evenProd_mul_a203568Series`) by induction on $N \ge 1$:
- **Base ($N = 1$):** $E_1(X) = 1$ (`Finset.Icc 1 0 = ∅`) and $P(1, X) = 0$, reducing to $A(X) = S_1(X)$ (Theorem 1.3).
- **Step ($N \mapsto N + 1$, $N \ge 1$):** Using $E_{N+1}(X) = (1 + X^{2N}) E_N(X)$, the inductive hypothesis, and `c037_shift_cancel`:
  $$\begin{aligned}
  E_{N+1}(X) A(X)
    &= (1 + X^{2N})\bigl(P(N, X) + S_N(X)\bigr) \\
    &= (1 + X^{2N}) P(N, X) + \bigl((-1)^{N+1} X^N + S_{N+1}(X)\bigr) \\
    &= P(N + 1, X) + S_{N+1}(X).
  \end{aligned}$$
Multiplying on the left by $E_N(X)^{-1} = \mathrm{invOfUnit}(E_N(X), 1)$ immediately gives Theorem 1.4's explicit identity (`c037_a203568_family_explicit`). Unfolding the two-term recurrence by induction on $N \ge 1$ simultaneously proves the closed form (`c037Poly_closed_form`):
$$P(N, X) = \sum_{m=1}^{N-1} (-1)^{m+1} X^m \prod_{j=m+1}^{N-1} (1 + X^{2j}).$$

### 6.3 Exact Quadratic Degree, Monicity, Uniqueness, and the $N = 5$ Coefficient $+2 X^{11}$

1. **Exact degree $N^2 - N - 1$ and monicity for $N > 1$ (`c037Poly_degree_and_monic`):**
   - At $N = 2$, $P(2, X) = (1 + X^2)\cdot 0 + (-1)^2 X^1 = X$, which is monic (`Polynomial.monic_X`) of exact `WithBot ℕ` degree $\deg X = 1 = 2^2 - 2 - 1$ (`Polynomial.degree_X`).
   - For $M \ge 2$, assume $P(M, X)$ is monic of degree $M^2 - M - 1$. Because $1 + X^{2M} = X^{2M} + 1$ is monic of degree $2M$ (`Polynomial.monic_X_pow_add_C`, `Polynomial.degree_X_pow_add_C`), the product $(1 + X^{2M}) P(M, X)$ is monic of exact degree
     $$2M + (M^2 - M - 1) = M^2 + M - 1 = (M + 1)^2 - (M + 1) - 1.$$
     Meanwhile, $(-1)^{M+1} X^M$ has exact degree $M$, and for every $M \ge 2$, $M < M^2 + M - 1$ (since $M^2 \ge 4 > 1$). By `Polynomial.degree_add_eq_left_of_degree_lt` and `Monic.add_of_left`, adding $(-1)^{M+1} X^M$ strictly below the leading term preserves both monicity and the exact degree $(M + 1)^2 - (M + 1) - 1$.

2. **Uniqueness (`c037_a203568_family`):**
   Suppose $Q \in \mathbb{Z}[X]$ satisfies $A(X) = E_N(X)^{-1} (Q(X) + S')$ with $\operatorname{HasSum}(\dots, S')$. By Hausdorff uniqueness of limits in $\mathbb{Z}\llbracket X \rrbracket$, $S' = S_N(X)$. Multiplying on the left by $E_N(X)$ cancels $E_N(X) E_N(X)^{-1} = 1$, giving $Q(X) + S_N(X) = E_N(X) A(X) = P(N, X) + S_N(X)$. Subtracting $S_N(X)$ gives `toPowerSeries Q = toPowerSeries (c037Poly N)`, whence $Q = P(N, X)$ in $\mathbb{Z}[X]$ by injectivity of $\mathbb{Z}[X] \hookrightarrow \mathbb{Z}\llbracket X \rrbracket$ (`Polynomial.coe_inj`). Notice that the degree bound is not even needed in the uniqueness direction: **only one polynomial in all of $\mathbb{Z}[X]$** clears the principal part for a given $N \ge 1$.

3. **Empirical values and the $N = 5$ coefficient collision (`c037Poly_empirical_values`, `c037Poly_five_and_coeff_11`):**
   Evaluating `c037Poly` for $N = 1..5$ gives:
   - $P(1, X) = 0$ ($\deg = \bot$);
   - $P(2, X) = X$ ($\deg = 1$);
   - $P(3, X) = X - X^2 + X^5$ ($\deg = 5$);
   - $P(4, X) = X - X^2 + X^3 + X^5 + X^7 - X^8 + X^{11}$ ($\deg = 11$);
   - $P(5, X) = (1 + X^8) P(4, X) - X^4 = X - X^2 + X^3 - X^4 + X^5 + X^7 - X^8 + X^9 - X^{10} + \mathbf{2 X^{11}} + X^{13} + X^{15} - X^{16} + X^{19}$ ($\deg = 19$).

   For $N \in \{1, 2, 3, 4\}$, every coefficient of $P(N, X)$ lies in $\{-1, 0, +1\}$. At $N = 5$, the shifted term $X^8 \cdot (+X^3)$ from $X^8 P(4, X)$ collides with $1 \cdot (+X^{11})$ from $P(4, X)$ (equivalently, in the closed form, $m = 1$ contributes $+X(X^4 \cdot X^6) = +X^{11}$ and $m = 3$ contributes $+X^3 \cdot X^8 = +X^{11}$), producing $[X^{11}] P(5, X) = +2$. Any heuristic ansatz restricting coefficients of $P(N, X)$ to $\{-1, 0, +1\}$ fails first at $N = 5$ (with maximum coefficient magnitude growing rapidly thereafter: $3, 4, 6, 16, 264, 5472$ at $N = 6, 7, 8, 10, 15, 20$).

---

## 7. Strength Delta and Scope Boundaries

- **Strength delta vs. source (`delta_vs_source: NONE`):** `Mathproofs.A203568RogersFineFamily` proves Peter Bala's complete February 11, 2021 conjecture on `OEIS A203568` at full strength from the primary `%N` partition definitions (`a026837`, `a026838`, `a203568`), providing **both** Bala's literal existential statement (`c037_a203568_family_exists`) **and** the strictly stronger explicit, monic, unique characterization (`c037_a203568_family`, `c037_a203568_family_explicit`, `c037Poly_closed_form`, `c037Poly_degree_and_monic`, `c037Poly_empirical_values`), together with Fine's theorem (`a203568_eq_pentagonal`) and the $N = 1$ base case (`c036_a203568_gf`).
- **What this paper does NOT show:**
  1. It does **not** claim standalone mathematical novelty for the $N = 1$ identity `C036`, which is adjudicated transparently as a one-step Rogers–Fine specialization of Ramanujan's Entry 9.4.4 once the parameter $b = -x$ ($\beta = -x^3$) is used.
  2. It does **not** formalize Peter Bala's separate February 13, 2021 conjecture on `OEIS A186424` (degree $N^2 - 1$, where the $N = 0$ case requires correcting $P(0, x) = 0$ to $Q_0(x) = 1$).
  3. It works entirely in the formal rings $\mathbb{Z}[X]$ and $\mathbb{Z}\llbracket X \rrbracket$ under the product (`WithPiTopology`) topology rather than analytic convergence on the complex open unit disk $\{z \in \mathbb{C} : |z| < 1\}$ (though analytic equality on $|z| < 1$ follows immediately by absolute convergence of every series involved).

---

## 8. Lean 4 Formalization and Verification Record

### 8.1 Declaration Map (`Mathproofs/A203568RogersFineFamily.lean`)

| Mathematical Item | Lean 4 Declaration | Status / Axiom Footprint |
| :--- | :--- | :--- |
| Primary `%N` odd-max distinct partitions | `a026837` | Pinned `def`, `[propext, Classical.choice, Quot.sound]` |
| Primary `%N` even-max distinct partitions | `a026838` | Pinned `def`, `[propext, Classical.choice, Quot.sound]` |
| Primary `%N` sequence `A203568` ($a(0) = 0$) | `a203568` | Pinned `def`, `[propext, Classical.choice, Quot.sound]` |
| Generating function $A(X) \in \mathbb{Z}\llbracket X \rrbracket$ | `a203568Series` | Pinned `def`, `[propext, Classical.choice, Quot.sound]` |
| Explicit polynomial family $P(N, X) \in \mathbb{Z}[X]$ | `c037Poly` | Pinned `def`, `[propext, Classical.choice, Quot.sound]` |
| **Theorem 1.1 (Fine's Partition Theorem)** | **`a203568_eq_pentagonal`** | **Proved (allowlist axioms only)** |
| **Theorem 1.2a (Closed form of $P(N, X)$)** | **`c037Poly_closed_form`** | **Proved (allowlist axioms only)** |
| **Theorem 1.2b (Empirical $P(1)..P(4)$)** | **`c037Poly_empirical_values`** | **Proved (allowlist axioms only)** |
| **Theorem 1.2c (Exact degree & monicity, $N > 1$)** | **`c037Poly_degree_and_monic`** | **Proved (allowlist axioms only)** |
| **Theorem 1.3 ($N = 1$ reduction `C036`)** | **`c036_a203568_gf`** | **Proved (allowlist axioms only)** |
| **Theorem 1.4a (Explicit `C037` family)** | **`c037_a203568_family_explicit`** | **Proved (allowlist axioms only)** |
| **Theorem 1.4b (Unique `∃! P` `C037` family)** | **`c037_a203568_family`** | **Proved (allowlist axioms only)** |
| **Theorem 1.4c (Verbatim `∃ P` `C037` family)** | **`c037_a203568_family_exists`** | **Proved (allowlist axioms only)** |
| Constructive $O(B^2)$ DP mirror & decoupled proof | `subsetSumCount`, `a203568Compute`, `a203568_eq_compute` | Computable `def` (`0` / `[propext]` axioms) + direct proof from `distincts` |
| Kernel `rfl` OEIS checks (`54`, `54`, `105` terms) | `a026837_oeis_54`, `a026838_oeis_54`, `a203568_oeis_105` | Proved in kernel (`rfl` + decoupled DP equivalence) |
| $N = 5$ polynomial & $+2 X^{11}$ collision | `c037Poly_five_and_coeff_11` | Proved in kernel |
| $N = 1, 2$ boundary & low-degree calibration | `c037_boundary_calibration` | Proved in kernel |

### 8.2 Recorded Trust, Axiom, Non-Vacuity, and Provenance Audit

1. **Artifact source digests bound to toolchain pin (`leanprover/lean4:v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, base `master` `a63c611f85afb848f43b78cae509dd47b6a47295`):**
   - Step 0 frozen statement stub (`Mathproofs/A203568RogersFineFamily.lean` at commit `501c82ec91a5cace871dd22133d9f2f337796406`, merged into `master` via PR #32 merge commit `6f2adbe9b438d46c582c49cdd9012f7bdf126f44`): SHA-256 `81ffa5649a10cee6be4b9402d47fbcbdee964773017f2e694ec831e04f785abc` (`lake build` exit `0`, `17,996` jobs; log SHA-256 `2b132bd20e0c816a60a2648c90d47dd1f133c17dbf3a86c3cdc2a922746b0bdd`).
   - Completed module `Mathproofs/A203568RogersFineFamily.lean` (`2,175` lines): SHA-256 `557d5472c2a1c0cb60138421531bd0f81f9d10d38ce9adcca2098379a2ec89d4` (**`0 diff chars`** across all 5 pinned definitions and all 8 pinned theorem signatures against `PIN-C037.md` v1 / Step 0; audit log SHA-256 `96eb7553a7f30dafcedb84157b9ab3b114d051f3bdf836c6f2a21af2dc270c0f`).
   - Root import barrel `Mathproofs.lean` (`90` lines; single line `import Mathproofs.A203568RogersFineFamily` appended at EOF): SHA-256 `84ab214c1ae3b645f958aeff949517c953162f689a229ce6364ae6c96ed8f059`.
   - `lakefile.toml` (`23` lines, unchanged from `master`): SHA-256 `12ca95376177738d3d2dc45c4bd083e78fbd80994d2447af3bf1201abec9eba9`.
   - Clean-slate full build (`rm -rf .lake/build && lake build`): exit `0` (`17,996` jobs; `0` errors, `0` sorries, `0` warnings on `Mathproofs.A203568RogersFineFamily`; log SHA-256 `5ee4780417cba49ae67ee842627a327256312e67a781ad51d4bb29d95e797257`).
2. **Axiom footprint (`#print axioms`), transitive closure, and kernel replay:**
   - Purely constructive DP definitions: `subsetSumCount` depends on **no axioms**; `a203568Compute` depends only on `[propext]`.
   - Every pinned declaration and theorem (`a026837`, `a026838`, `a203568`, `a203568Series`, `c037Poly`, `a203568_eq_pentagonal`, `c037Poly_closed_form`, `c037Poly_empirical_values`, `c037Poly_degree_and_monic`, `c036_a203568_gf`, `c037_a203568_family_explicit`, `c037_a203568_family`, `c037_a203568_family_exists`) and every Section 7 calibration theorem: `[propext, Classical.choice, Quot.sound]` (exact allowlist; log SHA-256 `6d15f87117f25c4fd2082be83c43c8e77ebf65ceab7f4d32728af17e488adbb7`).
   - `CoreM` transitive constant-closure audit (`allowOpaque := true`, `14,584` reachable constants): `AXIOMS_FOUND = [propext, Classical.choice, Quot.sound]`, `DISALLOWED_AXIOMS = []`, `HAS_SORRYAX = false`, `HAS_OFREDUCEBOOL = false`, `HAS_OFREDUCENAT = false`.
   - Comment/string-stripped lexical scan (`evidence/lexical_screen.py`) across `Mathproofs/A203568RogersFineFamily.lean`, `Mathproofs.lean`, and `Main.lean`: **`0` active hits** and **`0` raw hits** for `sorry`, `admit`, `sorryAx`, `axiom`, `native_decide`, `ofReduceBool`, `implemented_by`, `unsafe` (log SHA-256 `305448b58e7be73648b26c2921cf376963ba86a82c6a57e83f20a6f9370f55e1`).
   - Fresh-kernel replay (`lake env leanchecker --fresh --verbose Mathproofs.A203568RogersFineFamily`): **exit `0`** (`replaying Mathproofs.A203568RogersFineFamily with --fresh`; log SHA-256 `a9fa52825f2af0be0bbaa30e96d035cf9ae7fe6565fa3ab9beda6603a5bfe180`).
3. **Non-vacuity and computation boundary (stated explicitly):**
   - Because `a026837`, `a026838`, and `a203568` are defined inside a `noncomputable section` using classical `Finset.filter` over `Nat.Partition.distincts n` (and `Polynomial ℤ` in Mathlib is `noncomputable`), `a203568 n` does not reduce directly by bare `rfl` in Lean's kernel.
   - **Proved inside Lean's kernel without circularity:** In Section 7, we define a purely constructive $O(B^2)$ subset-sum dynamic-programming mirror (`distinctMaxParityDP`, `a026837Compute`, `a026838Compute`, `a203568Compute`) and prove `a026837_eq_compute`, `a026838_eq_compute`, and `a203568_eq_compute` **directly from `Nat.Partition.distincts`** (without touching `a203568_eq_pentagonal`, avoiding circularity). Rewriting by those equivalences and closing by kernel `rfl` verifies all `54` printed terms of `OEIS A026837` (`a026837_oeis_54`), all `54` printed terms of `OEIS A026838` (`a026838_oeis_54`), and all `105` printed terms of `OEIS A203568` (`a203568_oeis_105`), while symbolic `ring`/`simp` proofs inside the kernel verify `P(1)..P(4)` (`c037Poly_empirical_values`), `P(5, X)` and `[X^{11}] P(5, X) = 2` (`c037Poly_five_and_coeff_11`), and the $N = 1, 2$ boundary cases (`c037_boundary_calibration`).
   - **Verified via independent Python recomputation (not claimed as kernel `rfl` reductions):** `evidence/recompute_c037.py` independently re-derives `A026837`/`A026838`/`A203568` for $n = 0..200$, checks Links 1–4 through degree $500$, confirms the `b = -x^(-1)` discrepancy (`1 - x S_1(x)`), and verifies `C037` across $N = 1..20$ and degrees $0..500$ (`10,020` coefficient comparisons, `0` mismatches).
4. **Provenance and review status:**
   - Route (`Step 0 + Links 1–4`, including the positive-valuation Rogers–Fine parameter correction) derived and audited in Seam B scoping (`SCOPING-C037.md` §2.2, `carbon-c037-scoping-20261114`), target contract frozen in `PIN-C037.md` v1, and Lean 4 formalization authored in `carbon-c037-proof-20261116` (`nibbles`, Gemini 4 Carbon High; coordinator route-around on `derekblair/math-proofs#6`).
   - Crossed-review status: **COMPLETE — `PASS WITH ISSUES`** (`0` blocking findings, `4` non-blocking prose/citation findings addressed in this revision), performed by an independent fresh Gemini 4 Neon XHigh session on `dominic`; PR #32 merged into `master` on `2026-11-19` (merge commit `6f2adbe9b438d46c582c49cdd9012f7bdf126f44`, PR head `e23795a03b094ae22d5446acc335d9acd78071a4`).

---

## References

1. Michael Somos and Peter Bala, *OEIS Sequence A203568: $a(n) = A026837(n) - A026838(n)$* (authored by Michael Somos, January 3, 2012; `%F` formula and conjecture block by Peter Bala, February 11, 2021; revision `#52`, February 18, 2021), The On-Line Encyclopedia of Integer Sequences, https://oeis.org/A203568.
2. Michael Somos and Peter Bala, *OEIS Sequence A143062: Expansion of false theta series variation of Euler's pentagonal number series in powers of $x$* (revision `#58`, May 30, 2026), and Peter Bala, *OEIS Sequence A186424* (revision `#52`, December 29, 2025), The On-Line Encyclopedia of Integer Sequences, https://oeis.org/A143062 and https://oeis.org/A186424.
3. Clark Kimberling, *OEIS Sequence A026837: Number of partitions of $n$ into distinct parts, the greatest being odd* (revision `#20`, February 17, 2021), The On-Line Encyclopedia of Integer Sequences, https://oeis.org/A026837.
4. Clark Kimberling, *OEIS Sequence A026838: Number of partitions of $n$ into distinct parts, the greatest being even* (revision `#24`, February 17, 2021), The On-Line Encyclopedia of Integer Sequences, https://oeis.org/A026838.
5. Igor Pak, *On Fine's Partition Theorems, Dyson, Andrews, and Missed Opportunities*, Mathematical Intelligencer **25**(1) (2003), 10–16 (open-access author preprint inspected).
6. James McLaughlin, Andrew V. Sills, and Peter Zimmer, *Rogers–Ramanujan–Slater Type Identities*, Electronic Journal of Combinatorics, Dynamic Survey `#DS15` (2022), §5.0, pp. 37–38, https://www.combinatorics.org/DS15.
7. George E. Andrews, Mohamed El Bachraoui, Aritram Dhar, Ankush Goswami, and Runqiao Li, *Weighted partitions with interval restrictions: exact formulas and a bivariate master identity*, arXiv:2606.11011v1 [math.NT], 2026, §4.1.
8. Shishuo Fu and Dazhao Tang, *Partitions with fixed largest hook length*, arXiv:1604.04028v1 [math.CO], April 14, 2016, §4.2.
9. The mathlib Community, *The Lean Mathematical Library (`Mathlib4`)*, commit `d13f23b723b8a846827a245b89c10fc7d3f11612` (`v4.34.1`), 2026.
