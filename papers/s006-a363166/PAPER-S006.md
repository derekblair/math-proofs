# An MSB Row-Slice Bijection for Bounded Three-Heap Nim P-Positions: Proof and Lean 4 Formalization of Gómez Calderón's OEIS A363166 Conjecture

**Preprint Draft (`PAPER-S006.md`) — 2026-11-16**  
**Repository / Module:** `derekblair/math-proofs` (`SeamC/A363166/Statement.lean`, `namespace SeamC.A363166`, `702` lines, `SHA-256: 4b4f91d73bade307c04c559448ada91129a1542cccbf2db2bd7e5a093e71fa20`)  
**Toolchain & Mathlib Pin:** `leanprover/lean4:v4.34.1` (`Lake 5.0.0-src+5045d00`), Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`  
**Target Contract:** `PIN-S006.md` v1 (`SHA-256: dfd590c8394fb5aa532cf7720ba252dae51ac698aad08b2388f2e149985bd165`, `delta_vs_source: NONE`)

---

## Abstract

Let $a(n)$ (`OEIS A363166`, *Bouton numbers*, introduced by Peter Rowlett in July 2023) denote the number of unordered $\mathcal{P}$-positions ("safe combinations") in three-heap Nim with nonzero heap sizes at most $n$—equivalently, by Bouton's 1901 theorem, the number of integer triples $1 \le x \le y \le z \le n$ with bitwise Nim-sum $(x \oplus y) \oplus z = 0$. While Bouton (1901) determined the dyadic-cap special values $a(2^m - 1) = (2^m - 1)(2^m - 2)/6$ (`OEIS A006095`), the general all-$n$ count remained open until Alan Michael Gómez Calderón (`OEIS A363166`, `%F` line 17, September 18, 2025) conjectured that
$$a(n) = T_n - A_{063915}(n - 1) \qquad (n \ge 1),$$
where $T_n = n(n + 1)/2$ (`OEIS A000217`) is the $n$-th triangular number and $A_{063915}$ is the divide-and-conquer sequence with binary recurrence $A_{063915}(m) = b(m + 1)$, $b(0) = 0$, $b(1) = 1$, $b(2k) = 2b(k) + 2b(k - 1) + 1$, $b(2k + 1) = 4b(k) + 1$ (`%F` line 17) and Kevin Ryde's closed form $A_{063915}(m) = (m + 2)2^{\lfloor \log_2(m + 2) \rfloor} - (2 \cdot 4^{\lfloor \log_2(m + 2) \rfloor} + 1)/3$ (`%F` line 18).

We give an elementary, division-free bijective proof and a complete Lean 4 formalization of Gómez Calderón's identity for all $n \ge 1$, together with formal proofs of Ryde's closed form, the coefficient-level ordinary generating function of `A063915` (`%N` line 10), the power-of-two flat-step law $a(2^m) = a(2^m - 1)$, and Bouton's 1901 dyadic-cap formula. Rather than counting pairs with $x \oplus y > n$—a naive heuristic that evaluates to $\binom{n}{2} - 3a(n) \ne A_{063915}(n - 1)$ and vanishes identically at every Mersenne cap $n = 2^m - 1$—we partition the $T_n$ pairs $\mathcal{T}_n = \{(y, z) : 1 \le z \le n,\; 0 \le y < z\}$ row by row at the highest power of two $2^{\lfloor \log_2 z \rfloor} \le z$. For each fixed maximum heap $z \ge 1$, the map $y \mapsto (y \oplus z, y)$ is a bijection from the upper slice $[2^{\lfloor \log_2 z \rfloor}, z)$ onto the valid zero-XOR triples with largest heap $z$, while the complementary lower-slice sizes $2^{\lfloor \log_2 z \rfloor}$ (`OEIS A053644`) sum directly to $B(n) = \sum_{z=1}^n 2^{\lfloor \log_2 z \rfloor} = A_{063915}(n - 1)$. All theorems compile cleanly in Lean 4 without `sorry`, custom axioms, `native_decide`, or `ofReduceBool`.

---

## 1. Introduction and Primary-Source Context

### 1.1 Bouton Numbers (`OEIS A363166`) and Gómez Calderón's Conjecture

In the paper that named and solved the game of Nim, Charles L. Bouton [1] characterized the $\mathcal{P}$-positions ("safe combinations", in which the second player has a winning strategy under normal play) as the heap configurations whose binary digits sum to zero without carry—that is, whose bitwise exclusive-or ($\oplus$) vanishes. Because reducing any pile to zero sticks collapses three-heap Nim to the trivial two-heap game $(0, y, y)$, Bouton restricted his three-heap enumeration to **nonzero** piles and listed the $35$ unordered safe combinations with fewer than $16$ sticks per pile (`1 2 3` through `7 11 12` [1, §3, p. 37]). More generally, when each pile is bounded by $2^m - 1$, the set $\{1, \dots, 2^m - 1\} = \mathbb{F}_2^m \setminus \{0\}$ is closed under distinct XOR, so every unordered pair $\{x, y\}$ of distinct nonzero heaps determines a unique third nonzero heap $z = x \oplus y \notin \{x, y\}$ inside the same cap; dividing $\binom{2^m - 1}{2}$ by the $3$ pairs per triple yields Bouton's classical dyadic-cap formula [1, §3, p. 37]:
$$a(2^m - 1) = \frac{(2^{m - 1} - 1)(2^m - 1)}{3} = \frac{(2^m - 1)(2^m - 2)}{6} = \begin{bmatrix} m \\ 2 \end{bmatrix}_{q = 2} \qquad (m \ge 1),$$
which is the $q = 2$ Gaussian binomial coefficient sequence `OEIS A006095(m)` $(0, 1, 7, 35, 155, 651, \dots)$ [5].

For arbitrary heap caps $n \ge 1$, $\{1, \dots, n\}$ is no longer closed under XOR, and Peter Rowlett [2, 3] introduced `OEIS A363166` (*Bouton numbers*, July 6, 2023) as the number $a(n)$ of unordered three-heap Nim $\mathcal{P}$-positions with nonzero heaps at most $n$:
$$(a(n))_{n \ge 1} = (0, 0, 1, 1, 2, 4, 7, 7, 8, 10, 13, 17, 22, 28, 35, 35, 36, 38, 41, 45, \dots).$$
On September 18, 2025, Alan Michael Gómez Calderón posted the exact all-$n$ formula conjecture on `OEIS A363166` (`%F` line 17, live revision `#26`, September 23, 2025 [3]):

> **Conjecture (Alan Michael Gómez Calderón, September 18, 2025).** *For every $n \ge 1$,*
> $$a(n) = A_{000217}(n) - A_{063915}(n - 1),$$
> *where $A_{000217}(n) = n(n + 1)/2$ and $A_{063915}$ (`1, 3, 5, 9, 13, 17, 21, 29, \dots`, offset $0$) is N. J. A. Sloane's divide-and-conquer sequence [4] defined by*
> - *(`%N` line 10) ordinary generating function $\displaystyle\frac{1 + \sum_{i \ge 0} 2^i x^{2^{i+1} - 1}}{(1 - x)^2}$;*
> - *(`%F` line 17) binary recurrence $A_{063915}(m) = b(m + 1)$ with $b(0) = 0$, $b(1) = 1$, $b(2k) = 2b(k) + 2b(k - 1) + 1$, and $b(2k + 1) = 4b(k) + 1$ ($k \ge 1$); and*
> - *(`%F` line 18, Kevin Ryde, November 27, 2020) closed form $A_{063915}(m) = (m + 2)2^k - (2 \cdot 4^k + 1)/3$ where $k = \lfloor \log_2(m + 2) \rfloor$.*

*Provenance and Prior-Art Audit.* Live searches conducted across OEIS, arXiv (including full-text inspection of Hwang, Janson, and Tsai [6], which analyzes $A_{063915}$ purely as a divide-and-conquer sum without Nim or XOR), Crossref, Zenodo, MathOverflow, Mathematics Stack Exchange, and primary sources (`SCOPING-S006.md` §3, `2026-11-15`; extended coordinator checks `2026-11-16`) confirmed that Gómez Calderón's all-$n$ conjecture is unproved in the literature. Scoping also corrected two bibliographic misattributions from an earlier triage note: `OEIS A363166` has only a single `%F` line (`%F` line 17; line 16 is the `%H` link to Bouton 1901), and Bouton's dyadic-cap sequence $(2^m - 1)(2^m - 2)/6$ is `OEIS A006095(m)`, whereas `OEIS A007583(k)` $= (2 \cdot 4^k + 1)/3$ is the subtrahend inside Ryde's closed form for $A_{063915}$.

### 1.2 Summary of Formalized Results

In `SeamC/A363166/Statement.lean` (`namespace SeamC.A363166`), following the 6-step scoping blueprint (`SCOPING-S006.md` §2.2), we formalize and prove:

- **Theorem 1.1 (Primary Identity — `SeamC.A363166.nim_triples_add_a063915_eq_triangular`).** *For every $n \in \mathbb{N}$ with $1 \le n$,*
  $$\mathrm{nimTriples}(n) + \mathrm{a063915}(n - 1) = \frac{n(n + 1)}{2}.$$
- **Theorem 1.2 (Kevin Ryde Closed Form — `SeamC.A363166.a063915_eq_closed_form`).** *For every $m \in \mathbb{N}$, letting $k = \lfloor \log_2(m + 2) \rfloor$ (`Nat.log 2 (m + 2)`),*
  $$3 \cdot \mathrm{a063915}(m) + (2 \cdot 4^k + 1) = 3(m + 2)2^k \quad \text{and} \quad \mathrm{a063915}(m) = (m + 2)2^k - \frac{2 \cdot 4^k + 1}{3}.$$
- **Corollary 1.3 (Closed-Form Nim Identity — `SeamC.A363166.nim_triples_add_closed_form_eq_triangular`).** *For every $n \in \mathbb{N}$ with $1 \le n$, letting $k = \lfloor \log_2(n + 1) \rfloor$,*
  $$\mathrm{nimTriples}(n) + \left((n + 1)2^k - \frac{2 \cdot 4^k + 1}{3}\right) = \frac{n(n + 1)}{2}.$$
- **Theorem 1.4 (Core MSB Row-Slice Bijection — `SeamC.A363166.msb_xor_slice_bij`).** *For every $z \ge 1$ with $r = \lfloor \log_2 z \rfloor$, the map $y \mapsto ((y \oplus z, y), z)$ is a bijection from $[2^r, z)$ onto the $z$-maximal fiber of valid Nim triples, which therefore has cardinality $z - 2^{\lfloor \log_2 z \rfloor}$ (`OEIS A053645(z)`).*
- **Theorem 1.5 (`%N` OGF Coefficient Identity, Flat Steps, Bouton Cap, & Sketch Refutation — `a063915_eq_ogf_coeff`, `nimTriples_two_pow_eq_pred`, `nimTriples_mersenne_eq_bouton`, `refute_intake_xor_gt_sketch`).** *For all $m \ge 0$, $[x^m]\bigl((1 + \sum_{i \ge 0} 2^i x^{2^{i+1} - 1})/(1 - x)^2\bigr) = \mathrm{a063915}(m)$; for all $m \ge 1$, $\mathrm{nimTriples}(2^m) = \mathrm{nimTriples}(2^m - 1)$ and $6 \cdot \mathrm{nimTriples}(2^m - 1) = (2^m - 1)(2^m - 2)$; and at $n = 3$, $\#\{1 \le x \le y \le 3 : x \oplus y > 3\} = 0 \ne 5 = \mathrm{a063915}(2)$.*

---

## 2. Formal Specification and Why the Naive $x \oplus y > n$ Heuristic Fails

### 2.1 Pinned Lean 4 Definitions (`PIN-S006.md` v1)

Per `OEIS A363166` (`%N` line 10, `%C` lines 12–13, `%e` line 20, and Rowlett's `%o` Python reference `combinations_with_replacement(range(1, n+1), 3)`), heaps are indistinguishable and nonzero. We therefore represent unordered triples canonically as sorted tuples $((x, y), z)$ in the three-fold Cartesian product of `Finset.Icc 1 n`, and define `a063915` directly from the literal `%F` line 17 binary recurrence:

```lean
def nimTriples (n : ℕ) : ℕ :=
  (((Finset.Icc 1 n ×ˢ Finset.Icc 1 n) ×ˢ Finset.Icc 1 n).filter
    (fun ((x, y), z) => x ≤ y ∧ y ≤ z ∧ Nat.xor (Nat.xor x y) z = 0)).card

def a063915Aux : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    if (n + 2) % 2 = 0 then
      2 * a063915Aux ((n + 2) / 2) + 2 * a063915Aux ((n + 2) / 2 - 1) + 1
    else
      4 * a063915Aux ((n + 2) / 2) + 1

def a063915 (m : ℕ) : ℕ :=
  a063915Aux (m + 1)
```

Three design invariants prevent vacuity or semantic drift:
1. **Unordered vs. ordered counting:** Because every nonzero zero-XOR triple satisfies strict $x < y < z$ (Lemma 3.1), counting ordered triples in $\{1, \dots, n\}^3$ would multiply $a(n)$ by $3! = 6$.
2. **Nonzero heaps ($1 \le x$):** Allowing $x = 0$ would inject the $n + 1$ degenerate two-heap/empty positions $(0, y, y)$ for $0 \le y \le n$.
3. **Truncation-free $\mathbb{N}$ arithmetic at $n = 1$:** Writing $\mathrm{nimTriples}(n) + \mathrm{a063915}(n - 1) = n(n + 1)/2$ for $1 \le n$ avoids $\mathbb{N}$ truncating subtraction while remaining equivalent to subtraction because $n(n + 1)$ is always even (`mul_succ_mod_two`). At $n = 1$, the sole candidate $((1, 1), 1)$ has $(1 \oplus 1) \oplus 1 = 1 \ne 0$, so $\mathrm{nimTriples}(1) = 0$, $\mathrm{a063915}(0) = 1$, and $0 + 1 = 1 \cdot 2 / 2$.

### 2.2 Refutation of the Naive $x \oplus y > n$ Sketch

Seeing $a(n) = T_n - A_{063915}(n - 1)$ with $T_n = \#\{(x, y) : 1 \le x \le y \le n\}$, it is tempting to guess that $A_{063915}(n - 1)$ counts pairs $1 \le x \le y \le n$ whose XOR overflows the cap ($x \oplus y > n$). **That guess is arithmetically false for every $n \ge 1$** (`SCOPING-S006.md` §2.1):

- The $n$ diagonal pairs $x = y$ have $x \oplus x = 0 \le n$.
- Among the $\binom{n}{2}$ strict pairs $1 \le x < y \le n$, each valid unordered zero-XOR triple $\{x, y, z\} \subseteq \{1, \dots, n\}$ contributes **three** pairs $(x, y)$, $(x, z)$, and $(y, z)$ whose XOR lies in $\{1, \dots, n\}$, while every pair with $x \oplus y > n$ contributes zero.
- Consequently,
  $$\#\{(x, y) : 1 \le x \le y \le n,\; x \oplus y > n\} = \binom{n}{2} - 3\,a(n) = T_n - n - 3\,a(n) \ne A_{063915}(n - 1).$$

In particular, at every Mersenne cap $n = 2^m - 1$, $\{1, \dots, 2^m - 1\}$ is closed under XOR, so $\#\{1 \le x \le y \le 2^m - 1 : x \oplus y > 2^m - 1\} = 0$, whereas $A_{063915}(2^m - 2) = (4^m - 1)/3$ ($1, 5, 21, 85, \dots$ for $m = 1, 2, 3, 4, \dots$). At $n = 3$, Lean's kernel directly verifies `refute_intake_xor_gt_sketch`: the overflow-pair count is $0$, while $\mathrm{a063915}(2) = 5$.

Instead of counting overflow pairs and dividing by $3$, indexing the $T_n$ pairs as $0 \le y < z \le n$ (`OEIS A000217` `%C` line 23) singles out each triple **uniquely by its largest heap $z$** and its middle heap $y$, yielding a direct, division-free row-by-row bijection.

---

## 3. The MSB Row-Slice Bijection (Steps 1–4)

### 3.1 Step 1: Strict Heap Inequalities (`strict_lt_of_xor_zero`)

Because $\oplus$ is associative, commutative, and self-inverse on $\mathbb{N}$ (`xor_eq_zero_iff_eq`, `xor_triple_eq_zero_iff`, `eq_xor_of_xor_triple_eq_zero`), $(x \oplus y) \oplus z = 0$ holds if and only if $z = x \oplus y$ (and symmetrically $x = y \oplus z$).

**Lemma 3.1 (`strict_lt_of_xor_zero`).** *If $1 \le x \le y \le z$ and $(x \oplus y) \oplus z = 0$, then $x < y < z$, $x = y \oplus z$, and $z = x \oplus y$.*

*Proof.* If $x = y$, then $z = x \oplus x = 0$, contradicting $1 \le x \le z$. If $y = z$, then $x = y \oplus y = 0$, contradicting $1 \le x$. $\square$

### 3.2 Step 2: Canonical Triangular Pair Model (`card_triangularPairs`)

Define the triangular index set
$$\mathcal{T}_n := \{(y, z) \in \mathbb{N}^2 : 1 \le z \le n,\; 0 \le y < z\}.$$
Row $z$ ($1 \le z \le n$) contains $|\{0, 1, \dots, z - 1\}| = z$ pairs, so $|\mathcal{T}_n| = \sum_{z=1}^n z = n(n + 1)/2$ (`sum_Icc_one_id`, `card_triangularPairs`).

### 3.3 Step 3: Core Lemma — The MSB Row-Slice Bijection (`msb_xor_slice_bij`)

Fix a maximum heap $z \ge 1$ and let $r = \lfloor \log_2 z \rfloor$ (`Nat.log 2 z`), so that $2^r \le z < 2^{r+1}$. Split row $z$ of $\mathcal{T}_n$ at $2^r$ into an upper slice and a lower slice:
$$\mathcal{T}_z^+ := [2^r, z) \quad (|\mathcal{T}_z^+| = z - 2^r), \qquad \mathcal{T}_z^- := [0, 2^r) \quad (|\mathcal{T}_z^-| = 2^r).$$
Let $\mathcal{P}_z$ (`maxFiber z`) be the finite set of valid sorted triples $((x, y), z')$ with largest heap $z' = z$, $1 \le x \le y \le z$, and $(x \oplus y) \oplus z = 0$.

To reason cleanly about `Nat.xor` and `Nat.log 2` in Lean without relying on bitblasting, we establish two general bit-level lemmas:
1. **`testBit_eq_true_of_mem_dyadic`:** Whenever $2^r \le n < 2^{r+1} = 2 \cdot 2^r$, integer division gives $\lfloor n / 2^r \rfloor = 1$, so bit $r$ of $n$ is `true`.
2. **`lt_two_pow_of_testBit_false`:** If `x.testBit j = false` for every $j \ge r$, then $x < 2^r$ (otherwise $x \ge 2^r > 0$ has $k := \lfloor \log_2 x \rfloor \ge r$ with $2^k \le x < 2^{k+1}$, forcing `x.testBit k = true`).

**Theorem 3.2 (`msb_xor_slice_bij`).** *For every $z \ge 1$ with $r = \lfloor \log_2 z \rfloor$, the map $\Phi_z : y \mapsto ((y \oplus z, y), z)$ is a bijection from $\mathcal{T}_z^+ = [2^r, z)$ onto $\mathcal{P}_z$. Consequently, $|\mathcal{P}_z| = z - 2^{\lfloor \log_2 z \rfloor}$.*

*Proof.*
- **Forward well-definedness (`xor_lt_two_pow_log`):** Take $y \in [2^r, z)$ and set $x := y \oplus z$. Since $2^r \le y < z < 2^{r+1}$, both $y$ and `z` lie in $[2^r, 2^{r+1})$. For $j = r$, `y.testBit r = true` and `z.testBit r = true`, so `x.testBit r = bne true true = false`. For $j > r$, $y < z < 2^{r+1} \le 2^j$, so `Nat.testBit_eq_false_of_lt` gives `y.testBit j = false` and `z.testBit j = false`, whence `x.testBit j = false`. By `lt_two_pow_of_testBit_false`, $x < 2^r \le y < z$. Moreover, $y < z$ implies $y \ne z$, so $x = y \oplus z \ge 1$, and $((y \oplus z) \oplus y) \oplus z = 0$ (`xor_cancel_triple`). Thus $\Phi_z(y) \in \mathcal{P}_z$.
- **Injectivity:** Immediate from the second coordinate $((y \oplus z, y), z) \mapsto y$.
- **Surjectivity (`two_pow_log_le_of_xor_zero`):** Let $((x, y), z) \in \mathcal{P}_z$. By Lemma 3.1, $1 \le x < y < z$ and $x = y \oplus z$ with $z = x \oplus y$. Suppose toward contradiction that $y < 2^r$. Then $x < y < 2^r$, so `x.testBit r = false` and `y.testBit r = false`, forcing `z.testBit r = bne false false = false`—contradicting $2^r \le z < 2^{r+1}$ (`z.testBit r = true`). Hence $2^r \le y < z$, so $y \in \mathcal{T}_z^+$ and $\Phi_z(y) = ((x, y), z)$. $\square$

### 3.4 Step 4: Row-Sum Partition and Combinatorial Meaning of $B(n)$

Partitioning `nimTripleSet (n + 1) = nimTripleSet n ∪ maxFiber (n + 1)` into disjoint sets (`z ≤ n` vs. `z = n + 1`) and applying Theorem 3.2 yields the first-difference law (`nimTriples_succ`)
$$a(n + 1) - a(n) = (n + 1) - 2^{\lfloor \log_2(n + 1) \rfloor} = A_{053645}(n + 1), \qquad a(n) = \sum_{z = 1}^n \bigl(z - 2^{\lfloor \log_2 z \rfloor}\bigr).$$
Defining the MSB partial sum $B(n) := \sum_{z = 1}^n 2^{\lfloor \log_2 z \rfloor}$ (`msbSum n`), since $2^{\lfloor \log_2 z \rfloor} \le z$ for every $z \ge 1$, summing row by row immediately gives (`nimTriples_add_msbSum_eq_triangular`):
$$a(n) + B(n) = \sum_{z = 1}^n \bigl(z - 2^{\lfloor \log_2 z \rfloor}\bigr) + \sum_{z = 1}^n 2^{\lfloor \log_2 z \rfloor} = \sum_{z = 1}^n z = \frac{n(n + 1)}{2}.$$

*Combinatorial interpretation of the $B(n)$ excluded pairs.* In each row $z$, the lower slice $\mathcal{T}_z^- = [0, 2^{\lfloor \log_2 z \rfloor})$ of size $2^{\lfloor \log_2 z \rfloor}$ consists of:
1. $y = 0$ ($1$ pair per row, $n$ total): the excluded zero-heap two-pile position $(0, z, z)$; and
2. $1 \le y < 2^{\lfloor \log_2 z \rfloor}$ ($2^{\lfloor \log_2 z \rfloor} - 1$ pairs per row): pairs whose XOR partner $x := y \oplus z$ retains bit $r = 1$, so $x \ge 2^r > y$, violating canonical order $x \le y \le z$ either because $y \oplus z > n$ (heap exceeds cap) or because $y < y \oplus z \le n$ (an out-of-order copy of a valid triple already counted once in its sorted row $\max(z, y \oplus z)$).

---

## 4. Binary Recurrence, Ryde's Closed Form, OGF, and Classical Corollaries (Steps 5–6)

### 4.1 Step 5: Bridging $B(n)$ to the `OEIS A063915` Binary Recurrence (`a063915Aux_eq_msbSum`)

For every $j \ge 1$, `Nat.log_of_one_lt_of_le` gives $\lfloor \log_2(2j) \rfloor = \lfloor \log_2(2j + 1) \rfloor = \lfloor \log_2 j \rfloor + 1$, so
$$2^{\lfloor \log_2(2j) \rfloor} = 2^{\lfloor \log_2(2j + 1) \rfloor} = 2 \cdot 2^{\lfloor \log_2 j \rfloor} \qquad (\text{`two\_pow\_log\_two\_mul`},\; \text{`two\_pow\_log\_two\_mul\_add\_one`}).$$
By induction on $k \ge 0$, stepping from $2k + 1$ to $2(k + 1) + 1$ appends $2(k + 1)$ and $2(k + 1) + 1$, adding $2 \cdot 2^{\lfloor \log_2(k+1) \rfloor} + 2 \cdot 2^{\lfloor \log_2(k+1) \rfloor} = 4 \cdot 2^{\lfloor \log_2(k+1) \rfloor}$:
$$B(2k + 1) = 4\,B(k) + 1 \qquad (\text{`msbSum\_two\_mul\_add\_one`}).$$
For $k \ge 1$, subtracting the last summand $2^{\lfloor \log_2(2k + 1) \rfloor} = 2 \cdot 2^{\lfloor \log_2 k \rfloor} = 2\bigl(B(k) - B(k - 1)\bigr)$ yields
$$B(2k) = 4\,B(k) + 1 - 2\bigl(B(k) - B(k - 1)\bigr) = 2\,B(k) + 2\,B(k - 1) + 1 \qquad (\text{`msbSum\_two\_mul`}).$$
Since $B(0) = 0 = \mathrm{a063915Aux}(0)$ and $B(1) = 1 = \mathrm{a063915Aux}(1)$, strong induction on $n$ proves $\mathrm{a063915Aux}(n) = B(n)$ for all $n \in \mathbb{N}$ (`a063915Aux_eq_msbSum`). Substituting $\mathrm{a063915}(n - 1) = \mathrm{a063915Aux}(n) = B(n)$ for $n \ge 1$ into Step 4 completes **Theorem 1.1** (`nim_triples_add_a063915_eq_triangular`).

### 4.2 Step 6: Kevin Ryde's Closed Form, Exact Division by $3$, and `%N` OGF

1. **Exact divisibility modulo $3$ (`three_dvd_two_mul_four_pow_add_one`):** By induction on $k$, $2 \cdot 4^0 + 1 = 3$ and $2 \cdot 4^{k+1} + 1 = (2 \cdot 4^k + 1) + 3(2 \cdot 4^k)$, so $3 \mid (2 \cdot 4^k + 1)$ for all $k \in \mathbb{N}$.
2. **Closed-form induction across the dyadic jump (`three_mul_msbSum_closed_form`):** We prove by induction on $n \ge 0$ that for $k = \lfloor \log_2(n + 1) \rfloor$,
   $$3\,B(n) + (2 \cdot 4^k + 1) = 3(n + 1)\,2^k.$$
   At $n = 0$ ($k = 0$), $3 \cdot 0 + 3 = 3 \cdot 1 \cdot 1$. For $n \to n + 1$, let $k' = \lfloor \log_2(n + 1) \rfloor$ and $k = \lfloor \log_2(n + 2) \rfloor$. Because $B(n + 1) = B(n) + 2^{k'}$ uses the **same** exponent $k'$ as the induction hypothesis,
   $$3\,B(n + 1) + (2 \cdot 4^{k'} + 1) = 3(n + 1)\,2^{k'} + 3 \cdot 2^{k'} = 3(n + 2)\,2^{k'}.$$
   Since $2^{k'} \le n + 1 < 2^{k' + 1}$, we have $n + 2 \le 2^{k' + 1}$:
   - If $n + 2 < 2^{k' + 1}$, then $k = k'$ (`Nat.log_eq_of_pow_le_of_lt_pow`) and the equation stands unchanged.
   - If $n + 2 = 2^{k' + 1}$ (the Mersenne-to-dyadic jump), then $k = k' + 1$ and $n + 2 = 2 \cdot 2^{k'}$. Writing $p = 2^{k'}$, adding $6p^2 = 2 \cdot 4^{k' + 1} - 2 \cdot 4^{k'}$ to $3\,B(n + 1) + (2p^2 + 1) = 6p^2$ yields $3\,B(n + 1) + (2 \cdot 4^{k' + 1} + 1) = 12p^2 = 3(2p)(2p) = 3(n + 2)2^k$ purely over $\mathbb{N}$ without subtraction.
   Setting $n = m + 1$ and dividing by $3$ using $3 \mid (2 \cdot 4^k + 1)$ proves **Theorem 1.2** (`a063915_eq_closed_form`) and **Corollary 1.3** (`nim_triples_add_closed_form_eq_triangular`).
3. **Coefficient-level `%N` OGF identity (`a063915_eq_ogf_coeff`):** For each $j \ge 0$, $2^{i+1} - 1 \le j \iff i < \lfloor \log_2(j + 1) \rfloor$, so $[x^j]\bigl((1 + \sum_{i \ge 0} 2^i x^{2^{i+1} - 1})/(1 - x)\bigr) = 1 + \sum_{i < \lfloor \log_2(j + 1) \rfloor} 2^i = 2^{\lfloor \log_2(j + 1) \rfloor}$. Accumulating a second prefix sum over $0 \le j \le m$ yields $B(m + 1) = \mathrm{a063915}(m)$.
4. **Power-of-two flat steps & Bouton's 1901 dyadic cap (`nimTriples_two_pow_eq_pred`, `nimTriples_mersenne_eq_bouton`):** At $n = 2^m$ ($m \ge 1$), $\lfloor \log_2(2^m) \rfloor = m$, so the upper slice $[2^m, 2^m)$ is empty and $a(2^m) = a(2^m - 1)$, explaining the flat steps $(7, 7), (35, 35), (155, 155), (651, 651), \dots$ in `A363166`. At $n = 2^m - 1$, combining Theorems 1.1 and 1.2 recovers $6\,a(2^m - 1) = (2^m - 1)(2^m - 2)$ for all $m \ge 1$.

---

## 5. Verification Record, Strength Delta, and Scope Boundary

### 5.1 Formal Verification Gates

All gates were executed under `leanprover/lean4:v4.34.1` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`:

| Gate | Exact Command | Result |
| :--- | :--- | :--- |
| Step 0 stub gate | `cd repo && lake build` | `exit 0` (`17,984` jobs; staged `PIN-S006.md` v1 stub compiled cleanly) |
| Clean-slate build | `cd repo && rm -rf .lake/build && lake build` | `exit 0` (`17,984` jobs; `0` errors / `0` sorries / `0` warnings on `SeamC/A363166/Statement.lean`) |
| Axiom allowlist + closure | `cd repo && lake env lean ../evidence/check_axioms_and_closure.lean` | `exit 0` (`[propext, Classical.choice, Quot.sound]` only across `5,093` transitive constants; `sorryAx=false`, `ofReduceBool=false`, `ofReduceNat=false`, `trustCompiler=false`) |
| Fresh-kernel replay | `cd repo && lake env leanchecker --fresh --verbose SeamC.A363166.Statement` | `exit 0` (`replaying SeamC.A363166.Statement with --fresh`) |
| Lexical trust-escape screen | `python3 evidence/lexical_screen.py` | `exit 0` (`0` active hits and `0` raw hits across `SeamC/A363166/Statement.lean`, `Mathproofs.lean`, `Main.lean`) |
| Pin fidelity & non-vacuity | `python3 evidence/check_pin_fidelity.py && python3 evidence/verify_s006_lane.py` | `exit 0` (`0` diff chars vs. Step 0 contract; `0` mismatches across `O(n^3)` `1..160`, `O(n^2)` `1..1024`, row bijection `1..512`, `A063915` 4-way `0..50000`) |

### 5.2 Non-Vacuity Boundary (Kernel Reduction vs. VM `#eval` and Python Recomputation)

Because `Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n` carries `Multiset.Nodup` proof terms over `Quot`, direct `rfl` unfolding of `nimTriples n` hits Lean's `maxRecDepth` for moderate $n$, while `a063915Aux` compiles via well-founded recursion (`WellFounded.fix`). We state the exact kernel/VM boundary explicitly:
- **Proved in the Lean 4 kernel (`0` sorries, `0` `native_decide`, `0` `ofReduceBool`):**
  1. Direct kernel `rfl` on the literal pinned `nimTriples` verifies `nimTriples 1 = 0`, `nimTriples 2 = 0`, `nimTriples 3 = 1`, and `nimTriples 4 = 1`, while kernel equation-lemma reduction verifies `a063915` on `m = 0..31` (`literal_kernel_boundary_checks`).
  2. A pure `Nat`-structural-recursion mirror `nimTriplesFast` is formally proved equal to `nimTriples` for all $n \in \mathbb{N}$ directly from `strict_lt_of_xor_zero` and `maxFiber` **without using Theorem 1.1** (`nimTriplesFast_eq_nimTriples`); kernel `rfl` on `nimTriplesFast` then transfers all $32$ values `nimTriples (1..32) = [0, 0, 1, 1, 2, 4, 7, 7, 8, 10, 13, 17, 22, 28, 35, 35, 36, 38, 41, 45, 50, 56, 63, 71, 80, 90, 101, 113, 126, 140, 155, 155]` and flat steps `(nimTriples (2^m), nimTriples (2^m - 1))` for `m = 1..6` (`n ≤ 64`, reaching `(651, 651)`) onto the pinned `SeamC.A363166.nimTriples` (`nimTriples_spot_checks_1_to_32`).
  3. Furthermore, `nimTriples_two_pow_eq_pred` and `nimTriples_mersenne_eq_bouton` are kernel-proved universally for **every** $m \ge 1$.
- **Evaluated via Lean VM `#eval` and independent Python recomputation (not claimed as kernel `rfl`):** Lean VM `#eval` directly evaluates the literal `Finset` `nimTriples` on `1..32`, `nimTriplesFast` on all `65` printed `A363166` terms (`1..65`), and `a063915` on all `55` printed `A063915` terms (`0..54`); `verify_s006_lane.py` independently checks $O(n^3)$ enumeration (`1..160`), $O(n^2)$ enumeration (`1..1024`), element-wise row bijections (`1..512`), and 4-way `A063915` equivalence (`0..50,000`) with `0` mismatches.

### 5.3 Strength Delta and What This Note Does NOT Show

- **Strength delta vs. source (`PIN-S006.md` v1):** **`NONE` (`equal`).** Theorems 1.1–1.2 and Corollary 1.3 prove Alan Michael Gómez Calderón's `OEIS A363166` `%F` line 17 conjecture and Kevin Ryde's `OEIS A063915` `%F` line 18 closed form unconditionally across their full domains ($n \ge 1$ and $m \ge 0$), written additively on $\mathbb{N}$ solely to avoid truncating-subtraction artifacts.
- **What this does NOT show:** Following Bouton [1] and `OEIS A363166` (`%C` line 13, `%o` lines 22–34), three-heap Nim $\mathcal{P}$-positions are formalized directly via their zero-Nim-sum condition `(x ⊕ y) ⊕ z = 0` rather than an extensive-form impartial game tree or Sprague–Grundy formalization in Lean. Likewise, this note does not derive enumerative formulas for $k$-heap Nim with $k \ge 4$ piles (cf. `OEIS A048833`, `A233810`), formal power-series ring identities in `PowerSeries ℚ` (Theorem 1.5 proves the exact coefficient-level identity of `A063915` `%N` line 10), or complex-analytic Mellin–Perron asymptotics of divide-and-conquer sums [6].

---

## References

1. C. L. Bouton, *Nim, A Game with a Complete Mathematical Theory*, Annals of Mathematics, Second Series, **3**(1/4) (1901), 35–39, https://doi.org/10.2307/1967631.
2. P. Rowlett, *Added a sequence to the OEIS: Bouton numbers (A363166)*, The Aperiodical, August 6, 2023.
3. P. Rowlett and A. M. Gómez Calderón, Sequence `A363166` (*Bouton numbers: $a(n)$ is the number of P positions in games of Nim with three nonzero heaps each containing at most $n$ sticks*), in *The On-Line Encyclopedia of Integer Sequences* (OEIS), July 6, 2023; formula conjecture September 18, 2025; live revision `#26`, September 23, 2025, https://oeis.org/A363166.
4. N. J. A. Sloane, R. Stephan, and K. Ryde, Sequence `A063915` (*Expansion of g.f. $(1 + \sum_{i \ge 0} 2^i x^{2^{i+1} - 1})/(1 - x)^2$*), Sequence `A053644` (*Most significant bit*), Sequence `A053645` (*Distance to largest power of $2 \le n$*), and Sequence `A000217` (*Triangular numbers*), in *The On-Line Encyclopedia of Integer Sequences* (OEIS), https://oeis.org/A063915, https://oeis.org/A000217.
5. N. J. A. Sloane and I. Duff, Sequence `A006095` (*Gaussian binomial coefficient $[n, 2]$ for $q = 2$*) and Sequence `A007583` (*$(2^{2n+1} + 1)/3$*), in *The On-Line Encyclopedia of Integer Sequences* (OEIS), https://oeis.org/A006095, https://oeis.org/A007583.
6. H.-K. Hwang, S. Janson, and T.-H. Tsai, *Identities and periodic oscillations of divide-and-conquer recurrences splitting at half*, arXiv:2210.10968 [cs.DS], 2022.
7. The mathlib Community, *The Lean Mathematical Library* (`Mathlib.Data.Nat.Bitwise`, `Mathlib.Data.Nat.Log`, `Mathlib.Order.Interval.Finset.Nat`), `v4.34.1` (`d13f23b723b8a846827a245b89c10fc7d3f11612`), 2026.
