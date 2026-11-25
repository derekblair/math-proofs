# A Sign-Reversing Color-Parity Involution and Halving Bijection for `{0,1}`-Colored Partitions: Proof and Lean 4 Formalization of Thomas Hutton's OEIS A392002 Conjecture

**Preprint Draft (`PAPER-S001.md`) — 2026-11-16**  
**Repository / Module:** `derekblair/math-proofs` (`Mathproofs/A392002TwoColorPartition.lean`, `namespace SeamC.A392002`)  
**Toolchain & Mathlib Pin:** `leanprover/lean4:v4.34.1` (`Lake 5.0.0-src+5045d00`), Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`  
**Target Contract:** `PIN-S001.md` v1 (`SHA-256: 2580ee3655551af8ca11a7901a1b646d0e3ded6e9d8288566111df03344e4bb6`, `delta_vs_source: NONE`)

---

## Abstract

Let $a(n)$ (`OEIS A392002`, authored by Thomas Hutton, December 26, 2025) denote the number of $2$-colored integer partitions of $n \ge 0$ with colors in $\{0, 1\}$ whose color sum—the number of $1$-colored parts—is odd, let $p_2(n)$ (`OEIS A000712`) denote the total number of $2$-colored partitions of $n$, and let $p(n)$ (`OEIS A000041`) denote the ordinary partition function. In `OEIS A392002` (`%F` lines 12–13, live revision `#11`, January 1, 2026), Hutton conjectured the ordinary generating-function identity
$$\sum_{n \ge 0} a(n) x^n = \frac{1}{2}\left(\prod_{j \ge 1} \frac{1}{(1 - x^j)^2} - \prod_{j \ge 1} \frac{1}{1 - x^{2j}}\right) = \frac{1}{2}\bigl(A_{000712}(x) - A_{000041}(x^2)\bigr).$$
We give a self-contained bijective proof and a complete Lean 4 formalization of the exact coefficient-level identity
$$2 a(n) = p_2(n) - \begin{cases} p(n/2), & \text{if } 2 \mid n, \\ 0, & \text{if } 2 \nmid n, \end{cases} \qquad \text{for all } n \ge 0.$$
Our proof constructs an explicit two-stage sign-reversing involution on $\{0, 1\}$-colored partitions of $n$: off the all-even-total-multiplicity locus, Stage 1 swaps $(m_{j,0}, m_{j,1}) \mapsto (m_{j,1}, m_{j,0})$ at the least part size $j$ with $m_{j,0} + m_{j,1}$ odd; on the locus where $2 \mid (m_{j,0} + m_{j,1})$ for every $j$, Stage 2 pairs nonzero $1$-colored multiplicities $\{1, 2\}, \{3, 4\}, \dots, \{2k_j - 1, 2k_j\}$ at the least $j$ with $m_{j,1} > 0$. Every non-fixed partition flips color-sum parity, while the true fixed points are precisely the all-$0$-colored partitions in which every part multiplicity is even—counted via an explicit halving bijection by $p(n/2)$ when $n$ is even and $0$ when $n$ is odd. We also prove equivalence in Lean's kernel between the pair-of-partitions and colored-multiset (`Multiset (ℕ+ × Fin 2)`) models, construct a structural-recursion bounded-part DP mirror proved equal to $a(n)$ independently of the main theorem for kernel `rfl` verification of `n = 0..12`, and formalize why conflating the color sum $\operatorname{length}(\lambda^{(1)})$ with the size sum $|\lambda^{(1)}|$ agrees at $n = 0$ and all odd $n$ while failing at every positive even $n$. All proofs compile cleanly in Lean 4 without `sorry`, custom axioms, `native_decide`, or `ofReduceBool`.

---

## 1. Introduction and Primary-Source Context

### 1.1 `{0,1}`-Colored Partitions and `OEIS A392002`

A **$2$-colored partition** (here $\{0, 1\}$-colored partition) of a nonnegative integer $n$ is a way of writing $n$ as an unordered sum of positive integers in which each summand carries a color $c \in \{0, 1\}$: parts of equal size and distinct colors are distinguished, whereas parts of equal size and equal color are indistinguishable. Equivalently, a $\{0, 1\}$-colored partition of $n$ is either:

1. a finite multiset of pairs $(s, c) \in \mathbb{N}_+ \times \{0, 1\}$ satisfying $\sum_{(s, c)} s = n$, or
2. an ordered pair of ordinary integer partitions $(\lambda^{(0)}, \lambda^{(1)})$ of nonnegative integers $(k_0, k_1)$ with $k_0 + k_1 = n$, where $\lambda^{(0)}$ collects the $0$-colored parts and $\lambda^{(1)}$ collects the $1$-colored parts.

The total number of $\{0, 1\}$-colored partitions of $n$ is the classical sequence $p_2(n)$ (`OEIS A000712`), with ordinary generating function $\prod_{j \ge 1} (1 - x^j)^{-2}$ and convolution formula $p_2(n) = \sum_{k=0}^n p(k)\,p(n - k)$, where $p(n)$ (`OEIS A000041`) is the number of ordinary partitions of $n$.

In `OEIS A392002` (submitted December 26, 2025; live revision `#11` dated January 1, 2026 [1]), Thomas Hutton introduced the sequence $a(n)$ counting $\{0, 1\}$-colored partitions of $n$ whose **colors sum to an odd integer**, i.e., for which $\sum_{(s,c)} c = \operatorname{length}(\lambda^{(1)}) \equiv 1 \pmod{2}$, beginning
$$(a(n))_{n \ge 0} = (0, 1, 2, 5, 9, 18, 31, 55, 90, 150, 237, 376, 577, \dots),$$
and recorded the two equivalent generating-function conjectures (`%F` lines 12–13 [1]):

> **Conjecture (Thomas Hutton, December 26, 2025).** *For `OEIS A392002`:*
> 1. *Conjectured g.f.:* $\dfrac{1}{2}\left(\displaystyle\prod_{j \ge 1} \frac{1}{(1 - x^j)^2} - \prod_{j \ge 1} \frac{1}{1 - x^{2j}}\right)$.
> 2. *Conjectured g.f.:* $\dfrac{1}{2}\bigl(\text{G.f. of } \mathrm{A000712}(x) - \text{G.f. of } \mathrm{A000041}(x^2)\bigr)$.

*Editorial context on Novelty.* Across live `OEIS A392002` (`#11`, January 1, 2026, where both `%F` lines remain explicitly labeled `Conjectured g.f.`), companions `A000712` and `A000041`, `trureturing`, arXiv, Zenodo, and web searches conducted during Seam C intake (`TRIAGE-SEAMC.md` §3.2, re-verified 2026-11-15), no prior written or formal proof of `A392002` was located. Algebraically, the generating-function identity reflects the classical bivariate specialization $(1 - x^j)^{-1}(1 - y x^j)^{-1}\big|_{y = -1} = (1 - x^{2j})^{-1}$; the contribution of this note is a self-contained, elementary bijective proof of Hutton's conjecture together with a complete, axiom-clean Lean 4 formalization directly over Mathlib's `Nat.Partition`.

### 1.2 Summary of Formalized Results

In `Mathproofs/A392002TwoColorPartition.lean` (`namespace SeamC.A392002`), we prove:

- **Theorem 1.1 (Main Identity — `SeamC.A392002.two_mul_oddColorPartitions_eq`).** *For every $n \in \mathbb{N}$,*
  $$2 \cdot a(n) = p_2(n) - \bigl(\text{if } \mathrm{Even}\;n \text{ then } p(n / 2) \text{ else } 0\bigr).$$
- **Theorem 1.2 (Model Equivalence & `A000712` Convolution — `equivColoredMultiset`, `colorSum_eq_coloredMultiset_colorSum`, `p₂_eq_sum_range`).** *The pair-of-partitions type `TwoColorPartition n` is in canonical bijection with finite multisets of pairs $(s, c) \in \mathbb{N}_+ \times \mathrm{Fin}\;2$ summing to $n$, under which $\mathrm{colorSum}(\pi) = \operatorname{length}(\lambda^{(1)})$ equals $\sum_{(s, c) \in \pi} c$, and $p_2(n) = \sum_{k=0}^n p(k)\,p(n - k)$.*
- **Theorem 1.3 (Color-Parity Involution & Halving Bijection — `colorParityInvolution_involutive`, `colorParityInvolution_nonfixed_parity`, `fixedEquivPartitionHalf`).** *The map `colorParityInvolution` is an involution on `{0, 1}`-colored partitions of $n$ that flips color-sum parity on every non-fixed partition, has no fixed points when $n$ is odd, and restricts to an explicit bijection between its fixed points and `Nat.Partition (n / 2)` when $n$ is even.*
- **Theorem 1.4 (Independent Computable DP Mirror & Color-Sum Trap — `a_dp_eq_a`, `a_spot_0_to_12`, `aWrongSizeSum_two_eq_one_ne_a_two`).** *A pure `Nat.rec` structural-recursion DP `a_dp`—proved equal to `a` directly from `Nat.Partition` without invoking Theorem 1.1—verifies `a(0..12) = [0, 1, 2, 5, 9, 18, 31, 55, 90, 150, 237, 376, 577]` by kernel `rfl`, while the size-sum variant `Odd |λ^{(1)}|` evaluates to $1 \ne 2 = a(2)$ at $n = 2$.*

---

## 2. Formal Definitions, Model Equivalence, and the Color-Sum Trap

### 2.1 Pinned Lean 4 Specification on `Nat.Partition`

Mathlib (`Mathlib.Combinatorics.Enumerative.Partition.Basic`) defines an ordinary partition `Nat.Partition m` as a `Multiset ℕ` of positive integers summing to `m`, equipped with `DecidableEq` and `Fintype`. Building directly on `Nat.Partition` and `Finset.antidiagonal n`, `PIN-S001.md` v1 specifies:

```lean
abbrev TwoColorPartition (n : ℕ) : Type :=
  Σ k : Finset.antidiagonal n, Nat.Partition k.1.1 × Nat.Partition k.1.2

def colorSum {n : ℕ} (π : TwoColorPartition n) : ℕ :=
  π.2.2.parts.card

def p (n : ℕ) : ℕ :=
  Fintype.card (Nat.Partition n)

def p₂ (n : ℕ) : ℕ :=
  Fintype.card (TwoColorPartition n)

def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun π : TwoColorPartition n => Odd (colorSum π))).card
```

At $n = 0$, `Finset.antidiagonal 0 = {(0, 0)}` and `Nat.Partition 0` is a singleton (`parts = 0`), so the unique empty pair $(\emptyset, \emptyset)$ has `colorSum = 0` (even). Thus $p(0) = 1$, $p_2(0) = 1$, $a(0) = 0$ (`p_zero`, `p₂_zero`, `a_zero`), and Theorem 1.1 reduces at $n = 0$ to $2 \cdot 0 = 1 - 1$. Multiplying through by $2$ over $\mathbb{N}$ avoids rational division while matching $[x^n]\,\frac{1}{2}(A_{000712}(x) - A_{000041}(x^2))$ for every $n \ge 0$.

To certify complete fidelity with the multiset-of-colored-parts formulation in `PIN-S001.md` (`fidelity_notes` L44–47), we also define `ColoredMultiset n` (`parts : Multiset (ℕ+ × Fin 2)` with `(parts.map (fun x => (x.1 : ℕ))).sum = n`) and construct an explicit equivalence `equivColoredMultiset n : TwoColorPartition n ≃ ColoredMultiset n` satisfying
$$\mathrm{colorSum}(\pi) = \sum_{(s, c) \in (\mathrm{equivColoredMultiset}\;n\;\pi).\mathrm{parts}} c$$
(`colorSum_eq_coloredMultiset_colorSum`). Since $c \in \{0, 1\}$, each $0$-colored part contributes $0$ to $\sum c$ and each $1$-colored part contributes $1$, so $\sum c = \operatorname{length}(\lambda^{(1)})$.

### 2.2 The Color-Sum Semantic Trap (`length(λ^{(1)})` vs. `|λ^{(1)}|`)

A subtle semantic trap arises if one misreads *"whose colors sum to an odd integer"* as *"whose $1$-colored parts have odd total size $|\lambda^{(1)}| = k_1$"* (`aWrongSizeSum`):

1. **Agreement at $n = 0$ and at every odd $n$.** At $n = 0$, $k_1 = 0$ is even, giving $0 = a(0)$. Whenever $n$ is odd and $k_0 + k_1 = n$, exactly one of $k_0, k_1$ is odd, so the global swap $(\lambda^{(0)}, \lambda^{(1)}) \mapsto (\lambda^{(1)}, \lambda^{(0)})$ is a fixed-point-free involution flipping the parity of $k_1$. Hence $2 \cdot \mathrm{aWrongSizeSum}(n) = p_2(n) = 2 \cdot a(n)$ for **every odd $n$**! A sanity check restricted to $n = 0, 1$ (or odd $n$) cannot detect the bug.
2. **Failure at every positive even $n = 2m$.** Summing $(-1)^{k_1}$ over $k_0 + k_1 = 2m$ computes $[x^{2m}]\,P(x)P(-x)$ rather than $[x^{2m}]\,P(x^2) = p(m)$, where $P(x) = \prod_{j \ge 1} (1 - x^j)^{-1}$. Already at $n = 2$, the five $\{0, 1\}$-colored partitions are:

| $(\lambda^{(0)}, \lambda^{(1)})$ | Colored multiset | $\mathrm{colorSum} = \operatorname{length}(\lambda^{(1)})$ | Size sum $k_1 = |\lambda^{(1)}|$ |
| :--- | :--- | :---: | :---: |
| $((2), \emptyset)$ | $\{(2, 0)\}$ | $0$ (even) | $0$ (even) |
| $(\emptyset, (2))$ | $\{(2, 1)\}$ | **$1$ (odd)** | $2$ (even) |
| $((1, 1), \emptyset)$ | $\{(1, 0), (1, 0)\}$ | $0$ (even) | $0$ (even) |
| $((1), (1))$ | $\{(1, 0), (1, 1)\}$ | **$1$ (odd)** | **$1$ (odd)** |
| $(\emptyset, (1, 1))$ | $\{(1, 1), (1, 1)\}$ | $2$ (even) | $2$ (even) |

Here $a(2) = 2$ (`((∅, (2)))` and `(((1), (1)))`), satisfying $2 \cdot 2 = 5 - 1 = p_2(2) - p(1)$, whereas `aWrongSizeSum 2 = 1` (counting `((1), (1))` alone, proved in the kernel as `aWrongSizeSum_two_eq_one_ne_a_two`). Across $n = 0..12$, `aWrongSizeSum` produces `[0, 1, 1, 5, 6, 18, 23, 55, 72, 150, 199, 376, 502]`, failing at $n \in \{2, 4, 6, 8, 10, 12\}$—precisely the $6/13$ spot-check failures observed when $|\lambda^{(1)}|$ is substituted for $\operatorname{length}(\lambda^{(1)})$.

---

## 3. The Two-Stage Sign-Reversing Color-Parity Involution

### 3.1 Multiplicity Coordinates on `PartPair n`

To avoid dependent type transports across `Finset.antidiagonal n` when an involution changes $k_0$ and $k_1$ while keeping $k_0 + k_1 = n$ fixed, we pass via `equivPartPair n : TwoColorPartition n ≃ PartPair n` to the flat structure `PartPair n` consisting of two positive-integer multisets $(\mathrm{parts}_0, \mathrm{parts}_1)$ with $\mathrm{parts}_0.\mathrm{sum} + \mathrm{parts}_1.\mathrm{sum} = n$. For each part size $j \ge 1$, write
$$m_{j,0}(x) := \mathrm{parts}_0.\mathrm{count}(j), \qquad m_{j,1}(x) := \mathrm{parts}_1.\mathrm{count}(j), \qquad m_j(x) := m_{j,0}(x) + m_{j,1}(x).$$
Then $\sum_{j \ge 1} j\, m_j(x) = n$ and the color sum is $\mathrm{parts}_1.\mathrm{card} = \sum_{j \ge 1} m_{j,1}(x)$.

Algebraically, tracking color-sum parity via $y = -1$ in the bivariate generating function gives
$$\sum_{n \ge 0} \bigl(e(n) - a(n)\bigr) x^n = \prod_{j \ge 1} \frac{1}{(1 - x^j)(1 + x^j)} = \prod_{j \ge 1} \sum_{m_j \ge 0} \left(\sum_{r = 0}^{m_j} (-1)^r\right) x^{j m_j} = \prod_{j \ge 1} \frac{1}{1 - x^{2j}} = \sum_{m \ge 0} p(m) x^{2m},$$
because the inner fiber sum $\sum_{r=0}^{m_j} (-1)^r = \frac{1 - (-1)^{m_j + 1}}{1 - (-1)}$ vanishes whenever $m_j$ is odd and equals $+1$ whenever $m_j = 2k_j$ is even (`TRIAGE-SEAMC.md` Table 1.3). Translating both cancellations into a single bijective involution on `PartPair n` naturally yields a two-stage map `colorParityInvolution`.

### 3.2 Stage 1 (`swapLeastOdd`): Canceling Odd Total Multiplicities

Define the finite set of odd-total-multiplicity part sizes
$$\mathrm{oddTotalSizes}(x) := \{j \in (\mathrm{parts}_0 + \mathrm{parts}_1).\mathrm{toFinset} \mid \mathrm{Odd}(m_{j,0}(x) + m_{j,1}(x))\}.$$
By `mem_oddTotalSizes`, $j \in \mathrm{oddTotalSizes}(x) \iff \mathrm{Odd}(m_{j,0}(x) + m_{j,1}(x))$ unconditionally for all $j \in \mathbb{N}$ (since $0 + 0 = 0$ is not odd). Whenever $\mathrm{oddTotalSizes}(x)$ is nonempty, let $j_0 = \min \mathrm{oddTotalSizes}(x)$ (`Finset.min'`) and define `swapAt j₀ x` by exchanging all occurrences of $j_0$ between $\mathrm{parts}_0$ and $\mathrm{parts}_1$:
$$(m_{j_0, 0}, m_{j_0, 1}) \longmapsto (m_{j_0, 1}, m_{j_0, 0}), \qquad (m_{k, 0}, m_{k, 1}) \longmapsto (m_{k, 0}, m_{k, 1}) \quad (k \ne j_0).$$
We establish three kernel lemmas for Stage 1:
1. **Size and support invariance (`swapAt`, `oddTotalSizes_swapAt`).** Every part in `swapAt j₀ x` comes from `x.parts₀` or `x.parts₁` (hence is positive), the total sum of sizes is preserved, and $m_{k,0} + m_{k,1}$ is unchanged for *every* $k \in \mathbb{N}$. Consequently, $\mathrm{oddTotalSizes}(\mathrm{swapAt}\;j_0\;x) = \mathrm{oddTotalSizes}(x)$ as `Finset ℕ`, so the minimum $j_0$ is identically preserved.
2. **Involutivity (`swapLeastOdd_involutive`).** Applying `swapAt j₀` twice restores $(m_{j_0, 0}, m_{j_0, 1})$.
3. **Color-sum parity flip (`card_parts₁_swapAt_add`).** Isolating part size $j_0$ in $\mathrm{parts}_1$ gives
   $$(\mathrm{swapAt}\;j_0\;x).\mathrm{parts}_1.\mathrm{card} + x.\mathrm{parts}_1.\mathrm{card} = \bigl(m_{j_0, 0}(x) + m_{j_0, 1}(x)\bigr) + 2 \cdot (\mathrm{parts}_1.\mathrm{filter}(\cdot \ne j_0)).\mathrm{card}.$$
   Since $m_{j_0, 0}(x) + m_{j_0, 1}(x)$ is odd, the two color sums have opposite parities (`swapAt j₀ x ≠ x`).

### 3.3 Why Stage 2 (`shiftEvenFiberAt`) Is Needed on the Even-Total-Multiplicity Locus

The fixed-point locus of Stage 1 (`swapLeastOdd_fixed_iff`) is $\{x \in \mathrm{PartPair}\;n \mid \forall j,\ \mathrm{Even}(m_{j,0}(x) + m_{j,1}(x))\}$. Crucially, **this locus is larger than $p(n/2)$ for every even $n \ge 2$**: when $m_j = 2k_j > 0$, there are $2k_j + 1$ ways to split $2k_j = m_{j,0} + m_{j,1}$, not $1$. For $n = 0..10$ ($2 \mid n$), the Stage-1 fixed-point counts are $1, 3, 8, 19, 41, 83$, whereas $p(n/2) = 1, 1, 2, 3, 5, 7$. For example, at $n = 2$, Stage 1 fixes all three partitions with $m_1 = 2$:
$$((1, 1), \emptyset)\ [\text{even}], \qquad ((1), (1))\ [\text{odd}], \qquad (\emptyset, (1, 1))\ [\text{even}].$$
Stage 2 (`shiftEvenFiberAt`) bijectively realizes the fiber identity $\sum_{r=0}^{2k_j} (-1)^r = 1 + \sum_{q=0}^{k_j - 1} \bigl((-1)^{2q+1} + (-1)^{2q+2}\bigr) = 1$: when $\mathrm{oddTotalSizes}(x) = \emptyset$, let $\mathrm{posOneSizes}(x) := \{j \mid m_{j,1}(x) > 0\}$. If $\mathrm{posOneSizes}(x)$ is nonempty, let $j_0 = \min \mathrm{posOneSizes}(x)$:
- If $m_{j_0, 1}(x) = 2q + 1$ is odd, then since $m_{j_0, 0}(x) + m_{j_0, 1}(x) = 2k_{j_0}$ is even, $m_{j_0, 0}(x)$ is also odd (hence $\ge 1$); we move one part $j_0$ from $\mathrm{parts}_0$ to $\mathrm{parts}_1$, giving $(m_{j_0, 0} - 1, 2q + 2)$.
- If $m_{j_0, 1}(x) = 2q + 2 > 0$ is even, then $m_{j_0, 1}(x) \ge 2$; we move one part $j_0$ from $\mathrm{parts}_1$ to $\mathrm{parts}_0$, giving $(m_{j_0, 0} + 1, 2q + 1)$.

By `shiftEvenFiberAt_props`, both transitions preserve $\mathrm{oddTotalSizes} = \emptyset$, preserve the exact support finset $\mathrm{posOneSizes}$ (since $2q + 2 \ge 2 > 0$ and $2q + 1 \ge 1 > 0$, keeping $j_0 = \min \mathrm{posOneSizes}$ invariant), reverse each other, and change $\mathrm{parts}_1.\mathrm{card}$ by $\pm 1$. Combining Stages 1 and 2 into `colorParityInvolution` yields an involution (`colorParityInvolution_involutive`) that flips `Odd parts₁.card` on every non-fixed element (`colorParityInvolution_nonfixed_parity`) and fixes $x$ if and only if
$$x.\mathrm{parts}_1 = 0 \quad \text{and} \quad \forall j \in \mathbb{N},\ \mathrm{Even}\bigl(x.\mathrm{parts}_0.\mathrm{count}(j)\bigr)$$
(`colorParityInvolution_fixed_iff`). Every fixed point has $\mathrm{parts}_1 = 0$, hence color sum $0$ (even; `not_odd_of_fixed`).

---

## 4. The Halving Bijection and Double-Counting Closure

### 4.1 Halving All-Even Multisets (`fixedEquivPartitionHalf`)

For any multiset $m : \mathrm{Multiset}\;\mathbb{N}$, define
$$\mathrm{halfMultiset}(m) := \sum_{k \in m.\mathrm{toFinset}} \mathrm{Multiset.replicate}\bigl(m.\mathrm{count}(k) / 2,\; k\bigr).$$
Using `Multiset.count_sum'`, we prove `(halfMultiset m).count x = m.count x / 2` for every $x \in \mathbb{N}$ (`count_halfMultiset`). Whenever $\forall x,\ \mathrm{Even}(m.\mathrm{count}\;x)$, extensionality of multiset counts immediately gives
$$\mathrm{halfMultiset}(m) + \mathrm{halfMultiset}(m) = m \qquad (\text{`halfMultiset\_add\_self`}),$$
and applying `Multiset.sum` yields $2 \cdot (\mathrm{halfMultiset}\;m).\mathrm{sum} = m.\mathrm{sum}$.

For a fixed point $x$ of `colorParityInvolution` on `PartPair n`, $x.\mathrm{parts}_1 = 0$ implies $x.\mathrm{parts}_0.\mathrm{sum} = n$, so $n = 2 \cdot (\mathrm{halfMultiset}\;x.\mathrm{parts}_0).\mathrm{sum}$:
- **Odd $n$ (`fixed_empty_of_not_even`):** No fixed point can exist when $\neg\mathrm{Even}\;n$, so the fixed-point finset has cardinality $0$.
- **Even $n$ (`fixedEquivPartitionHalf`):** When $\mathrm{Even}\;n$, $\mathrm{halfMultiset}\;x.\mathrm{parts}_0$ has positive parts summing to $n / 2$, defining a map to `Nat.Partition (n / 2)` with two-sided inverse $\mu \mapsto (\mu.\mathrm{parts} + \mu.\mathrm{parts},\; 0)$. Hence `card_fixed_partPair` gives
  $$\bigl|\{x \in \mathrm{PartPair}\;n \mid \mathrm{colorParityInvolution}\;x = x\}\bigr| = \begin{cases} p(n / 2), & \text{if } \mathrm{Even}\;n, \\ 0, & \text{otherwise.} \end{cases}$$

### 4.2 Three-Way Partition of `PartPair n` (`two_mul_oddColorPartitions_eq`)

Partition `Finset.univ : Finset (PartPair n)` into three pairwise disjoint subsets:
1. $\mathrm{oddSet} := \{x \mid \mathrm{Odd}\;x.\mathrm{parts}_1.\mathrm{card}\}$, of cardinality $a(n)$ (`card_odd_partPair_eq_a`);
2. $\mathrm{pairedEvenSet} := \{x \mid \neg\mathrm{Odd}\;x.\mathrm{parts}_1.\mathrm{card} \land \mathrm{colorParityInvolution}\;x \ne x\}$; and
3. $\mathrm{fixedSet} := \{x \mid \mathrm{colorParityInvolution}\;x = x\}$, of cardinality `if Even n then p (n / 2) else 0`.

Because every fixed point has color sum $0$ (even), `colorParityInvolution` maps $\mathrm{oddSet}$ bijectively onto $\mathrm{pairedEvenSet}$ (`pairedEvenSet = oddSet.image colorParityInvolution`), so $|\mathrm{pairedEvenSet}| = |\mathrm{oddSet}| = a(n)$ by `Finset.card_image_of_injOn`. Summing the three disjoint cardinalities yields
$$p_2(n) = 2 \cdot a(n) + \bigl(\text{if } \mathrm{Even}\;n \text{ then } p(n / 2) \text{ else } 0\bigr) \qquad (\text{`p₂\_eq\_two\_mul\_a\_add\_fixed`}),$$
from which subtraction over $\mathbb{N}$ gives `SeamC.A392002.two_mul_oddColorPartitions_eq` for all $n \in \mathbb{N}$.

---

## 5. Verification Record, Strength Delta, and Scope Boundary

### 5.1 Formal Verification Gates

All verification gates were executed under `leanprover/lean4:v4.34.1` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`:

| Gate | Command | Result |
| :--- | :--- | :--- |
| Clean-slate build | `rm -rf .lake/build && lake build` | `exit 0` (`17,980` jobs; `0` errors / `0` sorries / `0` warnings in `A392002TwoColorPartition.lean`) |
| Axiom allowlist + closure | `lake env lean ../evidence/check_axioms_and_closure.lean` | `exit 0` (`[propext, Classical.choice, Quot.sound]` only across `1,151` transitive constants; `sorryAx=false`, `ofReduceBool=false`, `ofReduceNat=false`, `trustCompiler=false`) |
| Fresh-kernel replay | `lake env leanchecker --fresh --verbose Mathproofs.A392002TwoColorPartition` | `exit 0` (`replaying Mathproofs.A392002TwoColorPartition with --fresh`) |
| Lexical trust-escape screen | `python3 evidence/lexical_screen.py` | `exit 0` (`0` active hits and `0` raw hits across `A392002TwoColorPartition.lean`, `Mathproofs.lean`, `Main.lean`) |
| Non-vacuity & OEIS checks | `lake env lean ../evidence/check_nonvacuity_eval.lean && python3 evidence/verify_nonvacuity_s001.py` | `exit 0` (`0` mismatches vs. printed `A392002` `n=0..43`, `A000712` `n=0..38`, `A000041` `n=0..49`, and bivariate DP `n=0..120`) |

### 5.2 Non-Vacuity Boundary (Kernel `rfl` vs. VM `#eval`)

Mathlib's `Fintype (Nat.Partition n)` instance (`Fintype.ofSurjective (ofComposition n) ofComposition_surj`) passes through `Multiset` quotients and `Classical.choice`, which blocks direct kernel `rfl` reduction on `p n`, `p₂ n`, and `a n`. We verify non-vacuity at two complementary levels:
- **In the Lean 4 kernel:** We prove boundary values `p 0 = 1`, `p 1 = 1`, `p₂ 0 = 1`, `a 0 = 0`, `p₂ 1 = 2` directly, and construct structural-recursion (`Nat.rec`) mirrors `p_dp`, `p₂_dp`, and `a_dp` formally proved equal to `p`, `p₂`, and `a` for all $n \in \mathbb{N}$ (`p_dp_eq_p`, `p₂_dp_eq_p₂`, `a_dp_eq_a`)—where `a_dp` sums $p(k)\,p_{\mathrm{odd}}(n - k)$ directly from the definition of `a` without using Theorem 1.1. Kernel `rfl` on the mirrors transfers `a(0..12)`, `p₂(0..12)`, and `p(0..12)` onto `SeamC.A392002.a`, `p₂`, and `p` (`a_spot_0_to_12`, `p₂_spot_0_to_12`, `p_spot_0_to_12`).
- **Via Lean VM `#eval` and Python cross-check (not claimed as kernel `rfl`):** Direct `#eval` on `SeamC.A392002.a`, `p₂`, `p` confirms `n = 0..12`, `#eval` on `a_dp`, `p₂_dp`, `p_dp` confirms all printed OEIS terms (`A392002` `n = 0..43`, `A000712` `n = 0..38`, `A000041` `n = 0..49`), and Python enumeration explicitly tests the involution on all colored partitions for `n = 0..10` and checks `n = 0..120` with `0` mismatches.

### 5.3 Strength Delta and What This Note Does NOT Show

- **Strength delta vs. source (`PIN-S001.md`):** **`NONE` (`equal`).** Theorem 1.1 proves the exact coefficient-for-coefficient statement of Thomas Hutton's `OEIS A392002` `%F` lines 12–13 identity across all $n \ge 0$, with no range restriction or auxiliary hypotheses.
- **What this does NOT show:** This formalization establishes the discrete coefficient-level identity over $\mathbb{N}$ (and the `A000712` convolution over `Nat.Partition`); it does not formalize a topological infinite-product identity in `PowerSeries ℚ` (which Mathlib's `Nat.Partition.GenFun` handles separately for `restricted` and `countRestricted`), nor does it generalize to $k$-colored partitions modulo $m > 2$ or derive Rademacher/Hardy–Ramanujan asymptotics for $a(n)$.

---

## References

1. T. Hutton, Sequence `A392002` (*Number of partitions of $n$ into parts colored by $\{0, 1\}$ such that the colors sum to an odd integer*), in *The On-Line Encyclopedia of Integer Sequences* (OEIS), December 26, 2025; live revision `#11`, January 1, 2026, https://oeis.org/A392002.
2. N. J. A. Sloane et al., Sequence `A000712` (*Number of partitions of $n$ into parts of $2$ kinds*) and Sequence `A000041` (*Number of partitions of $n$*), in *The On-Line Encyclopedia of Integer Sequences* (OEIS), https://oeis.org/A000712 and https://oeis.org/A000041.
3. The mathlib Community, *The Lean Mathematical Library* (`Mathlib.Combinatorics.Enumerative.Partition.Basic`), `v4.34.1` (`d13f23b723b8a846827a245b89c10fc7d3f11612`), 2026.
