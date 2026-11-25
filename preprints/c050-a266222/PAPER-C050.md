# Two-Step Defect Annihilation and Formal Generating Functions for Wolfram's Rule 7 Cellular Automaton: Proof and Lean 4 Formalization of Colin Barker's OEIS A266222 Conjecture Bundle

**Preprint Draft (`PAPER-C050.md`) — 2026-11-16**  
**Repository / Module:** `derekblair/math-proofs` (`Mathproofs/A266222.lean`, `namespace A266222`)  
**Toolchain & Mathlib Pin:** `leanprover/lean4:v4.34.1` (`commit 5045d0056413266e57c625dcd7c365b10e377c52`), Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`  
**Target Contract:** `PIN-C050.md` v1 (`SHA-256: 318c0949375a216bede12adcb902486d454b5a42afbc4fc2917bb81a30b0ac69`, `delta_vs_source: NONE`)

---

## Abstract

Let `ca : ℕ → ℤ → Bool` denote the global state on $\mathbb{Z}$ of Wolfram's Elementary Cellular Automaton Rule 7 (`7 = 0b00000111`, local update $(l, c, r) \mapsto (\neg l \land \neg c) \lor (\neg l \land c \land \neg r)$) initialized at generation $n = 0$ with a single ON (`true`) cell at $j = 0$ surrounded by OFF (`false`) cells at all $j \ne 0$, and let $a(n)$ (`OEIS A266222`, authored by Robert Price, December 24, 2015) count the OFF (`false`) cells inside the truncated active light-cone window $[-n, n] \cap \mathbb{Z}$ of length $2n + 1$. Because Rule 7 maps $(0, 0, 0) \mapsto 1$ and $(1, 1, 1) \mapsto 0$, the infinite exterior $|j| > n$ alternates globally between `false` (even $n$) and `true` (odd $n$); rules of this class were omitted from Sloane's global ON-cell study (`arXiv:1503.01168`), and Colin Barker's December 26, 2015 / April 13, 2019 formulas for $a(n)$ (`OEIS A266222`, `%F` lines 16–20) have remained open-labeled conjectures.

We give a self-contained elementary proof and a complete Lean 4 formalization of Barker's full three-part conjecture bundle: (1) $2 a(n) = (1 + (-1)^n)(1 + 2n)$ for all $n > 1$; (2) $a(n) = 2 a(n - 2) - a(n - 4)$ for all $n > 5$; and (3) $((1 - X)^2 (1 + X)^2) \sum_{n \ge 0} a(n) X^n = X(1 + 5X - 2X^2 - X^3 + X^4)$ in $\mathbb{Q}\llbracket X \rrbracket$. Evolving `ca` on all of $\mathbb{Z}$ before restricting to $[-n, n]$ eliminates all boundary case-splitting: generation $1$ has a unique OFF defect at $j = 1$ against an all-ON infinite background, generation $2$ annihilates that defect across all $j \in \mathbb{Z}$ because Rule 7 requires at least two `false` inputs to output `true`, and generations $n \ge 2$ satisfy the spatially constant parity invariant $\mathrm{ca}(n, j) = \mathrm{decide}(\mathrm{Odd}\; n)$ for all $j \in \mathbb{Z}$. We also formalize a polynomial-time causal-cone mirror proved equal to $a(n)$ for kernel `rfl` verification against `OEIS A266222`, prove sharpness of both index guards ($n > 1$ and $n > 5$), and prove formally why naive growing-window zero-padding fails at $n = 2$ ($3 \ne 5$). All proofs compile cleanly in Lean 4 without `sorry`, custom axioms, `native_decide`, or `ofReduceBool`.

---

## 1. Introduction and Primary-Source Context

### 1.1 Wolfram's Rule 7 on $\mathbb{Z}$ and `OEIS A266222`

In Wolfram's numbering of one-dimensional radius-$1$, two-state elementary cellular automata (ECAs) [2], each cell $j \in \mathbb{Z}$ updates synchronously from its three-cell neighborhood $(l, c, r) = (\mathrm{ca}(n, j - 1), \mathrm{ca}(n, j), \mathrm{ca}(n, j + 1)) \in \{0, 1\}^3$ by reading bit $\mathrm{idx} = 4l + 2c + r \in \{0, \dots, 7\}$ of the rule number. For **Rule 7** ($7 = 0\mathrm{b}00000111$), the local update outputs $1$ (`true`, ON/black) if and only if $\mathrm{idx} \in \{0, 1, 2\}$, i.e., $(l, c, r) \in \{(0, 0, 0), (0, 0, 1), (0, 1, 0)\}$, and $0$ (`false`, OFF/white) on the remaining five triples.

In his systematic 2015 study of ON-cell counts in cellular automata [3, §6.1], N. J. A. Sloane restricted attention to rules preserving the quiescent zero state ($(0, 0, 0) \mapsto 0$), because rules with $(0, 0, 0) \mapsto 1$—such as Rule 7—turn infinitely many exterior cells ON at odd generations, making the unrestricted sum $\sum_{j \in \mathbb{Z}} \mathrm{ca}(n, j)$ infinite. To obtain well-defined integer sequences for such rules, Robert Price introduced a family of OEIS entries in December 2015 (including `A266216`–`A266223` for Rule 7) that evolve the automaton on the infinite lattice $\mathbb{Z}$ from a single ON cell at $j = 0$ using Mathematica's `{All, All}` causal-cone mode and then slice generation $n$ to the active light-cone interval $[-n, n]$ of width $2n + 1$ [1]:

```mathematica
rule=7; rows=20; ca=CellularAutomaton[rule,{{1},0},rows-1,{All,All}];
catri=Table[Take[ca[[k]],{rows-k+1,rows+k-1}],{k,1,rows}];
nbc=Table[Total[catri[[k]]],{k,1,rows}];
Table[Length[catri[[k]]]-nbc[[k]],{k,1,rows}]
```

Entry `OEIS A266222` records the OFF-cell (white, `0`) count $a(n)$ in $[-n, n]$ at generation $n \ge 0$, beginning
$$(a(n))_{n \ge 0} = (0, 1, 5, 0, 9, 0, 13, 0, 17, 0, 21, 0, 25, \dots).$$
On December 26, 2015 and April 13, 2019, Colin Barker posted the following three-part conjecture block (`OEIS A266222`, `%F` lines 16–20, live revision `#17` dated February 16, 2025 [1]):

> **Conjecture Bundle (Colin Barker, 2015 / 2019).** *For `OEIS A266222`:*
> 1. $a(n) = \frac{1}{2}\bigl(1 + (-1)^n\bigr)(1 + 2n)$ *for* $n > 1$.
> 2. $a(n) = 2 a(n - 2) - a(n - 4)$ *for* $n > 5$.
> 3. *Ordinary generating function:* $\sum_{n \ge 0} a(n) x^n = \dfrac{x(1 + 5x - 2x^2 - x^3 + x^4)}{(1 - x)^2 (1 + x)^2}$.

*Editorial context on Novelty and Adjacent Entries.* Across OEIS (`#17`, February 16, 2025), arXiv, OpenAlex, and general literature searches, no written or formal proof of `A266222` (or of its seven ON/OFF ECA siblings `A266220`, `A266256`, `A266258`, `A266437`, `A266439`, `A266662`, `A266664`) appears in the literature, and all eight entries remain explicitly under `Conjectures from _Colin Barker_`. On the adjacent binary/decimal row-encoding entries `A266217` and `A266218`, Karl V. Keller, Jr. contributed unproved closed-form Python one-liners in August 2021 where OEIS editors removed the `Conjectures` label without an accompanying proof. Accordingly, the contribution of this note is framed modestly: a first written and machine-checked proof of Barker's open-labeled `A266222` conjecture bundle, together with a formal clarification of the infinite-lattice background semantics needed to state it faithfully.

### 1.2 Summary of Main Results

In `Mathproofs/A266222.lean` (`namespace A266222`), we establish:

- **Theorem 1.1 (Spatially Constant Parity Invariant — `A266222.ca_eq_decide_odd`).** *After generation $0$ ($\mathrm{ca}(0, j) = \mathrm{decide}(j = 0)$) and generation $1$ ($\mathrm{ca}(1, j) = \mathrm{decide}(j \ne 1)$), the single defect at $j = 1$ annihilates at generation $2$ ($\forall j \in \mathbb{Z},\ \mathrm{ca}(2, j) = \mathtt{false}$), and for every $n \ge 2$ and every $j \in \mathbb{Z}$, $\mathrm{ca}(n, j) = \mathrm{decide}(\mathrm{Odd}\; n)$.*
- **Theorem 1.2 (Closed Form and Guard Sharpness — `A266222.a_closed_form`).** *For all $n > 1$, $2 a(n) = (1 + (-1)^n)(1 + 2n)$ over $\mathbb{Z}$ (equivalently $a(2m) = 4m + 1$ and $a(2m + 1) = 0$ for $m \ge 1$), while equality fails at both excluded indices $n = 0$ ($0 \ne 2$) and $n = 1$ ($2 \ne 0$).*
- **Theorem 1.3 (Four-Step Recurrence and Guard Sharpness — `A266222.a_recurrence`).** *For all $n > 5$, $a(n) = 2 a(n - 2) - a(n - 4)$ over $\mathbb{Z}$, while equality fails at $n = 4$ ($9 \ne 10$) and $n = 5$ ($0 \ne -1$).*
- **Theorem 1.4 (Formal Generating Function and Full Bundle — `A266222.a_gf`, `A266222.c050_bundle`).** *In `PowerSeries ℚ`,*
  $$\bigl((1 - X)^2 (1 + X)^2\bigr) \sum_{n \ge 0} (a(n) : \mathbb{Q}) X^n = X(1 + 5X - 2X^2 - X^3 + X^4).$$

---

## 2. Formal Definitions, Alternating Background Semantics, and the Zero-Padding Trap

### 2.1 Pinned Lean 4 Specification

The frozen target manifest `PIN-C050.md` (v1) specifies the Rule 7 local update, global $\mathbb{Z}$-evolution, and truncated $[-n, n]$ OFF-cell count directly over `Bool`, `ℤ`, and `Finset ℤ`:

```lean
def rule7 (l c r : Bool) : Bool := (!l && !c) || (!l && c && !r)

def ca : ℕ → ℤ → Bool
  | 0, j => decide (j = 0)
  | n + 1, j => rule7 (ca n (j - 1)) (ca n j) (ca n (j + 1))

def a (n : ℕ) : ℕ := ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun j => !(ca n j))).card
```

Here Lean 4's standard coercion `Coe Bool Prop` (`b ↦ (b = true)`) supplies a canonical `DecidablePred` instance for `Finset.filter`, and `Int.instLocallyFiniteOrder` supplies `Finset.Icc (-(n : ℤ)) (n : ℤ)` of cardinality $2n + 1$. By exhaustive eight-case kernel reduction (`A266222.rule7_eq_testBit`), `rule7 l c r` coincides identically with `Nat.testBit 7 (4 * l.toNat + 2 * c.toNat + r.toNat)`:

| $(l, c, r)$ (`Bool`) | $(l, c, r)$ (`0/1`) | Wolfram $\mathrm{idx} = 4l + 2c + r$ | Bit $\mathrm{idx}$ of $7$ | `rule7 l c r` |
| :--- | :---: | :---: | :---: | :---: |
| `(true, true, true)` | `(1, 1, 1)` | `7` | `0` | `false` |
| `(true, true, false)` | `(1, 1, 0)` | `6` | `0` | `false` |
| `(true, false, true)` | `(1, 0, 1)` | `5` | `0` | `false` |
| `(true, false, false)` | `(1, 0, 0)` | `4` | `0` | `false` |
| `(false, true, true)` | `(0, 1, 1)` | `3` | `0` | `false` |
| `(false, true, false)` | `(0, 1, 0)` | `2` | `1` | `true` |
| `(false, false, true)` | `(0, 0, 1)` | `1` | `1` | `true` |
| `(false, false, false)` | `(0, 0, 0)` | `0` | `1` | `true` |

Left-to-right spatial orientation ($l$ at $j - 1$, $r$ at $j + 1$) matches companion `OEIS A266216` (`%e`: generation $1$ on $[-1, 1]$ is `1 1 0`, with the unique `0` on the right at $j = +1$), distinguishing Rule 7 from its spatial reflection Rule 21 (`A266377`, row $1$ = `0 1 1`).

### 2.2 The Alternating Background Lesson and the Zero-Padding Trap

A crucial semantic trap arises if one conflates "counting cells in $[-n, n]$" with "simulating a finite array on $[-n, n]$ padded with zeros outside":

1. **Alternating infinite exterior.** At $n = 0$, every cell with $|j| \ge 1$ is `false`. Because $\mathrm{rule7}(\mathtt{false}, \mathtt{false}, \mathtt{false}) = \mathtt{true}$ and $\mathrm{rule7}(\mathtt{true}, \mathtt{true}, \mathtt{true}) = \mathtt{false}$, the infinite exterior $\{j \in \mathbb{Z} : |j| > n\}$ is **not** quiescent: it flips globally at every generation (`false` for even $n$, `true` for odd $n$). Any bounded simulator that treats cells outside its tracked array as fixedly `false` miscomputes the boundary neighborhoods and fails on $12$ of the first $13$ rows of `A266222`.
2. **Failure of growing-window zero-padding at $n = 2$ (`A266222.aZeroPad_two_eq_three`).** Under true $\mathbb{Z}$-evolution, generation $1$ has `true` across all $j \ne 1$—in particular at the exterior sites $j = -2$ and $j = +2$. Thus at generation $2$:
   - cell $j = -2$ reads $(-3, -2, -1) \mapsto (\mathtt{true}, \mathtt{true}, \mathtt{true}) \mapsto \mathtt{false}$;
   - cell $j = +2$ reads $(1, 2, 3) \mapsto (\mathtt{false}, \mathtt{true}, \mathtt{true}) \mapsto \mathtt{false}$,
   giving $[-2, 2] \mapsto [0, 0, 0, 0, 0]$ (`A266216` row $2$) and $a(2) = 5$. By contrast, if one zero-pads $[-1, 1] = [1, 1, 0]$ with `false` outside $[-1, 1]$ at step $1$, then $j = -2$ reads $(0, 0, 1) \mapsto 1$ and $j = +2$ reads $(0, 0, 0) \mapsto 1$, producing $[1, 0, 0, 0, 1]$ and an OFF count of **$3 \ne 5$** (and overall sequence $0, 1, 3, 2, 7, 2, 11, \dots$). We formalize this growing-window zero-padded operator as `caZeroPad` / `aZeroPad` and prove `aZeroPad 2 = 3 ∧ aZeroPad 2 ≠ a 2` directly in Lean's kernel.

Evolving `ca : ℕ → ℤ → Bool` on all of $\mathbb{Z}$ first and restricting to `Finset.Icc (-(n : ℤ)) (n : ℤ)` only inside `a n` both reproduces Price's `{All, All}` Mathematica specification faithfully and simplifies the inductive invariant by making $\mathbb{Z}$ translation-invariant at every step.

---

## 3. Two-Step Defect Annihilation and the Spatially Constant Invariant

### 3.1 Generations $n = 0, 1, 2$

1. **Generation $0$ (`ca_zero`, `a_zero`).** By definition, $\mathrm{ca}(0, j) = \mathrm{decide}(j = 0)$. On $\mathrm{Icc}(0, 0) = \{0\}$, $\neg \mathrm{ca}(0, 0) = \mathtt{false}$, so the filtered finset is empty and $a(0) = 0$.

2. **Generation $1$ (`ca_one`, `a_one`).** Fix $j \in \mathbb{Z}$ and partition $\mathbb{Z}$ into five disjoint linear-arithmetic cases:
   - $j \le -2$ or $j \ge 2$: none of $j - 1, j, j + 1$ equals $0$, so $(\mathrm{ca}(0, j-1), \mathrm{ca}(0, j), \mathrm{ca}(0, j+1)) = (\mathtt{false}, \mathtt{false}, \mathtt{false}) \mapsto \mathtt{true}$.
   - $j = -1$: $(-2, -1, 0)$ has state $(\mathtt{false}, \mathtt{false}, \mathtt{true}) \mapsto \mathtt{true}$.
   - $j = 0$: $(-1, 0, 1)$ has state $(\mathtt{false}, \mathtt{true}, \mathtt{false}) \mapsto \mathtt{true}$.
   - $j = 1$: $(0, 1, 2)$ has state $(\mathtt{true}, \mathtt{false}, \mathtt{false}) \mapsto \mathtt{false}$.

   Hence $\mathrm{ca}(1, j) = \mathrm{decide}(j \ne 1)$ for all $j \in \mathbb{Z}$. Filtering $\mathrm{Icc}(-1, 1) = \{-1, 0, 1\}$ by $\neg \mathrm{ca}(1, j)$ isolates the singleton $\{1\}$, giving $a(1) = 1$.

3. **Two-step defect annihilation at Generation $2$ (`rule7_eq_false_of_two_true`, `ca_two`).** Structurally, `rule7 l c r = true` requires $l = \mathtt{false}$ together with either $c = \mathtt{false}$ or $r = \mathtt{false}$—that is, **at least two `false` entries** in the three-cell neighborhood $(j - 1, j, j + 1)$. Since $j - 1, j, j + 1$ are distinct integers and $\mathrm{ca}(1, \cdot)$ takes the value `false` ONLY at $x = 1$, every neighborhood at generation $1$ contains at least two `true` entries! Explicitly partitioning $j \in \mathbb{Z}$ into $j \le -1$, $j = 0$, $j = 1$, $j = 2$, and $j \ge 3$ realizes only four reachable triples on $\mathbb{Z}$:
   $$(\mathtt{true}, \mathtt{true}, \mathtt{true}) \mapsto \mathtt{false},\quad
     (\mathtt{true}, \mathtt{true}, \mathtt{false}) \mapsto \mathtt{false},\quad
     (\mathtt{true}, \mathtt{false}, \mathtt{true}) \mapsto \mathtt{false},\quad
     (\mathtt{false}, \mathtt{true}, \mathtt{true}) \mapsto \mathtt{false}.$$
   Therefore $\mathrm{ca}(2, j) = \mathtt{false}$ for **every** $j \in \mathbb{Z}$.

### 3.2 Proof of Theorem 1.1 (`ca_eq_decide_odd`)

Write $n = k + 2$ ($k \ge 0$) and argue by induction on $k$ with the quantifier $\forall j \in \mathbb{Z}$ inside the induction hypothesis:

- **Base ($k = 0$, $n = 2$):** $2$ is not odd, so $\mathrm{decide}(\mathrm{Odd}\; 2) = \mathtt{false} = \mathrm{ca}(2, j)$ for all $j \in \mathbb{Z}$.
- **Step ($k \mapsto k + 1$, $m = k + 2 \mapsto m + 1$):** Assume $\forall j \in \mathbb{Z},\ \mathrm{ca}(m, j) = \mathrm{decide}(\mathrm{Odd}\; m)$. Fix $j \in \mathbb{Z}$. Applying the inductive hypothesis at $j - 1$, $j$, and $j + 1$ simultaneously gives
  $$\mathrm{ca}(m + 1, j) = \mathrm{rule7}(b, b, b), \qquad b := \mathrm{decide}(\mathrm{Odd}\; m).$$
  - If $m$ is even ($\neg \mathrm{Odd}\; m$), then $b = \mathtt{false}$ and $\mathrm{Odd}(m + 1)$ holds, so $\mathrm{rule7}(\mathtt{false}, \mathtt{false}, \mathtt{false}) = \mathtt{true} = \mathrm{decide}(\mathrm{Odd}(m + 1))$.
  - If $m$ is odd ($\mathrm{Odd}\; m$), then $b = \mathtt{true}$ and $\neg \mathrm{Odd}(m + 1)$ holds, so $\mathrm{rule7}(\mathtt{true}, \mathtt{true}, \mathtt{true}) = \mathtt{false} = \mathrm{decide}(\mathrm{Odd}(m + 1))$. $\square$

---

## 4. Window Counting, Closed Form, Recurrence, and Guard Sharpness

### 4.1 Proof of Theorem 1.2 (`a_even_of_ge_two`, `a_odd_of_ge_two`, `a_closed_form`)

For every $n \in \mathbb{N}$, `#Finset.Icc (-(n : ℤ)) (n : ℤ) = ((n : ℤ) + 1 - (-(n : ℤ))).toNat = 2n + 1` (`Int.card_Icc`). Now let $n > 1$ ($n \ge 2$):

- **Even $n = 2m$ ($m \ge 1$):** Since $\neg \mathrm{Odd}(2m)$, Theorem 1.1 gives $\neg \mathrm{ca}(2m, j) = \mathtt{true}$ for all $j \in \mathrm{Icc}(-2m, 2m)$. By `Finset.filter_true_of_mem`, the filter retains the entire interval, so $a(2m) = 2(2m) + 1 = 4m + 1$. Over $\mathbb{Z}$, $(-1)^{2m} = 1$, so
  $$2 a(2m) = 2(4m + 1) = (1 + 1)(1 + 4m) = \bigl(1 + (-1)^{2m}\bigr)(1 + 2(2m)).$$
- **Odd $n = 2m + 1$ ($m \ge 1$):** Since $\mathrm{Odd}(2m + 1)$, Theorem 1.1 gives $\neg \mathrm{ca}(2m + 1, j) = \mathtt{false}$ for all $j \in \mathrm{Icc}(-(2m+1), 2m+1)$. The filtered finset is empty, so $a(2m + 1) = 0$. Over $\mathbb{Z}$, $(-1)^{2m+1} = -1$, so
  $$2 a(2m + 1) = 0 = (1 - 1)(1 + 2(2m + 1)) = \bigl(1 + (-1)^{2m+1}\bigr)(1 + 2(2m + 1)).$$

Since $\mathbb{Z}$ has characteristic zero (`2 ≠ 0`), $(a(n) : \mathbb{Z}) \cdot 2 = (1 + (-1)^n)(1 + 2n)$ is strictly logically equivalent to $a(n) = \frac{1}{2}(1 + (-1)^n)(1 + 2n)$ in $\mathbb{Q}$. At the excluded indices:
- $n = 0$: $2 a(0) = 0 \ne 2 = (1 + (-1)^0)(1 + 0)$ (`a_closed_form_false_zero`);
- $n = 1$: $2 a(1) = 2 \ne 0 = (1 + (-1)^1)(1 + 2)$ (`a_closed_form_false_one`). $\square$

### 4.2 Proof of Theorem 1.3 (`a_recurrence`)

Let $n > 5$ ($n \ge 6$). Then $n > 1$, $n - 2 \ge 4 > 1$, and $n - 4 \ge 2 > 1$ without $\mathbb{N}$-subtraction truncation, and $(-1)^n = (-1)^{n-2} = (-1)^{n-4}$. Applying Theorem 1.2 to $n$, $n - 2$, and $n - 4$ over $\mathbb{Z}$ yields
$$\begin{aligned}
\bigl(a(n) - (2 a(n - 2) - a(n - 4))\bigr) \cdot 2
  &= 2 a(n) - 2\bigl(2 a(n - 2)\bigr) + 2 a(n - 4) \\
  &= \bigl(1 + (-1)^{n-4}\bigr)\Bigl((1 + 2n) - 2\bigl(1 + 2(n - 2)\bigr) + \bigl(1 + 2(n - 4)\bigr)\Bigr) \\
  &= \bigl(1 + (-1)^{n-4}\bigr)(0) = 0.
\end{aligned}$$
Cancelling $2 \ne 0$ in $\mathbb{Z}$ gives $a(n) = 2 a(n - 2) - a(n - 4)$. At the excluded indices $n = 4, 5$ where $n - 4 \in \{0, 1\}$ exits the $n > 1$ regime:
- $n = 4$: $a(4) = 9 \ne 10 = 2(5) - 0 = 2 a(2) - a(0)$ (`a_recurrence_false_four`);
- $n = 5$: $a(5) = 0 \ne -1 = 2(0) - 1 = 2 a(3) - a(1)$ (`a_recurrence_false_five`). $\square$

---

## 5. Coefficient-Wise Proof of the Formal Generating Function (`a_gf`)

Let $F := \sum_{n \ge 0} (a(n) : \mathbb{Q}) X^n = \mathrm{PowerSeries.mk}(\lambda n \Rightarrow (a(n) : \mathbb{Q})) \in \mathbb{Q}\llbracket X \rrbracket$, and put
$$Q(X) := (1 - X)^2 (1 + X)^2, \qquad P(X) := X(1 + 5X - 2X^2 - X^3 + X^4).$$
Because $\mathrm{constantCoeff}(Q) = 1 \in \mathbb{Q}^\times$, $Q(X)$ is a unit in $\mathbb{Q}\llbracket X \rrbracket$ (`PowerSeries.isUnit_iff_constantCoeff`), so the denominator-cleared identity $Q(X) F = P(X)$ is strictly logically equivalent (`↔`) to $F = P(X) Q(X)^{-1}$ (`PowerSeries.eq_mul_inv_iff_mul_eq`).

In `CommRing (PowerSeries ℚ)`, polynomial ring normalization (`ring`) expands both sides into linear combinations of monomial shifts:
$$Q(X) F = F - 2(X^2 F) + X^4 F, \qquad P(X) = X + 5X^2 - 2X^3 - X^4 + X^5.$$
(`ring` alone cannot close the theorem because `PowerSeries.mk` is opaque to pure ring identities.) By formal power series extensionality (`PowerSeries.ext`), equality holds if and only if $[X^n](Q(X) F) = [X^n] P(X)$ for every $n \in \mathbb{N}$. Pushing the $\mathbb{Q}$-linear coefficient functional `PowerSeries.coeff n` through $+$, $-$, and scalar numerals (`map_add`, `map_sub`, `PowerSeries.coeff_ofNat_mul`) and applying `PowerSeries.coeff_X_pow_mul'`, `PowerSeries.coeff_mk`, `PowerSeries.coeff_X`, and `PowerSeries.coeff_X_pow` reduces the $n$-th coefficient goal to
$$(a(n) : \mathbb{Q}) - 2 \cdot \mathbf{1}_{2 \le n}\,(a(n - 2) : \mathbb{Q}) + \mathbf{1}_{4 \le n}\,(a(n - 4) : \mathbb{Q}) = [X^n] P(X).$$

1. **Initial transient ($n = 0..5$):** Substituting the proved values $a(0) = 0, a(1) = 1, a(2) = 5, a(3) = 0, a(4) = 9, a(5) = 0$ checks all six degrees by rational arithmetic (`norm_num`):

| Degree $n$ | LHS $[X^n](Q(X) F)$ | Numerical Evaluation | RHS $[X^n] P(X)$ | Role |
| ---: | :--- | :---: | ---: | :--- |
| $0$ | $a(0)$ | $0$ | $0$ | Seed $a(0) = 0$ |
| $1$ | $a(1)$ | $1$ | $1$ | Defect $a(1) = 1$ |
| $2$ | $a(2) - 2 a(0)$ | $5 - 0 = 5$ | $5$ | Post-annihilation $a(2) = 5$ |
| $3$ | $a(3) - 2 a(1)$ | $0 - 2 = -2$ | $-2$ | Echo of $a(1) = 1$ |
| $4$ | $a(4) - 2 a(2) + a(0)$ | $9 - 10 + 0 = -1$ | $-1$ | Residual at $n = 4$ ($9 - 10 = -1$) |
| $5$ | $a(5) - 2 a(3) + a(1)$ | $0 - 0 + 1 = 1$ | $+1$ | Residual at $n = 5$ ($0 - (-1) = +1$) |

   Notably, the degree-$4$ and degree-$5$ corrections $-X^4 + X^5$ in Barker's numerator $P(X)$ encode precisely the two guard-excluded residuals of the 4-step recurrence at $n = 4$ and $n = 5$.

2. **Recurrence tail ($n = k + 6 \ge 6$):** Here $2 \le k + 6$, $4 \le k + 6$, and $k + 6 \notin \{1, 2, 3, 4, 5\}$, so the RHS coefficient $[X^{k+6}] P(X)$ vanishes and the LHS equals $(a(k + 6) : \mathbb{Q}) - 2(a(k + 4) : \mathbb{Q}) + (a(k + 2) : \mathbb{Q}) = 0$ by casting Theorem 1.3 at $n = k + 6 > 5$ from $\mathbb{Z}$ to $\mathbb{Q}$ (`exact_mod_cast` + `linarith`). $\square$

---

## 6. Strength Delta and Scope Boundaries

- **Strength delta vs. source (`delta_vs_source: NONE`):** `A266222.c050_bundle` proves all three assertions of Colin Barker's `%F` conjecture block on `OEIS A266222` (`a_closed_form` for $n > 1$, `a_recurrence` for $n > 5$, and `a_gf` over all $n \ge 0$) at full strength under Robert Price's exact `%t` $\mathbb{Z}$-evolution and $[-n, n]$ active-window specification, with sharp guards and bi-equivalent algebraic clearing.
- **What this paper does NOT show:**
  1. It does **not** formalize the seven sibling ON/OFF ECA conjecture bundles (`A266220` ON cells of Rule 7; `A266256`/`A266258` Rule 11; `A266437`/`A266439` Rule 23; `A266662`/`A266664` Rule 47), although `A266220(n) = (2n + 1) - A266222(n)` is an immediate corollary once pinned separately.
  2. It does **not** formalize the binary/decimal row-encoding formulas on `OEIS A266217` and `A266218`.

---

## 7. Lean 4 Formalization and Verification Record

### 7.1 Declaration Map (`Mathproofs/A266222.lean`)

| Mathematical Item | Lean 4 Declaration | Status / Axiom Footprint |
| :--- | :--- | :--- |
| Wolfram ECA Rule 7 local update | `A266222.rule7` | Pinned computable `def`, `0` axioms |
| Global $\mathbb{Z}$-evolution `ca : ℕ → ℤ → Bool` | `A266222.ca` | Pinned computable `def`, `0` axioms |
| Truncated $[-n, n]$ OFF-cell count | `A266222.a` | Pinned `def`, `[propext, Classical.choice, Quot.sound]` |
| Wolfram bitmask `7 = 0b00000111` agreement | `A266222.rule7_eq_testBit` | Proved (`[propext]`) |
| Generation-1 single-defect profile | `A266222.ca_one`, `A266222.a_one` | Proved |
| Two-step defect annihilation ($\forall j,\ \mathrm{ca}(2, j) = \mathtt{false}$) | `A266222.ca_two` | Proved (`[propext, Quot.sound]`) |
| Spatially constant parity invariant ($n \ge 2$) | `A266222.ca_eq_decide_odd` | Proved (`[propext, Classical.choice, Quot.sound]`) |
| **Theorem 1.2 (Closed form, $n > 1$)** | **`A266222.a_closed_form`** | **Proved (allowlist axioms only)** |
| **Theorem 1.3 (Recurrence, $n > 5$)** | **`A266222.a_recurrence`** | **Proved (allowlist axioms only)** |
| **Theorem 1.4 (Generating function in `PowerSeries ℚ`)** | **`A266222.a_gf`** | **Proved (allowlist axioms only)** |
| **Full C050 Bundle** | **`A266222.c050_bundle`** | **Proved (allowlist axioms only)** |
| Causal-cone mirror & formal equivalence | `A266222.a_dp`, `A266222.a_dp_eq_a` | Computable $O(n^2)$ `def` + `∀ n, a_dp n = a n` |
| Kernel spot checks ($n = 0..12$) | `A266222.a_dp_spot_0_to_12`, `A266222.a_spot_0_to_12` | Proved in kernel (`rfl` + `a_dp_eq_a`) |
| Guard-exclusion counterexamples ($n = 0, 1; 4, 5$) | `A266222.a_closed_form_false_zero`, `_one`, `a_recurrence_false_four`, `_five` | Proved in kernel |
| Zero-padding trap separation ($a_{\mathrm{zp}}(2) = 3 \ne 5$) | `A266222.aZeroPad_two_eq_three` | Proved in kernel |

### 7.2 Recorded Trust, Axiom, Non-Vacuity, and Provenance Audit

1. **Artifact source digests bound to toolchain pin (`leanprover/lean4:v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, base `master` `2d8267e1f5e7543e2915d8ed4aee8ae917531882`):**
   - `Mathproofs/A266222.lean` (`504` lines): `2214201545f03424061571ea13eb3cdd51715f8efea33c49e36ec1de192aa6fb` (`0 diff chars` across all seven pinned definitions and theorem signatures against `PIN-C050.md` v1).
   - `Mathproofs.lean` (`81` lines): `6a8961afb57c42516de40bbed1869747c618d944bf32de5b9478eecd806aacfe`.
   - `lakefile.toml` (`19` lines, unchanged from `master`): `5a82a75a91dc597eccd9305c998dffaf6273956b9c0819f0c28cc86040316a21`.
   - Clean-slate full build (`rm -rf .lake/build && lake build`): exit `0` (`17,978` jobs; `0` errors, `0` sorries, `0` warnings on `Mathproofs.A266222`; log SHA-256 `356d2be449252499fe5f2c31d90ebcb85ee8233db1154f0d3e527fa997656bdc`).
2. **Axiom footprint (`#print axioms`):**
   - `A266222.rule7`, `A266222.ca`: depend on **no axioms**.
   - `A266222.a`, `A266222.a_closed_form`, `A266222.a_recurrence`, `A266222.a_gf`, `A266222.c050_bundle`, `A266222.a_dp_eq_a`, `A266222.a_spot_0_to_12`: `[propext, Classical.choice, Quot.sound]` (exact allowlist).
3. **Transitive kernel closure & lexical trust-escape screen:**
   - Comment/string-stripped lexical scan across `Mathproofs/A266222.lean`, `Mathproofs.lean`, and `Main.lean`: **`0` active hits** (and **`0` raw hits**) for `sorry`, `admit`, `sorryAx`, `axiom`, `native_decide`, `ofReduceBool`, `implemented_by`, `unsafe`.
   - `CoreM` transitive constant-closure audit (`1,255` constants): `DISALLOWED_AXIOMS = []`, `sorryAx = false`, `ofReduceBool = false`, `ofReduceNat = false`, `trustCompiler = false`.
   - Fresh-kernel replay (`lake env leanchecker --fresh --verbose Mathproofs.A266222`): **exit `0`** (`replaying Mathproofs.A266222 with --fresh`).
4. **Non-vacuity & computation boundary (stated explicitly):**
   - Because `A266222.a` uses `Finset.Icc` / `Finset.filter` over `ℤ` (importing `Classical.choice` and `Quot.sound` in Mathlib) and unmemoized recursion in `A266222.ca` makes $(2n+1)\cdot 3^n$ tree calls, `A266222.a` does not reduce directly by bare `rfl` in Lean's kernel.
   - **Proved inside Lean's kernel:** `A266222.a_dp_spot_0_to_12` evaluates the shrinking causal-cone mirror `A266222.a_dp` on `n = 0..12` to `[0, 1, 5, 0, 9, 0, 13, 0, 17, 0, 21, 0, 25]` by pure kernel `rfl`, `A266222.a_spot_0_to_12` transfers that equality onto the pinned `A266222.a` via the formally proved equivalence `A266222.a_dp_eq_a`, and the four guard-exclusion theorems (`a_closed_form_false_zero`, `a_closed_form_false_one`, `a_recurrence_false_four`, `a_recurrence_false_five`) plus `aZeroPad_two_eq_three` are proved in the kernel.
   - **Verified via Lean VM `#eval` and Python recomputation (not claimed as kernel `rfl` reductions):** `#eval` on `A266222.a_dp` across $n = 0..100$ and independent Python simulation across $n = 0..500$ agree with all $500$ terms of Robert Price's OEIS table `b266222.txt` (`0` mismatches).
5. **Provenance & review status:**
   - High-level route from Seam B triage (`TRIAGE-SEAMB.md` §3.2), re-derived and audited against Mathlib `v4.34.1` in `SCOPING-C050.md` (`carbon-c050-scoping-20261114`), target frozen in `PIN-C050.md` v1, and Lean 4 proof authored in `carbon-c050-proof-20261116` (`nibbles`, Gemini 4 Carbon High).
   - Crossed-review status at initial draft PR opening: **`NOT YET RUN (PENDING)`** (awaiting review by a fresh Gemini 4 Carbon High session disjoint from this author session — session-level independence).

---

## References

1. Robert Price and Colin Barker, *OEIS Sequence A266222: Number of OFF (white) cells in the $n$-th iteration of the "Rule 7" elementary cellular automaton starting with a single ON (black) cell* (authored by Robert Price, December 24, 2015; `%F` conjectures by Colin Barker, December 26, 2015 and April 13, 2019; revision `#17`, February 16, 2025), and companion sequences `A266216`–`A266221`, `A266223`, The On-Line Encyclopedia of Integer Sequences, https://oeis.org/A266222.
2. Stephen Wolfram, *A New Kind of Science*, Wolfram Media, Champaign, IL, 2002, p. 55.
3. N. J. A. Sloane, *On the Number of ON Cells in Cellular Automata*, arXiv:1503.01168v1 [math.CO], March 4, 2015.
4. The mathlib Community, *The Lean Mathematical Library (`Mathlib4`)*, commit `d13f23b723b8a846827a245b89c10fc7d3f11612` (`v4.34.1`), 2026.
