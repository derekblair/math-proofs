# Cumulative Prefix Partitions and Overflow-to-Gap Lattice Transposition: Proof and Lean 4 Formalization of Werner Schulte's OEIS A385590 Fibonacci Triangle Bijection Conjecture

**Preprint Draft (`PAPER-S003.md`) — 2026-11-16**  
**Repository / Module:** `derekblair/math-proofs` (`SeamC/A385590/Statement.lean`, `namespace SeamC.A385590`)  
**Toolchain & Mathlib Pin:** `leanprover/lean4:v4.34.1` (`commit 5045d0056413266e57c625dcd7c365b10e377c52`), Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`  
**Target Contract:** `PIN-S003.md` v1 (`SHA-256: 577beae0ddb023bb2afdf9cb8f9d4d97cd7ebbd2b247bd37a226e469c2106d7d`, `delta_vs_source: NONE`)

---

## Abstract

Let $(F_m)_{m \ge 0} = (0, 1, 1, 2, 3, 5, 8, 13, \dots)$ denote the Fibonacci numbers (`OEIS A000045`). For every integer $n \ge 1$, let $i = \operatorname{A130233}(n) \ge 2$ be the unique index satisfying $F_i \le n < F_{i+1}$. On July 3, 2025, Werner Schulte introduced the triangular array `OEIS A385590`,
$$T(n, k) := F_{i-1}^2 + 1 - \big((i - 1) \bmod 2\big) + (n - F_i) F_{i-2} + (k - 1) F_{i-1} \qquad (1 \le k \le n),$$
and conjectured (`%C` line 11) that $T$ yields a permutation of the positive integers $\mathbb{N}_{\ge 1} = \{1, 2, 3, \dots\}$.

Individual Fibonacci row blocks $\Delta_i := \{(n, k) \in \mathbb{N}^2 : F_i \le n < F_{i+1},\ 1 \le k \le n\}$ do **not** tile consecutive square intervals $[F_{i-1}^2 + 1, F_i^2]$: asymptotically $|\Delta_i| / (F_i^2 - F_{i-1}^2) \to \varphi^2 / 2 = (3 + \sqrt{5})/4 \approx 1.3090 > 1$, so every block for $i \ge 4$ both omits values below $F_i^2$ and overflows past $F_i^2$. We resolve Schulte's conjecture unconditionally across all $(n, k)$ with $1 \le k \le n$ by proving an exact cumulative prefix-partition invariant. Writing $b_i := F_{i-1}^2 + 1 - ((i - 1) \bmod 2) = F_{i-1}^2 + (i \bmod 2)$, Cassini's identity $F_{i-1}^2 - F_i F_{i-2} = (-1)^i$ implies the block-base recurrence $b_i + F_i F_{i-1} = b_{i+1}$ and shows that row $r = n - F_i$ of $\Delta_i$ has one-past-the-end value $b_{i+1} + r F_i < b_{i+2}$. Crucially, the overflow set $O_i := T(\Delta_i) \cap [b_{i+1}, \infty)$ coincides via the involutive lattice transposition $(r, t) \mapsto (F_i - t, F_{i-1} - r)$ with the pre-start residue-class gap set $G_{i+1}$ of the next block $\Delta_{i+1}$. Consecutive-Fibonacci coprimality $\gcd(F_i, F_{i-1}) = 1$ then forces $O_i \cap T(\Delta_{i+1}) = \emptyset$ and $[b_{i+1}, b_{i+2} - 1] \subseteq O_i \sqcup T(\Delta_{i+1})$, establishing by induction on $i \ge 2$ that the prefix union $\bigcup_{j=2}^i T(\Delta_j)$ is a pairwise disjoint union equal to $[1, b_{i+1} - 1] \sqcup O_i$, with $b_{i+1} = T(F_{i+1}, 1)$ as the exact least missing positive integer. The proof, structural corollaries, and kernel `rfl` verifications of `OEIS A385590` rows `1..13` are formalized in Lean 4 with zero `sorry`s, zero custom axioms, and zero trust escapes.

---

## 1. Introduction and Primary-Source Context

### 1.1 Werner Schulte's Fibonacci Triangle (`OEIS A385590`)

Let $F_0 = 0, F_1 = 1, F_{m+2} = F_m + F_{m+1}$ denote the standard Fibonacci sequence (`OEIS A000045` [2]). Because $F_2 = 1$ and $F_{i+1} - F_i = F_{i-1} \ge 1$ for every $i \ge 2$, the sequence $(F_i)_{i \ge 2} = (1, 2, 3, 5, 8, 13, 21, \dots)$ is strictly increasing, and the half-open intervals $[F_i, F_{i+1})$ ($i \ge 2$) partition $\mathbb{N}_{\ge 1}$ into pairwise disjoint blocks of lengths $F_{i+1} - F_i = F_{i-1}$. For $n \ge 1$, the unique index $i \ge 2$ with $F_i \le n < F_{i+1}$ agrees with Hieronymus Fischer's lower Fibonacci inverse $i = \operatorname{A130233}(n) := \max\{k \ge 0 : F_k \le n\}$ [3] (noting at the boundary $n = 1$ that $F_1 = F_2 = 1 < 2 = F_3$ gives $\operatorname{A130233}(1) = 2$).

On July 3, 2025, Werner Schulte introduced the triangular array `OEIS A385590` (`#7 Jul 07 2025 20:01:36`, offset `%O A385590 1,2` [1]), defined for $n \ge 1$ and $1 \le k \le n$ (`%N` line 10) by
$$T(n, k) = F_{i-1}^2 + 1 - \big((i - 1) \bmod 2\big) + (n - F_i) F_{i-2} + (k - 1) F_{i-1}, \qquad F_i \le n < F_{i+1},\ i > 1.$$
The first eight rows (`%e` lines 16–23 of [1], corresponding to Fibonacci blocks $\Delta_2, \Delta_3, \Delta_4, \Delta_5$, and the first row of $\Delta_6$) begin:

$$\begin{array}{r|cccccccc}
n \backslash k & 1 & 2 & 3 & 4 & 5 & 6 & 7 & 8 \\ \hline
1 \ (\Delta_2) & 1 \\
2 \ (\Delta_3) & 2 & 3 \\
3 \ (\Delta_4) & 4 & 6 & 8 \\
4 \ (\Delta_4) & 5 & 7 & 9 & 11 \\
5 \ (\Delta_5) & 10 & 13 & 16 & 19 & 22 \\
6 \ (\Delta_5) & 12 & 15 & 18 & 21 & 24 & 27 \\
7 \ (\Delta_5) & 14 & 17 & 20 & 23 & 26 & 29 & 32 \\
8 \ (\Delta_6) & 25 & 30 & 35 & 40 & 45 & 50 & 55 & 60
\end{array}$$

Schulte recorded two conjectures in `OEIS A385590`:
1. **`%C` line 11 (`S003` — target of this paper):** *"Conjecture: This triangle yields a permutation of the natural numbers."*
2. **`%F` line 12 (`S004` — sibling affine row-sum conjecture):** $\sum_{k=1}^n (-1)^k \binom{n-1}{k-1} T(n, k) = 0$ for $n > 2$ and $(-1)^n$ for $n < 3$.

Because $T(n, k)$ is affine-linear in $k$ along each fixed row $n$, the sibling `%F` line 12 identity follows immediately from $\sum_{j=0}^{n-1} (-1)^j \binom{n-1}{j} = 0$ ($n \ge 2$) and $\sum_{j=0}^{n-1} (-1)^j j \binom{n-1}{j} = 0$ ($n \ge 3$), and was previously formalized in `the-omega-institute/trureturing` (`D5/S1/Recurrence/Parity/A385590.alternating_binomial_sum` [4]), whose blueprint explicitly notes: *"The other conjecture in the entry, that the triangle permutes the natural numbers, is a separate question."* Prior-art screening across live OEIS, `trureturing` (`HEAD`), arXiv, Zenodo, and web search confirmed that `%C` line 11 (`S003`) remained completely unproved prior to the present work.

### 1.2 Main Results

We prove Schulte's `%C` line 11 conjecture unconditionally at full strength, together with the exact prefix-partition structure governing how consecutive Fibonacci blocks interleave:

- **Theorem 1.1 (Main Theorem — `SeamC.A385590.triangle_bijective_posNat`).** *The Fibonacci triangle map*
  $$T : \big\{ (n, k) \in \mathbb{N} \times \mathbb{N} \;\big|\; 1 \le n \wedge 1 \le k \wedge k \le n \big\} \longrightarrow \big\{ m \in \mathbb{N} \;\big|\; 1 \le m \big\}$$
  *is bijective (`Function.Bijective`).*
- **Theorem 1.2 (Overflow-to-Gap Lattice Transposition — `SeamC.A385590.overflow_eq_next_gap`).** *For every $i \ge 2$, let $b_i := F_{i-1}^2 + 1 - ((i - 1) \bmod 2)$ and $O_i := T(\Delta_i) \cap [b_{i+1}, \infty)$. Then $(r, t) \mapsto (F_i - t, F_{i-1} - r)$ bijectively identifies $O_i$ with the pre-start residue-class gap set*
  $$G_{i+1} := \big\{\, b_{i+1} + r' F_{i-1} - u F_i \;\big|\; 0 \le r' < F_i,\ u \ge 1,\ u F_i \le r' F_{i-1} \,\big\}.$$
- **Theorem 1.3 (Cumulative Prefix Partition & Least Missing Law — `cumulative_prefix_partition`, `least_missing_posNat_prefix`).** *For every $i \ge 2$, the block images $T(\Delta_2), \dots, T(\Delta_i)$ are pairwise disjoint and satisfy*
  $$\bigsqcup_{j=2}^i T(\Delta_j) = \{1, 2, \dots, b_{i+1} - 1\} \sqcup O_i, \qquad O_i \subseteq [b_{i+1} + 1,\ b_{i+2} - 1].$$
  *In particular, rows $1, \dots, F_{i+1} - 1$ cover $[1, F_i^2]$ completely when $i$ is even and $[1, F_i^2 - 1]$ completely when $i$ is odd, with $b_{i+1} = T(F_{i+1}, 1)$ as the exact least positive integer not yet attained.*

---

## 2. Formal Specification and Convention Audit

In Lean 4 (`SeamC/A385590/Statement.lean`, `namespace SeamC.A385590`), the pinned definitions and theorem statement of `PIN-S003.md` v1 are formalized directly over Mathlib's `Nat.fib` and `Nat.greatestFib`:

```lean
abbrev F : ℕ → ℕ := Nat.fib

def blockIndex (n : ℕ) : ℕ :=
  Nat.greatestFib n

def T (n k : ℕ) : ℕ :=
  let i := blockIndex n
  F (i - 1) ^ 2 + 1 - ((i - 1) % 2) + (n - F i) * F (i - 2) + (k - 1) * F (i - 1)

theorem triangle_bijective_posNat :
    Function.Bijective
      (fun q : { p : ℕ × ℕ // 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.2 ≤ p.1 } =>
        (⟨T q.val.1 q.val.2, one_le_T q.property.1 q.val.2⟩ : { m : ℕ // 1 ≤ m }))
```

Three foundational fidelity checks confirm zero convention drift against Schulte's `OEIS A385590` record (`delta_vs_source: NONE`):

1. **1-indexed triangle domain and positive-integer codomain $\mathbb{N}_{\ge 1}$.** The triangle domain $\{(n, k) : 1 \le n \wedge 1 \le k \le n\}$ and positive-integer codomain $\{m \in \mathbb{N} : 1 \le m\}$ are fixed unambiguously by `%O A385590 1,2`, `%e` line 13 (`"Triangle T(n, k) for 1 <= k <= n starts:"`), `%S` line 7 (`1,2,3,4,6,8,5,7,9,11,10,13,...`), `%o` line 30 (`(k-1)*fibonacci(i-1)`), and keyword `tabl`. Algebraically (`one_le_T`), for $n \ge 1$ we have $i \ge 2$, so $F_{i-1} \ge F_1 = 1$ and $(i - 1) \bmod 2 \le 1$, giving $(F_{i-1}^2 + 1) - ((i - 1) \bmod 2) \ge 2 - 1 = 1$; thus $T(n, k) \ge 1$ holds unconditionally across the entire domain, and $0$ never occurs. *(Note: preliminary intake notes misquoted `%S` line 7 as `1, 3, 4, 2, 5, ...` and wrote `T(3, 1) = 2`; the live OEIS record has row 3 equal to `4, 6, 8`, verified in the Lean kernel by `T_boundary_spot_checks` and `T_oeis_rows_1_to_13`.)*
2. **Computable exactness of `blockIndex n = Nat.greatestFib n` (`fibBlockIndex_existsUnique`).** Mathlib's `Nat.greatestFib n = (n + 1).findGreatest (fun k => Nat.fib k ≤ n)` (`Mathlib.Data.Nat.Fib.Zeckendorf`) is purely computable (free of `Classical.choice` and `Nat.find`) and satisfies `m ≤ greatestFib n ↔ fib m ≤ n`. For every $n \ge 1$, $F_2 = 1 \le n$ gives $2 \le \operatorname{blockIndex}(n)$ and $F_{\operatorname{blockIndex}(n)} \le n < F_{\operatorname{blockIndex}(n)+1}$ (`blockIndex_spec`), and `fibBlockIndex_existsUnique` proves in Lean's kernel that `blockIndex n` is the unique $i \ge 2$ with $F_i \le n < F_{i+1}$.
3. **The $n = 1$ boundary and non-truncating $\mathbb{N}$-subtractions.** At $(n, k) = (1, 1)$, although $F_1 = F_2 = 1$, the half-open condition $F_i \le 1 < F_{i+1}$ with $i > 1$ uniquely selects $i = 2$ (`blockIndex 1 = 2` by `rfl`, matching `A130233(1) = 2` and `%o` PARI), yielding $T(1, 1) = 1 + 1 - 1 + 0 + 0 = 1$. Every subtraction in `T n k` (`i - 1`, `i - 2`, `(F(i - 1)^2 + 1) - ((i - 1) % 2)`, `n - F i`, `k - 1`) is guarded against $\mathbb{N}$-truncation across $1 \le k \le n$, as certified by the exact $\mathbb{Z}$-lifting identity `T_cast_int_eq_blockLocal`.

---

## 3. Failure of Per-Block Square Tiling and the Overflow Mechanism

A naive first guess (`TRIAGE-SEAMC.md` §1.2–§1.3, refuted during coordinator verification and `SCOPING-S003.md` §2.1) suggests that each Fibonacci row block $\Delta_i = \{(n, k) : F_i \le n < F_{i+1},\ 1 \le k \le n\}$ might bijectively tile the consecutive square interval $[F_{i-1}^2 + 1, F_i^2]$. **Both the cardinality equality and the interval inclusion are arithmetically false:**

- **Block cardinality vs. square-gap width:** Since row $n$ has $n$ entries and $F_{i+1} - F_i = F_{i-1}$,
  $$|\Delta_i| = \sum_{n = F_i}^{F_{i+1} - 1} n = \frac{F_{i-1}(2 F_i + F_{i-1} - 1)}{2}, \qquad \text{whereas} \qquad F_i^2 - F_{i-1}^2 = F_{i-2} F_{i+1}.$$
  Dividing by $F_i^2$ and letting $i \to \infty$ ($F_{i-1}/F_i \to \varphi^{-1}$) gives
  $$\lim_{i \to \infty} \frac{|\Delta_i|}{F_i^2 - F_{i-1}^2} = \frac{\varphi^{-1}(2 + \varphi^{-1}) / 2}{1 - \varphi^{-2}} = \frac{2\varphi + 1}{2\varphi} = \frac{\varphi^2}{2} = \frac{3 + \sqrt{5}}{4} \approx 1.3090 > 1.$$
  In fact, $|\Delta_i| = F_i^2 - F_{i-1}^2$ fails for **every** $i \ge 2$ (`0 / 18` blocks across $i = 2..19$).
- **Explicit counterexample at $i = 4$ (`block4_refutes_per_block_tiling`):** Block $\Delta_4$ consists of rows $3$ and $4$ ($F_4 = 3 \le n < 5 = F_5$), giving $|\Delta_4| = 3 + 4 = 7 \ne 5 = 3^2 - 2^2$. Its image is
  $$T(\Delta_4) = \{4, 6, 8\} \cup \{5, 7, 9, 11\} = \{4, 5, 6, 7, 8, 9, 11\},$$
  which *underflows* $[5, 9]$ at $4 = F_3^2$ (filling the single value below $4$ left uncovered by $T(\Delta_2) \cup T(\Delta_3) = \{1, 2, 3\}$), *overflows* $[5, 9]$ at $11$, and *omits* $10$, which appears first at $T(5, 1) = 10 \in T(\Delta_5)$.

Why does $11 \in T(\Delta_4)$ never collide with $\Delta_5$ or any later block, and why is every value omitted above $b_5 = 10$ by $\Delta_4$ filled by $\Delta_5$? In block $\Delta_5$ (rows $5, 6, 7$, step $F_4 = 3$), the three rows start at $10, 12, 14$:
- Row $5$ ($0 \bmod 3$ shifted by $10$): $10, 13, 16, 19, 22$ (starts at $10$; no gap $\ge 10$ below $10$).
- Row $6$ ($2 \bmod 3$ shifted by $10$): $12, 15, 18, 21, 24, 27$ (starts at $12$; misses none in $[10, 11]$ since $12 - 3 = 9 < 10$).
- Row $7$ ($1 \bmod 3$ shifted by $10$): $14, 17, 20, 23, 26, 29, 32$ (starts at $14$; misses **$14 - 3 = 11 \ge 10$**!).

The single pre-start gap of $\Delta_5$ in $[b_5, \infty)$ is $\{11\}$, which is **identical** to the overflow $O_4 = \{11\}$ of $\Delta_4$. Theorem 1.2 (`overflow_eq_next_gap`) proves that this exact cancellation $O_i = G_{i+1}$ holds for every $i \ge 2$.

---

## 4. Proof of the Main Theorem (`L1`–`L10` Decomposition)

Throughout this section we follow the ten-lemma architecture `L1`–`L10` formulated during scoping (`SCOPING-S003.md` §2.3), re-derived with exact index bounds (`i ≥ 2` in `L2` so $i - 2 \ge 0$ never truncates in $\mathbb{N}$). For $i \ge 2$, write
$$b_i := F_{i-1}^2 + 1 - \big((i - 1) \bmod 2\big) = F_{i-1}^2 + (i \bmod 2) \qquad (\text{`b`, `b_eq_fib_sq_add_mod`}),$$
and parameterize $\Delta_i$ by block-local coordinates $r = n - F_i \in \{0, \dots, F_{i-1} - 1\}$ and $c = k - 1 \in \{0, \dots, F_i + r - 1\}$.

### 4.1 Block Coordinates, Cassini's Identity, and the Block-Base Recurrence (`L1`–`L4`)

- **Lemma 4.1 (`L1` — `fibBlockIndex_existsUnique`, `T_eq_blockLocal`, `T_cast_int_eq_blockLocal`).** *For every $n \ge 1$, there is a unique $i \ge 2$ with $F_i \le n < F_{i+1}$, namely $i = \operatorname{blockIndex}(n)$. For $(n, k) \in \Delta_i$ with $r = n - F_i$ and $c = k - 1$, one has $0 \le r < F_{i-1}$, $0 \le c < F_i + r$, $T(n, k) \ge 1$, and*
  $$T(n, k) = b_i + r F_{i-2} + c F_{i-1}$$
  *(both in $\mathbb{N}$ and after casting to $\mathbb{Z}$).*
- **Lemma 4.2 (`L2` — `fib_cassini_shift`, `fib_cassini_and_coprime`).** *For every $m \in \mathbb{N}$, $F_{m+1}^2 - F_{m+2} F_m = (-1)^m$ in $\mathbb{Z}$. Equivalently, for every $i \ge 2$,*
  $$F_{i-1}^2 - F_i F_{i-2} = (-1)^i \qquad \text{and} \qquad \gcd(F_{i-1}, F_{i-2}) = 1.$$
  *Proof.* Induction on $m$ using $F_{m+3} = F_{m+1} + F_{m+2}$ and $F_{m+2} = F_m + F_{m+1}$ gives $F_{m+2}^2 - F_{m+3} F_{m+1} = -(F_{m+1}^2 - F_{m+2} F_m) = (-1)^{m+1}$; setting $m = i - 2$ ($i \ge 2$) yields $(-1)^{i-2} = (-1)^i$, and coprimality follows from `Nat.fib_coprime_fib_succ`. $\square$

- **Lemma 4.3 (`L3` — `blockBase_succ_eq`).** *For every $i \ge 2$, $b_i + F_i F_{i-1} = b_{i+1}$, $b_i < b_{i+1}$, $i - 1 \le b_i$, and*
  $$b_{i+1} - 1 = \begin{cases} F_i^2 & \text{if } i \equiv 0 \pmod 2, \\ F_i^2 - 1 & \text{if } i \equiv 1 \pmod 2. \end{cases}$$
  *Proof.* Writing $i = k + 1$ ($k \ge 1$), $F_k^2 + F_{k+1} F_k = F_k(F_k + F_{k+1}) = F_{k+2} F_k = F_{k+1}^2 - (-1)^k$ by Lemma 4.2. Checking $k \bmod 2 \in \{0, 1\}$ gives $((k + 1) \bmod 2) - (-1)^k = (k + 2) \bmod 2$, so $b_{k+1} + F_{k+1} F_k = b_{k+2}$. Since $F_i, F_{i-1} \ge 1$, $b_i < b_{i+1}$, and $i - 1 \le b_i$ follows by induction from $b_2 = 1$. $\square$

- **Lemma 4.4 (`L4` — `row_endpoint_eq`, `row_endpoint_and_max_lt`).** *For every $i \ge 2$ and $r \in \mathbb{N}$, the one-past-the-end row value ($c = F_i + r$) satisfies*
  $$e_{i, r} := b_i + r F_{i-2} + (F_i + r) F_{i-1} = b_{i+1} + r F_i.$$
  *Consequently, for every $(n, k) \in \Delta_i$, $b_i \le T(n, k) < b_{i+2}$.*
  *Proof.* Using $F_{i-2} + F_{i-1} = F_i$ and Lemma 4.3, $b_i + r F_{i-2} + (F_i + r)F_{i-1} = (b_i + F_i F_{i-1}) + r(F_{i-2} + F_{i-1}) = b_{i+1} + r F_i$. On $\Delta_i$, $c < F_i + r$ and $F_{i-1} \ge 1$ give $T(n, k) < b_{i+1} + r F_i$, and $r < F_{i-1} \le F_{i+1}$ gives $b_{i+1} + r F_i \le b_{i+1} + F_{i+1} F_i = b_{i+2}$. $\square$

### 4.2 Intra-Block Injectivity and the Overflow-to-Gap Transposition (`L5`–`L7`)

- **Lemma 4.5 (`L5` — `triangle_injective_on_block`).** *For every $i \ge 2$, $T$ is injective on $\Delta_i$.*
  *Proof.* Suppose $b_i + r_1 F_{i-2} + c_1 F_{i-1} = b_i + r_2 F_{i-2} + c_2 F_{i-1}$ with $0 \le r_1 \le r_2 < F_{i-1}$. Then $(r_2 - r_1) F_{i-2} = F_{i-1}(c_1 - c_2)$ in $\mathbb{N}$, so $F_{i-1} \mid (r_2 - r_1) F_{i-2}$. By $\gcd(F_{i-1}, F_{i-2}) = 1$ (`L2`), $F_{i-1} \mid r_2 - r_1$. Since $0 \le r_2 - r_1 < F_{i-1}$, $r_1 = r_2$, and cancelling $F_{i-1} > 0$ gives $c_1 = c_2$. $\square$

- **Lemma 4.6 (`L6` — `block_overflow_iff`).** *For every $i \ge 2$ and $m \in \mathbb{N}$, $m \in O_i := T(\Delta_i) \cap [b_{i+1}, \infty)$ if and only if there exist $r, t \in \mathbb{N}$ such that*
  $$0 \le r < F_{i-1}, \qquad t \ge 1, \qquad t F_{i-1} \le r F_i, \qquad m = b_{i+1} + r F_i - t F_{i-1} \quad (\text{in } \mathbb{Z}).$$
  *Proof.* Re-index $c \in \{0, \dots, F_i + r - 1\}$ from the right endpoint by $t := F_i + r - c \ge 1$. By Lemma 4.4, $b_i + r F_{i-2} + c F_{i-1} = e_{i, r} - t F_{i-1} = b_{i+1} + r F_i - t F_{i-1}$ in $\mathbb{Z}$, so $m \ge b_{i+1}$ holds iff $t F_{i-1} \le r F_i$. Conversely, $t F_{i-1} \le r F_i < F_{i-1} F_i$ forces $1 \le t < F_i \le F_i + r$, so $c := F_i + r - t \in \{0, \dots, F_i + r - 1\}$ reconstructs a valid point of $\Delta_i$. $\square$

- **Lemma 4.7 (`L7` — `overflow_eq_next_gap`).** *For every $i \ge 2$, $O_i = G_{i+1}$.*
  *Proof.* Given $(r, t)$ witnessing $m \in O_i$, $t F_{i-1} \le r F_i < F_{i-1} F_i$ gives $1 \le t < F_i$. Define $(r', u) := (F_i - t,\ F_{i-1} - r)$. Then $0 \le r' < F_i$, $u \ge 1$, and in $\mathbb{Z}$ we have the polynomial identity
  $$r' F_{i-1} - u F_i = (F_i - t) F_{i-1} - (F_{i-1} - r) F_i = r F_i - t F_{i-1} \ge 0,$$
  so $u F_i \le r' F_{i-1}$ and $m = b_{i+1} + r' F_{i-1} - u F_i \in G_{i+1}$. Conversely, given $(r', u)$ witnessing $m \in G_{i+1}$, $u F_i \le r' F_{i-1} < F_i F_{i-1}$ gives $1 \le u < F_{i-1}$, and the inverse map $(r, t) := (F_{i-1} - u,\ F_i - r')$ places $m \in O_i$. $\square$

### 4.3 Modular Dichotomy, Cumulative Prefix Induction, and Bijectivity (`L8`–`L10`)

- **Lemma 4.8 (`L8` — `mod_fib_rep_unique`, `mod_fib_rep_exists`, `mod_fib_dichotomy`).** *For every $i \ge 2$:*
  1. *Every $x \in \mathbb{Z}$ admits a unique representation $x = r' F_{i-1} + z F_i$ with $0 \le r' < F_i$ and $z \in \mathbb{Z}$.*
  2. *$O_i \cap T(\Delta_{i+1}) = \emptyset$, $b_{i+1} \notin O_i$, and every $m \in [b_{i+1}, b_{i+2} - 1]$ belongs to $O_i \cup T(\Delta_{i+1})$.*
  *Proof.* For uniqueness, if $r_1 F_{i-1} + z_1 F_i = r_2 F_{i-1} + z_2 F_i$ with $0 \le r_1 \le r_2 < F_i$, then $(r_2 - r_1) F_{i-1} = (z_1 - z_2) F_i \ge 0$, so $F_i \mid (r_2 - r_1) F_{i-1}$; coprimality $\gcd(F_i, F_{i-1}) = 1$ gives $F_i \mid r_2 - r_1$, hence $r_1 = r_2$ and $z_1 = z_2$. For existence, set $a := x (-1)^i F_{i-1}$, $r' := a \bmod F_i \in [0, F_i - 1]$, and $q := \lfloor a / F_i \rfloor$, so $r' + F_i q = a$. Defining $z := -x (-1)^i F_{i-2} + q F_{i-1}$, Cassini's identity $F_{i-1}^2 - F_i F_{i-2} = (-1)^i$ yields
  $$r' F_{i-1} + z F_i = (a - F_i q) F_{i-1} + \big(-x(-1)^i F_{i-2} + q F_{i-1}\big) F_i = x(-1)^i\big(F_{i-1}^2 - F_i F_{i-2}\big) = x.$$
  Applying this to $x = m - b_{i+1}$: elements of $O_i = G_{i+1}$ have $z = -u < 0$, whereas elements of $T(\Delta_{i+1})$ have $0 \le z = c' < F_{i+1} + r'$. By uniqueness of $(r', z)$, $O_i \cap T(\Delta_{i+1}) = \emptyset$ (and $b_{i+1}$ has $(r', z) = (0, 0) \in T(\Delta_{i+1})$, so $b_{i+1} \notin O_i$). Finally, if $b_{i+1} \le m < b_{i+2}$, then:
  - if $z < 0$, $u := -z \ge 1$ satisfies $u F_i \le r' F_{i-1}$ because $m - b_{i+1} \ge 0$, so $m \in G_{i+1} = O_i$;
  - if $z \ge 0$, $c' := z \ge 0$ satisfies $b_{i+1} + r' F_{i-1} + c' F_i = m < b_{i+2} \le b_{i+2} + r' F_{i+1} = b_{i+1} + r' F_{i-1} + (F_{i+1} + r') F_i$ (by Lemma 4.4 at $i + 1$), whence $c' < F_{i+1} + r'$ and $m \in T(\Delta_{i+1})$. $\square$

- **Lemma 4.9 (`L9` — `cumulative_prefix_partition`).** *For every $i \ge 2$, let $U_i := \bigcup_{j=2}^i T(\Delta_j)$. Then $U_i = [1, b_{i+1} - 1] \sqcup O_i$, and $T(\Delta_{j_1}) \cap T(\Delta_{j_2}) = \emptyset$ whenever $2 \le j_1 < j_2$.*
  *Proof.* We induct on $i \ge 2$. At $i = 2$, $\Delta_2 = \{(1, 1)\}$, $T(\Delta_2) = \{1\}$, $b_3 = 2$, and $O_2 = \emptyset$, so $U_2 = \{1\} = [1, 1] \sqcup \emptyset$. Given $U_i = [1, b_{i+1} - 1] \sqcup O_i$, notice first that every $m \in T(\Delta_{i+1})$ satisfies $m \ge b_{i+1}$ (`L4`) and $m \notin O_i$ (`L8`), so $U_i \cap T(\Delta_{i+1}) = \emptyset$ (`disjoint_prefixImage_succ`, which immediately implies $T(\Delta_{j_1}) \cap T(\Delta_{j_2}) = \emptyset$ for all $2 \le j_1 < j_2$). Next, splitting $T(\Delta_{i+1})$ at $b_{i+2}$ into $\big(T(\Delta_{i+1}) \cap [b_{i+1}, b_{i+2} - 1]\big) \sqcup O_{i+1}$ and combining $O_i \subseteq [b_{i+1}, b_{i+2} - 1]$ (`L4`) with $[b_{i+1}, b_{i+2} - 1] \subseteq O_i \cup T(\Delta_{i+1})$ (`L8`) yields $U_{i+1} = U_i \cup T(\Delta_{i+1}) = [1, b_{i+2} - 1] \sqcup O_{i+1}$. $\square$

- **Proof of Theorem 1.1 (`L10` — `triangle_bijective_posNat`).**
  - *Injectivity:* Let $q_1 = ((n_1, k_1), \_)$ and $q_2 = ((n_2, k_2), \_)$ satisfy $T(n_1, k_1) = T(n_2, k_2)$. Let $i_1 = \operatorname{blockIndex}(n_1) \ge 2$ and $i_2 = \operatorname{blockIndex}(n_2) \ge 2$. Then $T(n_1, k_1) \in T(\Delta_{i_1}) \cap T(\Delta_{i_2})$, so pairwise block disjointness (`L9`) forces $i_1 = i_2$, and intra-block injectivity (`L5`) forces $(n_1, k_1) = (n_2, k_2)$, hence $q_1 = q_2$.
  - *Surjectivity:* Given $m \ge 1$, Lemma 4.3 gives $m + 2 = (m + 3) - 1 \le b_{m+3}$, so $1 \le m < b_{(m+2)+1}$. By Lemma 4.9 at $i = m + 2 \ge 2$, $m \in U_{m+2}$, providing $j \in \{2, \dots, m + 2\}$ and $(n, k) \in \Delta_j$ with $T(n, k) = m$ and $1 = F_2 \le F_j \le n$. $\square$

---

## 5. Strength Delta and What This Paper Does Not Show

- **Strength delta vs. published source (`delta_vs_source: NONE`, `equal`):** Theorem 1.1 (`SeamC.A385590.triangle_bijective_posNat`) establishes Werner Schulte's `OEIS A385590` `%C` line 11 conjecture (`#7 Jul 07 2025`) unconditionally across the full triangle domain $\{(n, k) : 1 \le k \le n\}$ onto $\mathbb{N}_{\ge 1}$, with zero range bounds, zero parity restrictions, and zero auxiliary hypotheses.
- **What this paper does NOT show:**
  1. It does **not** re-prove or claim authorship of the sibling `%F` line 12 alternating binomial row-sum identity (`S004`), which was already proved and formalized in `the-omega-institute/trureturing` (`D5/S1/Recurrence/Parity/A385590.alternating_binomial_sum` [4]).
  2. While `triangle_bijective_posNat` proves existence and uniqueness of $T^{-1}(m)$ for every $m \ge 1$ (and `mod_fib_rep_exists` gives an explicit closed-form modular formula within each consecutive block transition), we do not formalize a separate OEIS inverse-sequence entry for the flattened row-major inverse permutation (no such inverse A-number is cross-referenced in `A385590`).
  3. We do not study generalizations of $T(n, k)$ to Lucas, Pell, or higher-order Ostrowski/Horadam numeration systems.

---

## 6. Lean 4 Formalization and Recorded Verification Audit

### 6.1 Declaration Map (`SeamC/A385590/Statement.lean`)

| Mathematical Component | Lean 4 Declaration (`SeamC.A385590.*`) | Role & Status |
| :--- | :--- | :--- |
| Fibonacci sequence $F = \mathrm{Nat.fib}$ (`A000045`) | `F` | Pinned computable `abbrev` (`0` axioms) |
| Block index $i = \mathrm{Nat.greatestFib}\ n$ (`A130233`) | `blockIndex` | Pinned computable `def` (`0` axioms) |
| `L1` block-index uniqueness & $\mathbb{Z}$-lift | `blockIndex_spec`, `fibBlockIndex_existsUnique`, `T_eq_blockLocal`, `T_cast_int_eq_blockLocal` | Proved (`0` sorries) |
| Triangle entry $T(n, k)$ (`A385590` `%N` L10) | `T`, `one_le_T` | Pinned computable `def` + positivity proof |
| `L2` Cassini's identity & $\gcd(F_{i-1}, F_{i-2}) = 1$ | `fib_cassini_shift`, `fib_cassini_and_coprime` | Proved |
| `L3` block-base recurrence $b_i + F_i F_{i-1} = b_{i+1}$ | `b`, `b_eq_fib_sq_add_mod`, `blockBase_step`, `blockBase_succ_eq` | Computable `def` + proved |
| `L4` row endpoint $e_{i, r}$ & $T(\Delta_i) < b_{i+2}$ | `row_endpoint_eq`, `row_endpoint_and_max_lt` | Proved |
| `L5` intra-block injectivity on $\Delta_i$ | `triangle_injective_on_block` | Proved |
| `L6` overflow characterization $O_i$ over $\mathbb{Z}$ | `blockImage`, `overflowSet`, `block_overflow_iff` | Proved |
| `L7` lattice transposition $O_i = G_{i+1}$ | `nextGapSet`, `overflow_eq_next_gap` | Proved |
| `L8` modular dichotomy on $[b_{i+1}, b_{i+2} - 1]$ | `mod_fib_rep_unique`, `mod_fib_rep_exists`, `mod_fib_dichotomy` | Proved |
| `L9` cumulative prefix partition & block disjointness | `prefixImage`, `disjoint_blockImage_of_lt`, `cumulative_prefix_partition` | Proved |
| **`L10` Pinned Main Theorem (`PIN-S003.md` v1)** | **`triangle_bijective_posNat`** | **Proved** |
| Structural corollaries & kernel `rfl` OEIS checks | `least_missing_posNat_prefix`, `T_boundary_spot_checks`, `T_oeis_rows_1_to_13`, `block4_refutes_per_block_tiling` | Kernel-proved |

### 6.2 Recorded Trust, Axiom, Non-Vacuity, and Provenance Audit

1. **Artifact source digests bound to toolchain pin (`leanprover/lean4:v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, base `master` `b1d68df13896aee5f2fac5962a6428bfb8bb9df0`):**
   - Step 0 staged contract `SeamC/A385590/Statement.lean` (`63` lines, commit `23b98b833c332f6aba30fe662be616e195a7a11a`): `2f19e572819ca7bb9f3859d8b13fae96ae8b10af9e0632f7673751681138d1ce` (`lake build` exit `0`, `17,982` jobs).
   - Proved module `SeamC/A385590/Statement.lean` (`786` lines): `0e27d946b3151cea49768706fe35d6145e24625690c8c2c8db477d052372d669` (`0 diff chars` across all Step 0 definitions `F`, `blockIndex`, `blockIndex_spec`, `fibBlockIndex_existsUnique`, `T`, `one_le_T`, and the `triangle_bijective_posNat` theorem signature).
   - `lakefile.toml` (`23` lines, adds `[[lean_lib]] name = "SeamC" globs = ["SeamC.+"]` per the C049 precedent): `12ca95376177738d3d2dc45c4bd083e78fbd80994d2447af3bf1201abec9eba9`.
   - `Mathproofs.lean` (`83` lines, adds `import SeamC.A385590.Statement`): `1c123abd39cab76a06bae48adef51a1222abe59896cc6b6cfd3aff13002f53cd`.
   - Clean-slate full build (`rm -rf .lake/build && lake build`): exit `0` (`17,982` jobs; `0` errors, `0` sorries, `0` warnings on `SeamC.A385590.Statement`; log SHA-256 `421b6f584479dca85f00b32cf3ad29e771cedecfa2bb46b568b9f8335a08039e`).
2. **Axiom footprint (`#print axioms`) and transitive kernel closure:**
   - `SeamC.A385590.F`, `SeamC.A385590.blockIndex`: depend on **no axioms**.
   - `SeamC.A385590.T`, `T_boundary_spot_checks`, `T_oeis_rows_1_to_13`, `block4_refutes_per_block_tiling`: `[propext]`.
   - `SeamC.A385590.triangle_bijective_posNat` and all `L1`–`L9` helpers (`blockIndex_spec`, `fibBlockIndex_existsUnique`, `one_le_T`, `T_cast_int_eq_blockLocal`, `fib_cassini_and_coprime`, `blockBase_succ_eq`, `row_endpoint_and_max_lt`, `triangle_injective_on_block`, `block_overflow_iff`, `overflow_eq_next_gap`, `mod_fib_dichotomy`, `cumulative_prefix_partition`, `least_missing_posNat_prefix`): `[propext, Classical.choice, Quot.sound]` (exact allowlist).
   - Transitive `CommandElabM` constant-closure audit across all `4,873` constants reachable from `triangle_bijective_posNat`: `disallowed_axioms = []`, `sorryAx = false`, `ofReduceBool = false`, `ofReduceNat = false`, `trustCompiler = false`.
   - Fresh-kernel replay (`lake env leanchecker --fresh --verbose SeamC.A385590.Statement`): **exit `0`**.
   - Comment/string-stripped lexical trust-escape screen across `SeamC/A385590/Statement.lean`, `Mathproofs.lean`, and `Main.lean`: **`0` active hits** (and `0` raw hits) for `sorry`, `admit`, `sorryAx`, `axiom`, `native_decide`, `ofReduceBool`, `implemented_by`, `unsafe`.
3. **Non-vacuity & OEIS spot checks (kernel `rfl` vs. VM `#eval` / Python boundary stated explicitly):**
   - **Proved directly in the Lean 4 kernel on the pinned `SeamC.A385590.T` (no mirror required, since `F`, `blockIndex`, and `T` are computable):** `T_boundary_spot_checks` (`blockIndex 1 = 2`, `T 1 1 = 1`, `T 2 1 = 2`, `T 2 2 = 3`, `T 3 1 = 4` by `rfl`), `T_oeis_rows_1_to_13` (all `91` entries of `OEIS A385590` `%e` rows `1..13` by `rfl`), `block4_refutes_per_block_tiling` (`rfl`), and `least_missing_posNat_prefix` (universally quantified over all `i ≥ 2`).
   - **Evaluated via Lean VM `#eval` and independent Python exact-integer recomputation** (not claimed as kernel `rfl` reductions): `#eval` on `SeamC.A385590.T` across all `83` printed `%S/%T/%U` terms and rows `1..33` (`561` entries, `0` duplicates, `[1, 441]` covered, `442 = T(34, 1)` first missing); Python exact-integer verification across `%o` PARI rows `1..100` (`5,050/5,050` matches), `O_i = G_{i+1}` and prefix coverage across `i = 2..16` (`1,274,406` entries, `0` duplicates; scoping lane verified prefix coverage through `i = 19`, `22,879,230` entries).
4. **Provenance & crossed-review status:**
   - Cumulative-coverage formulation first identified in coordinator verification (`ownharness-seamc-s003-a385590-20261115.md`); algebraic `O_i = G_{i+1}` lattice transposition, `L1`–`L10` blueprint, and frozen target contract `PIN-S003.md` v1 produced in `SCOPING-S003.md` (`carbon-seamc-s003-scoping-20261115`); Step 0 materialization and Lean 4 formalization authored in `carbon-s003-proof-20261116` (`dominic`, `gemini-4-carbon-high`, `google-ai-ultra` pool).
   - Crossed-review status at draft PR opening: **`NOT YET RUN (PENDING)`** — awaiting independent review by a fresh agy Gemini 4 Carbon High session disjoint from this author session, on a different machine where possible (session-level independence, per Derek's 2026-11-10 order).

---

## References

1. Werner Schulte, *OEIS Sequence A385590: Triangle read by rows, based on Fibonacci numbers* (authored July 3, 2025; revision `#7` July 7, 2025), The On-Line Encyclopedia of Integer Sequences, https://oeis.org/A385590.
2. N. J. A. Sloane, *OEIS Sequence A000045: Fibonacci numbers: $F(n) = F(n-1) + F(n-2)$ with $F(0) = 0$ and $F(1) = 1$*, The On-Line Encyclopedia of Integer Sequences, https://oeis.org/A000045.
3. Hieronymus Fischer, *OEIS Sequence A130233: Maximal $k$ such that $\mathrm{Fibonacci}(k) \le n$ (the "lower" Fibonacci Inverse)* (authored May 17, 2007), The On-Line Encyclopedia of Integer Sequences, https://oeis.org/A130233.
4. The Omega Institute, *`trureturing` Formalization Node `D5/S1/Recurrence/Parity/A385590.lean` (`alternating_binomial_sum`, sibling `%F` line 12 conjecture)*, 2026, https://github.com/the-omega-institute/trureturing.
5. The mathlib Community, *The Lean Mathematical Library (`Mathlib4`: `Mathlib.Data.Nat.Fib.Basic`, `Mathlib.Data.Nat.Fib.Zeckendorf`)*, commit `d13f23b723b8a846827a245b89c10fc7d3f11612` (`v4.34.1`), 2026.
