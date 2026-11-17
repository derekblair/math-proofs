# Top-Two Diagonal-Count Strata of King-Graph Domicule Tilings on the $2n \times 2n$ Square: Induction-Free Proof and Lean 4 Formalization of Ryłko's OEIS A401673 Conjectures

**Preprint Draft (`PAPER-S017.md`) — 2026-11-16**  
**Repository / Module:** `derekblair/math-proofs` (`SeamC/A401673.lean`, `namespace SeamC.A401673`, `2,320` lines, `SHA-256: 34fbb153d0caa172377b30ce532a4aa61697d016b59dd9240b0366298e24dae7`)  
**Toolchain & Mathlib Pin:** `leanprover/lean4:v4.34.1` (`Lake 5.0.0-src+5045d00`), Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`  
**Target Contract:** `PIN-S017.md` v1 (`SHA-256: a8e068f665e5e51c5f27659bb41f7da83e4731e75064e6443e366c316fb428a9`, `delta_vs_source: NONE`)

---

## Abstract

A *domicule* (`OEIS A239264`, `A239273`) is a pair of distinct unit squares in a rectangular grid that share either a side (an orthogonal domino) or a corner (a diagonal domicule); a *domicule tiling* of the $2n \times 2n$ square board $B_n = \{0, \dots, 2n - 1\}^2$ is a partition of its $4n^2$ cells into $2n^2$ pairwise vertex-disjoint domicules, i.e., a perfect matching of the $2n \times 2n$ chessboard king graph $K_{2n, 2n}$ (with crossing diagonal domicules in a $2 \times 2$ block permitted). Because every orthogonal domino covers one black and one white cell under a checkerboard coloring whereas every diagonal domicule covers two cells of the same color, every domicule tiling of $B_n$ uses an even number $2k$ ($0 \le k \le n^2$) of diagonal domicules. On November 1, 2026, Dawid Ryłko introduced the triangle `OEIS A401673` (`%F` line 17, live revision `#9`, November 9, 2026), where $T(n, k)$ counts domicule tilings of $B_n$ with **exactly $2k$** diagonal domicules, computed rows $0 \le n \le 10$ via transfer matrices, and conjectured that
$$T(n, n^2) = 1 \quad (n \ge 0) \qquad \text{and} \qquad T(n, n^2 - 1) = A_{011379}(n) = n^2(n + 1) \quad (n \ge 1).$$

We prove both identities unconditionally and provide a complete, **induction-free** Lean 4 formalization in `SeamC/A401673.lean`. Partitioning $B_n$ by coordinate parities $(r \bmod 2, c \bmod 2)$ into four equinumerous classes $A, B, C, D$ indexed by $I_n = \{0, \dots, n - 1\}^2$, diagonal edges decompose into $A$–$B$ edges on $V_0 = A \sqcup B$ satisfying $i - i' \in \{0, 1\},\; j - j' \in \{0, 1\}$ and $C$–$D$ edges on $V_1 = C \sqcup D$ satisfying $i - i' \in \{0, 1\}$ and the **opposite** column inequality $j' - j \in \{0, 1\}$. For $k = n^2$, vanishing of nonnegative coordinate sums over the resulting bijections $\phi, \psi : I_n \to I_n$ immediately forces $\phi = \psi = \mathrm{id}_{I_n}$, uniquely singling out the disjoint $n \times n$ grid $M_*$ of $2 \times 2$ X-crosses. For $k = n^2 - 1$ ($n \ge 1$), vertex parity forces exactly two orthogonal dominoes leaving one defect vertex in each of $A, B, C, D$, splitting disjointly into horizontal-domino matchings $\mathcal{F}_H$ and vertical-domino matchings $\mathcal{F}_V$ related bijectively by cell transposition $(r, c) \mapsto (c, r)$. In $\mathcal{F}_H$, summing the directed column steps over the punctured bijections $I_n \setminus \{p_A\} \to I_n \setminus \{p_B\}$ and $I_n \setminus \{p_C\} \to I_n \setminus \{p_D\}$ yields the four-inequality collapse
$$j_C \le j_A \le j_B \le j_D \le j_C \implies j_A = j_B = j_C = j_D =: j_0,$$
confining both horizontal dominoes to a single $2$-cell-wide vertical strip $j_0$ with $0 \le i_A \le i_B < n$ and decoupling all remaining columns to the identity. Partitioning the punctured 1D fiber $\{0, \dots, n - 1\} \setminus \{i_A\}$ into $[0, i_A) \sqcup (i_A, i_B] \sqcup (i_B, n)$ uniquely determines the $i_B - i_A$ seam-straddling X-crosses between rows $2i_A$ and $2i_B + 1$, establishing an explicit bijection with $\{(j_0, i_A, i_B) \in \{0, \dots, n - 1\}^3 : i_A \le i_B\}$ of size $n\binom{n + 1}{2} = \frac{1}{2}n^2(n + 1)$, whence $T(n, n^2 - 1) = |\mathcal{F}_H| + |\mathcal{F}_V| = n^2(n + 1)$. All proofs compile cleanly in Lean 4 without `sorry`, custom axioms, `native_decide`, or `ofReduceBool`.

---

## 1. Introduction and Primary-Source Context

### 1.1 King-Graph Domicule Tilings and Ryłko's Triangle `OEIS A401673`

Classical domino tilings of the $2n \times 2n$ chessboard (`OEIS A004003` [1], solved by Kasteleyn [2] and Temperley and Fisher [3] via planar Pfaffian orientations) correspond to perfect matchings of the $2n \times 2n$ grid graph $P_{2n} \square P_{2n}$. Adjoining the two diagonal edges inside every $2 \times 2$ cell block produces the non-planar **$2n \times 2n$ king graph** $K_{2n, 2n}$ (`OEIS A239273` [4], `A239264` [5]), whose edges—called *domicules* by Heinz and Howroyd—join pairs of distinct unit squares at Chebyshev (chessboard king) distance $1$:
$$\max(|r_1 - r_2|,\, |c_1 - c_2|) = 1.$$
Crucially, a domicule tiling is a vertex-disjoint edge cover (a graph-theoretic perfect matching of $K_{2n, 2n}$), so the two diagonal domicules $\{(r, c), (r + 1, c + 1)\}$ and $\{(r, c + 1), (r + 1, c)\}$ of a $2 \times 2$ square share no cells and **cross legally** (`A239273` `%C` line 11; `A401673` `%e` line 24 [6]). Because $K_{2n, 2n}$ is non-planar for $n \ge 1$, Kasteleyn's sign-free Pfaffian determinant breaks down (cf. Wildeboer and Seidel [7] and Sandvik and Moessner [8]), and no closed form is known for the unweighted matching count $A_{239273}(n)$.

On November 1, 2026, Dawid Ryłko [6, 9] refined $A_{239273}(n)$ by the diagonal-piece fugacity polynomial
$$P_{2n, 2n}(x) = \sum_{M \in \mathcal{M}(K_{2n, 2n})} x^{\mathrm{diag}(M)},$$
where $\mathrm{diag}(M)$ is the number of diagonal domicules in $M$. Coloring $(r, c) \in B_n$ black when $r + c$ is even ($2n^2$ cells) and white when $r + c$ is odd ($2n^2$ cells), every orthogonal domino covers one cell of each color whereas every diagonal domicule covers two cells of the same color; consequently, every matching $M$ has equally many black and white diagonal domicules, so $\mathrm{diag}(M) = 2k$ is always even (`A401673` `%C` line 11). Extracting the even-degree coefficients defines the triangle `OEIS A401673`:
$$T(n, k) := [x^{2k}]\,P_{2n, 2n}(x) \qquad (n \ge 0,\; 0 \le k \le n^2),$$
whose rows begin:
- $n = 0$: $[1]$;
- $n = 1$: $[2,\; 1]$;
- $n = 2$: $[36,\; 126,\; 105,\; 12,\; 1]$;
- $n = 3$: $[6728,\; 84132,\; 413932,\; 934213,\; 1000638,\; 491689,\; 99554,\; 6638,\; 36,\; 1]$.

Each row starts at the Kasteleyn domino count $T(n, 0) = A_{004003}(n)$ and sums to $\sum_{k = 0}^{n^2} T(n, k) = A_{239273}(n)$. Computing rows $0 \le n \le 6$ in exact integers and rows $7 \le n \le 10$ via profile transfer modulo $60$-bit primes with Chinese Remainder Theorem reconstruction (`b401673.txt`, $396$ entries), Ryłko observed that the rightmost two diagonals stabilize to $1$ and $n^2(n + 1) = A_{011379}(n)$ (`0, 2, 12, 36, 80, 150, 252, 392, 576, 810, 1100, \dots` [10]), and posted (`OEIS A401673` `%F` line 17, live revision `#9`, November 9, 2026 [6]):

> **Conjecture (Dawid Ryłko, November 1, 2026).** *$T(n, n^2) = 1$ and $T(n, n^2 - 1) = A_{011379}(n) = n^2(n + 1)$; true for $n \le 10$.*

In his companion research note *Rectangles by number of diagonal pieces* (rebuilt November 15, 2026 [9]), Ryłko explicitly recorded the open status of both formulas: *"exactly one tiling uses only diagonal pieces, and $T(n, n^2 - 1) = n^2(n + 1)$ (OEIS A011379). The last two are observations on these rows, not proofs."* Live prior-art checks across OEIS, Ryłko's Zenodo preprints [11, 12], arXiv, Crossref, and the complete untruncated `the-omega-institute/trureturing` git tree (`SCOPING-S017.md` §3, `2026-11-15`) confirmed that neither identity had a published proof or formalization.

### 1.2 Summary of Formalized Results

In `SeamC/A401673.lean` (`namespace SeamC.A401673`), we formalize and prove without a single mathematical or natural-number induction:

- **Theorem 1.1 (Unique All-Diagonal Tiling — `domiculeTilings_max_diag_eq_one`).** *For every $n \in \mathbb{N}$,*
  $$\mathrm{domiculeTilings}\;n\;(n^2) = 1.$$
- **Theorem 1.2 (Exact Sub-Maximal Diagonal Count — `domiculeTilings_sub_one_diag_eq`, `domiculeTilings_sub_one_diag_eq_A011379`).** *For every $n \in \mathbb{N}$ with $1 \le n$,*
  $$\mathrm{domiculeTilings}\;n\;(n^2 - 1) = n^2(n + 1) = A_{011379}(n).$$
- **Theorem 1.3 (Strip Collapse & 1D Fiber Classification — `one_defect_strip_collapse_and_fiber_uniqueness`, `isDomiculeTiling_constructH`).** *For every $1 \le n$, every horizontal-defect matching $M \in \mathcal{F}_H(n)$ collapses to a unique strip column $j_0 \in \mathrm{Fin}\;n$ and row pair $0 \le i_A \le i_B < n$ with $M = \mathrm{constructH}\;n\;j_0\;i_A\;i_B$, while cell transposition $(r, c) \mapsto (c, r)$ establishes $|\mathcal{F}_V(n)| = |\mathcal{F}_H(n)|$.*
- **Theorem 1.4 (Diagonal Parity, Triangle Support, Boundary Witnesses, & Computable Mirror — `domicule_diag_card_even`, `domiculeTilings_eq_zero_of_gt`, `boundary_zero_guard_necessary`, `crossing_diagonals_board1`, `seam_shift_board2`, `domiculeTilingsDec_eq`).** *Every domicule tiling of $B_n$ has an even number of diagonal domicules; $\mathrm{domiculeTilings}\;n\;k = 0$ for all $k > n^2$; the $1 \le n$ guard on $\mathbb{N}$ is witnessed necessary at $n = 0$; the crossing $2 \times 2$ witness at $n = 1$ and seam-straddling witness at $n = 2$ are verified inside the Lean 4 kernel; and `domiculeTilingsDec` provides a constructively decidable powerset mirror proved equal to `domiculeTilings` for all $n, k \in \mathbb{N}$.*

---

## 2. Formal Specification, Conventions, and Source-Audit Corrections

### 2.1 Pinned Lean 4 Definitions (`PIN-S017.md` v1)

The target specification in `SeamC/A401673.lean` matches `PIN-S017.md` v1 verbatim (`0` diff characters):

```lean
abbrev Board (n : ℕ) : Type := Fin (2 * n) × Fin (2 * n)

def kingAdj (n : ℕ) (u v : Board n) : Prop :=
  u ≠ v ∧ Nat.dist u.1.val v.1.val ≤ 1 ∧ Nat.dist u.2.val v.2.val ≤ 1

def diagAdj (n : ℕ) (u v : Board n) : Prop :=
  Nat.dist u.1.val v.1.val = 1 ∧ Nat.dist u.2.val v.2.val = 1

def IsDomiculeTiling (n : ℕ) (M : Finset (Sym2 (Board n))) : Prop :=
  (∀ e ∈ M, ¬ e.IsDiag ∧ ∀ u v, e = s(u, v) → kingAdj n u v) ∧
    (∀ v : Board n, ∃! e, e ∈ M ∧ v ∈ e)

def IsDiagDomicule (n : ℕ) (e : Sym2 (Board n)) : Prop :=
  ∃ u v, e = s(u, v) ∧ diagAdj n u v

open scoped Classical in
noncomputable def domiculeTilings (n k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Sym2 (Board n)))).filter (fun M =>
    IsDomiculeTiling n M ∧ (M.filter (IsDiagDomicule n)).card = 2 * k)).card

def A011379 (n : ℕ) : ℕ := n ^ 2 * (n + 1)
```

Three design features are load-bearing (`PIN-S017.md` `fidelity_notes` §§1–3):

1. **The `2 * k` diagonal-count factor:** Per `%N` line 10 (*"with exactly $2k$ diagonal domicules, $0 \le k \le n^2$"*) and the PARI code `%o` line 27 (`polcoef(q, 2*(k-1))` in 1-based vector indexing), the second argument $k$ of $T(n, k)$ indexes **pairs** of diagonal domicules ($2k$ diagonal edges total). Thus $T(n, n^2)$ counts tilings with $2n^2$ diagonal domicules (all $2n^2$ edges diagonal, $0$ orthogonal dominoes), and $T(n, n^2 - 1)$ counts tilings with $2(n^2 - 1) = 2n^2 - 2$ diagonal domicules and $2$ orthogonal dominoes. Omitting the factor of $2$ would silently halve the diagonal count and falsify both theorems for $n \ge 1$.
2. **Unordered pairs `Sym2 (Board n)` and legal crossings:** Representing each domicule as an unordered pair `s(u, v) : Sym2 (Board n)` with `¬ e.IsDiag` and the partition clause `∀ v : Board n, ∃! e, e ∈ M ∧ v ∈ e` formalizes graph-theoretic perfect matchings of $K_{2n, 2n}$ directly without planar-embedding side conditions. On $B_1 = \{0, 1\}^2$, the two crossing diagonals `s((0, 0), (1, 1))` and `s((0, 1), (1, 0))` partition the four cells cleanly (`crossing_diagonals_board1`), matching `%e` line 24: $T(1, 1) = 1$.
3. **Empty board $n = 0$ and mandatory $1 \le n$ hypothesis on $\mathbb{N}$:** At $n = 0$, `Board 0 = Fin 0 × Fin 0` is empty, and $M = \emptyset$ vacuously satisfies `IsDomiculeTiling 0 ∅` with $0 = 2 \cdot 0^2$ diagonal edges, giving $\mathrm{domiculeTilings}\;0\;0 = 1$ (matching `%S` index $0$ and PARI `if(h*w == 0, return(1))`). In `%N` line 10, the triangle domain is $0 \le k \le n^2$, so $k = n^2 - 1$ belongs to the triangle if and only if $n \ge 1$. Because natural-number subtraction truncates $(0 : \mathbb{N})^2 - 1 = 0$, evaluating $\mathrm{domiculeTilings}\;0\;(0^2 - 1)$ on $\mathbb{N}$ reads $T(0, 0) = 1 \ne 0 = 0^2(0 + 1)$ (`boundary_zero_guard_necessary`). Hence `(hn : 1 ≤ n)` is mandatory on the $\mathbb{N}$-indexed signature `domiculeTilings_sub_one_diag_eq`, while under the standard zero-outside-support integer-index extension $T_{\mathbb{Z}}(n, k) := \mathrm{domiculeTilings}\;n\;k$ for $k \ge 0$ and $0$ for $k < 0$, $T_{\mathbb{Z}}(0, -1) = 0 = 0^2(0 + 1)$ also holds at $n = 0$.

### 2.2 Corrections to Intake Heuristics and Triage Note Errors

During scoping (`SCOPING-S017.md` §1.3 & §2), auditing the initial triage dossier (`TRIAGE-SEAMC.md`) against live OEIS data and exact recomputations uncovered three documentary note errors in the triage text (none in `OEIS A401673` itself) and two qualitative inaccuracies in its one-line geometric heuristic:

1. **Triage data-citation corrections:**
   - `TRIAGE-SEAMC.md` L260 misstated that the $35$ printed `%S/%T/%U` terms reached `"T(5, 8) = 4,670,848,475"`. In fact, the $35$ printed `%S/%T/%U` entries are complete rows $n = 0..4$ ($1 + 2 + 5 + 10 + 17 = 35$, ending at $T(4, 16) = 1$); the true value of $T(5, 8)$ (`b401673.txt` index $43$, verified by exact profile DP) is $17{,}801{,}889{,}457{,}794{,}564{,}900$, while $4{,}670{,}848{,}475$ does not appear anywhere in `A401673`.
   - `TRIAGE-SEAMC.md` L115 cited $7{,}547{,}382{,}758$ as the row-$5$ maximum; $7{,}547{,}382{,}758$ is $T(5, 22)$ (`b401673.txt` index $57$), whereas the true row-$5$ maximum is $T(5, 11) = 68{,}111{,}720{,}190{,}795{,}660{,}589$ (`b401673.txt` index $46$).
   - `TRIAGE-SEAMC.md` §3.10 paraphrased `%N`; `PIN-S017.md` restores the verbatim `%N` line 10 text from live `A401673` (`#9`).
2. **Correction of the geometric heuristic:** `TRIAGE-SEAMC.md` L72 described $M_*$ as *"nested $2 \times 2$ X-crosses"* and $T(n, n^2 - 1)$ as *"single-defect perturbations across seams"*. In fact:
   - $M_*$ is the **disjoint $n \times n$ grid** of $2 \times 2$ X-crosses $[2i, 2i + 1] \times [2j, 2j + 1]$ ($0 \le i, j < n$), not concentric nested rings; and
   - In every one-defect matching $M \in \mathcal{F}_H(n)$, the two horizontal dominoes $\{(2i_A, 2j_0), (2i_A, 2j_0 + 1)\}$ and $\{(2i_B + 1, 2j_0), (2i_B + 1, 2j_0 + 1)\}$ lie **inside** a single $2$-cell-wide block column $j_0$ (never straddling a vertical seam between $2j_0 + 1$ and $2j_0 + 2$), while it is the $i_B - i_A$ *shifted X-crosses* between them that straddle the horizontal block seams $\{2i - 1, 2i\}$ ($i_A < i \le i_B$).

---

## 3. Matching–Involution Correspondence and Steps 1–4 (`T(n, n^2) = 1`)

### 3.1 Matching–Involution Bridge (`mate` and `matchingOfInvolution`)

Working directly with `∃! e, e ∈ M ∧ v ∈ e` over nested `Sym2` quotients across multi-case constructions would create heavy boilerplate. In Section 1 of `SeamC/A401673.lean`, we bridge `IsDomiculeTiling n M` cleanly to fixed-point-free king-adjacent involutions on `Board n`:

- **From tilings to involutions (`mate`):** Given `hM : IsDomiculeTiling n M` and $v \in B_n$, let `edgeOf hM v` be the unique $e \in M$ with $v \in e$, and define $\mu(v) := \mathrm{mate}\;hM\;v$ via Mathlib's computable `Sym2.Mem.other'`. By `Sym2.other_spec'` and `edgeOf_unique`, $\mu$ satisfies `kingAdj n v (μ v)` (`kingAdj_mate`), $\mu(\mu(v)) = v$ (`mate_invol`), and
  $$s(u, v) \in M \iff \mathrm{mate}\;hM\;u = v \qquad (\texttt{mk\_mem\_iff\_mate}).$$
  In particular, two tilings $M_1, M_2$ are equal if and only if their partner involutions agree pointwise (`tiling_ext_mate`).
- **From involutions to tilings (`matchingOfInvolution`, `isDomiculeTiling_of_invol`):** Conversely, for any map $\mu : B_n \to B_n$ satisfying $\mu(\mu(v)) = v$ and `kingAdj n v (μ v)` for all $v \in B_n$, the image
  $$\mathrm{matchingOfInvolution}\;n\;\mu \;:=\; \mathrm{Finset.univ.image}\bigl(v \mapsto s(v, \mu(v))\bigr)$$
  satisfies `IsDomiculeTiling n` (`isDomiculeTiling_of_invol`) with partner map equal to $\mu$ (`mate_matchingOfInvolution`).

### 3.2 Step 1 (`board_four_cases`) and Step 2 (`diagAdj_embA_embB_iff`, `diagAdj_embC_embD_iff`)

Let $I_n := \mathrm{Fin}\;n \times \mathrm{Fin}\;n$ (`Idx n`, $|I_n| = n^2$ by `card_idx`). Define the four injective embeddings $I_n \hookrightarrow B_n$:
$$\mathrm{embA}(i, j) = (2i, 2j), \quad \mathrm{embB}(i, j) = (2i + 1, 2j + 1), \quad \mathrm{embC}(i, j) = (2i, 2j + 1), \quad \mathrm{embD}(i, j) = (2i + 1, 2j),$$
with common left inverse $\mathrm{blk}(r, c) := (\lfloor r/2 \rfloor, \lfloor c/2 \rfloor)$ (`blk_embA`–`blk_embD`). By `(r mod 2, c mod 2)` case analysis (`board_four_cases`), $B_n = A \sqcup B \sqcup C \sqcup D$, with checkerboard classes $V_0 = A \sqcup B$ ($r + c \equiv 0 \pmod 2$) and $V_1 = C \sqcup D$ ($r + c \equiv 1 \pmod 2$).

Unfolding `Nat.dist a b = (a - b) + (b - a)` (`nat_dist_def`) yields the exact Step 2 edge-type classification:

1. **Diagonal domicules (`|r_1 - r_2| = 1 \land |c_1 - c_2| = 1`):** Both coordinates flip parity (`diagAdj_embA_target`–`diagAdj_embD_target`), so diagonal edges connect $A \leftrightarrow B$ inside $V_0$ or $C \leftrightarrow D$ inside $V_1$, with **opposite** column monotonicity:
   - On $A$–$B$ (`diagAdj_embA_embB_iff`): $\mathrm{diagAdj}\bigl((2i, 2j),\, (2i' + 1, 2j' + 1)\bigr) \iff i' \le i \le i' + 1 \;\land\; \mathbf{j' \le j \le j' + 1}$.
   - On $C$–$D$ (`diagAdj_embC_embD_iff`): $\mathrm{diagAdj}\bigl((2i, 2j + 1),\, (2i' + 1, 2j')\bigr) \iff i' \le i \le i' + 1 \;\land\; \mathbf{j \le j' \le j + 1}$.
2. **Orthogonal dominoes (`kingAdj ∧ ¬ diagAdj`):** Exactly one coordinate changes by $1$ and the other is fixed, flipping $(r + c) \bmod 2$ between $V_0$ and $V_1$ (`orth_parity_flip`). For the horizontal subtypes:
   - `H_even` ($A$–$C$, `kingAdj_embA_embC_iff`): $\mathrm{kingAdj}\bigl((2i_A, 2j_A),\, (2i_C, 2j_C + 1)\bigr) \iff i_C = i_A \;\land\; j_C \le j_A \le j_C + 1$.
   - `H_odd` ($B$–$D$, `kingAdj_embB_embD_iff`): $\mathrm{kingAdj}\bigl((2i_B + 1, 2j_B + 1),\, (2i_D + 1, 2j_D)\bigr) \iff i_D = i_B \;\land\; j_B \le j_D \le j_B + 1$.

### 3.3 Step 3: Diagonal Parity Law (`filter_diag_card_eq_two_mul`, `domicule_diag_card_even`)

Fix `hM : IsDomiculeTiling n M` with partner involution $\mu = \mathrm{mate}\;hM$. For $X \in \{A, B, C, D\}$, partition $I_n = \mathrm{diagIdx}X \sqcup \mathrm{orthIdx}X$ according to whether $\mathrm{emb}X(p)$ is diagonally adjacent to $\mu(\mathrm{emb}X(p))$.

- Because $\mu$ pairs $A$-diagonals bijectively with $B$-diagonals and $C$-diagonals with $D$-diagonals, $|\mathrm{diagIdxB}| = |\mathrm{diagIdxA}| =: d_0$ (`card_diagIdxB_eq`) and $|\mathrm{diagIdxD}| = |\mathrm{diagIdxC}| =: d_1$ (`card_diagIdxD_eq`), whence $|\mathrm{orthIdxA}| = |\mathrm{orthIdxB}| = n^2 - d_0$ and $|\mathrm{orthIdxC}| = |\mathrm{orthIdxD}| = n^2 - d_1$.
- Because $\mu$ maps orthogonal vertices in $V_0$ bijectively onto orthogonal vertices in $V_1$ (`card_orthV0_eq_orthV1`), we obtain $2(n^2 - d_0) = 2(n^2 - d_1)$, so $|\mathrm{orthIdxA}| = |\mathrm{orthIdxC}|$ (`card_orthIdxA_eq_orthIdxC`) and $d_0 = d_1$ (`card_diagIdxA_eq_diagIdxC`).
- Orienting each diagonal edge in $V_0$ from its unique $A$-endpoint and each diagonal edge in $V_1$ from its unique $C$-endpoint expresses `M.filter (IsDiagDomicule n)` as a disjoint union of injective images of `diagIdxA` and `diagIdxC`, yielding (`filter_diag_card_eq_two_mul`):
  $$\bigl|\{e \in M : \mathrm{IsDiagDomicule}\;n\;e\}\bigr| = d_0 + d_1 = 2\,d_0.$$
  Immediate corollaries are `domicule_diag_card_even` (`Even (M.filter (IsDiagDomicule n)).card`) and `domiculeTilings_eq_zero_of_gt` ($T(n, k) = 0$ whenever $k > n^2$, since $d_0 \le |I_n| = n^2$).

### 3.4 Step 4: Nonnegative Coordinate-Sum Vanishing and Proof of `T(n, n^2) = 1`

To avoid $\mathbb{Z}$-casts or truncated-subtraction pitfalls, Section 4 establishes a clean $\mathbb{N}$-valued coordinate-sum lemma (`injOn_endo_eq_of_le`):

**Lemma 3.1 (`injOn_endo_eq_of_le`, `injOn_endo_eq_of_ge`).** *Let $S$ be a `Finset α`, $\phi : \alpha \to \alpha$ satisfy $\phi(S) \subseteq S$ and `Set.InjOn φ S`, and $w : \alpha \to \mathbb{N}$ satisfy $w(\phi(x)) \le w(x)$ for all $x \in S$ (respectively $w(x) \le w(\phi(x))$). Then $w(\phi(x)) = w(x)$ for all $x \in S$.*

*Proof.* Finite pigeonhole (`Finset.surj_on_of_inj_on_of_card_le`) gives `S.image φ = S`, so $\sum_{x \in S} w(\phi(x)) = \sum_{y \in S} w(y)$ by `Finset.sum_image`. Since $w(\phi(x)) \le w(x)$ on $S$, natural-number addition gives
$$\left(\sum_{x \in S} \bigl(w(x) - w(\phi(x))\bigr)\right) + \sum_{x \in S} w(\phi(x)) = \sum_{x \in S} w(x),$$
forcing $\sum_{x \in S} (w(x) - w(\phi(x))) = 0$. By `Finset.sum_eq_zero_iff_of_nonneg`, $w(x) - w(\phi(x)) = 0$ and hence $w(\phi(x)) = w(x)$ for every $x \in S$. $\square$

*Proof of Theorem 1.1 (`domiculeTilings_max_diag_eq_one`).*
- **Existence (`M_star`):** Define `flip2 n : Fin (2 * n) → Fin (2 * n)` swapping $2i \leftrightarrow 2i + 1$, and set $\mu_*(r, c) := (\mathrm{flip2}(r),\, \mathrm{flip2}(c))$ (`muStar`). Then $\mu_*$ is a king- and diagonally-adjacent involution (`muStar_invol`, `muStar_diagAdj`), so $M_* := \mathrm{matchingOfInvolution}\;n\;\mu_*$ is a valid domicule tiling (`isDomiculeTiling_M_star`) with `diagIdxA = Finset.univ` and $2n^2$ diagonal domicules (`card_diag_M_star`).
- **Uniqueness (`eq_M_star_of_max_diag`):** Conversely, if `hM : IsDomiculeTiling n M` has $2n^2$ diagonal domicules, Step 3 gives $d_0 = d_1 = n^2$, so `orthIdxA = orthIdxC = ∅`. Thus $\phi(p) := \mathrm{blk}(\mu(\mathrm{embA}(p)))$ and $\psi(p) := \mathrm{blk}(\mu(\mathrm{embC}(p)))$ are injective self-maps on $I_n$ satisfying:
  $$(\phi(p))_1 \le p_1,\quad (\phi(p))_2 \le p_2, \qquad (\psi(p))_1 \le p_1,\quad p_2 \le (\psi(p))_2.$$
  Applying `injOn_endo_eq_of_le` three times and `injOn_endo_eq_of_ge` once forces $\phi(p) = p$ and $\psi(p) = p$ for all $p \in I_n$. Thus $\mu$ agrees with $\mu_*$ on $A$ and $C$, and by involution (`mate_invol`) on $B$ and $D$, giving $M = M_*$ by `tiling_ext_mate`. Hence the filtered `Finset` in `domiculeTilings n (n^2)` is the singleton $\{M_*\}$, of cardinality $1$. $\square$

---

## 4. Steps 5–7: One-Defect Dichotomy, Strip Collapse, and `T(n, n^2 - 1) = n^2(n + 1)`

Now assume $1 \le n$, so $n^2 \ge 1$. Partition the `Finset` `subOneTilings n` of matchings with $2(n^2 - 1)$ diagonal domicules by the predicate `∃ e ∈ M, IsHorizDomino n e` into $\mathcal{F}_H(n)$ (`F_H n`) and $\mathcal{F}_V(n)$ (`F_V n`), so that (`domiculeTilings_sub_one_eq_FH_add_FV`):
$$\mathrm{domiculeTilings}\;n\;(n^2 - 1) = |\mathcal{F}_H(n)| + |\mathcal{F}_V(n)|.$$

### 4.1 Step 5: Orthogonal-Pair Dichotomy and Transpose Bijection (`one_defect_dichotomy`, `card_FV_eq_card_FH`)

For any $M \in \mathrm{subOneTilings}(n)$, Step 3 gives $d_0 = d_1 = n^2 - 1$, so $|\mathrm{orthIdxA}| = |\mathrm{orthIdxB}| = |\mathrm{orthIdxC}| = |\mathrm{orthIdxD}| = 1$. Let $\mathrm{orthIdx}X = \{p_X\}$ for $X \in \{A, B, C, D\}$. Because $\mu(\mathrm{embA}(p_A))$ and $\mu(\mathrm{embB}(p_B))$ are distinct orthogonal vertices in $V_1 = \{\mathrm{embC}(p_C), \mathrm{embD}(p_D)\}$, injectivity of $\mu$ leaves exactly two mutually exclusive pairings (`one_defect_dichotomy`):
1. **Case H ($M \in \mathcal{F}_H(n)$):** $\mu(\mathrm{embA}(p_A)) = \mathrm{embC}(p_C)$ (`H_even`) and $\mu(\mathrm{embB}(p_B)) = \mathrm{embD}(p_D)$ (`H_odd`), witnessed by the horizontal domino $s(\mathrm{embA}(p_A), \mathrm{embC}(p_C)) \in M$.
2. **Case V ($M \in \mathcal{F}_V(n)$):** $\mu(\mathrm{embA}(p_A)) = \mathrm{embD}(p_D)$ (`V_even`) and $\mu(\mathrm{embB}(p_B)) = \mathrm{embC}(p_C)$ (`V_odd`), in which **no** edge of $M$ is horizontal (diagonal edges change row by $1$, and both $A$–$D$ and $B$–$C$ edges change row parity).

Cell transposition $\tau(r, c) = (c, r)$ induces an involution `transposeMatching n M := M.image (Sym2.map Prod.swap)` preserving `IsDomiculeTiling` (`isDomiculeTiling_transpose`) and diagonal count (`card_diag_transpose`), while interchanging horizontal and vertical orthogonal dominoes (`transpose_mem_FV_of_mem_FH`, `transpose_mem_FH_of_mem_FV`). Hence `Finset.card_bij` gives $|\mathcal{F}_V(n)| = |\mathcal{F}_H(n)|$ (`card_FV_eq_card_FH`).

### 4.2 Step 6: Punctured Coordinate-Sum Strip Collapse (`punctured_bij_sum_diff`)

For punctured bijections $\phi : \mathrm{univ.erase}\;a_0 \to \mathrm{univ.erase}\;b_0$ with $w(\phi(x)) \le w(x)$ (and dually $w(x) \le w(\psi(x))$), combining `Finset.surj_on_of_inj_on_of_card_le`, `Finset.sum_image`, and `Finset.sum_erase_add` yields the exact $\mathbb{N}$ identities (`punctured_bij_sum_diff`, `punctured_bij_sum_diff_ge`):
$$\left(\sum_{x \ne a_0} \bigl(w(x) - w(\phi(x))\bigr)\right) + w(a_0) = w(b_0), \qquad \left(\sum_{x \ne c_0} \bigl(w(\psi(x)) - w(x)\bigr)\right) + w(d_0) = w(c_0).$$

Take any $M \in \mathcal{F}_H(n)$ (`Case H`), and write $p_X = (i_X, j_X)$ for $X \in \{A, B, C, D\}$.
- From `kingAdj_embA_embC_iff` and `kingAdj_embB_embD_iff`, the two horizontal dominoes satisfy $i_C = i_A$, $i_D = i_B$, **$j_C \le j_A$**, and **$j_B \le j_D$**.
- Meanwhile, $\phi : I_n \setminus \{p_A\} \to I_n \setminus \{p_B\}$ has $(\phi(p))_2 \le p_2$, so `punctured_bij_sum_diff` gives $\bigl(\sum (p_2 - (\phi(p))_2)\bigr) + j_A = j_B$, whence **$j_A \le j_B$**.
- Crucially, $\psi : I_n \setminus \{p_C\} \to I_n \setminus \{p_D\}$ has the **opposite** column inequality $p_2 \le (\psi(p))_2$, so `punctured_bij_sum_diff_ge` gives $\bigl(\sum ((\psi(p))_2 - p_2)\bigr) + j_D = j_C$, whence **$j_D \le j_C$**.

Chaining the four inequalities collapses all four column indices to a single strip $j_0 \in \mathrm{Fin}\;n$:
$$j_C \le j_A \le j_B \le j_D \le j_C \implies j_A = j_B = j_C = j_D =: j_0.$$
Substituting $j_B = j_A$ and $j_D = j_C$ back into the two sum identities forces both nonnegative sums to equal $0$; by `Finset.sum_eq_zero_iff_of_nonneg`, $(\phi(p))_2 = p_2$ and $(\psi(p))_2 = p_2$ for every $p \ne (i_A, j_0)$! Finally, applying `punctured_bij_sum_diff` to the row coordinate $w(p) = p_1$ on $\phi$ gives $\bigl(\sum (p_1 - (\phi(p))_1)\bigr) + i_A = i_B$, whence **$i_A \le i_B$**.

### 4.3 Step 7: 1D Fiber Uniqueness, `constructH`, and Exact Count (`one_defect_strip_collapse_and_fiber_uniqueness`)

Because $p_C = (i_A, j_0) = p_A$ and $p_D = (i_B, j_0) = p_B$, both $\phi$ and $\psi$ satisfy the hypotheses of a single 1D fiber lemma (`punctured_strip_map_unique`): an injective map $\Phi : I_n \setminus \{(i_A, j_0)\} \to I_n \setminus \{(i_B, j_0)\}$ ($i_A \le i_B$) with $(\Phi(p))_2 = p_2$ and $(\Phi(p))_1 \le p_1 \le (\Phi(p))_1 + 1$.

- **Columns $j \ne j_0$:** $f(i) := (\Phi(i, j))_1$ is an injective self-map on $\mathrm{Fin}\;n$ with $f(i) \le i$, so Lemma 3.1 gives $f(i) = i$, i.e., $\Phi(i, j) = (i, j)$.
- **Defect column $j = j_0$:** Let $f(i) := (\Phi(i, j_0))_1$ on $\mathrm{Fin}\;n \setminus \{i_A\}$, where $f(i) \ne i_B$ and $f(i) \le i \le f(i) + 1$. Partition $\mathrm{Fin}\;n \setminus \{i_A\} = L \sqcup M_{\mathrm{dom}} \sqcup U$ with $L = \{i < i_A\}$, $U = \{i > i_B\}$, and $M_{\mathrm{dom}} = \{i_A < i \le i_B\}$:
  1. On $L$: $f(i) \le i < i_A \implies f(L) \subseteq L$, so Lemma 3.1 gives $f(i) = i$.
  2. On $U$: $i_B + 1 \le i \le f(i) + 1$ and $f(i) \ne i_B \implies f(i) > i_B$, so $f(U) \subseteq U$ and Lemma 3.1 gives $f(i) = i$.
  3. On $M_{\mathrm{dom}}$: $i_A + 1 \le i \le f(i) + 1$ and $f(i) \le i \le i_B$ with $f(i) \ne i_B$ imply $i_A \le f(i) < i_B$, so $f$ maps $M_{\mathrm{dom}}$ injectively into $M_{\mathrm{cod}} := \{i_A \le k < i_B\}$. Since $i \mapsto i - 1$ (`sh`) is a bijection $M_{\mathrm{dom}} \xrightarrow{\sim} M_{\mathrm{cod}}$ preserving sum $\sum_{M_{\mathrm{dom}}} (i - 1) = \sum_{M_{\mathrm{cod}}} k$, pigeonhole gives `M_dom.image f = M_cod` and $\sum_{i \in M_{\mathrm{dom}}} \bigl(f(i) - (i - 1)\bigr) = 0$, whence `Finset.sum_eq_zero_iff_of_nonneg` forces $f(i) = i - 1$ for all $i \in M_{\mathrm{dom}}$.

Conversely, given any $(j_0, i_A, i_B) \in (\mathrm{Fin}\;n)^3$ with $i_A \le i_B$, define the strip row involution `rowH i_A i_B hle : Fin (2 * n) → Fin (2 * n)` fixing rows $2i_A$ and $2i_B + 1$, pairing $2i \leftrightarrow 2i - 1$ on $2i_A < r < 2i_B + 1$, and acting as `flip2` outside $[2i_A, 2i_B + 1]$. Setting
$$\mu_H(r, c) := \begin{cases} (\mathrm{rowH}(r),\, \mathrm{flip2}(c)) & \text{if } \lfloor c/2 \rfloor = j_0, \\ \mu_*(r, c) & \text{if } \lfloor c/2 \rfloor \ne j_0 \end{cases}$$
defines a king-adjacent involution (`muH_invol`, `muH_kingAdj`) whose matching `constructH n j₀ i_A i_B hle` belongs to $\mathcal{F}_H(n)$ (`constructH_mem_FH`), recovers $(j_0, i_A, i_B)$ injectively from its unique non-diagonal $A$- and $B$-vertices (`constructH_injective`), and matches every $M \in \mathcal{F}_H(n)$ by `one_defect_strip_collapse_and_fiber_uniqueness`. Hence $|\mathcal{F}_H(n)| = |\mathrm{ParamH}(n)| = n \cdot |U_{\le}|$ (`card_FH_eq_card_ParamH`), where $U_{\le} = \{(i, j) \in I_n : i \le j\}$. Splitting $I_n = U_{\le} \sqcup U_{>}$ and $U_{\le} = \mathrm{Diag} \sqcup U_{<}$ with `Prod.swap : U_< ≃ U_>` gives $2|U_{\le}| = n(n + 1)$ without induction (`two_mul_card_upperTri`), closing (`domiculeTilings_sub_one_diag_eq`):
$$T(n, n^2 - 1) = |\mathcal{F}_H(n)| + |\mathcal{F}_V(n)| = 2\,|\mathcal{F}_H(n)| = n \cdot \bigl(2\,|U_{\le}|\bigr) = n \cdot n(n + 1) = n^2(n + 1). \quad \square$$

---

## 5. Verification Record, Non-Vacuity Boundary, and Scope Note

### 5.1 Formal Verification Gates

All verification gates were executed under `leanprover/lean4:v4.34.1` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`:

| Gate | Exact Command | Result |
| :--- | :--- | :--- |
| Step 0 stub gate | `cd repo && lake build` | `exit 0` (`17,992` jobs; staged `PIN-S017.md` v1 stub compiled cleanly at commit `a663bd36a399eaddc43e64423d53225b2e2c36e9`, `SeamC/A401673.lean` stub `SHA-256: 885b1f0e…`) |
| Clean-slate build | `cd repo && rm -rf .lake/build && lake build` | `exit 0` (`17,992` jobs; `lake env lean SeamC/A401673.lean` → `exit 0`, `0` errors / `0` sorries / `0` warnings) |
| Axiom allowlist + closure | `cd repo && lake env lean ../evidence/check_axioms_and_closure.lean` | `exit 0` (`[propext, Classical.choice, Quot.sound]` only across `6,287` transitive constants; `sorryAx=false`, `ofReduceBool=false`, `ofReduceNat=false`, `trustCompiler=false`, `CLOSURE_UNSAFE_CONSTANTS=[]`) |
| Fresh-kernel replay | `cd repo && lake env leanchecker --fresh SeamC.A401673` | `exit 0` |
| Lexical trust-escape screen | `python3 evidence/lexical_screen.py` | `exit 0` (`0` active hits and `0` raw hits across `SeamC/A401673.lean`, `Mathproofs.lean`, `Main.lean`) |
| Pin fidelity & recomputation | `python3 evidence/check_pin_fidelity.py && python3 evidence/verify_s017_lane.py 7` | `exit 0` (`0` diff chars vs. `PIN-S017.md` v1 & Step 0 commit; `PASSES=91, FAILURES=0` across exact DP rows `0..7`, `ROW8`, `b401673` rows `0..10`, and backtracking `n = 0..5`) |

### 5.2 Non-Vacuity Boundary (Kernel Reduction vs. VM `#eval` and Python Recomputation)

Because `domiculeTilings` filters `(Finset.univ : Finset (Finset (Sym2 (Board n))))` (whose ambient powerset has $2^{\binom{4n^2 + 1}{2}}$ subsets: $1$ at $n = 0$, $1{,}024$ at $n = 1$, and $2^{136}$ at $n = 2$) using `Classical.propDecidable`, direct kernel `rfl` on the literal `domiculeTilings` is blocked by `Classical.choice` and exponential powerset blowup for $n \ge 2$. Following `review-checklist.md` §§A–B, we record explicitly what ran in the Lean 4 kernel versus Lean VM `#eval` and Python:

- **Proved inside the Lean 4 kernel (`0` sorries, `0` `native_decide`, `0` `ofReduceBool`):**
  1. `pinned_boundary_and_spot_checks` proves directly on the literal pinned `domiculeTilings` and `A011379` that `domiculeTilings 0 0 = 1`, `domiculeTilings 1 1 = 1`, `domiculeTilings 1 0 = 2`, `domiculeTilings 2 4 = 1`, `domiculeTilings 2 3 = 12`, `domiculeTilings 5 25 = 1`, `domiculeTilings 5 24 = 150`, `domiculeTilings 6 36 = 1`, `domiculeTilings 6 35 = 252`, and `(List.range 11).map A011379 = [0, 2, 12, 36, 80, 150, 252, 392, 576, 810, 1100]` (`rfl`).
  2. `boundary_zero_guard_necessary` proves inside the kernel that `domiculeTilings 0 (0^2 - 1) = 1 ≠ 0 = A011379 0`, confirming non-vacuity and necessity of `(hn : 1 ≤ n)`.
  3. `crossing_diagonals_board1` and `seam_shift_board2` verify inside the kernel that the crossing $2 \times 2$ diagonals at $n = 1$ (`%e` line 24) and the seam-straddling X-cross `s((1, 0), (2, 1))`, `s((2, 0), (1, 1))` at $n = 2$ genuinely occur in `M_star 1` and `constructH 2 0 0 1`.
  4. `domiculeTilingsDec_eq` proves `domiculeTilingsDec n k = domiculeTilings n k` for all $n, k \in \mathbb{N}$ for the constructively decidable `Sym2`-powerset mirror, and `kernel_rfl_board0` checks `domiculeTilingsDec 0 0 = 1 ∧ domiculeTilingsDec 0 1 = 0` by kernel `rfl`.
- **Evaluated via Lean VM `#eval` and independent Python recomputation (not claimed as kernel `rfl`):**
  1. In `evidence/check_spot_checks.lean` (`lake env lean`), Lean VM `#eval` evaluates `domiculeTilingsDec` directly over all $2^0 = 1$ (`n = 0`) and $2^{10} = 1{,}024$ (`n = 1`) subsets of `Sym2 (Board n)` (`[1, 0]` and `[2, 1, 0]`) and runs an independent Lean profile-transfer DP reproducing rows `n = 0..6` (all `98` entries, `0` mismatches).
  2. In `evidence/verify_s017_lane.py` (`PASSES=91, FAILURES=0`), Python exact-integer profile-transfer DP independently computes complete rows `n = 0..7` (`148` triangle entries, including all `98` entries of `n = 0..6` and all `50` entries of the modulo-prime-derived row `n = 7` in `19.45s`), cross-checks `ROW8_computed.txt` (`65` entries at `n = 8`) and all `396` entries of `b401673.txt` (`n = 0..10`) against `A239273`, `A004003`, and `A011379`, and verifies by exhaustive MRV backtracking (`n = 0..5`) that `Enum(2n^2) = {M_*}`, `Enum(2n^2 - 1) = ∅`, and `Enum(2(n^2 - 1)) = F_H ⊔ F_V`.

### 5.3 Strength Delta and What This Note Does NOT Show

- **Strength delta vs. source (`PIN-S017.md` v1):** **`NONE` (`equal`).** Theorems 1.1 and 1.2 establish both formulas of Dawid Ryłko's `OEIS A401673` `%F` line 17 conjecture at full generality across `%N` line 10's entire triangle domain (`n ≥ 0` for $T(n, n^2) = 1$; `n ≥ 1` on $\mathbb{N}$ for $T(n, n^2 - 1) = n^2(n + 1)$).
- **What this does NOT show:**
  1. **Lower diagonal strata $T(n, k)$ for $0 \le k \le n^2 - 2$:** At $k = n^2 - 2$ ($4$ orthogonal dominoes: `1, 105, 6638, 363228, 17208514, 742106657, ...`), two pairs of defects can interact either within one strip or across two strips (and $4$-cycles of one vertical + one horizontal pair appear), while at $k = 0$ one recovers Kasteleyn's product formula `A004003(n)`; closed forms for general $T(n, k)$ or the full row sum `A239273(n)` remain open.
  2. **General rectangular boards $h \times w$ or toroidal grids (`A401670`) and asymptotic entropy (`A401669`):** Our coordinate-sum collapse exploits the exact $2n \times 2n$ even-side-length four-class balance $|A| = |B| = |C| = |D| = n^2$; rectangular boards with odd dimensions have zero all-diagonal matchings, and toroidal boundary conditions (`A401670`) admit global winding shifts that destroy boundary coordinate-sum pinning.

---

## References

1. N. J. A. Sloane et al., Sequence `A004003` (*Number of domino tilings of $2n \times 2n$ board*), in *The On-Line Encyclopedia of Integer Sequences* (OEIS), live revision `#172`, November 11, 2026, https://oeis.org/A004003.
2. P. W. Kasteleyn, *The statistics of dimers on a lattice. I. The number of dimer arrangements on a quadratic lattice*, Physica **27** (1961), 1209–1225, https://doi.org/10.1016/0031-8914(61)90063-5.
3. H. N. V. Temperley and M. E. Fisher, *Dimer problem in statistical mechanics—an exact result*, Philosophical Magazine **6** (1961), 1061–1063, https://doi.org/10.1080/14786436108243366.
4. A. Heinz and A. Howroyd, Sequence `A239273` (*Number of domicule tilings of a $2n \times 2n$ square; number of perfect matchings in the $2n \times 2n$ kings graph*), in *The On-Line Encyclopedia of Integer Sequences* (OEIS), live revision `#51`, November 11, 2026, https://oeis.org/A239273.
5. A. Heinz, Sequence `A239264` (*Triangle read by rows: $T(n, k)$ is the number of domicule tilings of a $k \times n$ rectangle*), in *The On-Line Encyclopedia of Integer Sequences* (OEIS), live revision `#42`, November 11, 2026, https://oeis.org/A239264.
6. D. Ryłko, Sequence `A401673` (*Triangle read by rows: $T(n, k)$ is the number of domicule tilings of the $2n \times 2n$ square with exactly $2k$ diagonal domicules, $0 \le k \le n^2$*), in *The On-Line Encyclopedia of Integer Sequences* (OEIS), November 1, 2026; live revision `#9`, November 9, 2026, https://oeis.org/A401673.
7. J. Wildeboer and A. Seidel, *Ground-state properties of a square-lattice quantum dimer model with crossing dimers*, Physical Review B **83** (2011), 184430.
8. A. W. Sandvik and R. Moessner, *Correlations and confinement in nonplanar two-dimensional dimer models*, Physical Review B **73** (2006), 144504.
9. D. Ryłko, *Rectangles by number of diagonal pieces* (`lattice-dimers` research notes), rebuilt November 15, 2026, https://dawidrylko.github.io/lattice-dimers/notes/domicules/rectangles-by-diagonal-pieces.html.
10. N. J. A. Sloane et al., Sequence `A011379` (*$a(n) = n^2(n + 1)$*), in *The On-Line Encyclopedia of Integer Sequences* (OEIS), live revision `#207`, November 26, 2025, https://oeis.org/A011379.
11. D. Ryłko, *The dimer entropy of the king's graph*, Zenodo, October 27, 2026, https://doi.org/10.5281/zenodo.23686056.
12. D. Ryłko, *Log-convexity of strip dimer counts on the king's graph*, Zenodo, October 27, 2026, https://doi.org/10.5281/zenodo.23686087.
13. The mathlib Community, *The Lean Mathematical Library* (`Mathlib.Data.Sym.Sym2`, `Mathlib.Algebra.Order.BigOperators.Group.Finset`, `Mathlib.Data.Finset.Card`, `Mathlib.Data.Fintype.Card`), `v4.34.1` (`d13f23b723b8a846827a245b89c10fc7d3f11612`), 2026.
