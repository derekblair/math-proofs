# DOSSIER — Independent Adversarial Audit of the Rule 129 / Rule 126 Proof Strategy (`A267442` vs `A043545` / `A036987`)

- **Lane:** `argon-rule129-audit-20261026`
- **Model / Harness:** `agy`, Gemini 4 Argon (High) · Machine: `xanthe` · Pool: `google-ai-ultra`
- **Date:** 2026-10-27
- **Mode:** Research-only independent adversarial audit (no coding, no repo writes, no GitHub writes)
- **Input Under Audit:** [SCREEN-DOSSIER.md](file:///root/math-fleet/lanes/argon-rule129-audit-20261026/SCREEN-DOSSIER.md) (copy of `argon-rule129-screen-20261026` `DOSSIER.md`), audited per [BRIEF.md](file:///root/math-fleet/lanes/argon-rule129-audit-20261026/BRIEF.md)

---

## Summary of Audit Verdicts (Overview)

| Audited Component | Verdict | Key Evidence & Required Action |
|---|---|---|
| **Prior-Art & Novelty Claim 1** (`A267442(n) = A043545(n)` unproved; ruling `(c)` with folklore disclosure) | **CONFIRMED (WITH 2 MINOR CITATION CORRECTIONS)** | Live OEIS `/internal` records fetched independently (`A267442` `#13`, `A043545` `#55`, `A036987` `#249`, `A071035` `#38`, `A267366` `#20`, `A267417` `#15`) and independent web search confirm zero mathematical or formal proofs exist. Minor record slips in `SCREEN-DOSSIER.md` §1.1: line 22 misquotes `%t A267442` (`CellularAutomaton[129, {{1}, 0}, 100, {{0}, {0}}] // Flatten` vs actual `rule=129; rows=20; ca=CellularAutomaton[rule,{{1},0},rows-1,{All,All}]; ...`), and line 40 misattributes `%H` links of `A071051` to `A071035`. Neither affects novelty ruling `(c)`. |
| **Route A — Lemma A1** (2-equal-inputs XOR law for $f_{126}$) | **SOUND** | Exhaustively verified across all $4 \times 3 = 12$ evaluations $(a, b) \in \{0, 1\}^2$ (§1.2). Requires a 2-line `Bool`-XOR-to-`Nat`-parity bridge `bne (A % 2 == 1) (C % 2 == 1) = ((A + C) % 2 == 1)` when invoked inside Lemma A2. |
| **Route A — Lemma A2** (Global closed form $C_{126}(n, x) = B(n, x)$) | **SOUND-WITH-REPAIR** | Mathematically **exact** across all $(n, x) \in \mathbb{N} \times \mathbb{Z}$: verified by hand for all $n = 0 \dots 6$, all $x \in \mathbb{Z}$ (Tables 1A–1B, 33 inductive transitions + reflection), with complete disjoint case coverage and zero floor/parity boundary failures. **Repairs required for Lean translation:** (1) `SCREEN-DOSSIER.md` line 236 mixes `Prop` (`... \bmod 2 = 1`) and `Bool` (`false`) across branches of `B : ℕ × ℤ → Bool` (fix: `== 1` or `decide`); (2) keep `n - x.natAbs` strictly inside `if h : x.natAbs ≤ n` and parametrize $x \ge 0$ as `x = (m : Int)` and `j = j' + 1`, `k = k' + 1` in Cases 4a/5a to eliminate `Nat` truncated subtraction obligations on `n - 1`, `j - 1`, `k - 1`; (3) unfold `ecaOrbit` via `Function.iterate_succ_apply'` (§1.3–§1.4). |
| **Route A — Lemma A3** (Central binomial parity `A001405(n) mod 2 = A036987(n)`) | **SOUND-WITH-REPAIR** | Mathematically **exact** on $g(0) = 1$, $g(2k) = 0$ ($k \ge 1$), $g(2k+1) = g(k)$ ($k \ge 0$), and strong binary induction. **Repairs required:** (1) `SCREEN-DOSSIER.md` line 254 cites `Nat.choose_modEq_choose_mod_mul_choose_div_nat`, which **does not exist** in `Nat` — in Mathlib4 (`Mathlib.Data.Nat.Choose.Lucas`) its name is **`Choose.choose_modEq_choose_mod_mul_choose_div_nat`** (requiring `Fact (Nat.Prime 2)`); (2) bridge `Bool`-valued `B(n, 0)` to `Nat`-valued `g(n)` via `Bool.toNat` (§1.5). |
| **Route A — Lemma A4** (Complementation bridge to Rule 129 & `A043545`) | **SOUND** | Both `ecaOrbit 129 n x = !(ecaOrbit 126 n x)` ($\forall n \ge 1, \forall x \in \mathbb{Z}$) and `a043545 n = 1 - a036987 n` ($\forall n \ge 0$) hold unconditionally; line-count estimate `~15 lines` on `Nat.digits 2 n` (`SCREEN-DOSSIER.md` line 257) is optimistic (~35–50 lines due to `List.foldl max`/`min` + `Nat.ofDigits` on `List.replicate`), non-blocking (§1.6). |
| **Reduction Claim 2** (`A267442(n) = A043545(n)` for $n > 0 \iff C_{126}(n, 0) = A036987(n)$ for $n \ge 0$) | **SOUND (NON-CIRCULAR)** | Independently re-derived from primary OEIS definitions (`%N A267442`, `%N A043545`, `%F A036987`); neither complementation ($C_{129} = 1 - C_{126}$ for $n \ge 1$) nor $A043545 = 1 - A036987$ ($n \ge 0$) assumes any property of Rule 126's orbit (§2). |
| **Pin Manifest & Statement File** (`SCREEN-DOSSIER.md` §5.1) | **NOT YET FREEZE-READY (7 ITEMS + 5 STATEMENT HAZARDS)** | Must resolve metadata placeholders (`status: DRAFT` removal, `frozen_by`, `sha256`, `commit`), tighten `verbatim_quote` formatting, fix verbal slip in `fidelity_notes` item 1 (`"alternates 0 -> 1 -> 1 -> ..."` $\to$ stabilizes at `1`), and explicitly add `import Mathlib.Logic.Function.Iterate` (rather than relying on transitive import via `Mathlib.Tactic.Ring` inside `Mathlib.Data.Nat.Digits.Defs`) before coordinator freeze (§3). |

---

## 1. Adversarial Audit of Route A (`SCREEN-DOSSIER.md` §4.2)

### 1.1 Independent Truth Table and Direct Simulation ($n = 0 \dots 6$, all $x \in \mathbb{Z}$)

By Wolfram's numbering convention, Rule $R \in \{0, \dots, 255\}$ maps neighborhood $(p, q, r) \in \{0, 1\}^3$ to bit $i = 4p + 2q + r$ of $R$. Since $126 = 64 + 32 + 16 + 8 + 4 + 2 = (01111110)_2$:

| $(p, q, r)$ | $111$ ($7$) | $110$ ($6$) | $101$ ($5$) | $100$ ($4$) | $011$ ($3$) | $010$ ($2$) | $001$ ($1$) | $000$ ($0$) |
|---|---|---|---|---|---|---|---|---|
| $f_{126}(p, q, r)$ | $0$ | $1$ | $1$ | $1$ | $1$ | $1$ | $1$ | $0$ |

Hence $f_{126}(p, q, r) = 0 \iff p = q = r$, and $f_{126}(p, q, r) = 1$ on all six non-uniform triples.

Starting from the single-ON seed $C_{126}(0, 0) = 1$ and $C_{126}(0, x) = 0$ for all $x \in \mathbb{Z} \setminus \{0\}$, direct synchronous evaluation of $C_{126}(n+1, x) = f_{126}(C_{126}(n, x-1), C_{126}(n, x), C_{126}(n, x+1))$ yields **Table 1A** for $n = 0 \dots 6$ and all $x \in \mathbb{Z}$ (every cell with $|x| \ge 7$ sees $(0, 0, 0) \mapsto 0$ throughout $0 \le n \le 6$):

#### Table 1A — Direct Hand Simulation of $C_{126}(n, x)$ vs Closed Form $B(n, x)$ ($n = 0 \dots 6$, all $x \in \mathbb{Z}$)

| $n$ | $\|x\| \ge 7$ | $x=-6$ | $x=-5$ | $x=-4$ | $x=-3$ | $x=-2$ | $x=-1$ | $x=0$ | $x=1$ | $x=2$ | $x=3$ | $x=4$ | $x=5$ | $x=6$ | Binomial row $\binom{n}{k} \bmod 2$ ($k = 0 \dots \lfloor n/2 \rfloor$) | Match $C_{126} = B$? |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| **$0$** | $0$ | $0$ | $0$ | $0$ | $0$ | $0$ | $0$ | **$1$** | $0$ | $0$ | $0$ | $0$ | $0$ | $0$ | $\binom{0}{0}=1 \equiv 1$ | **EXACT** |
| **$1$** | $0$ | $0$ | $0$ | $0$ | $0$ | $0$ | $1$ | **$1$** | $1$ | $0$ | $0$ | $0$ | $0$ | $0$ | $\binom{1}{0}=1 \equiv 1$ | **EXACT** |
| **$2$** | $0$ | $0$ | $0$ | $0$ | $0$ | $1$ | $1$ | **$0$** | $1$ | $1$ | $0$ | $0$ | $0$ | $0$ | $\binom{2}{0}=1\equiv 1,\; \binom{2}{1}=2\equiv 0$ | **EXACT** |
| **$3$** | $0$ | $0$ | $0$ | $0$ | $1$ | $1$ | $1$ | **$1$** | $1$ | $1$ | $1$ | $0$ | $0$ | $0$ | $\binom{3}{0}=1\equiv 1,\; \binom{3}{1}=3\equiv 1$ | **EXACT** |
| **$4$** | $0$ | $0$ | $0$ | $1$ | $1$ | $0$ | $0$ | **$0$** | $0$ | $0$ | $1$ | $1$ | $0$ | $0$ | $\binom{4}{0}=1,\; \binom{4}{1}=4\equiv 0,\; \binom{4}{2}=6\equiv 0$ | **EXACT** |
| **$5$** | $0$ | $0$ | $1$ | $1$ | $1$ | $1$ | $0$ | **$0$** | $0$ | $1$ | $1$ | $1$ | $1$ | $0$ | $\binom{5}{0}=1,\; \binom{5}{1}=5\equiv 1,\; \binom{5}{2}=10\equiv 0$ | **EXACT** |
| **$6$** | $0$ | $1$ | $1$ | $0$ | $0$ | $1$ | $1$ | **$0$** | $1$ | $1$ | $0$ | $0$ | $1$ | $1$ | $\binom{6}{0}=1,\; \binom{6}{1}=6\equiv 0,\; \binom{6}{2}=15\equiv 1,\; \binom{6}{3}=20\equiv 0$ | **EXACT** |

*(Cross-check: rows $n = 0 \dots 6$ on $[-n, n]$ match the primary triangle in OEIS `A071035` `#38` verbatim, and column $x = 0$ gives `1, 1, 0, 1, 0, 0, 0`, matching `A036987(0..6)`.)*

---

### 1.2 Audit of Lemma A1 (`SCREEN-DOSSIER.md` lines 231–233)

- **Claim under audit:** Over $\{0, 1\}$ (`Bool`), for all $a, b$:
  $$f_{126}(a, a, b) = a \oplus b, \qquad f_{126}(a, b, b) = a \oplus b, \qquad f_{126}(a, b, a) = a \oplus b.$$
- **Exhaustive hand check (all 12 cases):**
  - $(a, b) = (0, 0)$: $a \oplus b = 0$; $f_{126}(0, 0, 0) = 0$ across all three patterns.
  - $(a, b) = (0, 1)$: $a \oplus b = 1$; $f_{126}(0, 0, 1) = 1$, $f_{126}(0, 1, 1) = 1$, $f_{126}(0, 1, 0) = 1$.
  - $(a, b) = (1, 0)$: $a \oplus b = 1$; $f_{126}(1, 1, 0) = 1$, $f_{126}(1, 0, 0) = 1$, $f_{126}(1, 0, 1) = 1$.
  - $(a, b) = (1, 1)$: $a \oplus b = 0$; $f_{126}(1, 1, 1) = 0$ across all three patterns.
- **Lean bridge note:** When `ecaRule 126` is typed `Bool → Bool → Bool → Bool`, $\oplus$ is `bne` (`xor`), so applying Lemma A1 to binomial parities requires the elementary bridge lemma `∀ A C : Nat, bne (A % 2 == 1) (C % 2 == 1) = ((A + C) % 2 == 1)` (proved in 2 lines by `omega` or mod-2 case split).
- **Verdict on Lemma A1:** **`SOUND`**.

---

### 1.3 Exhaustive Step-by-Step Hand Trace of Lemma A2 ($n = 0 \dots 5 \to n+1 = 1 \dots 6$, all $x \in \mathbb{Z}$)

In [SCREEN-DOSSIER.md](file:///root/math-fleet/lanes/argon-rule129-audit-20261026/SCREEN-DOSSIER.md#L235-L250), Lemma A2 defines
$$B(n, x) := \begin{cases} \left(\dbinom{n}{\lfloor (n - |x|) / 2 \rfloor} \bmod 2 = 1\right), & |x| \le n, \\[6pt] \mathrm{false}, & |x| > n, \end{cases}$$
reduces $x < 0$ to $x > 0$ via spatial reflection, and splits $x \ge 0$ at step $n \to n + 1$ into five cases:
1. **Exterior ($x \ge n + 2$)**
2. **Outer edge ($x = n + 1$)**
3. **Inner edge ($x = n \ge 1$)**
4. **Interior ($1 \le x \le n - 1$, $u = n - x$):** **4a** ($u = 2j,\; j \ge 1$) and **4b** ($u = 2j + 1,\; j \ge 0$)
5. **Colliding-wave origin ($x = 0$):** **5-0** ($n = 0$), **5a** ($n = 2k,\; k \ge 1$), and **5b** ($n = 2k + 1,\; k \ge 0$)

**Table 1B** audits every inductive step $n \to n + 1$ ($0 \le n \le 5$) across every non-negative position $x \ge 0$ (all 33 transitions; negative $x < 0$ is audited in §1.4 item 1):

#### Table 1B — Complete Case-by-Case Induction Audit of Lemma A2 ($n = 0 \dots 5$, all $x \ge 0$)

| Step $n \to n+1$ | $x$ | Lemma A2 Case Assigned | Parameters | Sim $(p, q, r)$ at $n$ | Claimed Structural Relation in Sketch | $f_{126}(p,q,r)$ | $B(n+1, x)$ Formula & Value | Status |
|---|---|---|---|---|---|---|---|---|
| **$0 \to 1$** | $0$ | **5-0** Origin ($n=0$) | — | $(0, 1, 0)$ | Explicit base $(0,1,0) \mapsto 1$ | $1$ | $\binom{1}{\lfloor 1/2 \rfloor}\bmod 2 = \binom{1}{0}\bmod 2 = 1$ | OK |
| $0 \to 1$ | $1$ | **2** Outer edge ($x=n+1$) | $n=0$ | $(1, 0, 0)$ | $(1, 0, 0) \mapsto 1$ | $1$ | $\binom{1}{0}\bmod 2 = 1$ | OK |
| $0 \to 1$ | $\ge 2$ | **1** Exterior ($x \ge n+2$) | $n=0$ | $(0, 0, 0)$ | $(0, 0, 0) \mapsto 0$ | $0$ | $\|x\| \ge 2 > 1 \implies 0$ | OK |
| **$1 \to 2$** | $0$ | **5b** Origin ($n=2k+1$) | $k=0$ | $(1, 1, 1)$ | $p = q = r = \binom{1}{0}\bmod 2 = 1$ | $0$ | $\binom{2}{1}\bmod 2 = 0$ | OK |
| $1 \to 2$ | $1$ | **3** Inner edge ($x=n \ge 1$) | $n=1$ | $(1, 1, 0)$ | $(1, 1, 0) \mapsto 1$ | $1$ | $\binom{2}{\lfloor 1/2 \rfloor}\bmod 2 = \binom{2}{0}\bmod 2 = 1$ | OK |
| $1 \to 2$ | $2$ | **2** Outer edge ($x=n+1$) | $n=1$ | $(1, 0, 0)$ | $(1, 0, 0) \mapsto 1$ | $1$ | $\binom{2}{0}\bmod 2 = 1$ | OK |
| $1 \to 2$ | $\ge 3$ | **1** Exterior ($x \ge n+2$) | $n=1$ | $(0, 0, 0)$ | $(0, 0, 0) \mapsto 0$ | $0$ | $\|x\| \ge 3 > 2 \implies 0$ | OK |
| **$2 \to 3$** | $0$ | **5a** Origin ($n=2k$) | $k=1$ | $(1, 0, 1)$ | $p = r = \binom{2}{0}\bmod 2 = 1,\; q = \binom{2}{1}\bmod 2 = 0$ | $1 \oplus 0 = 1$ | $\binom{3}{1}\bmod 2 = 1$ | OK |
| $2 \to 3$ | $1$ | **4b** Interior ($u=2j+1$) | $u=1, j=0$ | $(0, 1, 1)$ | $q = r = \binom{2}{0}\bmod 2 = 1,\; p = \binom{2}{1}\bmod 2 = 0$ | $0 \oplus 1 = 1$ | $\binom{3}{1}\bmod 2 = 1$ | OK |
| $2 \to 3$ | $2$ | **3** Inner edge ($x=n \ge 1$) | $n=2$ | $(1, 1, 0)$ | $(1, 1, 0) \mapsto 1$ | $1$ | $\binom{3}{0}\bmod 2 = 1$ | OK |
| $2 \to 3$ | $3$ | **2** Outer edge ($x=n+1$) | $n=2$ | $(1, 0, 0)$ | $(1, 0, 0) \mapsto 1$ | $1$ | $\binom{3}{0}\bmod 2 = 1$ | OK |
| $2 \to 3$ | $\ge 4$ | **1** Exterior ($x \ge n+2$) | $n=2$ | $(0, 0, 0)$ | $(0, 0, 0) \mapsto 0$ | $0$ | $\|x\| \ge 4 > 3 \implies 0$ | OK |
| **$3 \to 4$** | $0$ | **5b** Origin ($n=2k+1$) | $k=1$ | $(1, 1, 1)$ | $p = q = r = \binom{3}{1}\bmod 2 = 1$ | $0$ | $\binom{4}{2}\bmod 2 = 0$ | OK |
| $3 \to 4$ | $1$ | **4a** Interior ($u=2j$) | $u=2, j=1$ | $(1, 1, 1)$ | $p = q = \binom{3}{1}\bmod 2 = 1,\; r = \binom{3}{0}\bmod 2 = 1$ | $1 \oplus 1 = 0$ | $\binom{4}{1}\bmod 2 = 0$ | OK |
| $3 \to 4$ | $2$ | **4b** Interior ($u=2j+1$) | $u=1, j=0$ | $(1, 1, 1)$ | $q = r = \binom{3}{0}\bmod 2 = 1,\; p = \binom{3}{1}\bmod 2 = 1$ | $1 \oplus 1 = 0$ | $\binom{4}{1}\bmod 2 = 0$ | OK |
| $3 \to 4$ | $3$ | **3** Inner edge ($x=n \ge 1$) | $n=3$ | $(1, 1, 0)$ | $(1, 1, 0) \mapsto 1$ | $1$ | $\binom{4}{0}\bmod 2 = 1$ | OK |
| $3 \to 4$ | $4$ | **2** Outer edge ($x=n+1$) | $n=3$ | $(1, 0, 0)$ | $(1, 0, 0) \mapsto 1$ | $1$ | $\binom{4}{0}\bmod 2 = 1$ | OK |
| $3 \to 4$ | $\ge 5$ | **1** Exterior ($x \ge n+2$) | $n=3$ | $(0, 0, 0)$ | $(0, 0, 0) \mapsto 0$ | $0$ | $\|x\| \ge 5 > 4 \implies 0$ | OK |
| **$4 \to 5$** | $0$ | **5a** Origin ($n=2k$) | $k=2$ | $(0, 0, 0)$ | $p = r = \binom{4}{1}\bmod 2 = 0,\; q = \binom{4}{2}\bmod 2 = 0$ | $0 \oplus 0 = 0$ | $\binom{5}{2}\bmod 2 = 0$ | OK |
| $4 \to 5$ | $1$ | **4b** Interior ($u=2j+1$) | $u=3, j=1$ | $(0, 0, 0)$ | $q = r = \binom{4}{1}\bmod 2 = 0,\; p = \binom{4}{2}\bmod 2 = 0$ | $0 \oplus 0 = 0$ | $\binom{5}{2}\bmod 2 = 0$ | OK |
| $4 \to 5$ | $2$ | **4a** Interior ($u=2j$) | $u=2, j=1$ | $(0, 0, 1)$ | $p = q = \binom{4}{1}\bmod 2 = 0,\; r = \binom{4}{0}\bmod 2 = 1$ | $0 \oplus 1 = 1$ | $\binom{5}{1}\bmod 2 = 1$ | OK |
| $4 \to 5$ | $3$ | **4b** Interior ($u=2j+1$) | $u=1, j=0$ | $(0, 1, 1)$ | $q = r = \binom{4}{0}\bmod 2 = 1,\; p = \binom{4}{1}\bmod 2 = 0$ | $0 \oplus 1 = 1$ | $\binom{5}{1}\bmod 2 = 1$ | OK |
| $4 \to 5$ | $4$ | **3** Inner edge ($x=n \ge 1$) | $n=4$ | $(1, 1, 0)$ | $(1, 1, 0) \mapsto 1$ | $1$ | $\binom{5}{0}\bmod 2 = 1$ | OK |
| $4 \to 5$ | $5$ | **2** Outer edge ($x=n+1$) | $n=4$ | $(1, 0, 0)$ | $(1, 0, 0) \mapsto 1$ | $1$ | $\binom{5}{0}\bmod 2 = 1$ | OK |
| $4 \to 5$ | $\ge 6$ | **1** Exterior ($x \ge n+2$) | $n=4$ | $(0, 0, 0)$ | $(0, 0, 0) \mapsto 0$ | $0$ | $\|x\| \ge 6 > 5 \implies 0$ | OK |
| **$5 \to 6$** | $0$ | **5b** Origin ($n=2k+1$) | $k=2$ | $(0, 0, 0)$ | $p = q = r = \binom{5}{2}\bmod 2 = 0$ | $0$ | $\binom{6}{3}\bmod 2 = 0$ | OK |
| $5 \to 6$ | $1$ | **4a** Interior ($u=2j$) | $u=4, j=2$ | $(0, 0, 1)$ | $p = q = \binom{5}{2}\bmod 2 = 0,\; r = \binom{5}{1}\bmod 2 = 1$ | $0 \oplus 1 = 1$ | $\binom{6}{2}\bmod 2 = 1$ | OK |
| $5 \to 6$ | $2$ | **4b** Interior ($u=2j+1$) | $u=3, j=1$ | $(0, 1, 1)$ | $q = r = \binom{5}{1}\bmod 2 = 1,\; p = \binom{5}{2}\bmod 2 = 0$ | $0 \oplus 1 = 1$ | $\binom{6}{2}\bmod 2 = 1$ | OK |
| $5 \to 6$ | $3$ | **4a** Interior ($u=2j$) | $u=2, j=1$ | $(1, 1, 1)$ | $p = q = \binom{5}{1}\bmod 2 = 1,\; r = \binom{5}{0}\bmod 2 = 1$ | $1 \oplus 1 = 0$ | $\binom{6}{1}\bmod 2 = 0$ | OK |
| $5 \to 6$ | $4$ | **4b** Interior ($u=2j+1$) | $u=1, j=0$ | $(1, 1, 1)$ | $q = r = \binom{5}{0}\bmod 2 = 1,\; p = \binom{5}{1}\bmod 2 = 1$ | $1 \oplus 1 = 0$ | $\binom{6}{1}\bmod 2 = 0$ | OK |
| $5 \to 6$ | $5$ | **3** Inner edge ($x=n \ge 1$) | $n=5$ | $(1, 1, 0)$ | $(1, 1, 0) \mapsto 1$ | $1$ | $\binom{6}{0}\bmod 2 = 1$ | OK |
| $5 \to 6$ | $6$ | **2** Outer edge ($x=n+1$) | $n=5$ | $(1, 0, 0)$ | $(1, 0, 0) \mapsto 1$ | $1$ | $\binom{6}{0}\bmod 2 = 1$ | OK |
| $5 \to 6$ | $\ge 7$ | **1** Exterior ($x \ge n+2$) | $n=5$ | $(0, 0, 0)$ | $(0, 0, 0) \mapsto 0$ | $0$ | $\|x\| \ge 7 > 6 \implies 0$ | OK |

*(Bonus check on the colliding-wave Mersenne step $6 \to 7$ at $x = 0$: $n = 6 = 2k$ with $k = 3$ gives $p = r = \binom{6}{2}\bmod 2 = 15\bmod 2 = 1$ and $q = \binom{6}{3}\bmod 2 = 20\bmod 2 = 0$, so $(1, 0, 1) \mapsto 1 \oplus 0 = 1 = \binom{7}{3}\bmod 2 = 35\bmod 2 = 1 = B(7, 0)$.)*

---

### 1.4 Boundary, Completeness, Floor/Parity, and Truncated-Subtraction Audit of Lemma A2

1. **Spatial reflection reduction ($x < 0 \to x > 0$, `SCREEN-DOSSIER.md` line 240):**
   - For $x < 0$, write $y = -x \ge 1$. Under the universally-quantified inductive hypothesis $\forall z \in \mathbb{Z},\; C_{126}(n, z) = B(n, z)$, we have $B(n, -z) = B(n, z)$ (since `(-z).natAbs = z.natAbs`) and amphichirality $f_{126}(r, q, p) = f_{126}(p, q, r)$ (verified on the two asymmetric pairs $(1,0,0) \leftrightarrow (0,0,1)$ and $(1,1,0) \leftrightarrow (0,1,1)$ in §1.1), giving:
     $$C_{126}(n+1, -y) = f_{126}\bigl(B(n, -(y+1)), B(n, -y), B(n, -(y-1))\bigr) = f_{126}\bigl(B(n, y-1), B(n, y), B(n, y+1)\bigr) = C_{126}(n+1, y) = B(n+1, y) = B(n+1, -y).$$
   - **Completeness check:** Together with $x \ge 0$, every $x \in \mathbb{Z}$ is covered.

2. **Completeness and disjointness of the 5-way split on $x \ge 0$ for all $n \ge 0$:**
   - At $n = 0$: Case 3 ($x = n \ge 1$) and Case 4 ($1 \le x \le -1$) are empty; Cases 5-0 ($x = 0$), 2 ($x = 1$), and 1 ($x \ge 2$) partition $\{x \in \mathbb{Z} : x \ge 0\} = \{0\} \sqcup \{1\} \sqcup [2, \infty)$.
   - At $n = 1$: Case 4 ($1 \le x \le 0$) is empty; Cases 5b ($x = 0$), 3 ($x = 1$), 2 ($x = 2$), and 1 ($x \ge 3$) partition $[0, \infty) = \{0\} \sqcup \{1\} \sqcup \{2\} \sqcup [3, \infty)$.
   - At $n \ge 2$: Cases 5 ($x = 0$), 4 ($1 \le x \le n - 1$), 3 ($x = n$), 2 ($x = n + 1$), and 1 ($x \ge n + 2$) partition $[0, \infty)$ into five nonempty disjoint sets.

3. **Boundary audit of every case transition:**
   - **Boundary $x = n + 2$ (Exterior vs Outer edge):** At $x = n + 2$, $x - 1 = n + 1 > n$, so all three of $x - 1, x, x + 1$ lie strictly outside $[-n, n]$ ($p = q = r = 0$), and $|x| = n + 2 > n + 1$ puts $(n + 1, x)$ outside $[-(n+1), n+1]$. At $x = n + 1$, $x - 1 = n$ hits the light-cone edge: $n - |n| = 0 \implies p = \binom{n}{0} \bmod 2 = 1$ (valid even at $n = 0$!), while $q = r = 0$, giving $(1, 0, 0) \mapsto 1 = \binom{n+1}{0} \bmod 2 = B(n+1, n+1)$.
   - **Boundary $x = n$ ($n \ge 1$, Inner edge vs Origin / Interior):**
     - Why $n \ge 1$ is required: At $n = 0$, $x = n = 0$ has $x - 1 = -1$ with $|-1| = 1 > 0$, so $p = B(0, -1) = 0 \ne 1$. Restricting Case 3 to $n \ge 1$ routes $(n, x) = (0, 0)$ cleanly to Case 5-0.
     - For all $n \ge 1$: $x - 1 = n - 1 \ge 0$ satisfies $|x - 1| = n - 1 \le n$ with $n - (n - 1) = 1$, $\lfloor 1/2 \rfloor = 0 \implies p = \binom{n}{0} \bmod 2 = 1$; $q = \binom{n}{0} \bmod 2 = 1$; $r = B(n, n + 1) = 0$. Thus $(p, q, r) = (1, 1, 0) \mapsto 1$. Meanwhile, $(n + 1) - |n| = 1$, $\lfloor 1/2 \rfloor = 0 \implies B(n+1, n) = \binom{n+1}{0} \bmod 2 = 1$.
     - Why $x = n$ ($u = 0$) could **not** be merged into Case 4a ($u = 2j$ at $j = 0$): At $u = 0$, $x + 1 = n + 1$ exits the light cone ($r = 0$, whereas unguarded `Nat` subtraction `(u - 1) / 2` at $u = 0$ would truncate `0 - 1 = 0` and falsely predict $r = \binom{n}{0} \bmod 2 = 1$). Separating $x = n$ prevents this exact bug.
   - **Boundaries of Case 4 ($1 \le x \le n - 1$, $u = n - x \in \{1, \dots, n - 1\}$):**
     - At $x = 1$ (lower spatial boundary, $u = n - 1$): $x - 1 = 0 \ge 0$ has $|x - 1| = 0 \le n$, so $n - |x - 1| = n = u + 1$ without sign flip.
     - At $x = n - 1$ (upper spatial boundary, $u = 1$): $x + 1 = n$ still satisfies $|x + 1| = n \le n$ (inside the light cone!), with $n - |x + 1| = 0 = u - 1$. Here $u = 1$ is odd ($j = 0$ in Case 4b), giving $u - 1 = 0 \ge 0$ (no negative subtraction).
     - **Even-$u$ boundary ($u = 2j$):** Since $u \ge 1$ and $u = 2j$, $j = 0$ is impossible, so $j \ge 1$ holds unconditionally. Thus $u - 1 = 2j - 1 \ge 1$, $\lfloor (2j-1)/2 \rfloor = j - 1 \ge 0$, $\lfloor 2j/2 \rfloor = \lfloor (2j+1)/2 \rfloor = j$, and target floor $\lfloor ((n+1)-x)/2 \rfloor = \lfloor (2j+1)/2 \rfloor = j$, matching $\binom{n}{j} + \binom{n}{j-1} = \binom{n+1}{j}$.
     - **Odd-$u$ boundary ($u = 2j + 1$):** Since $j \ge 0$, $u - 1 = 2j \ge 0$, $\lfloor 2j/2 \rfloor = \lfloor (2j+1)/2 \rfloor = j$, $\lfloor (2j+2)/2 \rfloor = j + 1$, and target floor $\lfloor ((n+1)-x)/2 \rfloor = \lfloor (2j+2)/2 \rfloor = j + 1$, matching $\binom{n}{j+1} + \binom{n}{j} = \binom{n+1}{j+1}$.
   - **Boundaries of Case 5 ($x = 0$):**
     - Separating $n = 0$ before $n = 2k$ ($k \ge 1$) is essential: at $n = 0$, $B(0, \pm 1)$ takes the exterior branch (`false`), and in `Nat` `\binom{2k}{k-1}` at $k = 0$ would truncate `0 - 1 = 0`, falsely yielding $\binom{0}{0} = 1$ instead of $0$. For $k \ge 1$, $2k \ge 2 > 1 = |\pm 1|$, $2k - 1 = 2(k-1) + 1 \ge 1$, $\lfloor (2k-1)/2 \rfloor = k - 1 \ge 0$, $\lfloor 2k/2 \rfloor = k$, and $\lfloor (2k+1)/2 \rfloor = k$.
     - For $n = 2k + 1$ ($k \ge 0$): even at $k = 0$ ($n = 1$), $|\pm 1| = 1 \le 2k + 1$, $(2k+1) - 1 = 2k \ge 0$, $\lfloor 2k/2 \rfloor = k = \lfloor (2k+1)/2 \rfloor$, so $p = q = r$ and $f_{126}(q, q, q) = 0$. Meanwhile $B(2k+2, 0)$ evaluates $\binom{2k+2}{k+1} = \binom{2k+1}{k} + \binom{2k+1}{k+1} = 2\binom{2k+1}{k} \equiv 0 \pmod 2$ for every $k \ge 0$.

4. **Formalization Defects Caught in Lemma A2 & Explicit Repairs:**
   - **Defect A2-1 (`Prop`-vs-`Bool` branch mismatch in `SCREEN-DOSSIER.md` line 236):** Line 236 defines `B : ℕ × ℤ → Bool` with `(\binom{n}{\lfloor (n - |x|)/2 \rfloor} \bmod 2 = 1)` (a `Prop`) in the $|x| \le n$ branch and `false` (a `Bool`) in the $|x| > n$ branch.
     - *Repair:* Define `def B (n : Nat) (x : Int) : Bool := if x.natAbs ≤ n then Nat.choose n ((n - x.natAbs) / 2) % 2 == 1 else false`.
   - **Defect A2-2 (Mixed `Nat`/`Int` subtraction & `j - 1` / `k - 1` obligations in lines 244–248):** Writing `1 ≤ x ≤ n - 1` or `j - 1` / `k - 1` on `Nat` creates avoidable `Nat.sub_add_cancel` and `Int.natAbs (x - 1)` sign-split goals (and unguarded `n - x.natAbs` fails at e.g. $(n, x) = (0, 1)$, where `0 - 1 = 0` in `Nat` gives `choose 0 0 % 2 == 1 = true` instead of `false`).
     - *Repair:* After reducing $x < 0$ to $x > 0$ via `Int.le_total 0 x`, write `x = (m : Int)` for `m : Nat` (so for `m = m' + 1`, `(x - 1).natAbs = m'`, `x.natAbs = m' + 1`, `(x + 1).natAbs = m' + 2` hold by `rfl` / `omega` with zero sign splits), and write `j = j' + 1` in Case 4a and `k = k' + 1` in Case 5a so `Nat.choose_succ_succ` applies without subtraction preconditions.
   - **Defect A2-3 (`Nat.iterate` unfolding direction on `ecaOrbit`, line 368 vs line 240):** In Lean/Mathlib, `(ecaStep R)^[n + 1] singleSeed` unfolds definitionally to `(ecaStep R)^[n] (ecaStep R singleSeed)` (`Function.iterate_succ_apply`), **not** `ecaStep R ((ecaStep R)^[n] singleSeed)`.
     - *Repair:* Begin the inductive step of Lemma A2 (and Lemma A4) with `rw [ecaOrbit, Function.iterate_succ_apply']`.

- **Verdict on Lemma A2:** **`SOUND-WITH-REPAIR`** (zero mathematical or boundary errors; apply Repairs A2-1, A2-2, A2-3 in Lean).

---

### 1.5 Audit of Lemma A3 (`SCREEN-DOSSIER.md` lines 251–255)

- **Mathematical check:**
  - At $x = 0$, $|0| = 0 \le n$ for every $n \in \mathbb{N}$, so $(B(n, 0)).\mathrm{toNat} = g(n) := \binom{n}{\lfloor n/2 \rfloor} \bmod 2$.
  - $g(0) = \binom{0}{0} \bmod 2 = 1$, matching $0 = 2^0 - 1$ ($m = 0$).
  - For $n = 2k$ ($k \ge 1$): $2k - 1 \ge 1$ and $k - 1 \ge 0$ (no `Nat` underflow; note $k = 0$ is excluded because $g(0) = 1 \ne 0$), and Pascal + symmetry (`Nat.choose_symm` at $2k - 1$, $k - 1$) give $\binom{2k}{k} = \binom{2k-1}{k-1} + \binom{2k-1}{k} = 2\binom{2k-1}{k-1}$, so $g(2k) = 0$. Conversely, $\exists m, 2k = 2^m - 1$ is false for $k \ge 1$ because $m = 0$ gives $0 \ne 2k$ and $m = m' + 1$ gives $2^{m'+1} - 1 = 2(2^{m'} - 1) + 1 \equiv 1 \not\equiv 0 \pmod 2$.
  - For $n = 2k + 1$ ($k \ge 0$): $(2k+1) \bmod 2 = 1$, $\lfloor (2k+1)/2 \rfloor = k$, and $\binom{1}{k \bmod 2} = 1$ for both $k \bmod 2 = 0$ and $k \bmod 2 = 1$. One step of Lucas's theorem mod $2$ gives $\binom{2k+1}{k} \equiv \binom{1}{k \bmod 2} \binom{k}{\lfloor k/2 \rfloor} = \binom{k}{\lfloor k/2 \rfloor} \pmod 2$, so $g(2k+1) = g(k)$. Since $k < 2k + 1$ for all $k \ge 0$, strong induction yields $g(2k+1) = 1 \iff \exists m', k = 2^{m'} - 1 \iff \exists m, 2k + 1 = 2^m - 1$ (using $2(2^{m'} - 1) + 1 = 2^{m'+1} - 1$ via `Nat.one_le_two_pow`, and ruling out $m = 0$ since $2k + 1 \ne 0$).
- **Formalization Defects Caught in Lemma A3 & Explicit Repairs:**
  - **Defect A3-1 (Non-existent Mathlib identifier on `SCREEN-DOSSIER.md` line 254):** Line 254 cites `Nat.choose_modEq_choose_mod_mul_choose_div_nat`. Direct inspection of Mathlib4 `Mathlib.Data.Nat.Choose.Lucas` confirms this theorem lives in the **`Choose`** namespace, **not** `Nat`: its exact name is `Choose.choose_modEq_choose_mod_mul_choose_div_nat`, with typeclass premise `[Fact (Nat.Prime p)]`.
    - *Repair:* Import `Mathlib.Data.Nat.Choose.Lucas` and `Mathlib.Data.Nat.Prime.Defs` (or `Basic`), supply `haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩`, and invoke `Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 2 * k + 1) (k := k) (p := 2)`.
  - **Defect A3-2 (`Bool`-vs-`Nat` type conflation on line 251):** Line 251 writes `C_{126}(n, 0) = g(n) := \binom{n}{\lfloor n/2 \rfloor} \bmod 2`, conflating `Bool`-valued `ecaOrbit 126 n 0` with `{0, 1}`-valued `g(n) : Nat`.
    - *Repair:* State `B n 0 = true ↔ g n = 1` (immediate from `Nat.mod_two_eq_zero_or_one`), yielding `rule126_middle_column_iff` first, and derive `rule126_middle_column_eq_a036987` in 4 lines via `by_cases h : ∃ m : Nat, n = 2 ^ m - 1` and `if_pos` / `if_neg`.
- **Verdict on Lemma A3:** **`SOUND-WITH-REPAIR`**.

---

### 1.6 Audit of Lemma A4 (`SCREEN-DOSSIER.md` line 257)

- **Check of part 1 (`∀ n ≥ 1, ∀ x : Int, ecaOrbit 129 n x = !(ecaOrbit 126 n x)`):**
  - Requires keeping `∀ x : Int` **inside** the inductive hypothesis on $n \ge 1$ (`n = k + 1`), rewriting `ecaOrbit` with `Function.iterate_succ_apply'`, and discharging the two finite 8-case `Bool` truth-table lemmas `∀ p q r : Bool, ecaRule 129 p q r = !(ecaRule 126 p q r)` (base $n = 1$) and `∀ p q r : Bool, ecaRule 129 (!p) (!q) (!r) = !(ecaRule 126 p q r)` (step $k + 1 \to k + 2$) via `cases p <;> cases q <;> cases r <;> decide` (kernel `decide` is standard `Decidable.decide`, **not** `native_decide` or `Lean.ofReduceBool`).
- **Check of part 2 (`∀ n : Nat, a043545 n = 1 - a036987 n`):**
  - Mathematically valid for all $n \ge 0$ (re-derived from primary definitions in §2.2 below).
  - *Line-count realism note:* Because `a043545` in `SCREEN-DOSSIER.md` line 383 uses `ds.foldl max d - ds.foldl min d` on `Nat.digits 2 n`, proving `ds.foldl max d = 1` (from `Nat.digits_lt_base` + `Nat.getLast_digit_ne_zero`) and `ds.foldl min d = 1 ↔ ∃ m, n = 2 ^ m - 1` (via `List.eq_replicate` + `Nat.ofDigits_digits` + geometric sum `Nat.ofDigits 2 (List.replicate m 1) = 2 ^ m - 1`) requires auxiliary `List.foldl` lemmas (~35–50 lines of Lean, vs the `~15 lines` estimated on `SCREEN-DOSSIER.md` line 257).
  - Combining parts 1 and 2 for $n > 0$: for any `b : Bool`, `(!b).toNat = 1 - b.toNat` (valid in `Nat` without truncation issue since `b.toNat ≤ 1`), so `a267442 n = (ecaOrbit 129 n 0).toNat = (!(ecaOrbit 126 n 0)).toNat = 1 - (ecaOrbit 126 n 0).toNat = 1 - a036987 n = a043545 n`.
- **Verdict on Lemma A4:** **`SOUND`**.

---

## 2. Independent Reduction & Primary-Record Audit (`SCREEN-DOSSIER.md` §§1–3)

### 2.1 Audit of Primary OEIS Quotes & Prior-Art Claim (`Claim 1`)

Independent live fetches of `/internal` records on `oeis.org` (2026-10-27) and independent web searches (`bx`) confirm **Claim 1**: Mathar's conjecture `A267442(n) = A043545(n)` ($n > 0$) and the equivalent Rule 126 middle-column claim $C_{126}(n, 0) = A036987(n)$ ($n \ge 0$) remain **unproved** in both mathematical literature and formal proof libraries, supporting **novelty ruling `(c)`** with mandatory folklore disclosure (`A071035` `%Y`, `A267366` Koeppl 2022, Sloane 2015, Macfarlane 2016).

Two factual citation slips in `SCREEN-DOSSIER.md` §1.1 were caught against the live `/internal` records (neither alters any mathematical claim):
1. **`A267442` `%t` misquote (`SCREEN-DOSSIER.md` line 22):** `SCREEN-DOSSIER.md` quotes `%t` of `A267442` (`#13`, Feb 16 2025) as `CellularAutomaton[129, {{1}, 0}, 100, {{0}, {0}}] // Flatten`. The actual `%t` line in `A267442/internal` is:
   > `%t rule=129; rows=20; ca=CellularAutomaton[rule,{{1},0},rows-1,{All,All}]; (* Start with single black cell *) catri=Table[Take[ca[[k]],{rows-k+1,rows+k-1}],{k,1,rows}]; (* Truncated list of each row *) Table[catri[[k]][[k]],{k,1,rows}] (* Keep only middle cell from each row *)`
   *(Note: In Mathematica, `CellularAutomaton[129, {{1}, 0}, rows-1, {All, All}]` evolves on the infinite integer lattice from `{{1}, 0}` — dynamically tracking the uniform background `0 -> 1 -> 1 -> ...` — and slices the $(2k-1)$-wide light cone at row $k$, from which `catri[[k]][[k]]` extracts $x = 0$. Thus $A267442(n) = C_{129}(n, 0)$ on $\mathbb{Z}$ is confirmed directly from Robert Price's actual `%t` code as well as `A267417` `#15` lines 97–133.)*
2. **`A071035` `%H` misattribution (`SCREEN-DOSSIER.md` line 40):** `SCREEN-DOSSIER.md` attributes `"Hans Havermann pattern plot; Eric Weisstein MathWorld Rule 126..."` to `%H` of `A071035`, whereas `A071035/internal` (`#38`, Feb 16 2025) lists only Robert Price's b-file, Weisstein's *Elementary Cellular Automaton*, Wolfram's *NKS*, and the two OEIS CA index links (Havermann's plot and MathWorld *Rule 126* live on `A071051`).

---

### 2.2 Independent Re-Derivation of Complementation ($C_{129}(n, x) = 1 - C_{126}(n, x)$ for $n \ge 1$)

Starting strictly from Wolfram's 8-bit rule encoding $f_R(p, q, r) = b_{4p + 2q + r}(R)$ for $(p, q, r) \in \{0, 1\}^3$:

1. **Output negation `(C0)`:** Since $126 = \sum_{i=1}^{6} 2^i = (01111110)_2$ and $129 = 2^7 + 2^0 = (10000001)_2$ satisfy $126 + 129 = 255 = \sum_{i=0}^{7} 2^i$, every bit $i \in \{0, \dots, 7\}$ satisfies $b_i(129) = 1 - b_i(126)$, i.e.,
   $$\forall p, q, r \in \{0, 1\},\qquad f_{129}(p, q, r) = 1 - f_{126}(p, q, r). \tag{C0}$$
2. **Input-complementation symmetry of $f_{126}$ and conjugacy `(C1)`:** Replacing $(p, q, r) \mapsto (1-p, 1-q, 1-r)$ maps $i = 4p + 2q + r$ to $4(1-p) + 2(1-q) + (1-r) = 7 - i$. Because $(01111110)_2$ is a palindrome ($b_{7-i}(126) = b_i(126)$ for all $0 \le i \le 7$), $f_{126}(1-p, 1-q, 1-r) = f_{126}(p, q, r)$. Applying $(\text{C0})$ at $(1-p, 1-q, 1-r)$ therefore gives:
   $$\forall p, q, r \in \{0, 1\},\qquad f_{129}(1-p, 1-q, 1-r) = 1 - f_{126}(p, q, r). \tag{C1}$$
3. **Evolution from the common seed $c_0(x) = \mathbf{1}_{x = 0}$:**
   - **At $n = 0$:** $C_{129}(0, x) = c_0(x) = C_{126}(0, x)$, so $C_{129}(0, x) \ne 1 - C_{126}(0, x)$ everywhere on $\mathbb{Z}$ (at $x = 0$, $1 \ne 0$; at $x \ne 0$, $0 \ne 1$).
   - **Base $n = 1$:** Because the $n = 0$ states are *identical* (not complemented), $(\text{C0})$ — not $(\text{C1})$ — applies at step $0 \to 1$:
     $$C_{129}(1, x) = f_{129}\bigl(c_0(x-1), c_0(x), c_0(x+1)\bigr) \stackrel{(\text{C0})}{=} 1 - f_{126}\bigl(c_0(x-1), c_0(x), c_0(x+1)\bigr) = 1 - C_{126}(1, x) \quad (\forall x \in \mathbb{Z}).$$
   - **Inductive step $n \to n + 1$ ($n \ge 1$):** Assuming $\forall y \in \mathbb{Z},\; C_{129}(n, y) = 1 - C_{126}(n, y)$, the states at step $n$ *are* complemented, so $(\text{C1})$ applies:
     $$C_{129}(n+1, x) = f_{129}\bigl(1 - C_{126}(n, x-1), 1 - C_{126}(n, x), 1 - C_{126}(n, x+1)\bigr) \stackrel{(\text{C1})}{=} 1 - C_{126}(n+1, x) \quad (\forall x \in \mathbb{Z}).$$
4. **Non-circularity verdict:** **NON-CIRCULAR.** This derivation depends solely on the 8-bit truth tables of $126$ and $129$ and holds from *every* initial configuration $c_0 : \mathbb{Z} \to \{0, 1\}$; it uses zero information about `A267442`, `A043545`, `A036987`, or $B(n, x)$.

---

### 2.3 Independent Re-Derivation of $A043545(n) = 1 - A036987(n)$ ($n \ge 0$) and Full Equivalence

1. **Primary OEIS definitions used (excluding Somos's `%F` formula to avoid circularity):**
   - `%N A043545`: `(Maximal base-2 digit of n) - (minimal base-2 digit of n)` with `%O 0,1` and canonical base-2 digit set $D_2(0) = \{0\}$ (`%S A043545` starts `0, 0, 1, 0, ...`; `%t` `IntegerDigits[0, 2] = {0}`).
   - `%N` / first `%F` of `A036987`: Fredholm-Rueppel sequence (`%O 0,1`), defined by $A036987(n) = 1$ iff $\exists m \in \mathbb{N},\; n = 2^m - 1$, and $0$ otherwise (equivalently `[x^n] \sum_{m \ge 0} x^{2^m - 1}`). *(Note: $m \in \mathbb{N}$ and $m \in \mathbb{Z}$ are identical for $n \in \mathbb{N}$ because $2^m - 1 \notin \mathbb{N}$ for all $m < 0$.)*
2. **Derivation for all $n \in \mathbb{N}$:**
   - **At $n = 0$:** $D_2(0) = \{0\}$, so $A043545(0) = \max\{0\} - \min\{0\} = 0$. Since $0 = 2^0 - 1$ ($m = 0$), $A036987(0) = 1$, giving $1 - A036987(0) = 0 = A043545(0)$.
   - **For $n \ge 1$:** Write the unique standard binary expansion $n = \sum_{j=0}^{k-1} d_j 2^j$ with $k \ge 1$, $d_j \in \{0, 1\}$, and leading bit $d_{k-1} = 1$.
     - Since $1 = d_{k-1} \in D_2(n) \subseteq \{0, 1\}$, $\max D_2(n) = 1$.
     - Since $\emptyset \ne D_2(n) \subseteq \{0, 1\}$, $\min D_2(n) \in \{0, 1\}$, and $\min D_2(n) = 1 \iff \forall j < k,\; d_j = 1 \iff n = \sum_{j=0}^{k-1} 2^j = 2^k - 1$. Because $n \ge 1$ excludes $m = 0$ ($2^0 - 1 = 0$) and binary length uniquely fixes $m = k$ for $m \ge 1$, $\min D_2(n) = 1 \iff \exists m \in \mathbb{N},\; n = 2^m - 1 \iff A036987(n) = 1$ (and both equal $0$ otherwise). Thus $\min D_2(n) = A036987(n)$, whence
       $$A043545(n) = \max D_2(n) - \min D_2(n) = 1 - A036987(n).$$
3. **Non-circularity & bidirectional equivalence check:**
   - **Non-circularity:** Neither step assumes Mathar's conjecture or the Rule 126 middle-column claim.
   - **Truncated-subtraction check on the inversion `1 - u = 1 - v ↔ u = v`:** Over `Nat`, `1 - u = 1 - v` does *not* imply `u = v` for arbitrary naturals (e.g., `1 - 2 = 0 = 1 - 3`), **but** here $C_{126}(n, 0) \in \{0, 1\}$ and $A036987(n) \in \{0, 1\}$ both satisfy $\le 1$, on which $u \mapsto 1 - u$ is a bijection $\{0, 1\} \to \{0, 1\}$.
   - **At $n = 0$:** $C_{126}(0, 0) = 1 = A036987(0)$ holds definitionally (`singleSeed 0 = true` and $0 = 2^0 - 1$).
   - **Conclusion on Claim 2:** **SOUND (EXACT & NON-CIRCULAR).** $\bigl(\forall n > 0,\; A267442(n) = A043545(n)\bigr) \iff \bigl(\forall n \ge 0,\; C_{126}(n, 0) = A036987(n)\bigr)$.

---

## 3. Pin-Freeze Readiness & Statement-File Hazard Assessment (`SCREEN-DOSSIER.md` §5.1)

### 3.1 Gate-by-Gate Audit of the `DRAFT` Pin Manifest

Audited against [pin-manifest-template.md](file:///root/math-fleet/files/pin-manifest-template.md) and the six gates in [BRIEF.md](file:///root/math-fleet/lanes/argon-rule129-audit-20261026/BRIEF.md#L15):

| Gate | Status | Inline Evidence & Assessment |
|---|---|---|
| **1. Verbatim source quotes present** | **PASS WITH FORMAT FIX** | All six quoted lines (`SCREEN-DOSSIER.md` lines 290–295) match the live OEIS records character-for-character (`A267442` `#13` lines 37, 58; `A043545` `#55` line 37; `A036987` `#249` lines 37, 118; `A267366` `#20` line 40). **Fix required:** change YAML `verbatim_quote: >` (which folds newlines into spaces) to `verbatim_quote: |`, and append the verbatim offset/cross-reference lines `%O A267442 0`, `%O A043545 0,1`, `%O A036987 0,1`, and `%Y A071035 Cf. A036987 (central column).`. |
| **2. Strongest published form stated** | **PASS** | `SCREEN-DOSSIER.md` lines 296–304 accurately state both the unproved `A267442` status (Mathar 2016; finite check $n \le 1{,}048{,}576$ in `derekblair/math-proofs#5`) and the unproved Rule 126 empirical citations (`A071035` `%Y`, `A267366` Koeppl 2022, Sloane 2015 `arXiv:1503.01168v3` §6.1, Macfarlane 2016 §9 Eq. 67). *(Optional enhancement: add 1 sentence noting Palamarchuk 2026 `ECA/Doubling.lean` `finRule_two_dbl` as the strongest formal near-miss on even-support doubled states.)* |
| **3. Exact theorem names** | **PASS** | Lines 310, 314, 317 match `namespace Mathproofs.Rule129MiddleColumn` + `theorem` declarations on lines 351, 386, 391, 396 verbatim (`Mathproofs.Rule129MiddleColumn.rule126_middle_column_iff`, `...rule126_middle_column_eq_a036987`, `...a267442_eq_a043545`). |
| **4. Axiom allowlist** | **PASS** | Line 322 specifies `[propext, Classical.choice, Quot.sound]`, matching `pin-manifest-template.md` line 27 verbatim. |
| **5. Trust policy** | **PASS** | Lines 323–327 specify `native_decide: forbidden`, `ofReduceBool: forbidden`, `custom_axioms: forbidden`, `sorry_in_solution: forbidden`, matching `pin-manifest-template.md` lines 28–32 verbatim. |
| **6. `delta_vs_source = NONE`** | **PASS (VERIFIED)** | Line 340 states `NONE`. Independently verified: `a267442_eq_a043545` quantifies over all `n : Nat` with `0 < n` (matching Mathar's `n>0`) and uses primary definitions of both `A267442` and `A043545` without baking in Somos's `1 - A036987(n)` reduction; `rule126_middle_column_iff` and `rule126_middle_column_eq_a036987` cover all `n : Nat` ($n \ge 0$). |

---

### 3.2 Mandatory Changes Before Coordinator Freeze (Checklist of 7 Items)

The manifest in `SCREEN-DOSSIER.md` §5.1 is **NOT YET FREEZE-READY** as a live contract until a coordinator executes these 7 items:

1. **Remove non-schema `status: DRAFT` key (`SCREEN-DOSSIER.md` line 278) and materialize at `~/workspace/math-fleet/pins/a267442-eq-a043545.md`:** Per [pin-manifest-template.md](file:///root/math-fleet/files/pin-manifest-template.md#L5-L40), the frozen contract lives on the coordinator's desk (`pins/`), registered in the lane `REGISTRY`, and starts with `candidate:`.
2. **Populate `frozen_by` and freeze date (`SCREEN-DOSSIER.md` lines 281–282):** Replace `DRAFT (prepared by argon-rule129-screen-20261026; ...)` with the freezing coordinator identity.
3. **Fix statement-file imports (§3.3 Hazard 1), compile under `leanprover/lean4:v4.34.1`, commit to `derekblair/math-proofs`, and fill `statement_file.sha256` + `statement_file.commit` (`SCREEN-DOSSIER.md` lines 307–308):** Replace both `<TBD_AT_FREEZE ...>` placeholders with recorded `sha256sum` and `git rev-parse HEAD` outputs after clean `lake env lean` verification.
4. **Switch `verbatim_quote: >` to `verbatim_quote: |` and include `%O` + `%Y A071035` (`SCREEN-DOSSIER.md` lines 289–295):** Preserve exact line breaks and include `%O A267442 0`, `%O A043545 0,1`, `%O A036987 0,1`, and `%Y A071035 Cf. A036987 (central column).`.
5. **Correct `fidelity_notes` item 1 background description and `Nat.digits 2 0` description (`SCREEN-DOSSIER.md` lines 331 & 335):**
   - Line 331 states `(where the infinite background alternates 0 -> 1 -> 1 -> ... for n >= 1)` — replace `"alternates"` with `"transitions 0 -> 1 at n = 1 and remains 1 for all n >= 1"` ($f_{129}(0,0,0) = 1$ and $f_{129}(1,1,1) = 1$, so it stabilizes rather than alternating).
   - Line 335 states `with 0 having single digit 0 (so a043545 0 = 0)` — clarify that in Mathlib `Nat.digits 2 0 = []`, which the explicit `| [] => 0` branch maps to `0` to match conventional $0 = (0)_2$ ($\max\{0\} - \min\{0\} = 0$).
6. **Enumerate the 7 locked `def` declarations in scope (`SCREEN-DOSSIER.md` lines 309–338):** Explicitly name `ecaRule`, `ecaStep`, `singleSeed`, `ecaOrbit`, `a267442`, `a036987`, and `a043545` in `theorems` or `fidelity_notes` (per `pin-manifest-template.md` line 26: `# repeat per theorem/definition in scope`) so reviewers verify zero silent edits to definitions as well as theorem headers.
7. **Bind `review_route` (`SCREEN-DOSSIER.md` line 342) to a named non-Gemini pool:** Replace the generic placeholder description with the concrete cross-model reviewer pool (e.g., OpenAI/Codex or Anthropic/Claude review lane).

---

### 3.3 Statement-File Hazard Audit (`Mathproofs/Rule129MiddleColumn.lean`, `SCREEN-DOSSIER.md` lines 348–400)

1. **Hazard S1 — Fragile / missing explicit import for `(ecaStep R)^[n]` (`SCREEN-DOSSIER.md` lines 349 & 368) [MUST FIX BEFORE FREEZE]:**
   - *Finding:* Line 349 imports only `import Mathlib.Data.Nat.Digits.Defs`, while line 368 uses `(ecaStep R)^[n] singleSeed`. Inspection of Mathlib4 docs (`Mathlib/Data/Nat/Digits/Defs.html` lines 11–17; `Mathlib/Logic/Function/Iterate.html` lines 19–22) shows `^[n]` (`Nat.iterate`) is defined in `Mathlib.Logic.Function.Iterate`, **not** in `Init` or `Mathlib.Data.Nat.Digits.Defs` directly (relying solely on whether `Digits.Defs` transitively imports `Iterate` through `Mathlib.Tactic.Ring` in `v4.34.1`). Moreover, `Nat.iterate` reduces `(ecaStep R)^[n+1] x` definitionally to `(ecaStep R)^[n] (ecaStep R x)` rather than `ecaStep R ((ecaStep R)^[n] x)`.
   - *Fix before freeze:* Explicitly add `import Mathlib.Logic.Function.Iterate` alongside `import Mathlib.Data.Nat.Digits.Defs` (or define `ecaOrbit` directly by `Nat` recursion: `| 0 => singleSeed | n + 1 => ecaStep R (ecaOrbit R n)`, which removes the `Iterate` dependency and makes step unfolding definitional).

2. **Hazard S2 — `noncomputable def a036987` via `open Classical` (`SCREEN-DOSSIER.md` lines 375–377) [SOUND, WITH AXIOM & SANITY-CHECK IMPLICATIONS]:**
   - *Finding:* `open Classical in if ∃ m : Nat, n = 2 ^ m - 1 then 1 else 0` is syntactically valid in Lean 4 (`Classical.propDecidable` is in core `Init`) and source-faithful to `%F A036987` (`a(n)=1 iff n = 2^m - 1`, with zero `Nat` subtraction bug because $2^m \ge 1$ for all `m : Nat`, including $2^0 - 1 = 0$).
   - *Implications:* (a) `rule126_middle_column_eq_a036987` will legitimately depend on `Classical.choice` (permitted by `axiom_allowlist`); (b) `#eval` and `decide` **cannot** evaluate `a036987` on numerals during pre-freeze testing (sanity-check `ecaOrbit 126 n 0`, `a267442 n`, and `a043545 n` via `#eval`, and unfold `a036987` in proofs via `simp only [a036987]; split_ifs`). Do **not** replace `a036987` with `!(n &&& (n + 1) != 0)` in the statement file, as that would substitute a secondary `%o` bit-hack for the primary `2^m - 1` characterization.

3. **Hazard S3 — `def a043545` `foldl` definition at $n = 0$ and on little-endian digits (`SCREEN-DOSSIER.md` lines 380–383) [SEMANTICALLY EXACT, PROOF-ERGONOMICS NOTE]:**
   - *Finding:* In Mathlib4, `Nat.digits 2 0 = []` (`Nat.digits_zero`), so line 382 (`| [] => 0`) returns `a043545 0 = 0`, matching `%S A043545` (`0, 0, 1, 0, ...`). For $n > 0$, `Nat.digits 2 n` is non-empty (`Nat.digits_ne_nil_iff_ne_zero`) and returns bits **little-endian** (`n % 2` first, MSB `1` last). Because `max` and `min` are commutative, associative, and idempotent on `Nat`, `ds.foldl max d` and `ds.foldl min d` match the true digit maximum and minimum for every $n > 0$ (hand-checked at $n = 1 \to [1] \mapsto 0$, $n = 2 \to [0,1] \mapsto 1$, $n = 3 \to [1,1] \mapsto 0$, $n = 4 \to [0,0,1] \mapsto 1$, $n = 5 \to [1,0,1] \mapsto 1$, $n = 6 \to [0,1,1] \mapsto 1$), and `ds.foldl min d ≤ ds.foldl max d` prevents `Nat` subtraction underflow. Note also that `a267442_eq_a043545` assumes `0 < n`, so the `[]` branch is never even exercised by Mathar's theorem (though keeping `a043545 0 = 0` correct preserves offset-0 sequence fidelity).

4. **Hazard S4 — `ecaRule` `Nat.testBit` encoding vs Wolfram bit order (`SCREEN-DOSSIER.md` lines 355–360) [VERIFIED EXACT]:**
   - *Finding:* Verified against `Init.Data.Nat.Bitwise.Basic` (`m.testBit n = (1 &&& m >>> n != 0)`): `testBit 0` reads LSB $2^0$ and `testBit 7` reads $2^7$, while `false.toNat = 0`, `true.toNat = 1`. In `ecaStep`, `p = c (x - 1)` (left, weight `4`), `q = c x` (center, weight `2`), `r = c (x + 1)` (right, weight `1`) match Wolfram's exact convention $f_R(p, q, r) = b_{4p + 2q + r}(R)$ (verified on asymmetric Rule 2 as well as amphichiral Rules 126 and 129). Because $4p + 2q + r \le 7$, bits $\ge 8$ of `R` are never queried.

5. **Hazard S5 — `bv_decide` axiom-leak trap under Lean `v4.34.1` (`SCREEN-DOSSIER.md` lines 322–327) [PROOF-LANE GUARDRAIL]:**
   - *Finding:* In Lean 4 (`> v4.28.0`, including target `v4.34.1`), `bv_decide` and `decide +native` emit `Lean.ofReduceBool` and per-computation native axioms (`ValidatingProofs` reference manual), which **violate** `ofReduceBool: forbidden` and `custom_axioms: forbidden`. Proof lanes must discharge finite 3-bit `Bool` lemmas (`Lemma A1`, `C0`, `C1`) via `cases p <;> cases q <;> cases r <;> rfl` (or kernel `decide`), **never** `bv_decide` or `native_decide`.

---

## 4. What This Audit Does NOT Show

1. **An audit of a strategy sketch is NOT a complete proof and NOT a Lean 4 verification:** Verifying the case splits, floor/parity identities, and truncated-subtraction guards of Route A on paper and across the $n = 0 \dots 6$ simulation table (`Tables 1A–1B`) shows that the strategy is mathematically viable after applying the documented Lean repairs (`Repairs A2-1..3`, `A3-1..2`), **not** that a machine-checked proof exists. Only a clean `lake build` + `#print axioms` check on `derekblair/math-proofs` with zero `sorry`s and axioms restricted to `[propext, Classical.choice, Quot.sound]` establishes a formal proof.
2. **No Lean compiler or `lake` build was executed on the statement file:** Under this lane's `RESEARCH ONLY` rules (no coding, no repo writes, no GitHub writes), `Mathproofs/Rule129MiddleColumn.lean` was audited analytically against Lean 4 core (`Init.Data.Nat.Bitwise.Basic`) and Mathlib4 (`Mathlib.Data.Nat.Digits.Defs`, `Mathlib.Logic.Function.Iterate`, `Mathlib.Data.Nat.Choose.Lucas`) documentation. Exact elaboration against `derekblair/math-proofs`'s pinned `leanprover/lean4:v4.34.1` toolchain must be verified by the coordinator at pin-freeze time.
3. **This dossier does NOT freeze the pin manifest:** The manifest in `SCREEN-DOSSIER.md` §5.1 remains `DRAFT`. A coordinator must apply all 7 pre-freeze changes in §3.2, resolve Hazard S1 (`import Mathlib.Logic.Function.Iterate` or recursive `ecaOrbit`), commit the statement file, and record `sha256` and `commit` in `~/workspace/math-fleet/pins/a267442-eq-a043545.md` before any proof lane launches.
4. **Prior-art confirmation is bounded by reachable public corpora:** Re-verifying live OEIS `/internal` records and web/literature indices confirms no published mathematical proof or proof-assistant formalization was found, but cannot certify absence from unindexed offline manuscripts, lecture exercises, or theses.
5. **Closed-form invariance is single-ON-seed specific:** While the complementation law $F_{129}^n(c_0) = \overline{F_{126}^n(c_0)}$ ($n \ge 1$) proved in §2.2 holds for *every* initial configuration $c_0 : \mathbb{Z} \to \{0, 1\}$, the binomial-parity closed form $B(n, x)$ in Lemma A2 and the `A036987` / `A043545` middle-column theorems hold strictly for `singleSeed` (`c_0(x) = \mathbf{1}_{x=0}`).

DOSSIER COMPLETE
