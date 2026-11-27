# PROOF — Refutation of C064 (OEIS `A115861` / `A391736`) via Carry-Automaton Decision and Certificate

## 1. Theorem Statement

Let $\otimes : \mathbb{N} \times \mathbb{N} \to \mathbb{N}$ denote carryless base-2 multiplication (`OEIS A048720`), defined by polynomial multiplication over $\mathbb{F}_2[X]$ evaluated in binary:
$$a \otimes 0 = 0, \qquad a \otimes (2k) = 2(a \otimes k), \qquad a \otimes (2k + 1) = (2(a \otimes k)) \oplus a,$$
where $\oplus$ denotes bitwise XOR. For $n \ge 1$, define:
$$Q(n) = \{ m \in \mathbb{N} \mid \exists i \ge 1,\; i \text{ odd},\; m \cdot i = n \otimes i \},$$
the set of distinct values occurring on row $n$ of `OEIS A391736`, and
$$Q_{\le n^3}(n) = \{ m \in \{1, \dots, n-1\} \mid \exists i \in \{1, \dots, n^3\},\; m \cdot i = n \otimes i \}, \qquad \mathrm{A115861}(n) = |Q_{\le n^3}(n)|.$$

**Theorem 1 (Refutation of C064 / `OEIS A391736` `%C`).**
1. *(Minimal Counterexample Witness)* For $n = 239$, $m = 215$, and $i = 302{,}775{,}165$:
   - $1 \le 215 < 239$, $i$ is odd, and $i = 302{,}775{,}165 > 13{,}651{,}919 = 239^3$;
   - $215 \cdot 302{,}775{,}165 = 65{,}096{,}660{,}475 = 239 \otimes 302{,}775{,}165$;
   - **No** integer $i' \in \{1, \dots, 2^{28} - 1\}$ (and in particular no $i' \in \{1, \dots, 239^3\}$) satisfies $215 \cdot i' = 239 \otimes i'$.
2. *(Cardinality Refutation)* For every $n \ge 1$, $|Q(n)| \ge 1 + \mathrm{A115861}(n)$, and at $n = 239$ the inequality is strict:
   $$1 + \mathrm{A115861}(239) = 4 < 5 = |Q(239)|.$$
   Hence Karttunen's conjecture on `A391736` (`|Q(n)| = 1 + A115861(n)` for all $n \ge 1$) is **FALSE**.
3. *(Refutation of `%F A115861`)* Under the published $n^3$-truncated definition of `A115861`, the formula $\mathrm{A115861}(2n) = \mathrm{A115861}(n)$ is **FALSE**: at $n = 478$,
   $$\mathrm{A115861}(478) = 3 < 4 = \mathrm{A115861}(956).$$

**Theorem 2 (Exact Carry-Automaton Decidability).**
For every odd $n \ge 1$ and odd $m \in \{1, \dots, n-1\}$, write $d = \lfloor \log_2 n \rfloor$. Let $G_{n, m}$ be the finite directed graph on vertex set
$$V_{n,m} = \{ (S, R) \in \{0, \dots, m-1\} \times \{0, \dots, 2^d - 1\} \mid S \equiv R \pmod 2 \}$$
with directed edges from $(S, R) \in V_{n,m}$ labeled by $b \in \{0, 1\}$ to
$$T_0(S, R) = \bigl(\lfloor S/2 \rfloor,\; \lfloor R/2 \rfloor\bigr), \qquad T_1(S, R) = \bigl(\lfloor (S + m)/2 \rfloor,\; \lfloor (R \oplus n)/2 \rfloor\bigr)$$
whenever the target lies in $V_{n,m}$. Then an odd integer $i = 1 + 2j$ satisfies $m \cdot i = n \otimes i$ if and only if:
- $m \equiv n \pmod 4$ (so the initial state $s_{\mathrm{start}} = ((m-1)/2, (n-1)/2)$ lies in $V_{n,m}$), and
- reading the binary digits of $j$ from LSB to MSB defines a directed walk in $G_{n,m}$ from $s_{\mathrm{start}}$ to an accepting diagonal state $(S, S) \in V_{n,m}$.

Consequently, the existence of an unrestricted solution $i \ge 1$ to $m \cdot i = n \otimes i$ is **finitely decidable** in $O(m \cdot 2^d) = O(n^2)$ time by BFS on $G_{n,m}$, and every solvable pair $(n, m)$ admits a solution with $i_{\min}(n, m) < 2^{|V_{n,m}|} \le 2^{n^2/2}$. This resolves Karttunen's Dec 15 2025 well-definedness question on `A115861`.

## 2. Construction and Proof of the Carry-Automaton Equations

Consider the generalized carry equation for arbitrary $n, m, S, R, i \in \mathbb{N}$:
$$S + m \cdot i = R \oplus (n \otimes i). \tag{$\star$}$$

- **Base case ($i = 0$):** Since $n \otimes 0 = 0$, $(\star)$ reduces immediately to $S = R$.
- **Parity invariant (for odd $n, m$):** Reducing $(\star)$ modulo $2$ gives $(S + i) \equiv (R + i) \pmod 2$ (as $(n \otimes i) \equiv n \cdot i \equiv i \pmod 2$), hence $S \equiv R \pmod 2$.
- **Even step ($i = 2j$):** Since $n \otimes (2j) = 2(n \otimes j)$, dividing $(\star)$ by $2$ yields
  $$\lfloor S/2 \rfloor + m \cdot j = \lfloor R/2 \rfloor \oplus (n \otimes j).$$
- **Odd step ($i = 2j + 1$):** Since $R \oplus ((2(n \otimes j)) \oplus n) = (R \oplus n) \oplus (2(n \otimes j))$, dividing $(\star)$ by $2$ yields
  $$\lfloor (S + m)/2 \rfloor + m \cdot j = \lfloor (R \oplus n)/2 \rfloor \oplus (n \otimes j).$$

Starting from $m \cdot i = n \otimes i$ with odd $i = 2j + 1$ corresponds to $(S, R) = (0, 0)$ with the odd step, landing at $s_{\mathrm{start}} = ((m-1)/2, (n-1)/2)$ with remaining multiplier $j$. If $(S, R)$ satisfies $S < m$ and $R < 2^d$ (where $2^d \le n < 2^{d+1}$), then $\lfloor (S+m)/2 \rfloor < m$ and $\lfloor (R \oplus n)/2 \rfloor < 2^d$, so $V_{n,m}$ is closed under both transitions. Conversely, any walk of length $t$ from $s_{\mathrm{start}}$ to $(S, S)$ reading bits $b_1, \dots, b_t$ yields $i = 1 + \sum_{k=1}^t b_k 2^k$ solving $m \cdot i = n \otimes i$.

For doubling (`A115861(478) < A115861(956)`): because $(2a) \otimes b = 2(a \otimes b)$, the injective map $x \mapsto 2x$ maps $Q_{\le 478^3}(478)$ into $Q_{\le 956^3}(956)$. At $y = 860 = 4 \cdot 215 < 956$:
- $860 \in Q_{\le 956^3}(956)$ via $i = 302{,}775{,}165 \le 873{,}722{,}816 = 956^3$ (as $860 \cdot i = 4(215 \cdot i) = 4(239 \otimes i) = 956 \otimes i$);
- $860 \notin 2 \cdot Q_{\le 478^3}(478)$, since $430 \in Q_{\le 478^3}(478)$ would give $i \in [1, 478^3]$ with $430 \cdot i = 478 \otimes i$, hence $215 \cdot i = 239 \otimes i$ with $i \le 478^3 = 109{,}215{,}352 < 2^{28}$, impossible.

## 3. Enumeration and Search Summary

Three independent search/verification engines were executed:
1. **Direct hardware-accelerated C scan (`search_c064.c`):** Uses x86-64 `PCLMULQDQ` (self-tested against scalar XOR-convolution on 40,000 pairs) + OpenMP across 16 cores. Verified an exact 105/105 match with OEIS `A115861(1..105)` in 0.007s; scanned $n = 1 \dots 100$ up to $n^4$ in 0.187s (0 witnesses); scanned $n = 1 \dots 239$ up to $n^4$ in 12.565s, finding the unique witness $(n, m, i) = (239, 215, 302{,}775{,}165)$ with both hardware and scalar carryless products equal to $65{,}096{,}660{,}475$.
2. **Exact carry-automaton BFS (`automaton_c064.c`):** Validated 105/105 against OEIS `A115861(1..105)`. Executed exhaustively over all odd $n \le 3000$ and all odd $m < n$ (unbounded $i \in \mathbb{N}$) in 31.143s on 16 cores. Discovered **384 exact counterexample pairs** across **282 distinct odd $n \le 3000$**:
   - Exceeding $n^3$: 384 pairs, smallest $n = 239$ ($m = 215$, $i_{\min} = 302{,}775{,}165$, $\log_n i_{\min} = 3.566$).
   - Exceeding $n^4$: 136 pairs, smallest $n = 391$ ($m = 367$, $i_{\min} = 186{,}185{,}132{,}365$, $\log_n i_{\min} = 4.348$).
   - Exceeding $n^5$: 42 pairs, smallest $n = 511$ ($m = 507$, $i_{\min} = 35{,}400{,}328{,}149{,}431$, $\log_n i_{\min} = 5.003$).
   - Exceeding $n^6$: 14 pairs, smallest $n = 991$ ($m = 807$, $i_{\min} = 5{,}439{,}165{,}481{,}431{,}352{,}125$, $\log_n i_{\min} = 6.253$).
   - Exceeding $n^7$: 3 pairs, smallest $n = 1775$ ($m = 751$, $i_{\min} = 261{,}340{,}756{,}356{,}961{,}818{,}838{,}785$, $\log_n i_{\min} = 7.207$); record exponent $\log_{2047} i_{\min} = 7.917$ at $(2047, 1895)$ with 88-bit $i_{\min} = 163{,}466{,}888{,}608{,}393{,}950{,}098{,}955{,}045$.
   - Since even $n = 2^k n_0$ has identical solutions $i$ with larger cube bound $(2^k n_0)^3 = 8^k n_0^3 \ge n_0^3$, $n = 239$ is provably the smallest counterexample in all of $\mathbb{N}$.
3. **Independent exact Python verifier (`verify_counterexample.py`):** Replays two independent carryless-multiply algorithms (bitwise shift-XOR and explicit $\mathbb{F}_2[X]$ polynomial convolution), exhaustively scans all odd $i \in [1, 239^3]$ in Python (finding $Q_{\le 239^3}(239) = \{91, 139, 203\}$ at $i = 31, 23, 631$), and independently replays the carry-automaton BFS on row $n = 239$ and 6 secondary witnesses (all checks PASS in 2.79s).

## 4. Certificate

The formal Lean 4 refutation uses two tiny, 100% kernel-checked certificates (zero `native_decide`, zero `ofReduceBool`):
1. **73-state carry-automaton reachability certificate (`certRows` in `Solution.lean`):**
   Starting from $(S, R) = (107, 119)$ at BFS layer $0$ for $(n = 239, m = 215)$, the entire reachable subgraph through layer $27$ comprises **only 73 states** (out of $215 \times 128 = 27{,}520$ possible states; only 86 states are reachable at all!). Every state in layers $0 \dots 27$ satisfies $S \ne R$, and every parity-valid transition out of layers $0 \dots 26$ lands in an explicitly indexed row of `certRows` at layer $\le k + 1$. The first accepting diagonal state is $(121, 121)$ at layer $28$, corresponding to bit-length $29$ and $i_{\min} = 302{,}775{,}165 = \mathtt{0b10010000010111111101101111101}_2$. By strong induction on $j$, no state at layer $k \le 27$ admits a solution with $j < 2^{27 - k}$, proving unconditionally that **no** $i \in [1, 2^{28})$ satisfies $215 \cdot i = 239 \otimes i$.
2. **29-step verified carryless multiplication chain (`chain_239`):**
   Records all 29 prefix products $(b_t, 239 \otimes b_t)$ from $(1, 239)$ to $(302{,}775{,}165, 65{,}096{,}660{,}475)$, checked in the Lean kernel by `rfl` via flat 9-bit GMP arithmetic (`xor9`), alongside verified chains `chain_391` (38 steps, $> 391^4$) and `chain_511` (46 steps, $> 511^5$).

## 5. Literature and Priority Search

Live retrieval on `2026-11-27T02:46Z` (`2026-11-26 18:46 PST`) confirmed:
- OEIS `A115861` (rev `#25`, Dec 19 2025 12:40:27) lists Karttunen's open question verbatim: *"Using n^3 as the upper search limit reproduced the original 102 initial terms. I don't know whether using larger values, like n^4 or n^5 would increase the values of some terms."*
- OEIS `A391736` (rev `#11`, Dec 18 2025 22:24:35) lists the conjecture verbatim: *"The number of distinct values that may occur on row n of this array is at least 1+A115861(n), and at most n, because A(n, k) <= n. We conjecture that 1+A115861(n) gives the exact value."*
- Related OEIS entries `A048720`, `A391735`, `A115859`, `A115869`, `A115871`, `A115872`, `A391725`, `A391726`, `A391572`, `A391573` and targeted web queries across arXiv, MathOverflow, Math StackExchange, and GitHub showed no prior refutation, counterexample, or carry-automaton decision procedure for this conjecture.
